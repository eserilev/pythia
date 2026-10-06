import SpecLean.Layer4.DecLemmas

/-!
# Layer 4 spike: the simulation invariant

`SInv fp h0 h vs s L` relates a state `s` of the denotation to the interpreter's heap `h` and
locals `L`, for a run that started at heap `h0` with arguments `vs`:

- each argument decodes to its tree in `s`;
- each local holds the same flat value, or the reference at its place;
- `WTree` over `fp` at the start, and every heap path to a reference is as at the start;
- the frame and the fresh-address rules of SPEC 9.2 hold from `h0` to `h`.

`write_inv` is the step that needs `WTree`: a write of a flat value through a place keeps the
invariant, because the written object has one path from the arguments.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode SpecLean.Validation.Where

/-- A denotation result and an interpreter value agree. -/
def ERel (h : Heap) (vs : List Value) : DRes → Value → Prop
  | .val v, w => w = v ∧ Flat v = true
  | .place k p, w => ∃ a, w = .ref a ∧ at? h vs k p = some (.ref a)
  | .tree d, w => (∃ n, dec h n w = some d) ∧
      ∀ q a, follow h w q = some (.ref a) → ∀ k p, at? h vs k p ≠ some (.ref a)

def LRel (h : Heap) (vs : List Value) : Option DRes → Option Value → Prop
  | none, none => True
  | some r, some w => ERel h vs r w
  | _, _ => False

/-- The part of the invariant that reads need. -/
structure RInv (h : Heap) (vs : List Value) (s : DSt) (L : Locals) : Prop where
  len : s.roots.length = vs.length
  roots : ∀ (k : Nat) (v : Value) (d : DV), vs[k]? = some v → s.roots[k]? = some d → ∃ n, dec h n v = some d
  loc : ∀ x, LRel h vs (s.loc x) (L x)

structure SInv (fp : Footprint) (h0 h : Heap) (vs : List Value) (s : DSt) (L : Locals) : Prop where
  r : RInv h vs s L
  wt : WTree h0 vs fp
  refs : ∀ k q b, at? h vs k q = some (.ref b) ↔ at? h0 vs k q = some (.ref b)
  rty : ∀ k ty, RootTy h vs k ty ↔ RootTy h0 vs k ty
  frame : Frame h0 h vs fp
  fresh : Fresh h0 h

theorem matchesB_iff : ∀ (ps : List PStep) (qs : List Nat), matchesB ps qs = true ↔ Matches ps qs
  | [], [] => by simp [matchesB, Matches]
  | [], _ :: _ => by simp [matchesB, Matches]
  | .exact _ :: _, [] => by simp [matchesB, Matches]
  | .any :: _, [] => by simp [matchesB, Matches]
  | .exact i :: ps, j :: qs => by simp [matchesB, Matches, matchesB_iff ps qs]
  | .any :: ps, _ :: qs => by simp [matchesB, Matches, matchesB_iff ps qs]

theorem at?_some {h : Heap} {vs : List Value} {k : Nat} {p : List Nat} {w : Value}
    (e : at? h vs k p = some w) : ∃ v, vs[k]? = some v ∧ follow h v p = some w := by
  unfold at? at e
  cases hv : vs[k]? with
  | none => simp [hv] at e
  | some v => exact ⟨v, rfl, by simpa [hv] using e⟩

/-- The tree at a place decodes from the object there. -/
theorem deref_dec {h : Heap} {vs : List Value} {s : DSt} {L : Locals} (hr : RInv h vs s L)
    {k : Nat} {p : List Nat} {w : Value} {d : DV} (hat : at? h vs k p = some w)
    (hd : s.deref k p = some d) : ∃ n, dec h n w = some d := by
  obtain ⟨v, hv, hf⟩ := at?_some hat
  unfold DSt.deref at hd
  cases hrk : s.roots[k]? with
  | none => simp [hrk] at hd
  | some d0 =>
    simp only [hrk, Option.bind_some] at hd
    obtain ⟨n, hn⟩ := hr.roots k v d0 hv hrk
    obtain ⟨m, d', h1, h2⟩ := dec_sub p n v w d0 hn hf
    rw [hd] at h1; cases h1
    exact ⟨m, h2⟩

/-- A child of the object at a place: its leaf value, or the reference one step further. -/
theorem child_rel {h : Heap} {vs : List Value} {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) {xs : List Value} (hk : okids (h.objs a) = some xs)
    {i m : Nat} {x : Value} (hx : xs[i]? = some x) {c : DV} (hc : dec h m x = some c) :
    ERel h vs (ofChild k (p ++ [i]) c) x := by
  by_cases hl : ∃ u, c = .leaf u
  · obtain ⟨u, rfl⟩ := hl
    obtain ⟨rfl, hu⟩ := dec_leaf hc
    exact ⟨rfl, hu⟩
  · obtain ⟨b, -, -, rfl, -, -, -⟩ := dec_node hc (fun u e => hl ⟨u, e⟩)
    have hof : ofChild k (p ++ [i]) c = .place k (p ++ [i]) := by
      cases c with
      | leaf u => exact absurd ⟨u, rfl⟩ hl
      | _ => rfl
    rw [hof]
    refine ⟨b, rfl, ?_⟩
    obtain ⟨v, hv, hf⟩ := at?_some hat
    simp only [at?, hv, Option.bind_some, follow_append, hf]
    rw [follow_ref_cons, hk]; simp [hx, follow]

theorem flat_refEq {x y : Value} (hx : Flat x = true) (hy : Flat y = true) : RefEq x y :=
  fun b => ⟨fun e => absurd e (flat_nonref hx b), fun e => absurd e (flat_nonref hy b)⟩

/-- Replacing a flat child by a flat value keeps the shape. -/
theorem skel_setChild {o : HeapObj} {xs : List Value} (hk : okids (some o) = some xs) {i : Nat}
    {x u : Value} (hx : xs[i]? = some x) (hxf : Flat x = true) (hu : Flat u = true) :
    SameSkel o (o.setChild i u) := by
  have key : ∀ (j : Nat) y z, xs[j]? = some y → (xs.set i u)[j]? = some z → RefEq y z := by
    intro j y z hy hz
    rw [List.getElem?_set] at hz
    by_cases hij : i = j
    · subst hij
      rw [hx] at hy; cases hy
      have hlt := (List.getElem?_eq_some_iff.mp hx).1
      simp [hlt] at hz; subst hz
      exact flat_refEq hxf hu
    · simp only [hij, if_false, hy, Option.some.injEq] at hz; subst hz; exact RefEq.refl _
  cases o with
  | container ty fs =>
    simp [okids] at hk; subst hk
    exact ⟨rfl, by simp, key⟩
  | list k e l ys =>
    simp [okids] at hk; subst hk
    exact ⟨rfl, rfl, rfl, by simp, key⟩
  | _ => simp [okids] at hk

theorem rootTy_of_dec {h : Heap} {vs : List Value} {k : Nat} {v : Value} (hv : vs[k]? = some v)
    {n : Nat} {ty : Name} {ds : List DV} (hd : dec h n v = some (.cont ty ds)) :
    RootTy h vs k ty := by
  obtain ⟨a, m, fs, rfl, -, ho, -⟩ := dec_cont hd
  exact ⟨a, fs, hv, ho⟩

/-- The written object is at a footprint path, and under `WTree` it has no other path. -/
theorem fp_unique {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : SInv fp h0 h vs s L) {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) (hfp : fpOk fp s.roots k p = true) :
    AtFp h vs fp a ∧ ∀ k' q', at? h vs k' q' = some (.ref a) → k' = k ∧ q' = p := by
  unfold fpOk at hfp
  obtain ⟨pat, hpat, hb⟩ := List.any_eq_true.mp hfp
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hroot, hm⟩ := hb
  rw [matchesB_iff] at hm
  obtain ⟨v, hv, -⟩ := at?_some hat
  have hty : RootTy h vs k pat.ty := by
    cases hrk : s.roots[k]? with
    | none => simp [hrk, rootIs] at hroot
    | some d =>
      rw [hrk] at hroot
      cases d with
      | cont ty ds =>
        simp [rootIs] at hroot; subst hroot
        obtain ⟨n, hn⟩ := hI.r.roots k v _ hv hrk
        exact rootTy_of_dec hv hn
      | _ => simp [rootIs] at hroot
  refine ⟨⟨k, pat, p, hpat, hty, hm, hat⟩, fun k' q' e => ?_⟩
  exact hI.wt k pat hpat ((hI.rty k _).mp hty) p hm a ((hI.refs k p a).mp hat) k' q'
    ((hI.refs k' q' a).mp e)

/-- A write of a flat value through a place keeps the invariant. -/
theorem write_inv {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : SInv fp h0 h vs s L) {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) {d : DV} (hroot : s.roots[k]? = some d) {i : Nat}
    {u : Value} (hu : Flat u = true) (hfp : fpOk fp s.roots k p = true)
    (hleaf : leafAt d p i = true) {o : HeapObj} (ho : h.objs a = some o) :
    SInv fp h0 (h.set a (o.setChild i u)) vs
      { s with roots := s.roots.set k (updAt p d i (.leaf u)) } L := by
  obtain ⟨v0, hv0, hf0⟩ := at?_some hat
  obtain ⟨n, hn⟩ := hI.r.roots k v0 d hv0 hroot
  -- The old child is flat.
  unfold leafAt at hleaf
  cases hsub : subAt p d with
  | none => simp [hsub] at hleaf
  | some nd =>
  simp only [hsub] at hleaf
  cases hki : nd.kids[i]? with
  | none => simp [hki] at hleaf
  | some c =>
  simp only [hki] at hleaf
  cases c with
  | cont _ _ => simp at hleaf
  | list _ _ _ _ => simp at hleaf
  | leaf w =>
  obtain ⟨m, d', h1, h2⟩ := dec_sub p n v0 (.ref a) d hn hf0
  rw [hsub] at h1; cases h1
  obtain ⟨a', m', xs, e, -, hk, hm⟩ := dec_node h2 (fun u e => by subst e; simp [DV.kids] at hki)
  cases e
  obtain ⟨x, hx, hdx⟩ := mapM_get hm hki
  obtain ⟨rfl, hwf⟩ := dec_leaf hdx
  rw [ho] at hk
  have skel := skel_setChild hk hx hwf hu
  obtain ⟨hatfp, huniq⟩ := fp_unique hI hat hfp
  -- The new heap and the old heap have the same paths to references.
  have hset : ∀ k' q b, at? (h.set a (o.setChild i u)) vs k' q = some (.ref b) ↔
      at? h vs k' q = some (.ref b) := fun k' q b => at?_skel ho skel vs k' q b
  refine ⟨⟨by simp [hI.r.len], ?_, ?_⟩, hI.wt, ?_, ?_, ?_, ?_⟩
  · intro k' v' d'' hv' hd''
    simp only [List.getElem?_set] at hd''
    by_cases hkk : k = k'
    · subst hkk
      rw [hv0] at hv'; cases hv'
      have hlt : k < s.roots.length := (List.getElem?_eq_some_iff.mp hroot).1
      simp [hlt] at hd''; subst hd''
      refine ⟨n, dec_at ho i hu p n v0 d hn fun q => ⟨fun e => ?_, fun e => by subst e; exact hf0⟩⟩
      exact (huniq k q (by simp [at?, hv0, e])).2
    · simp only [hkk, if_false] at hd''
      obtain ⟨n', hn'⟩ := hI.r.roots k' v' d'' hv' hd''
      refine ⟨n', ?_⟩
      rw [dec_away _ n' v' fun q e => hkk (huniq k' q (by simp [at?, hv', e])).1.symm]
      exact hn'
  · intro x
    have := hI.r.loc x
    revert this
    cases s.loc x with
    | none => cases L x <;> simp [LRel]
    | some r =>
      cases L x with
      | none => simp [LRel]
      | some w =>
        cases r with
        | val v => simp [LRel, ERel]
        | place k2 p2 =>
          simp only [LRel, ERel]
          rintro ⟨b, rfl, hb⟩
          exact ⟨b, rfl, (hset k2 p2 b).mpr hb⟩
        | tree dt =>
          simp only [LRel, ERel]
          rintro ⟨⟨nt, hnt⟩, hdj⟩
          refine ⟨⟨nt, (dec_away _ nt w (fun q e => hdj q a e k p hat)).trans hnt⟩,
            fun q b e k2 p2 e2 => ?_⟩
          exact hdj q b ((follow_skel ho skel q w w (RefEq.refl w) b).mp e) k2 p2 ((hset k2 p2 b).mp e2)
  · intro k' q b; rw [hset]; exact hI.refs k' q b
  · intro k' ty; rw [rootTy_skel ho skel]; exact hI.rty k' ty
  · refine Frame_trans hI.frame (Frame_set hatfp) fun a2 ⟨k2, pat, q, hp, hty, hmq, hq⟩ => ?_
    exact ⟨k2, pat, q, hp, (hI.rty k2 _).mp hty, hmq, (hI.refs k2 q a2).mp hq⟩
  · exact Fresh_trans hI.fresh (Fresh_set ho)

variable [LibModel]

/-- A new local keeps the invariant. -/
theorem setLoc_inv {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : SInv fp h0 h vs s L) (x : Name) {r : DRes} {w : Value} (hr : ERel h vs r w) :
    SInv fp h0 h vs { s with loc := setLoc s.loc x r } (L.set x w) := by
  refine ⟨⟨hI.r.len, hI.r.roots, fun y => ?_⟩, hI.wt, hI.refs, hI.rty, hI.frame, hI.fresh⟩
  simp only [setLoc, Locals.set_apply]
  split
  · exact hr
  · exact hI.r.loc y

end SpecLean.Layer4
