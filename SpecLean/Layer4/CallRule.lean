import SpecLean.Layer4.Skel
import SpecLean.Layer4.Fn

/-!
# Layer 4: the call rule

`CInv` is `SInv` with two more facts: the run kept the shape of the heap (`Skel`), and a run
with an empty footprint left the heap as it was.

`call_rule`: at a call that writes through its one place argument `(k, p)`,

- the callee's `WTree` over its own footprint follows from the caller's `WTree` and the check
  `coversAll`: every callee footprint path is a caller footprint path below `p`, and the other
  arguments are flat;
- after the callee, the caller's invariant holds again with the callee's tree of the argument
  put in at `p` (`dec_graft`). The callee changes only objects at its footprint paths, so only
  objects below `p`, each with one caller path.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode SpecLean.Validation.Where

structure CInv (fp : Footprint) (h0 h : Heap) (vs : List Value) (s : DSt) (L : Locals) :
    Prop where
  i : SInv fp h0 h vs s L
  skel : Skel h0 h
  ro : fp = [] → h = h0

theorem CInv.start {fp : Footprint} {h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hr : RInv h vs s L) (hw : WTree h vs fp) : CInv fp h h vs s L :=
  ⟨⟨hr, hw, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, Frame_refl h vs fp, Fresh_refl h⟩,
    Skel_refl h, fun _ => rfl⟩

/-- The written object keeps its shape. -/
theorem write_skel {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : SInv fp h0 h vs s L) {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) {d : DV} (hroot : s.roots[k]? = some d) {i : Nat}
    {u : Value} (hu : Flat u = true) (hleaf : leafAt d p i = true) {o : HeapObj}
    (ho : h.objs a = some o) : SameSkel o (o.setChild i u) := by
  obtain ⟨v0, hv0, hf0⟩ := at?_some hat
  obtain ⟨n, hn⟩ := hI.r.roots k v0 d hv0 hroot
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
  exact skel_setChild hk hx hwf hu

theorem fpOk_ne {fp : Footprint} {roots : List DV} {k : Nat} {p : List Nat}
    (h : fpOk fp roots k p = true) : fp ≠ [] := by
  intro e; subst e; simp [fpOk] at h

theorem write_cinv {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) {d : DV} (hroot : s.roots[k]? = some d) {i : Nat}
    {u : Value} (hu : Flat u = true) (hfp : fpOk fp s.roots k p = true)
    (hleaf : leafAt d p i = true) {o : HeapObj} (ho : h.objs a = some o) :
    CInv fp h0 (h.set a (o.setChild i u)) vs
      { s with roots := s.roots.set k (updAt p d i (.leaf u)) } L :=
  ⟨write_inv hI.i hat hroot hu hfp hleaf ho,
    Skel_trans hI.skel (Skel_set ho (write_skel hI.i hat hroot hu hleaf ho)),
    fun e => absurd e (fpOk_ne hfp)⟩

/-! ## Results -/

variable [LibModel]

def CStmtOK (fp : Footprint) (h0 : Heap) (vs : List Value) :
    Res (Outcome × DSt) → Res (Outcome × Locals × Heap) → Prop
  | .ok (o, s'), .ok (o', L', h') => o' = o ∧ CInv fp h0 h' vs s' L'
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

/-- A statement-level expression: the value, and the invariant with the new trees. -/
def CallOK (fp : Footprint) (h0 : Heap) (vs : List Value) (s : DSt) (L : Locals) :
    Res (DRes × List DV) → Res (Value × Heap) → Prop
  | .ok (r, rs), .ok (w, h') => ERel h' vs r w ∧ CInv fp h0 h' vs { s with roots := rs } L
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

/-- The contract of a function body. -/
def FnRel (fp : Footprint) (h : Heap) (vs : List Value) :
    Res (Value × List DV) → Res (Value × Heap) → Prop
  | .ok (v, rs), .ok (w, h') =>
    w = v ∧ DecArgs h' vs rs ∧ Frame h h' vs fp ∧ Skel h h' ∧ (fp = [] → h' = h)
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem cstmtOK_err {fp : Footprint} {h0 : Heap} {vs : List Value} {e : SpecError}
    (hne : e ≠ .outOfFuel) : CStmtOK fp h0 vs (.error e) (.error e) := ⟨rfl, hne⟩

/-! ## Arguments -/

def ERels (h : Heap) (vs : List Value) : List DRes → List Value → Prop
  | [], [] => True
  | r :: rs, w :: ws => ERel h vs r w ∧ ERels h vs rs ws
  | _, _ => False

theorem ERels_get {h : Heap} {vs : List Value} :
    ∀ {rs : List DRes} {ws : List Value}, ERels h vs rs ws → rs.length = ws.length ∧
      ∀ (j : Nat) r w, rs[j]? = some r → ws[j]? = some w → ERel h vs r w
  | [], [], _ => ⟨rfl, fun j r w hr _ => by simp at hr⟩
  | r :: rs, w :: ws, ⟨h1, h2⟩ => by
    obtain ⟨hl, hp⟩ := ERels_get h2
    refine ⟨by simp [hl], fun j r' w' hr hw => ?_⟩
    cases j with
    | zero => simp at hr hw; subst hr; subst hw; exact h1
    | succ j => exact hp j r' w' (by simpa using hr) (by simpa using hw)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The argument trees decode from the argument values. -/
theorem argRoots_dec {h : Heap} {vs : List Value} {s : DSt} {L : Locals} (hr : RInv h vs s L) :
    ∀ {rs : List DRes} {ws : List Value} {rg : List DV}, ERels h vs rs ws →
      rs.mapM (argRoot s) = some rg → DecArgs h ws rg
  | [], [], rg, _, hm => by simp at hm; subst hm; exact ⟨rfl, fun k v d hv _ => by simp at hv⟩
  | r :: rs, w :: ws, rg, ⟨h1, h2⟩, hm => by
    rw [List.mapM_cons] at hm
    cases hr1 : argRoot s r with
    | none => simp [hr1] at hm
    | some d1 =>
      cases hm2 : rs.mapM (argRoot s) with
      | none => simp [hr1, hm2] at hm
      | some rg' =>
        simp [hr1, hm2] at hm; subst hm
        obtain ⟨hl, hp⟩ := argRoots_dec hr h2 hm2
        refine ⟨by simp [hl], fun k v d hv hd => ?_⟩
        cases k with
        | zero =>
          simp at hv hd; subst hv; subst hd
          cases r with
          | val u => obtain ⟨rfl, hu⟩ := h1; simp [argRoot] at hr1; subst hr1; exact ⟨0, dec_flat hu 0⟩
          | place k p =>
            obtain ⟨a, rfl, hat⟩ := h1
            exact deref_dec hr hat hr1
        | succ k => exact hp k v d (by simpa using hv) (by simpa using hd)
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

theorem onePlace_spec : ∀ {rs : List DRes} {i k : Nat} {p : List Nat},
    onePlace rs = some (i, k, p) → rs[i]? = some (.place k p) ∧
      ∀ (j : Nat) r, rs[j]? = some r → j ≠ i → ∃ v, r = .val v
  | [], _, _, _, h => by simp [onePlace] at h
  | .val v :: rs, i, k, p, h => by
    simp only [onePlace, Option.map_eq_some_iff] at h
    obtain ⟨⟨i', k', p'⟩, h1, h2⟩ := h
    simp at h2; obtain ⟨rfl, rfl, rfl⟩ := h2
    obtain ⟨a1, a2⟩ := onePlace_spec h1
    refine ⟨by simpa using a1, fun j r hr hj => ?_⟩
    cases j with
    | zero => simp at hr; exact ⟨v, hr.symm⟩
    | succ j => exact a2 j r (by simpa using hr) (by omega)
  | .place k' p' :: rs, i, k, p, h => by
    simp only [onePlace] at h
    split at h
    · next hall =>
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun j r hr hj => ?_⟩
      cases j with
      | zero => exact absurd rfl hj
      | succ j =>
        have hm : r ∈ rs := List.mem_of_getElem? (by simpa using hr)
        have := List.all_eq_true.mp hall r hm
        cases r with
        | val v => exact ⟨v, rfl⟩
        | place _ _ => simp at this
    · cases h

/-! ## The call rule -/

section rule

variable {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
  {rs : List DRes} {ws : List Value} {i k : Nat} {p : List Nat} {rg : List DV} {dk dr : DV}
  {fpG : Footprint}

/-- A path of the callee's arguments to a reference is a caller path below `p`. -/
theorem callee_path (hrel : ERels h vs rs ws) (hone : onePlace rs = some (i, k, p))
    {kg : Nat} {q : List Nat} {b : Nat} (hb : at? h ws kg q = some (.ref b)) :
    kg = i ∧ ∃ a, ws[i]? = some (.ref a) ∧ at? h vs k p = some (.ref a) ∧
      at? h vs k (p ++ q) = some (.ref b) := by
  obtain ⟨hl, hp⟩ := ERels_get hrel
  obtain ⟨hi, hother⟩ := onePlace_spec hone
  obtain ⟨wk, hwk, -⟩ := at?_some hb
  have hki : kg = i := by
    refine Classical.byContradiction fun hne => ?_
    have hlt : kg < rs.length := hl ▸ (List.getElem?_eq_some_iff.mp hwk).1
    obtain ⟨v, hv⟩ := hother kg rs[kg] (List.getElem?_eq_getElem hlt) hne
    obtain ⟨rfl, hfl⟩ : wk = v ∧ Flat v = true := by
      have := hp kg rs[kg] wk (List.getElem?_eq_getElem hlt) hwk; rw [hv] at this; exact this
    unfold at? at hb; rw [hwk] at hb
    cases q with
    | nil => simp [follow] at hb; subst hb; simp [Flat] at hfl
    | cons j q => simp [follow_nonref (flat_nonref hfl)] at hb
  subst hki
  have hwi := hp kg (.place k p) wk hi hwk
  obtain ⟨a, rfl, hat⟩ := hwi
  refine ⟨rfl, a, hwk, hat, ?_⟩
  obtain ⟨v0, hv0, hf0⟩ := at?_some hat
  unfold at? at hb ⊢
  rw [hwk] at hb
  simp only [hv0, Option.bind_some, follow_append, hf0]
  simpa using hb

/-- The callee's footprint paths are caller footprint paths, with one caller path each. -/
theorem callee_fp (hI : CInv fp h0 h vs s L) (hrel : ERels h vs rs ws)
    (hone : onePlace rs = some (i, k, p)) (hdk : s.deref k p = some dk)
    (hcov : coversAll fp s.roots k p dk fpG = true)
    {kg : Nat} {pg : FPat} (hpg : pg ∈ fpG) (hty : RootTy h ws kg pg.ty) {q : List Nat}
    (hq : Matches pg.steps q) {b : Nat} (hb : at? h ws kg q = some (.ref b)) :
    kg = i ∧ AtFp h vs fp b ∧
      ∀ k' q', at? h vs k' q' = some (.ref b) → k' = k ∧ q' = p ++ q := by
  obtain ⟨rfl, a, hwi, hat, hpq⟩ := callee_path hrel hone hb
  refine ⟨rfl, ?_⟩
  -- The argument tree has the class of the callee pattern.
  obtain ⟨c, fs, hc, hoc⟩ := hty
  rw [hwi] at hc; cases hc
  obtain ⟨nn, hn⟩ := deref_dec hI.i.r hat hdk
  have hdkty : rootIs pg.ty (some dk) = true := by
    obtain ⟨m, rfl⟩ : ∃ m, nn = m + 1 := by
      cases nn with
      | zero => simp [dec_zero_ref] at hn
      | succ m => exact ⟨m, rfl⟩
    rw [dec_ref_succ, hoc] at hn
    cases hm : fs.mapM (dec h m) with
    | none => simp [hm] at hn
    | some ds => simp [hm] at hn; subst hn; simp [rootIs]
  have hall := List.all_eq_true.mp hcov pg hpg
  simp only [hdkty, Bool.not_true, Bool.false_or] at hall
  obtain ⟨cpat, hcp, hcb⟩ := List.any_eq_true.mp hall
  simp only [Bool.and_eq_true] at hcb
  obtain ⟨hroot, hcov'⟩ := hcb
  have hm := coversB_matches _ _ _ q hcov' hq
  obtain ⟨v0, hv0, -⟩ := at?_some hat
  have hcty : RootTy h vs k cpat.ty := by
    cases hrk : s.roots[k]? with
    | none => simp [hrk, rootIs] at hroot
    | some d =>
      rw [hrk] at hroot
      cases d with
      | cont ty ds =>
        simp [rootIs] at hroot; subst hroot
        obtain ⟨n, hn⟩ := hI.i.r.roots k v0 _ hv0 hrk
        exact rootTy_of_dec hv0 hn
      | _ => simp [rootIs] at hroot
  refine ⟨⟨k, cpat, p ++ q, hcp, hcty, hm, hpq⟩, fun k' q' e => ?_⟩
  exact hI.i.wt k cpat hcp ((hI.i.rty k _).mp hcty) (p ++ q) hm b ((hI.i.refs _ _ b).mp hpq) k' q'
    ((hI.i.refs k' q' b).mp e)

/-- The callee's `WTree`. -/
theorem callee_wtree (hI : CInv fp h0 h vs s L) (hrel : ERels h vs rs ws)
    (hone : onePlace rs = some (i, k, p)) (hdk : s.deref k p = some dk)
    (hcov : coversAll fp s.roots k p dk fpG = true) : WTree h ws fpG := by
  intro kg pg hpg hty q hq b hb k' q' hb'
  obtain ⟨rfl, -, huniq⟩ := callee_fp hI hrel hone hdk hcov hpg hty hq hb
  obtain ⟨rfl, -, -, -, hpq'⟩ := callee_path hrel hone hb'
  obtain ⟨-, e⟩ := huniq k (p ++ q') hpq'
  exact ⟨rfl, List.append_cancel_left e⟩

/-- After the callee, the caller's invariant holds with the callee's tree put in at `p`. -/
theorem call_rule (hI : CInv fp h0 h vs s L) (hrel : ERels h vs rs ws)
    (hone : onePlace rs = some (i, k, p)) (hdk : s.deref k p = some dk)
    (hdr : s.roots[k]? = some dr) (hfpne : fp ≠ [])
    (hcov : coversAll fp s.roots k p dk fpG = true) {h' : Heap} {rg' : List DV} {di : DV}
    (hfr : Frame h h' ws fpG) (hsk : Skel h h') (hda : DecArgs h' ws rg')
    (hdi : rg'[i]? = some di) :
    CInv fp h0 h' vs { s with roots := s.roots.set k (setAt p dr di) } L := by
  obtain ⟨hi, -⟩ := onePlace_spec hone
  obtain ⟨hl, hp⟩ := ERels_get hrel
  obtain ⟨a, hwi, hat⟩ : ∃ a, ws[i]? = some (.ref a) ∧ at? h vs k p = some (.ref a) := by
    have hlt : i < ws.length := hl ▸ (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨a, he, hat⟩ := hp i _ ws[i] hi (List.getElem?_eq_getElem hlt)
    exact ⟨a, by rw [List.getElem?_eq_getElem hlt, he], hat⟩
  -- Every changed object is at a callee footprint path, so below `p` with one caller path.
  have changed : ∀ b, h'.objs b ≠ h.objs b → AtFp h vs fp b ∧ ∃ q,
      ∀ k' q', at? h vs k' q' = some (.ref b) → k' = k ∧ q' = p ++ q := by
    intro b hne
    have hold : h.objs b ≠ none := by
      intro hn
      rcases hsk.2 b with e | ⟨o, -, ho, -, -⟩
      · exact hne e
      · rw [hn] at ho; cases ho
    have hat' : AtFp h ws fpG b := Classical.byContradiction fun hn => hne (hfr b hold hn)
    obtain ⟨kg, pg, q, hpg, hty, hq, hb⟩ := hat'
    obtain ⟨-, hfp, huniq⟩ := callee_fp hI hrel hone hdk hcov hpg hty hq hb
    exact ⟨hfp, q, huniq⟩
  have hset : ∀ k' q b, at? h' vs k' q = some (.ref b) ↔ at? h vs k' q = some (.ref b) :=
    fun k' q b => at?_Skel hsk vs k' q b
  obtain ⟨v0, hv0, hf0⟩ := at?_some hat
  obtain ⟨ddi, hddi⟩ := hda.2 i (.ref a) di hwi hdi
  refine ⟨⟨⟨by simp [hI.i.r.len], fun k' v' d'' hv' hd'' => ?_, fun x => ?_⟩, hI.i.wt, ?_, ?_,
    ?_, ?_⟩, Skel_trans hI.skel hsk, fun e => absurd e hfpne⟩
  · simp only [List.getElem?_set] at hd''
    by_cases hkk : k = k'
    · subst hkk
      rw [hv0] at hv'; cases hv'
      have hlt : k < s.roots.length := (List.getElem?_eq_some_iff.mp hdr).1
      simp [hlt] at hd''; subst hd''
      obtain ⟨n, hn⟩ := hI.i.r.roots k v0 dr hv0 hdr
      refine dec_graft (.ref a) di ddi hddi p n v0 dr hn hf0 fun q b e hne => ?_
      obtain ⟨-, q0, huniq⟩ := changed b hne
      exact ⟨q0, (huniq k q (by simp [at?, hv0, e])).2⟩
    · simp only [hkk, if_false] at hd''
      obtain ⟨n', hn'⟩ := hI.i.r.roots k' v' d'' hv' hd''
      refine ⟨n', ?_⟩
      rw [dec_unchanged n' v' fun q b e => Classical.byContradiction fun hne => ?_]
      · exact hn'
      · obtain ⟨-, q0, huniq⟩ := changed b hne
        exact hkk (huniq k' q (by simp [at?, hv', e])).1.symm
  · have := hI.i.r.loc x
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
  · intro k' q b; rw [hset]; exact hI.i.refs k' q b
  · intro k' ty; rw [rootTy_Skel hsk]; exact hI.i.rty k' ty
  · refine Frame_trans hI.i.frame (fun b hold hn => Classical.byContradiction fun hne =>
      hn (changed b hne).1) fun a2 ⟨k2, pat, q, hp2, hty, hmq, hq⟩ => ?_
    exact ⟨k2, pat, q, hp2, (hI.i.rty k2 _).mp hty, hmq, (hI.i.refs k2 q a2).mp hq⟩
  · exact Fresh_trans hI.i.fresh (Fresh_of_Skel hsk)

end rule

end SpecLean.Layer4
