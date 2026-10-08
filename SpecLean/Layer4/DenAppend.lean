import SpecLean.Layer4.DenExpr

/-!
# Layer 4: `o.append(v)`

The heap after an append: the list object at `a` gets one more item `w` at its end. The list
has one path from the arguments, and `w` reaches only objects at `lo` or above, which neither
the arguments nor the locals reach before. So the run keeps the invariant, with a list that
grows by a new item (`SkelL`).
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode SpecLean.Validation.Where

/-! ## The heap after the append -/

/-- A value that never reaches `a` reads the same after a write to `a`. -/
theorem follow_set_away {h : Heap} {a : Nat} (o : HeapObj) {v : Value} (hv : ∀ q, follow h v q ≠ some (.ref a)) (q : List Nat) :
    follow (h.set a o) v q = follow h v q :=
  follow_unchanged q v fun q' c e => by
    have hc : c ≠ a := fun hc => hv q' (hc ▸ e)
    simp [hc]

/-- A path after the append to an object at `lo` or above goes through the new item. -/
theorem follow_append_split {h : Heap} {a : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} {w : Value} (ho : h.objs a = some (.list k e l xs)) {lo : Nat}
    (hw : ∀ q c, follow h w q = some (.ref c) → lo ≤ c) :
    ∀ (q : List Nat) (v : Value), (∀ q c, follow h v q = some (.ref c) → c < lo) →
      ∀ c, follow (h.set a (.list k e l (xs ++ [w]))) v q = some (.ref c) → lo ≤ c →
        ∃ q0 rest, q = q0 ++ xs.length :: rest ∧ follow h v q0 = some (.ref a) ∧
          follow h w rest = some (.ref c)
  | [], v, hv, c, hf, hc => by
    simp only [follow, Option.some.injEq] at hf; subst hf
    have := hv [] c rfl; omega
  | j :: q, v, hv, c, hf, hc => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      rw [follow_ref_cons] at hf
      by_cases hba : b = a
      · subst hba
        have hal : b < lo := hv [] b rfl
        simp only [Heap.set_objs, if_true, okids, Option.bind_some] at hf
        cases hy : (xs ++ [w])[j]? with
        | none => rw [hy] at hf; cases hf
        | some y =>
          rw [hy] at hf
          simp only [Option.bind_some] at hf
          by_cases hj : j < xs.length
          · have hxj : xs[j]? = some y := by
              rw [List.getElem?_append_left hj] at hy; exact hy
            have hvy : ∀ q c, follow h y q = some (.ref c) → c < lo := fun q c e =>
              hv (j :: q) c (by rw [follow_ref_cons, ho]; simp [okids, hxj, e])
            obtain ⟨q0, rest, rfl, h1, h2⟩ := follow_append_split ho hw q y hvy c hf hc
            refine ⟨j :: q0, rest, rfl, ?_, h2⟩
            rw [follow_ref_cons, ho]; simp [okids, hxj, h1]
          · have hjl : j = xs.length := by
              have := (List.getElem?_eq_some_iff.mp hy).1
              simp at this; omega
            subst hjl
            rw [List.getElem?_append_right (Nat.le_refl _)] at hy
            simp at hy; subst hy
            have away : ∀ q, follow h w q ≠ some (.ref b) := fun q e => by
              have := hw q b e; omega
            rw [follow_set_away _ away] at hf
            exact ⟨[], q, rfl, by simp [follow], hf⟩
      · have hob : (h.set a (.list k e l (xs ++ [w]))).objs b = h.objs b := by simp [hba]
        rw [hob] at hf
        cases hk : okids (h.objs b) with
        | none => rw [hk] at hf; cases hf
        | some ys =>
          rw [hk] at hf
          simp only [Option.bind_some] at hf
          cases hy : ys[j]? with
          | none => rw [hy] at hf; cases hf
          | some y =>
            rw [hy] at hf
            simp only [Option.bind_some] at hf
            have hvy : ∀ q c, follow h y q = some (.ref c) → c < lo := fun q c e =>
              hv (j :: q) c (by rw [follow_ref_cons, hk]; simp [hy, e])
            obtain ⟨q0, rest, rfl, h1, h2⟩ := follow_append_split ho hw q y hvy c hf hc
            refine ⟨j :: q0, rest, rfl, ?_, h2⟩
            rw [follow_ref_cons, hk]; simp [hy, h1]
    · rw [follow_nonref (fun b e => hr ⟨b, e⟩)] at hf; cases hf

/-- The list after the append decodes to its old tree with the tree of `w` at the end. -/
theorem dec_set_append {h : Heap} {a : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} {w : Value} (ho : h.objs a = some (.list k e l xs)) {n : Nat} {ds : List DV}
    (hd : dec h n (.ref a) = some (.list k e l ds))
    (hxs : ∀ (i : Nat) x q, xs[i]? = some x → follow h x q ≠ some (.ref a))
    (hwa : ∀ q, follow h w q ≠ some (.ref a)) {nw : Nat} {dw : DV} (hdw : dec h nw w = some dw) :
    ∃ n', dec (h.set a (.list k e l (xs ++ [w]))) n' (.ref a) = some (.list k e l (ds ++ [dw])) := by
  obtain ⟨a', m, xs', ha, rfl, ho', hm⟩ := dec_list hd
  cases ha
  rw [ho] at ho'; cases ho'
  refine ⟨m + nw + 1, ?_⟩
  rw [dec_ref_succ]
  simp only [Heap.set_objs, if_true]
  have hm' : xs.mapM (dec (h.set a (.list k e l (xs ++ [w]))) (m + nw)) = some ds := by
    rw [mapM_some_iff]
    obtain ⟨hl, hp⟩ := (mapM_some_iff xs ds).mp hm
    refine ⟨hl, fun i x hx => ?_⟩
    have hlt : i < ds.length := by have := (List.getElem?_eq_some_iff.mp hx).1; omega
    rw [dec_away _ _ x (hxs i x · hx), List.getElem?_eq_getElem hlt]
    have h1 := hp i x hx
    rw [List.getElem?_eq_getElem hlt] at h1
    exact dec_mono m nw x _ h1
  have hw' : dec (h.set a (.list k e l (xs ++ [w]))) (m + nw) w = some dw := by
    rw [dec_away _ _ w hwa, Nat.add_comm]; exact dec_mono nw m w dw hdw
  simp [List.mapM_append, hm', hw']

/-! ## The invariant after the append -/

/-- The append keeps the invariant. The list at `a` has a footprint path, and `w` reaches only
objects at `lo` or above, each by one path from `w`. Before the append, the arguments and the
trees of the locals reach only objects below `lo`. -/
theorem append_cinv {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) {dk : DV} (hroot : s.roots[k]? = some dk)
    {kd : ListKind} {el : SszTy} {l : Option Nat} {ds : List DV}
    (hder : s.deref k p = some (.list kd el l ds)) {xs : List Value}
    (ho : h.objs a = some (.list kd el l xs)) (hfp : fpOk fp s.roots k p = true)
    {w : Value} {dw : DV} {nw : Nat} (hdw : dec h nw w = some dw) {lo : Nat} (hlo : h0.next ≤ lo)
    (hnew : NewIn lo h w)
    (hargs : ∀ k q c, at? h vs k q = some (.ref c) → c < lo)
    (hlocs : ∀ x dt t, s.loc x = some (.tree dt) → L x = some t →
      ∀ q c, follow h t q = some (.ref c) → c < lo)
    (huniq : ∀ q q' c, follow h w q = some (.ref c) → follow h w q' = some (.ref c) → q' = q) :
    CInv fp h0 (h.set a (.list kd el l (xs ++ [w]))) vs
        { s with roots := s.roots.set k (setAt p dk (.list kd el l (ds ++ [dw]))) } L ∧
      SkelL lo h (h.set a (.list kd el l (xs ++ [w]))) := by
  have hb := hI.below
  obtain ⟨hatfp, huq⟩ := fp_unique hI.i hat hfp
  have hal : a < lo := hargs k p a hat
  have hwa : ∀ q, follow h w q ≠ some (.ref a) := fun q e => by
    have := (hnew q a e).1; omega
  have hgrow : GrowSkel lo (h.set a (.list kd el l (xs ++ [w]))) (.list kd el l xs)
      (.list kd el l (xs ++ [w])) := by
    refine ⟨rfl, rfl, rfl, by simp, fun i x y hx hy => ?_, fun i y hi hy => ?_⟩
    · have hlt := (List.getElem?_eq_some_iff.mp hx).1
      rw [List.getElem?_append_left hlt, hx] at hy; cases hy; exact RefEq.refl _
    · have hlt := (List.getElem?_eq_some_iff.mp hy).1
      simp only [List.length_append, List.length_singleton] at hlt
      rw [List.getElem?_append_right hi] at hy
      have : i - xs.length = 0 := by omega
      rw [this] at hy; simp at hy; subst hy
      intro q c e
      rw [follow_set_away _ hwa] at e
      exact ⟨(hnew q c e).1, by simpa using (hnew q c e).2⟩
  have hs : SkelL lo h (h.set a (.list kd el l (xs ++ [w]))) := SkelL_set ho hgrow
  -- A path from the arguments to `a` is `(k, p)`.
  have hxs : ∀ (i : Nat) x q, xs[i]? = some x → follow h x q ≠ some (.ref a) := by
    intro i x q hx e
    obtain ⟨v0, hv0, hf0⟩ := at?_some hat
    have : at? h vs k (p ++ i :: q) = some (.ref a) := by
      simp only [at?, hv0, Option.bind_some, follow_append, hf0, follow_ref_cons, ho, okids, hx, e]
    have := (huq k _ this).2
    have := congrArg List.length this; simp at this
  -- Locals with a tree do not reach `a`.
  have htree : ∀ x dt t, s.loc x = some (.tree dt) → L x = some t →
      (∃ n, dec h n t = some dt) ∧ ∀ q c, follow h t q = some (.ref c) → ∀ k p, at? h vs k p ≠ some (.ref c) := by
    intro x dt t hx ht
    have := hI.i.r.loc x
    rw [hx, ht] at this
    exact this
  refine ⟨⟨⟨⟨by simp [hI.i.r.len], fun k' v' d' hv' hd' => ?_, fun x => ?_⟩, hI.i.wt,
    fun k' q c e => at?_SkelL_fwd hs hb k' q c (hI.i.refsF k' q c e),
    fun k' q c e => ?_, fun k1 q1 c k2 q2 e1 hc e2 => ?_, hI.i.below0,
    fun k' ty => (rootTy_SkelL hs hb k' ty).trans (hI.i.rty k' ty), ?_,
    Fresh_trans hI.i.fresh (Fresh_set ho)⟩,
    SkelL_trans hI.skel hs hlo, fun hf => by subst hf; simp [fpOk] at hfp, hI.wf0,
    fun x r t hx ht => ?_⟩, hs⟩
  · -- The trees of the arguments.
    simp only [List.getElem?_set] at hd'
    by_cases hkk : k = k'
    · subst hkk
      have hlt : k < s.roots.length := (List.getElem?_eq_some_iff.mp hroot).1
      simp only [hlt, if_true, Option.some.injEq] at hd'; subst hd'
      obtain ⟨v0, hv0, hf0⟩ := at?_some hat
      have hvv : v' = v0 := by rw [hv0] at hv'; exact (Option.some.inj hv').symm
      subst hvv
      obtain ⟨n0, hn0⟩ := hI.i.r.roots k v' dk hv0 hroot
      obtain ⟨nl, hnl⟩ := deref_dec hI.i.r hat hder
      obtain ⟨mw, hmw⟩ := dec_set_append ho hnl hxs hwa hdw
      refine dec_graft (.ref a) _ mw hmw p n0 v' dk hn0 hf0 fun q c e hne => ⟨[], ?_⟩
      have hca : c = a := by
        by_cases hca : c = a
        · exact hca
        · exact absurd (by simp [hca]) hne
      subst hca
      have := (huq k q (by simp [at?, hv0, e])).2
      simp [this]
    · simp only [hkk, if_false] at hd'
      obtain ⟨n', hn'⟩ := hI.i.r.roots k' v' d' hv' hd'
      refine ⟨n', ?_⟩
      rw [dec_away _ n' v' fun q e => hkk (huq k' q (by simp [at?, hv', e])).1.symm]
      exact hn'
  · -- The locals.
    have := hI.i.r.loc x
    revert this
    cases hsx : s.loc x with
    | none => cases L x <;> simp [LRel]
    | some r =>
      cases hLx : L x with
      | none => simp [LRel]
      | some t =>
        cases r with
        | val v => simp [LRel, ERel]
        | place k2 p2 =>
          simp only [LRel, ERel]
          rintro ⟨c, rfl, hc⟩
          exact ⟨c, rfl, at?_SkelL_fwd hs hb k2 p2 c hc⟩
        | tree dt =>
          simp only [LRel, ERel]
          rintro ⟨⟨nt, hnt⟩, hdj⟩
          have away : ∀ q, follow h t q ≠ some (.ref a) := fun q e => hdj q a e k p hat
          refine ⟨⟨nt, (dec_away _ nt t away).trans hnt⟩, fun q c e k2 p2 e2 => ?_⟩
          rw [follow_set_away _ away] at e
          have hcl := hlocs x dt t hsx hLx q c e
          rcases at?_SkelL_back hs hb k2 p2 c e2 with h2 | ⟨h2, -⟩
          · exact hdj q c e k2 p2 h2
          · omega
  · rcases at?_SkelL_back hs hb k' q c e with h2 | ⟨h2, -⟩
    · exact hI.i.refsB k' q c h2
    · exact .inr (Nat.le_trans hlo h2)
  · -- A new object has one path.
    rcases at?_SkelL_back hs hb k1 q1 c e1 with o1 | ⟨n1, -⟩ <;>
      rcases at?_SkelL_back hs hb k2 q2 c e2 with o2 | ⟨n2, -⟩
    · exact hI.i.fresh1 k1 q1 c k2 q2 o1 hc o2
    · have := hargs k1 q1 c o1; omega
    · have := hargs k2 q2 c o2; omega
    · have split : ∀ k' q', at? (h.set a (.list kd el l (xs ++ [w]))) vs k' q' = some (.ref c) →
          ∃ rest, q' = p ++ xs.length :: rest ∧ k' = k ∧ follow h w rest = some (.ref c) := by
        intro k' q' e'
        obtain ⟨v', hv', hf'⟩ := at?_some e'
        have hv : ∀ q c, follow h v' q = some (.ref c) → c < lo := fun q c e =>
          hargs k' q c (by simp [at?, hv', e])
        obtain ⟨q0, rest, rfl, h1, h2⟩ :=
          follow_append_split ho (fun q c e => (hnew q c e).1) q' v' hv c hf' n1
        obtain ⟨rfl, rfl⟩ := huq k' q0 (by simp [at?, hv', h1])
        exact ⟨rest, rfl, rfl, h2⟩
      obtain ⟨r1, rfl, rfl, f1⟩ := split k1 q1 e1
      obtain ⟨r2, rfl, rfl, f2⟩ := split k2 q2 e2
      rw [huniq r1 r2 c f1 f2]
      exact ⟨rfl, rfl⟩
  · refine Frame_trans' hI.i.frame (Frame_set hatfp) fun a2 hold ⟨k2, pat, q, hp, hty, hmq, hq⟩ => ?_
    rcases hI.i.refsB k2 q a2 hq with h0q | hnew0
    · exact ⟨k2, pat, q, hp, (hI.i.rty k2 _).mp hty, hmq, h0q⟩
    · exact absurd (hI.wf0 a2 hnew0) hold
  · -- The trees of the locals are new.
    cases r with
    | tree dt =>
      intro q c e
      obtain ⟨-, hdj⟩ := htree x dt t hx ht
      have away : ∀ q, follow h t q ≠ some (.ref a) := fun q e => hdj q a e k p hat
      rw [follow_set_away _ away] at e
      exact hI.tlo x (.tree dt) t hx ht q c e
    | _ => trivial

/-- A local with a tree reaches only objects below `next`. -/
theorem CInv.locBelow {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (x : Name) (dt : DV) (t : Value) (hx : s.loc x = some (.tree dt))
    (ht : L x = some t) : Below h t := by
  have := hI.i.r.loc x
  rw [hx, ht] at this
  obtain ⟨⟨n, hn⟩, -⟩ := this
  exact dec_below hI.wf n t dt hn

/-- A new container with flat fields: its one path from itself. -/
theorem follow_alloc_flat {h : Heap} {ty : Name} {ws : List Value} (hf : ∀ v ∈ ws, Flat v = true) :
    ∀ q c, follow (h.alloc (.container ty ws)).2 (.ref h.next) q = some (.ref c) → q = [] ∧ c = h.next := by
  have hobj : (h.alloc (.container ty ws)).2.objs h.next = some (.container ty ws) := by
    simp [Heap.alloc]
  intro q c e
  cases q with
  | nil => simp [follow] at e; exact ⟨rfl, e.symm⟩
  | cons j q =>
    rw [follow_ref_cons, hobj] at e
    simp only [okids, Option.bind_some] at e
    cases hx : ws[j]? with
    | none => simp [hx] at e
    | some x =>
      simp only [hx, Option.bind_some] at e
      have hfx : Flat x = true := hf x (List.mem_of_getElem? hx)
      exact absurd e (fun e' => follow_nonref_ref (flat_nonref hfx) e')

theorem dec_alloc_flat {h : Heap} {ty : Name} {ws : List Value} (hf : ∀ v ∈ ws, Flat v = true) :
    dec (h.alloc (.container ty ws)).2 2 (.ref h.next) = some (.cont ty (ws.map DV.leaf)) := by
  have hobj : (h.alloc (.container ty ws)).2.objs h.next = some (.container ty ws) := by
    simp [Heap.alloc]
  rw [dec_ref_succ, hobj]
  have : ws.mapM (dec (h.alloc (.container ty ws)).2 1) = some (ws.map DV.leaf) := by
    rw [mapM_some_iff]
    refine ⟨by simp, fun i x hx => ?_⟩
    have hfx : Flat x = true := hf x (List.mem_of_getElem? hx)
    simp [dec_flat hfx, hx]
  simp [this]

variable [LibModel] [ExtTab]

attribute [local instance high] LibModel.toLibValues

/-- A keyword constructor that gives a tree: the interpreter allocates one container with flat
fields, after the arguments. -/
theorem kwCall_new {env : Env} (hlf : LibFlat env) {m : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals} {ev : Expr → DM DRes}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L (m + 1) ev)
    {g : Name} {l l' : Line} {args : List Arg}
    (hloc : s.loc g = none) (hc : callable env g = true) {d : DV}
    (hd : DM.bind (kwsOf ev args) (fun kvs => kwCtor env g kvs) = some (.ok (.tree d))) :
    ∃ h2 ty ws, Ext h h2 ∧ (∀ v ∈ ws, Flat v = true) ∧ d = .cont ty (ws.map .leaf) ∧
      evalExpr env (m + 2) L h (.call l (.name l' g) args) =
        .ok (.ref h2.next, (h2.alloc (.container ty ws)).2) := by
  have hL : L g = none := by
    have := hI.i.r.loc g; rw [hloc] at this
    revert this; cases L g <;> simp [LRel]
  obtain ⟨hlk, hany⟩ := callable_lookup hc hL
  rw [evalExpr]
  have hname : evalExpr env (m + 1) L h (.name l' g) = .ok (.glob g, h) := by
    rw [evalExpr]; simp [hlk]
  simp only [hname, Except.bind_ok', hany]
  rcases bind_case hd with ⟨err, he, hr⟩ | ⟨kvs, he, hd2⟩
  · cases hr
  · have := kwsOf_sound ih args h _ hI he
    revert this
    cases hea : evalArgs env (m + 1) L h args with
    | error e' => intro hx; cases hx
    | ok q =>
      obtain ⟨ws, kws, h2⟩ := q
      rintro ⟨hx2, rfl, rfl⟩
      simp only [Except.bind_ok']
      unfold kwCtor at hd2
      cases hg : env.globals.lookup g with
      | none => simp [hg] at hd2
      | some gl =>
      rw [hg] at hd2
      cases gl with
      | type t =>
        cases t with
        | container ty =>
          simp only at hd2
          rw [callValue_type_kw _ _ _ _ hg]
          cases hfs : env.containers.lookup ty with
          | none => simp [hfs] at hd2
          | some fs =>
          rw [hfs] at hd2
          simp only at hd2
          split at hd2
          · next hall =>
            rcases bind_case hd2 with ⟨err, hk, hr⟩ | ⟨ws, hk, hd3⟩
            · cases hr
            · rw [hlf.kwctor h2 ty fs kws _ hfs hall hk]
              simp [DM.ok] at hd3; subst hd3
              exact ⟨h2, ty, ws, hx2, kwFields_flat fs ws hk, rfl, rfl⟩
          · cases hd2
        | _ => simp at hd2
      | _ => simp at hd2

/-! ## The interpreter on `o.m(a)` -/

theorem eval_method_err {env : Env} {m : Nat} {L : Locals} {h : Heap} {l l' : Line} {o a : Expr}
    {f : Name} {e : SpecError} (ho : evalExpr env m L h o = .error e) :
    evalExpr env (m + 2) L h (.call l (.attr l' o f) [.pos a]) = .error e := by
  rw [evalExpr, evalExpr]; simp [ho]

theorem eval_method_arg_err {env : Env} {m : Nat} {L : Locals} {h h1 : Heap} {l l' : Line}
    {o a : Expr} {f : Name} {a0 : Nat} {k : ListKind} {el : SszTy} {lm : Option Nat}
    {xs : List Value} {e : SpecError}
    (ho : evalExpr env m L h o = .ok (.ref a0, h1)) (hobj : h1.objs a0 = some (.list k el lm xs))
    (ha : evalExpr env (m + 1) L h1 a = .error e) :
    evalExpr env (m + 2) L h (.call l (.attr l' o f) [.pos a]) = .error e := by
  rw [evalExpr, evalExpr]; simp [ho, getAttr, hobj, anyAll, evalArgs, ha]

theorem eval_method {env : Env} {m : Nat} {L : Locals} {h h1 h2 : Heap} {l l' : Line}
    {o a : Expr} {f : Name} {a0 : Nat} {k : ListKind} {el : SszTy} {lm : Option Nat}
    {xs : List Value} {w : Value}
    (ho : evalExpr env m L h o = .ok (.ref a0, h1)) (hobj : h1.objs a0 = some (.list k el lm xs))
    (ha : evalExpr env (m + 1) L h1 a = .ok (w, h2)) :
    evalExpr env (m + 2) L h (.call l (.attr l' o f) [.pos a]) = applyMethod env h2 (.ref a0) f [w] := by
  rw [evalExpr, evalExpr]; simp [ho, getAttr, hobj, anyAll, evalArgs, ha, callValue.eq_def]

theorem appendOf_spec {env : Env} {e o a : Expr} (h : appendOf env e = some (o, a)) :
    ∃ l l', e = .call l (.attr l' o env.nm.append) [.pos a] := by
  unfold appendOf at h
  split at h
  · next l l' o' m a' =>
    split at h
    · next hm => simp at h; obtain ⟨rfl, rfl⟩ := h; subst hm; exact ⟨l, l', rfl⟩
    · cases h
  · cases h

/-- The interpreter's append, after the coercion of the item, against the denotation's. -/
theorem append_tail {fp : Footprint} {h0 h hs : Heap} {vs : List Value} {s : DSt}
    {L : Locals} (hI : CInv fp h0 hs vs s L) (hsk : SkelL h0.next h hs) {k : Nat} {p : List Nat}
    {a0 : Nat} (hat : at? hs vs k p = some (.ref a0)) {dk : DV} (hroot : s.roots[k]? = some dk)
    {kd : ListKind} {el : SszTy} {lm : Option Nat} {ds : List DV}
    (hder : s.deref k p = some (.list kd el lm ds)) {xs : List Value}
    (ho : hs.objs a0 = some (.list kd el lm xs)) (hfp : fpOk fp s.roots k p = true)
    (hlen : ds.length = xs.length)
    {w : Value} {dw : DV} {nw : Nat} (hdw : dec hs nw w = some dw) {lo : Nat} (hlo : h0.next ≤ lo)
    (hnew : NewIn lo hs w)
    (hargs : ∀ k q c, at? hs vs k q = some (.ref c) → c < lo)
    (hlocs : ∀ x dt t, s.loc x = some (.tree dt) → L x = some t →
      ∀ q c, follow hs t q = some (.ref c) → c < lo)
    (huniq : ∀ q q' c, follow hs w q = some (.ref c) → follow hs w q' = some (.ref c) → q' = q)
    {r : Res (DRes × List DV)}
    (hd : DM.bind (lift (Ssz.checkLength kd lm (ds.length + 1))) (fun _ =>
      DM.ok (DRes.val .none, s.roots.set k (setAt p dk (.list kd el lm (ds ++ [dw]))))) = some r) :
    CallOK fp h0 h vs s L r ((Ssz.checkLength kd lm (xs.length + 1)).bind fun _ =>
      .ok (.none, hs.set a0 (.list kd el lm (xs ++ [w])))) := by
  rw [hlen] at hd
  rcases bind_case hd with ⟨err, hc, rfl⟩ | ⟨u, hc, hd2⟩
  · obtain ⟨hcr, hne⟩ := lift_some hc
    rw [← hcr]
    exact ⟨rfl, hne err hcr.symm⟩
  · obtain ⟨hcr, -⟩ := lift_some hc
    rw [← hcr]
    simp [DM.ok] at hd2; subst hd2
    obtain ⟨hI3, hs3⟩ := append_cinv hI hat hroot hder ho hfp hdw hlo hnew hargs hlocs huniq
    exact ⟨⟨rfl, rfl⟩, trivial, hI3, SkelL_trans hsk (SkelL_mono hlo hs3) (Nat.le_refl _)⟩

/-- `o.append(a)` at one fuel step agrees with the interpreter. -/
theorem appendStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L)
    (hEx : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → EvOK env h0.next h vs L n ((den env fps n).expr fp s))
    (hSub : ∀ m, n = m + 1 → ∀ fp h0 h vs s L, CInv fp h0 h vs s L →
      EvOK env h0.next h vs L m ((den env fps n).sub fp s))
    {l l' : Line} {o a : Expr} {r : Res (DRes × List DV)}
    (hd : appendStep env n (den env fps n) fp s o a = some r) :
    CallOK fp h0 h vs s L r (evalExpr env (n + 1) L h (.call l (.attr l' o env.nm.append) [.pos a])) := by
  cases n with
  | zero => simp [appendStep] at hd
  | succ m =>
  simp only [appendStep] at hd
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
  · obtain ⟨_, hoe, hn, hne⟩ := gok_error (hSub m rfl fp h0 h vs s L hI o _ he)
    rw [eval_method_err hoe]; exact ⟨hn, hne⟩
  obtain ⟨ov, h1, hoe, hx1, -, hrel1⟩ := gok_ok_lo (hSub m rfl fp h0 h vs s L hI o _ he)
  have hI1 := hI.ext hx1
  cases ro with
  | val _ => simp at hd2
  | tree _ => simp at hd2
  | place k p =>
  obtain ⟨a0, rfl, hat1⟩ := hrel1
  simp only at hd2
  cases hdk : s.deref k p with
  | none => simp [hdk] at hd2
  | some dd =>
  cases hdr : s.roots[k]? with
  | none => cases dd <;> simp [hdk, hdr] at hd2
  | some dk =>
  cases dd with
  | leaf _ => simp [hdk, hdr] at hd2
  | cont _ _ => simp [hdk, hdr] at hd2
  | list kd el lm ds =>
  simp only [hdk, hdr] at hd2
  by_cases hcnd : (appendable kd el && fpOk fp s.roots k p) = true
  rotate_left
  · rw [if_neg hcnd] at hd2; cases hd2
  rw [if_pos hcnd] at hd2
  simp only [Bool.and_eq_true] at hcnd
  obtain ⟨hap, hfp⟩ := hcnd
  obtain ⟨nn, hn⟩ := deref_dec hI1.i.r hat1 hdk
  obtain ⟨a', mm, xs, ha, -, ho1, hm⟩ := dec_list hn
  cases ha
  have hlen : ds.length = xs.length := ((mapM_some_iff xs ds).mp hm).1
  rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ra, he2, hd3⟩
  · obtain ⟨_, hae, hn, hne⟩ := gok_error (hEx fp h0 h1 vs s L hI1 a _ he2)
    rw [eval_method_arg_err hoe ho1 hae]; exact ⟨hn, hne⟩
  obtain ⟨w, h2, hae, hx2, hlo2, hrel2⟩ := gok_ok_lo (hEx fp h0 h1 vs s L hI1 a _ he2)
  have hI2 := hI1.ext hx2
  have ho2 : h2.objs a0 = some (.list kd el lm xs) :=
    (hx2.2.2 a0 (at?_below hI1.below hat1)).trans ho1
  have hat2 : at? h2 vs k p = some (.ref a0) := (at?_Ext hx2 hI1.below k p a0).mpr hat1
  rw [eval_method hoe ho1 hae, hlf.append h2 a0 kd el lm xs w ho2 hap]
  have hsk2 : SkelL h0.next h h2 := SkelL_of_Ext (Ext_trans hx1 hx2) _
  rcases bind_case hd3 with ⟨err, he3, rfl⟩ | ⟨dw, he3, hd4⟩
  · -- The item does not coerce.
    cases ra with
    | place _ _ => simp [appendItemD] at he3
    | tree dt =>
      exfalso
      cases dt with
      | cont ty' ds' =>
        simp only [appendItemD] at he3
        split at he3
        · split at he3 <;> simp [DM.ok] at he3
        · cases he3
      | _ => simp [appendItemD] at he3
    | val v =>
      obtain ⟨rfl, hv⟩ := hrel2
      simp only [appendItemD] at he3
      rcases bind_case he3 with ⟨err', hc, he4⟩ | ⟨v', hc, he4⟩
      · simp only [Except.error.injEq] at he4
        subst he4
        obtain ⟨hc1, -⟩ := dCoerce_some hlf.coerce hv hc h2
        obtain ⟨hco, hne⟩ := hc1 _ rfl
        rw [hco]; exact ⟨rfl, hne⟩
      · split at he4 <;> simp [DM.ok] at he4
  cases ra with
  | place _ _ => simp [appendItemD] at he3
  | val v =>
    obtain ⟨rfl, hv⟩ := hrel2
    simp only [appendItemD] at he3
    rcases bind_case he3 with ⟨err', hc, he4⟩ | ⟨v', hc, he4⟩
    · cases he4
    split at he4
    rotate_left
    · cases he4
    next hv' =>
    simp [DM.ok] at he4; subst he4
    obtain ⟨-, hc2⟩ := dCoerce_some hlf.coerce hv hc h2
    rw [hc2 v' rfl]
    exact append_tail hI2 hsk2 hat2 hdr hdk ho2 hfp hlen (dec_flat hv' 0) hI2.i.fresh.1
      (fun q c e => absurd e (fun e' => follow_nonref_ref (flat_nonref hv') e'))
      (fun k q c e => at?_below hI2.below e)
      (fun x dt t hx ht q c e => hI2.locBelow x dt t hx ht q c e)
      (fun q q' c e => absurd e (fun e' => follow_nonref_ref (flat_nonref hv') e')) hd4
  | tree dt =>
    cases dt with
    | leaf _ => simp [appendItemD] at he3
    | list _ _ _ _ => simp [appendItemD] at he3
    | cont ty dsT =>
    simp only [appendItemD] at he3
    split at he3
    rotate_left
    · cases he3
    next g cargs ty' hch =>
    by_cases hkw : (allKw cargs && ty' == ty) = true
    rotate_left
    · rw [if_neg hkw] at he3; cases he3
    rw [if_pos hkw] at he3
    simp [DM.ok] at he3; subst he3
    simp only [Bool.and_eq_true, beq_iff_eq] at hkw
    obtain ⟨hkw, rfl⟩ := hkw
    obtain ⟨l1, l1', rfl, hloc, hc⟩ := callHead_spec hch
    -- The argument is a keyword constructor: one new container.
    cases m with
    | zero =>
      rw [den_expr] at he2
      simp [exprStep] at he2
    | succ m' =>
    rw [den_expr] at he2
    simp only [exprStep, hch, if_pos hkw] at he2
    obtain ⟨hk, ty2, ws, hxk, hfw, hdt, hev⟩ :=
      kwCall_new hlf hI1 (fun h3 hI3 => hSub (m' + 1) rfl fp h0 h3 vs s L hI3) hloc hc he2
    rw [hae] at hev
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    simp only [DV.cont.injEq] at hdt
    obtain ⟨hty, hds⟩ := hdt
    subst hty
    subst hds
    have hIk := hI1.ext hxk
    have hobj : (hk.alloc (.container ty' ws)).2.objs hk.next = some (.container ty' ws) := by
      simp [Heap.alloc]
    rw [hlf.coerceCont _ _ _ _ hobj]
    have hxa := Ext_alloc hk (.container ty' ws)
    refine append_tail hI2 hsk2 hat2 hdr hdk ho2 hfp hlen (dec_alloc_flat hfw) hIk.i.fresh.1
      (fun q c e => ?_) (fun k2 q c e => ?_) (fun x dt t hx ht q c e => ?_)
      (fun q q' c e e' => ?_) hd4
    · obtain ⟨-, rfl⟩ := follow_alloc_flat hfw q c e
      exact ⟨Nat.le_refl _, by simp [Heap.alloc]⟩
    · exact at?_below hIk.below ((at?_Ext hxa hIk.below k2 q c).mp e)
    · exact hIk.locBelow x dt t hx ht q c ((follow_Ext hxa q (hIk.locBelow x dt t hx ht) c).mp e)
    · rw [(follow_alloc_flat hfw q c e).1, (follow_alloc_flat hfw q' c e').1]

end SpecLean.Layer4
