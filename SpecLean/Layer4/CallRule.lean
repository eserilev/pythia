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

/-- Every object of a tree value is at `lo` or above: made after the run started. -/
def TLo (lo : Nat) (h : Heap) : DRes → Value → Prop
  | .tree _, w => ∀ q a, follow h w q = some (.ref a) → lo ≤ a
  | _, _ => True

theorem tlo_ofChild {lo : Nat} {h : Heap} (k : Nat) (p : List Nat) (c : DV) (w : Value) :
    TLo lo h (ofChild k p c) w := by
  cases c <;> trivial

structure CInv (fp : Footprint) (h0 h : Heap) (vs : List Value) (s : DSt) (L : Locals) :
    Prop where
  i : SInv fp h0 h vs s L
  skel : Skel h0 h
  ro : fp = [] → Ext h0 h
  wf0 : HeapWF h0
  /-- The trees in the locals are new. -/
  tlo : ∀ x r w, s.loc x = some r → L x = some w → TLo h0.next h r w

theorem CInv.start {fp : Footprint} {h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hr : RInv h vs s L) (hw : WTree h vs fp) (hwf : HeapWF h)
    (htlo : ∀ x r w, s.loc x = some r → L x = some w → TLo h.next h r w) : CInv fp h h vs s L :=
  ⟨⟨hr, hw, fun _ _ _ e => e, fun _ _ _ e => .inl e,
      fun k q b _ _ e hb _ => absurd (at?_below0 hwf ⟨hr.len, hr.roots⟩ e) (by omega),
      fun k q b e => at?_below0 hwf ⟨hr.len, hr.roots⟩ e, fun _ _ => Iff.rfl, Frame_refl h vs fp,
      Fresh_refl h⟩,
    Skel_refl h, fun _ => Ext_refl h, hwf, htlo⟩

theorem CInv.wf {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) : HeapWF h := hI.i.fresh.2 hI.wf0

/-- The arguments reach only objects below `next`. -/
theorem CInv.below {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) : BelowArgs h vs :=
  decArgs_below hI.wf hI.i.r.roots hI.i.r.len

theorem at?_below {h : Heap} {vs : List Value} (hb : BelowArgs h vs) {k : Nat} {p : List Nat}
    {a : Nat} (hat : at? h vs k p = some (.ref a)) : a < h.next := by
  obtain ⟨v, hv, hf⟩ := at?_some hat
  exact hb k v hv p a hf

theorem ERel_ext {h h' : Heap} {vs : List Value} (hwf : HeapWF h) (hb : BelowArgs h vs)
    (e : Ext h h') {r : DRes} {w : Value} (hr : ERel h vs r w) : ERel h' vs r w := by
  cases r with
  | val v => exact hr
  | place k p =>
    obtain ⟨a, rfl, hat⟩ := hr
    exact ⟨a, rfl, (at?_Ext e hb k p a).mpr hat⟩
  | tree d =>
    obtain ⟨⟨n, hn⟩, hdj⟩ := hr
    have hbw : Below h w := dec_below hwf n w d hn
    refine ⟨⟨n, (dec_unchanged n w fun q a ha => e.2.2 a (hbw q a ha)).trans hn⟩,
      fun q a ea k p ep => ?_⟩
    exact hdj q a ((follow_Ext e q hbw a).mp ea) k p ((at?_Ext e hb k p a).mp ep)

theorem dec_ext {h h' : Heap} (e : Ext h h') {v : Value} (hb : Below h v) (n : Nat) :
    dec h' n v = dec h n v :=
  dec_unchanged n v fun q a ha => e.2.2 a (hb q a ha)

/-- A run that changes no old object keeps the invariant. -/
theorem CInv.ext {fp : Footprint} {h0 h h' : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (e : Ext h h') : CInv fp h0 h' vs s L := by
  have hb := hI.below
  have hsk := Skel_of_Ext e
  refine ⟨⟨⟨hI.i.r.len, fun k v d hv hd => ?_, fun x => ?_⟩, hI.i.wt,
    fun k q b e0 => (at?_Ext e hb k q b).mpr (hI.i.refsF k q b e0),
    fun k q b e1 => hI.i.refsB k q b ((at?_Ext e hb k q b).mp e1),
    fun k q b k' q' e1 hb' e2 => hI.i.fresh1 k q b k' q' ((at?_Ext e hb k q b).mp e1) hb'
      ((at?_Ext e hb k' q' b).mp e2), hI.i.below0,
    fun k ty => ?_, fun a ha hn => ?_, Fresh_trans hI.i.fresh (Fresh_of_Skel hsk)⟩,
    Skel_trans hI.skel hsk, fun hf => Ext_trans (hI.ro hf) e, hI.wf0, fun x r w hx hw => ?_⟩
  · obtain ⟨n, hn⟩ := hI.i.r.roots k v d hv hd
    exact ⟨n, (dec_ext e (hb k v hv) n).trans hn⟩
  · have := hI.i.r.loc x
    revert this
    cases s.loc x <;> cases L x <;> simp only [LRel] <;> try exact id
    exact ERel_ext hI.wf hb e
  · rw [rootTy_Skel hsk hb]; exact hI.i.rty k ty
  · have ha0 : a < h0.next := Nat.lt_of_not_le fun hle => ha (hI.wf0 a hle)
    rw [e.2.2 a (Nat.lt_of_lt_of_le ha0 hI.i.fresh.1)]
    exact hI.i.frame a ha hn
  · have ht := hI.tlo x r w hx hw
    cases r with
    | tree d =>
      have hl := hI.i.r.loc x
      rw [hx, hw] at hl
      obtain ⟨⟨n, hn⟩, -⟩ := hl
      have hbw : Below h w := dec_below hI.wf n w d hn
      exact fun q a ea => ht q a ((follow_Ext e q hbw a).mp ea)
    | _ => trivial

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
  ⟨write_inv hI.i hat hroot hu hfp hleaf ho hI.wf0,
    Skel_trans hI.skel (Skel_set ho (write_skel hI.i hat hroot hu hleaf ho)),
    fun e => absurd e (fpOk_ne hfp), hI.wf0, fun x r w hx hw => by
      have ht := hI.tlo x r w hx hw
      cases r with
      | tree d =>
        exact fun q b e => ht q b ((follow_skel ho (write_skel hI.i hat hroot hu hleaf ho) q w w
          (RefEq.refl w) b).mp e)
      | _ => trivial⟩

/-! ## Results -/

variable [LibModel]

/-- How a statement ends, in the denotation and in the interpreter. -/
def ORel (lo : Nat) (h : Heap) (vs : List Value) : DOut → Outcome → Prop
  | .normal, .normal => True
  | .brk, .brk => True
  | .cont, .cont => True
  | .ret r, .ret w => ERel h vs r w ∧ TLo lo h r w
  | _, _ => False

def CStmtOK (fp : Footprint) (h0 h : Heap) (vs : List Value) :
    Res (DOut × DSt) → Res (Outcome × Locals × Heap) → Prop
  | .ok (o, s'), .ok (o', L', h') => ORel h0.next h' vs o o' ∧ CInv fp h0 h' vs s' L' ∧ SkelL h0.next h h'
  | .error e, .error e' => normE e' = normE e ∧ e ≠ .outOfFuel
  | _, _ => False

/-- A statement-level expression: the value, and the invariant with the new trees. -/
def CallOK (fp : Footprint) (h0 h : Heap) (vs : List Value) (s : DSt) (L : Locals) :
    Res (DRes × List DV) → Res (Value × Heap) → Prop
  | .ok (r, rs), .ok (w, h') =>
    ERel h' vs r w ∧ TLo h0.next h' r w ∧ CInv fp h0 h' vs { s with roots := rs } L ∧
      SkelL h0.next h h'
  | .error e, .error e' => normE e' = normE e ∧ e ≠ .outOfFuel
  | _, _ => False

/-- A statement that starts after a run that changes no old object. -/
theorem CStmtOK.pre {fp : Footprint} {h0 h h1 : Heap} {vs : List Value} {r : Res (DOut × DSt)}
    {out : Res (Outcome × Locals × Heap)} (e : Ext h h1) (hk : CStmtOK fp h0 h1 vs r out) :
    CStmtOK fp h0 h vs r out := by
  cases r <;> cases out <;> simp only [CStmtOK] at hk ⊢ <;> try exact hk
  next a b =>
    obtain ⟨o, s'⟩ := a
    obtain ⟨o', L', h'⟩ := b
    exact ⟨hk.1, hk.2.1, SkelL_trans (SkelL_of_Ext e h0.next) hk.2.2 (Nat.le_refl _)⟩

theorem CStmtOK.preS {fp : Footprint} {h0 h h1 : Heap} {vs : List Value} {r : Res (DOut × DSt)}
    {out : Res (Outcome × Locals × Heap)} (hs : SkelL h0.next h h1) (hk : CStmtOK fp h0 h1 vs r out) :
    CStmtOK fp h0 h vs r out := by
  cases r <;> cases out <;> simp only [CStmtOK] at hk ⊢ <;> try exact hk
  next a b =>
    obtain ⟨o, s'⟩ := a
    obtain ⟨o', L', h'⟩ := b
    exact ⟨hk.1, hk.2.1, SkelL_trans hs hk.2.2 (Nat.le_refl _)⟩

theorem CallOK.pre {fp : Footprint} {h0 h h1 : Heap} {vs : List Value} {s : DSt} {L : Locals}
    {r : Res (DRes × List DV)} {out : Res (Value × Heap)} (e : Ext h h1)
    (hk : CallOK fp h0 h1 vs s L r out) : CallOK fp h0 h vs s L r out := by
  cases r <;> cases out <;> simp only [CallOK] at hk ⊢ <;> try exact hk
  next a b =>
    obtain ⟨r', rs⟩ := a
    obtain ⟨w, h'⟩ := b
    exact ⟨hk.1, hk.2.1, hk.2.2.1, SkelL_trans (SkelL_of_Ext e h0.next) hk.2.2.2 (Nat.le_refl _)⟩

/-- The contract of a function body. A tree result is new: made after the call started. -/
def FnRel (fp : Footprint) (h : Heap) (vs : List Value) :
    Res (DRes × List DV) → Res (Value × Heap) → Prop
  | .ok (r, rs), .ok (w, h') =>
    ERel h' vs r w ∧ TLo h.next h' r w ∧ DecArgs h' vs rs ∧ Frame h h' vs fp ∧ Skel h h' ∧
      (fp = [] → Ext h h') ∧
      ∀ kg q b kg' q', at? h' vs kg q = some (.ref b) → h.next ≤ b →
        at? h' vs kg' q' = some (.ref b) → kg' = kg ∧ q' = q
  | .error e, .error e' => normE e' = normE e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem cstmtOK_err {fp : Footprint} {h0 h : Heap} {vs : List Value} {e : SpecError}
    (hne : e ≠ .outOfFuel) : CStmtOK fp h0 h vs (.error e) (.error e) := ⟨rfl, hne⟩

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
          | tree dt =>
            obtain ⟨⟨nt, hnt⟩, -⟩ := h1
            simp [argRoot] at hr1; subst hr1; exact ⟨nt, hnt⟩
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
        | tree _ => simp at this
    · cases h
  | .tree _ :: rs, i, k, p, h => by simp [onePlace] at h

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
  rcases hI.i.refsB k (p ++ q) b hpq with h0p | hnew
  · have hb0 := hI.i.below0 k (p ++ q) b h0p
    rcases hI.i.refsB k' q' b e with h0q | hnew'
    · exact hI.i.wt k cpat hcp ((hI.i.rty k _).mp hcty) (p ++ q) hm b h0p k' q' h0q
    · omega
  · exact hI.i.fresh1 k (p ++ q) b k' q' hpq hnew e

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
    (hf1 : ∀ kg q b kg' q', at? h' ws kg q = some (.ref b) → h.next ≤ b →
        at? h' ws kg' q' = some (.ref b) → kg' = kg ∧ q' = q)
    (hdi : rg'[i]? = some di) :
    CInv fp h0 h' vs { s with roots := s.roots.set k (setAt p dr di) } L := by
  obtain ⟨hi, -⟩ := onePlace_spec hone
  obtain ⟨hl, hp⟩ := ERels_get hrel
  obtain ⟨a, hwi, hat⟩ : ∃ a, ws[i]? = some (.ref a) ∧ at? h vs k p = some (.ref a) := by
    have hlt : i < ws.length := hl ▸ (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨a, he, hat⟩ := hp i _ ws[i] hi (List.getElem?_eq_getElem hlt)
    exact ⟨a, by rw [List.getElem?_eq_getElem hlt, he], hat⟩
  -- Every changed object is at a callee footprint path, so below `p` with one caller path.
  have hbl := hI.below
  have changed : ∀ b, b < h.next → h'.objs b ≠ h.objs b → AtFp h vs fp b ∧ ∃ q,
      ∀ k' q', at? h vs k' q' = some (.ref b) → k' = k ∧ q' = p ++ q := by
    intro b hb hne
    have hold : h.objs b ≠ none := by
      intro hn
      rcases hsk.2.2 b hb with e | ⟨o, -, ho, -, -⟩
      · exact hne e
      · rw [hn] at ho; cases ho
    have hat' : AtFp h ws fpG b := Classical.byContradiction fun hn => hne (hfr b hold hn)
    obtain ⟨kg, pg, q, hpg, hty, hq, hb⟩ := hat'
    obtain ⟨-, hfp, huniq⟩ := callee_fp hI hrel hone hdk hcov hpg hty hq hb
    exact ⟨hfp, q, huniq⟩
  have hfwd : ∀ k' q b, at? h vs k' q = some (.ref b) → at? h' vs k' q = some (.ref b) :=
    fun k' q b => at?_SkelL_fwd hsk hbl k' q b
  have hback : ∀ k' q b, at? h' vs k' q = some (.ref b) →
      at? h vs k' q = some (.ref b) ∨ (h.next ≤ b ∧ b < h'.next) :=
    fun k' q b => at?_SkelL_back hsk hbl k' q b
  obtain ⟨v0, hv0, hf0⟩ := at?_some hat
  obtain ⟨ddi, hddi⟩ := hda.2 i (.ref a) di hwi hdi
  -- A tree local reaches no changed object, so it reads the same.
  have tree_same : ∀ x w dt, L x = some w → s.loc x = some (.tree dt) →
      (∀ q b, follow h w q = some (.ref b) → h'.objs b = h.objs b) ∧ Below h w := by
    intro x w dt hw hx
    have hlx := hI.i.r.loc x
    rw [hx, hw] at hlx
    obtain ⟨⟨nt, hnt⟩, hdj⟩ := hlx
    have hbw : Below h w := dec_below hI.wf nt w dt hnt
    refine ⟨fun q b e => Classical.byContradiction fun hne => ?_, hbw⟩
    obtain ⟨⟨k3, pat, q3, -, -, -, hq3⟩, -⟩ := changed b (hbw q b e) hne
    exact hdj q b e k3 q3 hq3
  -- A new object that the caller's arguments reach is reached through the callee's argument.
  have newpath : ∀ k' q' b, at? h' vs k' q' = some (.ref b) → h.next ≤ b →
      ∃ cq, k' = k ∧ q' = p ++ cq ∧ at? h' ws i cq = some (.ref b) := by
    intro k' q' b e hn
    obtain ⟨v', hv', hf'⟩ := at?_some e
    obtain ⟨q0, c, j, rest, y, xs, ys, rfl, hc0, hc, hxs, hys, hj, hy, hrest⟩ :=
      follow_new_split hsk q' v' (hbl k' v' hv') b hf' hn
    have hne : h'.objs c ≠ h.objs c := by
      intro e'
      rw [e', hxs] at hys; cases hys
      have := (List.getElem?_eq_some_iff.mp hy).1; omega
    obtain ⟨-, qq, huq⟩ := changed c hc hne
    obtain ⟨rfl, rfl⟩ := huq k' q0 (by simp [at?, hv', hc0])
    refine ⟨qq ++ j :: rest, rfl, by simp, ?_⟩
    have hac : follow h (.ref a) qq = some (.ref c) := by
      unfold at? at hat; rw [hv'] at hat; simp only [Option.bind_some] at hat
      rw [hv'] at hv0; cases hv0
      have := hc0; rw [follow_append, hf0] at this; simpa using this
    have hac' : follow h' (.ref a) qq = some (.ref c) :=
      follow_SkelL_fwd hsk qq _ _ (RefEq.refl _) (fun q b e => hbl _ _ hv0 (p ++ q) b
        (by rw [follow_append, hf0]; simpa using e)) c hac
    unfold at?
    rw [hwi]
    simp only [Option.bind_some, follow_append, hac', follow_ref_cons, hys, hy]
    simpa using hrest
  refine ⟨⟨⟨by simp [hI.i.r.len], fun k' v' d'' hv' hd'' => ?_, fun x => ?_⟩, hI.i.wt,
    fun k' q b e => hfwd k' q b (hI.i.refsF k' q b e), fun k' q b e => ?_, ?_, hI.i.below0, ?_,
    ?_, ?_⟩, Skel_trans hI.skel hsk, fun e => absurd e hfpne, hI.wf0, fun x r w hx hw => ?_⟩
  · simp only [List.getElem?_set] at hd''
    by_cases hkk : k = k'
    · subst hkk
      rw [hv0] at hv'; cases hv'
      have hlt : k < s.roots.length := (List.getElem?_eq_some_iff.mp hdr).1
      simp [hlt] at hd''; subst hd''
      obtain ⟨n, hn⟩ := hI.i.r.roots k v0 dr hv0 hdr
      refine dec_graft (.ref a) di ddi hddi p n v0 dr hn hf0 fun q b e hne => ?_
      obtain ⟨-, q0, huniq⟩ := changed b (hbl k v0 hv0 q b e) hne
      exact ⟨q0, (huniq k q (by simp [at?, hv0, e])).2⟩
    · simp only [hkk, if_false] at hd''
      obtain ⟨n', hn'⟩ := hI.i.r.roots k' v' d'' hv' hd''
      refine ⟨n', ?_⟩
      rw [dec_unchanged n' v' fun q b e => Classical.byContradiction fun hne => ?_]
      · exact hn'
      · obtain ⟨-, q0, huniq⟩ := changed b (hbl k' v' hv' q b e) hne
        exact hkk (huniq k' q (by simp [at?, hv', e])).1.symm
  · have := hI.i.r.loc x
    revert this
    cases hsx : s.loc x with
    | none => cases L x <;> simp [LRel]
    | some r =>
      cases hLx : L x with
      | none => simp [LRel]
      | some w =>
        cases r with
        | val v => simp [LRel, ERel]
        | place k2 p2 =>
          simp only [LRel, ERel]
          rintro ⟨b, rfl, hb⟩
          exact ⟨b, rfl, hfwd k2 p2 b hb⟩
        | tree dt =>
          simp only [LRel, ERel]
          rintro ⟨⟨nt, hnt⟩, hdj⟩
          obtain ⟨hun, hbw⟩ := tree_same x w dt hLx hsx
          refine ⟨⟨nt, (dec_unchanged nt w hun).trans hnt⟩, fun q b e k3 p3 e3 => ?_⟩
          rw [follow_unchanged q w hun] at e
          rcases hback k3 p3 b e3 with e3' | ⟨hnb, -⟩
          · exact hdj q b e k3 p3 e3'
          · have := hbw q b e; omega
  · rcases hback k' q b e with e' | ⟨hnb, -⟩
    · exact hI.i.refsB k' q b e'
    · exact .inr (Nat.le_trans hI.i.fresh.1 hnb)
  · intro k1 q1 b k2 q2 e1 hb e2
    by_cases hold : b < h.next
    · rcases hback k1 q1 b e1 with e1' | ⟨hnb, -⟩
      · rcases hback k2 q2 b e2 with e2' | ⟨hnb, -⟩
        · exact hI.i.fresh1 k1 q1 b k2 q2 e1' hb e2'
        · omega
      · omega
    · obtain ⟨cq1, rfl, rfl, hc1⟩ := newpath k1 q1 b e1 (by omega)
      obtain ⟨cq2, rfl, rfl, hc2⟩ := newpath k2 q2 b e2 (by omega)
      obtain ⟨-, rfl⟩ := hf1 i cq1 b i cq2 hc1 (by omega) hc2
      exact ⟨rfl, rfl⟩
  · intro k' ty; rw [rootTy_Skel hsk hbl]; exact hI.i.rty k' ty
  · refine Frame_trans' hI.i.frame (fun b hold hn => Classical.byContradiction fun hne =>
      hn (changed b (Nat.lt_of_not_le fun hle => hold (hI.wf b hle)) hne).1)
      fun a2 hold0 ⟨k2, pat, q, hp2, hty, hmq, hq⟩ => ?_
    rcases hI.i.refsB k2 q a2 hq with h0q | hnew
    · exact ⟨k2, pat, q, hp2, (hI.i.rty k2 _).mp hty, hmq, h0q⟩
    · exact absurd (hI.wf0 a2 hnew) hold0
  · exact Fresh_trans hI.i.fresh (Fresh_of_Skel hsk)
  · have ht := hI.tlo x r w hx hw
    cases r with
    | tree d =>
      obtain ⟨hun, -⟩ := tree_same x w d hw hx
      exact fun q a ea => ht q a (by rw [follow_unchanged q w hun] at ea; exact ea)
    | _ => trivial

end rule

end SpecLean.Layer4
