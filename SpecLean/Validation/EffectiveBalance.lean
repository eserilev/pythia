import SpecLean.Validation.Credentials

/-!
# Validation: `process_effective_balance_updates`

The spec writes `validator.effective_balance = …`, where `validator` is the loop variable of
`enumerate(state.validators)`. In the heap this is a write through the element reference. The
readable Lean writes `state.validators[index]`. The proof shows that the two agree.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Gen SpecLean.Encode

variable (sha : Oracle) {gfp : Footprint}

/-! ## The readable loop in normal form -/

open Readable in
/-- The update of one validator. -/
def pebUpdate (s : BeaconState) (i : Nat) (v : Validator) (b : Gwei) : SpecM BeaconState := do
  let md : Gwei ← erase (Gwei.mk <$> chkMod b.val 1000000000)
  let rounded : Gwei ← erase (Gwei.mk <$> chkSub b.val md.val)
  let v' : Validator := { v with effective_balance := umin rounded (get_max_effective_balance v) }
  pure { s with validators := s.validators.set i v' }

open Readable in
/-- The validator after the update. -/
def pebNew (v : Validator) (b : Gwei) : Validator :=
  let rounded : Gwei := ⟨b.val - b.val % 1000000000⟩
  { v with effective_balance := umin rounded (get_max_effective_balance v) }

open Readable in
/-- The loop body with the constants folded and the checked operations on numbers. -/
theorem peb_body_eq (s : BeaconState) (i : Nat) :
    process_effective_balance_updates.body s i =
      (match s.validators[i]? with
      | none => .error .invalid
      | some v =>
        match s.balances[i]? with
        | none => .error .invalid
        | some b => do
          let below : Gwei ← erase (Gwei.mk <$> chkAdd b.val 250000000)
          if below.val < v.effective_balance.val then pebUpdate s i v b
          else do
            let above : Gwei ← erase (Gwei.mk <$> chkAdd v.effective_balance.val 1250000000)
            if decide (above.val < b.val) = true then pebUpdate s i v b else pure s) := by
  unfold process_effective_balance_updates.body listGet
  cases s.validators[i]? with
  | none => rfl
  | some v =>
    cases s.balances[i]? with
    | none => rfl
    | some b =>
      have r1 : (uDiv EFFECTIVE_BALANCE_INCREMENT (cast HYSTERESIS_QUOTIENT) : SpecM Gwei) =
          .ok ⟨250000000⟩ := by rw [uDiv_eq]; rfl
      have r2 : (toUint (⟨250000000⟩ : Gwei) : SpecM Uint64) = .ok ⟨250000000⟩ := by
        rw [toUint_eq]; rfl
      have r3 : uMul (⟨250000000⟩ : Uint64) HYSTERESIS_DOWNWARD_MULTIPLIER = .ok ⟨250000000⟩ := by
        rw [uMul_eq]; rfl
      have r4 : uMul (⟨250000000⟩ : Uint64) HYSTERESIS_UPWARD_MULTIPLIER = .ok ⟨1250000000⟩ := by
        rw [uMul_eq]; rfl
      simp only [Except.pure_ok', Except.bind_ok', r1, r2, r3, r4, uAdd_eq, uMod_eq, uSub_eq,
        ↓reduceIte]
      rfl

theorem peb_loop_eq (s : Readable.BeaconState) (i : Nat) :
    Readable.process_effective_balance_updates.loop s i =
      if i < s.validators.length then
        Readable.process_effective_balance_updates.body s i >>= fun s' =>
          Readable.process_effective_balance_updates.loop s' (i + 1)
      else pure s := by
  rw [Readable.process_effective_balance_updates.loop]
  split
  · split <;> rename_i heq <;> rw [heq] <;> rfl
  · rfl

/-! ## Loop invariant -/

/-- `Footprint process_effective_balance_updates`: it writes each validator object in place. -/
def peb_fp : Footprint := [⟨Id.BeaconState, [.exact fValidators, .any]⟩]

/-- The heap objects of the state at loop start. The loop never writes them. -/
structure PebLayout where
  root : Nat
  va : Nat
  ba : Nat
  fs : List Value
  vrefs : List Value
  bs : List Value

def PebLayout.Ok (Ly : PebLayout) (h : Heap) : Prop :=
  h.objs Ly.root = some (.container Id.BeaconState Ly.fs) ∧
  Ly.fs[fValidators]? = some (.ref Ly.va) ∧ Ly.fs[fBalances]? = some (.ref Ly.ba) ∧
  h.objs Ly.va = some (.list .progressiveList (.container Id.Validator) none Ly.vrefs) ∧
  h.objs Ly.ba = some (.list .progressiveList (.uint gweiTy) none Ly.bs)

/-- Under the layout, a state decodes from its validator and balance lists. -/
theorem decState_layout {Ly : PebLayout} {h : Heap} (hl : Ly.Ok h) :
    decState h (.ref Ly.root) = (do
      let validators ← Ly.vrefs.mapM (decValidator h)
      let balances ← Ly.bs.mapM decGwei
      pure { validators, balances }) := by
  obtain ⟨ho, hv, hb, hova, hoba⟩ := hl
  simp [decState, ho, hv, hb, decList, hova, hoba]

/-- The locals that the body reads and never assigns. -/
def ReadsOk (L : Locals) (root : Nat) : Prop :=
  L Id.state = some (.ref root) ∧ L Id.EFFECTIVE_BALANCE_INCREMENT = none ∧
  L Id.HYSTERESIS_QUOTIENT = none ∧ L Id.HYSTERESIS_DOWNWARD_MULTIPLIER = none ∧
  L Id.HYSTERESIS_UPWARD_MULTIPLIER = none ∧ L Id.Uint64 = none ∧ L Id.min = none ∧
  L Id.get_max_effective_balance = none

/-- The invariant before item `i`. `h0` is the heap at the call. It does not depend on `i`:
the readable loop reads the current state at each index. -/
def PebInv (h0 : Heap) (Ly : PebLayout) (_i : Nat) (s : Readable.BeaconState) (L : Locals)
    (h : Heap) : Prop :=
  Ly.Ok h ∧ decState h (.ref Ly.root) = some s ∧ ReadsOk L Ly.root ∧
  WTree h [.ref Ly.root] peb_fp ∧ Frame h0 h [.ref Ly.root] peb_fp ∧ Fresh h0 h ∧ Ly.Ok h0 ∧
  StateRest h0 h (.ref Ly.root) ∧
  (∀ k q b, at? h [.ref Ly.root] k q = some (.ref b) → at? h0 [.ref Ly.root] k q = some (.ref b))

theorem StateRest_trans {h1 h2 h3 : Heap} {v : Value} (a : StateRest h1 h2 v)
    (b : StateRest h2 h3 v) : StateRest h1 h3 v :=
  fun i q h1' h2' => (b i q h1' h2').trans (a i q h1' h2')

theorem peb_inv_keep {h0 Ly i s L h L'} (hp : PebInv h0 Ly i s L h)
    (hL : ReadsOk L' Ly.root) : PebInv h0 Ly (i + 1) s L' h := by
  obtain ⟨hl, hd, -, hw, hf, hfr, hl0, hr, ha⟩ := hp
  exact ⟨hl, hd, hL, hw, hf, hfr, hl0, hr, ha⟩

/-- The heap paths of the layout objects and of validator `j`. -/
theorem peb_at {Ly : PebLayout} {h : Heap} (hl : Ly.Ok h) :
    at? h [.ref Ly.root] 0 [] = some (.ref Ly.root) ∧
    at? h [.ref Ly.root] 0 [fValidators] = some (.ref Ly.va) ∧
    at? h [.ref Ly.root] 0 [fBalances] = some (.ref Ly.ba) ∧
    ∀ (j : Nat) x, Ly.vrefs[j]? = some x → at? h [.ref Ly.root] 0 [fValidators, j] = some x := by
  obtain ⟨ho, hv, hb, hova, -⟩ := hl
  refine ⟨by simp [at?, follow], by simp [at?, follow, ho, hv],
    by simp [at?, follow, ho, hb], fun j x hj => by simp [at?, follow, ho, hv, hova, hj]⟩

theorem peb_inv_update {h0 Ly i s L h L'} (hp : PebInv h0 Ly i s L h)
    (hL : ReadsOk L' Ly.root) {r : Nat} (hr : Ly.vrefs[i]? = some (.ref r))
    {vfs : List Value} (hvo : h.objs r = some (.container Id.Validator vfs))
    {v : Readable.Validator} (hv : s.validators[i]? = some v)
    (hvf : decValidatorFields vfs = some v) (m : Nat) (hm : m < 2 ^ 64) :
    PebInv h0 Ly (i + 1)
      { s with validators := s.validators.set i { v with effective_balance := ⟨m⟩ } } L'
      (h.set r (.container Id.Validator (vfs.set fEffectiveBalance (.uint gweiTy m)))) := by
  obtain ⟨hl, hd, -, hw, hf, hfr, hl0, hrest, ha⟩ := hp
  obtain ⟨atr, atv, atb, atj⟩ := peb_at hl
  have hfp : (⟨Id.BeaconState, [PStep.exact fValidators, .any]⟩ : FPat) ∈ peb_fp := by
    simp [peb_fp]
  have hfp' : (⟨Id.BeaconState, [PStep.exact fValidators, .any]⟩ : FPat) ∈ peb_fp := by
    simp [peb_fp]
  have hty : RootTy h [.ref Ly.root] 0 Id.BeaconState := rootTy_container rfl hl.1
  have hm' : Matches [PStep.exact fValidators, .any] [fValidators, i] := ⟨rfl, trivial⟩
  have ati := atj i _ hr
  have hrr : Ly.root ≠ r := wtree_ne hw hfp hty hm' ati atr (by simp)
  have hvr : Ly.va ≠ r := wtree_ne hw hfp hty hm' ati atv (by simp)
  have hbr : Ly.ba ≠ r := wtree_ne hw hfp hty hm' ati atb (by simp)
  obtain ⟨ho, hv', hb', hova, hoba⟩ := hl
  have hl' : Ly.Ok (h.set r (.container Id.Validator (vfs.set fEffectiveBalance (.uint gweiTy m)))) :=
    ⟨by simp [hrr, ho], hv', hb', by simp [hvr, hova], by simp [hbr, hoba]⟩
  have hfeb := decValidatorFields_eb hvf
  have skel : SameSkel (.container Id.Validator vfs)
      (.container Id.Validator (vfs.set fEffectiveBalance (.uint gweiTy m))) := by
    refine ⟨rfl, by simp, fun j x y hx hy => ?_⟩
    by_cases hj : j = fEffectiveBalance
    · subst hj
      rw [hfeb.1] at hx; cases hx
      rw [List.getElem?_set_self (by rw [hfeb.2.2.2]; decide)] at hy; cases hy
      intro b; constructor <;> intro e <;> cases e
    · rw [List.getElem?_set_ne (Ne.symm hj), hx] at hy; cases hy; exact RefEq.refl _
  have hmono : ∀ a, AtFp h [.ref Ly.root] peb_fp a → AtFp h0 [.ref Ly.root] peb_fp a := by
    rintro a ⟨k, pat, q, hpat, ⟨c, hc, -⟩, hq, hat⟩
    refine ⟨k, pat, q, hpat, ?_, hq, ha k q a hat⟩
    simp [peb_fp] at hpat; subst hpat
    match k, hc with
    | 0, hc => simp at hc; subst hc; exact rootTy_container rfl hl0.1
    | _ + 1, hc => simp at hc
  refine ⟨hl', ?_, hL, WTree_skel hvo skel hw,
    Frame_trans hf (Frame_set ⟨0, _, [fValidators, i], hfp', hty, hm', ati⟩) hmono,
    Fresh_trans hfr (Fresh_set hvo), hl0,
    StateRest_trans hrest ?_, fun k q b e => ha k q b ((at?_skel hvo skel _ k q b).mp e)⟩
  · rw [decState_layout hl']
    rw [decState_layout ⟨ho, hv', hb', hova, hoba⟩] at hd
    cases hmv : Ly.vrefs.mapM (decValidator h) with
    | none => simp [hmv] at hd
    | some vals =>
      cases hmb : Ly.bs.mapM decGwei with
      | none => simp [hmv, hmb] at hd
      | some bals =>
        simp only [hmv, hmb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hd
        subst hd
        obtain ⟨hlen, hel⟩ := (mapM_some_iff _ _).mp hmv
        have hmv' : Ly.vrefs.mapM (decValidator (h.set r
            (.container Id.Validator (vfs.set fEffectiveBalance (.uint gweiTy m))))) =
            some (vals.set i { v with effective_balance := ⟨m⟩ }) := by
          refine (mapM_some_iff _ _).mpr ⟨by simp [hlen], fun j x hx => ?_⟩
          by_cases hji : j = i
          · subst hji
            rw [hr] at hx; cases hx
            have hil : j < vals.length := (List.getElem?_eq_some_iff.mp hv).1
            simp [decValidator, decValidatorFields_set_eb hvf m hm, hil]
          · rw [List.getElem?_set_ne (Ne.symm hji), ← hel j x hx]
            cases x with
            | ref c =>
              have hc : c ≠ r := wtree_ne hw hfp hty hm' ati (atj j _ hx) (by simp [hji])
              exact decValidator_congr (by simp [hc])
            | _ => rfl
        simp [hmv']
  · intro j q hj1 hj2
    apply follow_set_away
    intro p rr hq hrr' hp
    obtain ⟨-, rfl⟩ := hw 0 _ hfp hty [fValidators, i] hm' r ati 0 p (by simpa [at?] using hp)
    simp at hq; exact hj1 hq.1

/-! ## One iteration -/

/-- One loop iteration: the target assignment and the body. -/
theorem peb_step (h0 : Heap) (Ly : PebLayout)
    (l : Line) (t : Target) (it : Expr) (body : List Stmt)
    (hfn : fn_process_effective_balance_updates.body = [.forStmt l t it body]) :
    ∀ n i s L h, PebInv h0 Ly i s L h → i < s.validators.length → ∃ x,
      iterItem h (.enum (.live Ly.va)) i = .ok (some x) ∧
      StepRel (PebInv h0 Ly (i + 1)) (do
        let (L1, h1) ← assignTarget (env sha) (n + 20) L h t x
        execBlock (env sha) (n + 20) L1 h1 body)
      (Readable.process_effective_balance_updates.body s i) := by
  simp only [fn_process_effective_balance_updates, List.cons.injEq, Stmt.forStmt.injEq,
    and_true] at hfn
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hfn
  intro k i s L h hp hi
  have hp' := hp
  obtain ⟨hl, hd, ⟨hLs, hL28, hL29, hL31, hL33, hLu, hLm, hLg⟩, -, -, -, -⟩ := hp'
  have hl' := hl
  obtain ⟨hroot, hfv, hfb, hova, hoba⟩ := hl'
  rw [decState_layout hl] at hd
  cases hmv : Ly.vrefs.mapM (decValidator h) with
  | none => simp [hmv] at hd
  | some vals =>
  cases hmb : Ly.bs.mapM decGwei with
  | none => simp [hmv, hmb] at hd
  | some bals =>
  simp only [hmv, hmb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hd
  subst hd
  obtain ⟨hvlen, hvel⟩ := (mapM_some_iff _ _).mp hmv
  obtain ⟨hblen, hbel⟩ := (mapM_some_iff _ _).mp hmb
  obtain ⟨v, hv⟩ : ∃ v, vals[i]? = some v := ⟨vals[i], List.getElem?_eq_getElem hi⟩
  obtain ⟨x, hx⟩ : ∃ x, Ly.vrefs[i]? = some x :=
    ⟨Ly.vrefs[i]'(hvlen ▸ hi), List.getElem?_eq_getElem _⟩
  have hdx := hvel i x hx
  rw [hv] at hdx
  cases x with
  | ref r => ?_
  | _ => simp [decValidator] at hdx
  obtain ⟨vfs, hvo, hvf⟩ := decValidator_some hdx
  obtain ⟨hveb, hv64, hvwc, hvlen8⟩ := decValidatorFields_eb hvf
  refine ⟨.tuple [.int i, .ref r], by simp [iterItem, seqItem, hova, hx, enumItem], ?_⟩
  have c11 : callValue (env sha) (k + 18) (.glob Id.get_max_effective_balance) [.ref r] [] h =
      .ok (.uint gweiTy (Readable.get_max_effective_balance v).val, h) := by
    rw [show k + 18 = (k + 4) + 14 by omega]
    exact get_max_effective_balance_run sha _ h r v hdx
  simp [assignTarget, assignTargets, execBlock, execStmt, evalExpr, evalList, evalArgs, lookupName,
    hLs, hL28, hL29, hL31, hL33, hLu, hLm, hLg, g_EBI sha, g_HQ sha, g_HDM sha, g_HUM sha,
    g_Uint64 sha, g_min sha, g_get_max sha, call_Uint64, c11, call_min, Ssz.construct,
    getAttr_container _ hroot (fi_balances sha), hfb, getItem_list_int hoba]
  rw [peb_body_eq]
  simp only [hv]
  have c11' : callValue (env sha) (k + 18) (.glob Id.get_max_effective_balance) [.ref r] [] h =
      .ok (.uint gweiTy (Readable.get_max_effective_balance v).val, h) := c11
  have hkeep : ∀ a1 a2 a3 a4 a5 : Value, ReadsOk ((((((((L.set Id.index (.int i)).set
      Id.validator (.ref r)).set Id.balance a1).set Id.HYSTERESIS_INCREMENT a2).set
      Id.DOWNWARD_THRESHOLD a3).set Id.UPWARD_THRESHOLD a4).set Id.max_effective_balance a5))
      Ly.root := by
    intro a1 a2 a3 a4 a5
    simp (config := { decide := true }) [ReadsOk, hLs, hL28, hL29, hL31, hL33, hLu, hLm, hLg]
  cases hbi : Ly.bs[i]? with
  | none =>
    have : bals[i]? = none := by rw [List.getElem?_eq_none_iff] at hbi ⊢; omega
    simp [this, StepRel, SpecError.fail]
  | some y =>
  have hdy := hbel i y hbi
  cases hgi : bals[i]? with
  | none =>
    have := (List.getElem?_eq_some_iff.mp hbi).1
    rw [List.getElem?_eq_none_iff] at hgi; omega
  | some g =>
  rw [hgi] at hdy
  obtain ⟨rfl, hg64⟩ := decGwei_some hdy
  have k2 : wrapUint u64Ty ((250000000 : Nat) : Int) = .ok (.uint u64Ty 250000000) := rfl
  have k1 : binopVal .floorDiv (.uint gweiTy 1000000000) (.uint u64Ty 4) =
    .ok (.uint gweiTy 250000000) := rfl
  have k3 : binopVal .mul (.uint u64Ty 250000000) (.uint u64Ty 1) =
    .ok (.uint u64Ty 250000000) := rfl
  have k4 : binopVal .mul (.uint u64Ty 250000000) (.uint u64Ty 5) =
    .ok (.uint u64Ty 1250000000) := rfl
  simp only [Except.bind_ok', Except.pure_ok', k1, k2, k3, k4]
  have rg : resolveUint gweiTy u64Ty = .ok gweiTy := rfl
  have rgg : resolveUint gweiTy gweiTy = .ok gweiTy := rfl
  simp only [evalBoolOp, evalExpr, evalCmp, lookupName, Locals.set_apply, seqBinop_uu,
    Except.bind_ok', Except.pure_ok', binop_add (hr := rg) (hb := rfl), ↓reduceIte,
    Nat.reduceEqDiff, List.isEmpty_cons, List.isEmpty_nil, Bool.false_eq_true]
  cases h1 : chkAdd g.val 250000000 with
  | error e => simp [StepRel, chkAdd_ne_oof h1, c11', SpecError.fail]
  | ok below =>
  obtain ⟨rfl, o1⟩ := chkAdd_ok h1
  have hb64 : g.val < 2 ^ 64 := hg64
  have hmod : chkMod g.val 1000000000 = .ok (g.val % 1000000000) :=
    chkMod_ok _ _ (by decide) (by decide)
  have hsub : chkSub g.val (g.val % 1000000000) = .ok (g.val - g.val % 1000000000) :=
    chkSub_ok _ _ (Nat.mod_le _ _) hb64
  have hrounded : g.val - g.val % 1000000000 ≤ g.val := Nat.sub_le _ _
  set_option maxRecDepth 4000 in
  have hupd : pebUpdate { validators := vals, balances := bals } i v g = .ok
      { validators := vals.set i (pebNew v g), balances := bals } := by
    simp only [pebUpdate, hmod, hsub, Except.map_ok', erase_ok, Except.bind_ok', Except.pure_ok']
    rfl
  have hm64 : (Readable.umin (⟨g.val - g.val % 1000000000⟩ : Readable.Gwei)
      (Readable.get_max_effective_balance v)).val < 2 ^ 64 := by
    unfold Readable.umin; split
    · unfold Readable.get_max_effective_balance; split <;> decide
    · exact Nat.lt_of_le_of_lt hrounded hb64
  have hmin : applyBuiltin (env sha) h .min [.uint gweiTy (g.val - g.val % 1000000000),
      .uint gweiTy (Readable.get_max_effective_balance v).val] [] =
      .ok (.uint gweiTy (Readable.umin (⟨g.val - g.val % 1000000000⟩ : Readable.Gwei)
        (Readable.get_max_effective_balance v)).val, h) := by
    simp only [applyBuiltin, LibModel.builtin, Ssz.builtin, pickBest, cmp_uint (hr := rgg),
      cmpInt, Except.bind_ok',
      decide_eq_true_eq, Int.ofNat_lt, Readable.umin, Except.pure_ok']
    by_cases hm : (Readable.get_max_effective_balance v).val < g.val - g.val % 1000000000
    · simp [hm, Readable.val]
    · simp [hm, Readable.val]
  have hset : setAttr (env sha) h (.ref r) Id.effective_balance
      (.uint gweiTy (Readable.umin (⟨g.val - g.val % 1000000000⟩ : Readable.Gwei)
        (Readable.get_max_effective_balance v)).val) =
      .ok (h.set r (.container Id.Validator (vfs.set fEffectiveBalance
        (.uint gweiTy (Readable.umin (⟨g.val - g.val % 1000000000⟩ : Readable.Gwei)
          (Readable.get_max_effective_balance v)).val)))) := by
    rw [setAttr_container _ hvo (fi_eb sha) _ (fun _ e => by cases e)]
    simp only [coerceField, gweiTy, UintTy.bits] at hm64 ⊢
    simp [hm64]
  simp only [Except.map_ok', Except.bind_ok', cmpInt, Int.ofNat_lt, decide_eq_true_eq, truthy, LibValues.truthy, Ssz.truthy, pyTruthy,
    c11', compareOp, truthyH, getAttr_container _ hvo (fi_eb sha), hveb, cmp_uint (hr := rgg),
    seqBinop_uu,
    binop_mod (hr := rgg) (hb := rfl), binop_sub (hr := rgg) (hb := rfl), hmod, hsub, erase_ok]
  by_cases c1 : g.val + 250000000 < v.effective_balance.val
  · simp only [c1, ↓reduceIte, Except.bind_ok', hmin, hset, hupd]
    exact peb_inv_update hp (hkeep _ _ _ _ _) hx hvo hv hvf _ hm64
  simp only [c1, ↓reduceIte, Except.bind_ok', seqBinop_uu,
    getAttr_container _ hvo (fi_eb sha), hveb, binop_add (hr := rg) (hb := rfl)]
  cases h2 : chkAdd v.effective_balance.val 1250000000 with
  | error e => simp [StepRel, chkAdd_ne_oof h2, c11', compareOp, truthyH, SpecError.fail]
  | ok above =>
  simp only [Except.map_ok', Except.bind_ok', cmp_uint (hr := rgg), cmpInt, Int.ofNat_lt,
    decide_eq_true_eq, erase_ok]
  by_cases c2 : above < g.val
  · simp only [c2, ↓reduceIte, Except.bind_ok', hmin, hset, hupd]
    exact peb_inv_update hp (hkeep _ _ _ _ _) hx hvo hv hvf _ hm64
  · simp only [c2, ↓reduceIte, Except.bind_ok', Bool.false_eq_true]
    exact peb_inv_keep hp (hkeep _ _ _ _ _)

/-! ## The whole function -/

/-- The result: `None`, the state decodes to the readable result, and the fields of the state
that the readable `BeaconState` leaves out are unchanged. -/
def PebExpect (h : Heap) (root : Nat) : Readable.BeaconState → Heap → Value → Prop :=
  fun s' h' v => v = .none ∧ decState h' (.ref root) = some s' ∧ StateRest h h' (.ref root)

theorem process_effective_balance_updates_run (k : Nat) (h : Heap) (root : Nat)
    (state : Readable.BeaconState) (hd : decState h (.ref root) = some state)
    (hw : WTree h [.ref root] peb_fp) :
    ResultMatches gfp peb_fp h [.ref root] (PebExpect h root)
      (callName (env sha) (k + state.validators.length + 26)
        Id.process_effective_balance_updates [.ref root] h)
      (Readable.process_effective_balance_updates state) := by
  obtain ⟨fs, va, ba, vrefs, bs, hroot, hfv, hfb, hova, hmv, hoba, hmb⟩ := decState_some hd
  let Ly : PebLayout := ⟨root, va, ba, fs, vrefs, bs⟩
  have hl : Ly.Ok h := ⟨hroot, hfv, hfb, hova, hoba⟩
  have hvlen : state.validators.length = vrefs.length := ((mapM_some_iff _ _).mp hmv).1
  obtain ⟨l, t, it, body, hfn⟩ : ∃ l t it body,
      fn_process_effective_balance_updates.body = [.forStmt l t it body] := ⟨_, _, _, _, rfl⟩
  have hfor := interp_for (env sha) t body (.enum (.live va)) 20
    (fun s => s.validators.length) (fun s i => Readable.process_effective_balance_updates.body s i)
    (fun s i => Readable.process_effective_balance_updates.loop s i) peb_loop_eq
    (fun s i s' e => Readable.process_effective_balance_updates.body_length e)
    (PebInv h Ly) ?hend (peb_step sha h Ly l t it body hfn)
    (k + state.validators.length + 3) 0 state
    (Locals.empty.set Id.state (.ref root)) h ?hinit (by omega)
  case hend =>
    intro i s L h' hp hi
    obtain ⟨hl', hd', -⟩ := hp
    have hova' := hl'.2.2.2.1
    rw [decState_layout hl'] at hd'
    cases hm : vrefs.mapM (decValidator h') with
    | none => simp [Ly, hm] at hd'
    | some vals =>
      cases hm2 : bs.mapM decGwei with
      | none => simp [Ly, hm, hm2] at hd'
      | some bals =>
        simp only [Ly, hm, hm2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hd'
        subst hd'
        have hl2 := ((mapM_some_iff _ _).mp hm).1
        have : vrefs[i]? = none := by
          rw [List.getElem?_eq_none_iff]; simp at hi; omega
        simp [iterItem, seqItem, Ly, hova', this]
  case hinit =>
    refine ⟨hl, hd, ?_, hw, Frame_refl h _ _, Fresh_refl h, hl, fun _ _ _ _ => rfl,
      fun _ _ _ e => e⟩
    simp (config := { decide := true }) [ReadsOk, Ly]
  simp only [fn_process_effective_balance_updates, List.cons.injEq, Stmt.forStmt.injEq,
    and_true] at hfn
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hfn
  rw [callName, callValue_fn _ _ _ (g_peb sha)]
  simp [callFn, fn_process_effective_balance_updates, execBlock, execStmt, evalExpr, evalList,
    evalArgs, lookupName, bindArgs, bindArgs.go, g_enumerate sha,
    getAttr_container _ hroot (fi_validators sha), hfv, call_enumerate, applyBuiltin,
    LibModel.builtin, Ssz.builtin,
    iterSource, toSeq, hova]
  rw [show k + state.validators.length + 24 = k + state.validators.length + 3 + 20 + 1 by omega]
  rw [Readable.process_effective_balance_updates]
  revert hfor
  generalize Readable.process_effective_balance_updates.loop state 0 = R
  generalize execFor _ _ _ _ _ _ _ _ = E
  intro hfor
  rcases E with e | ⟨o, L', h'⟩ <;> rcases R with e' | s'
  · simp only [StepRel] at hfor; simp [ResultMatches, hfor]
  · simp only [StepRel] at hfor
  · cases o <;> simp only [StepRel] at hfor
  · cases o <;> simp only [StepRel] at hfor
    obtain ⟨i, ⟨-, hd', -, -, hf', hfr, -, hrest, ha⟩, -⟩ := hfor
    simp only [Except.bind_ok', ResultMatches, PebExpect]
    exact ⟨⟨trivial, hd', hrest⟩, hf', hfr, noNewPaths_of_reach
      fun k q b e => .inl (ha k q b e)⟩

/-- SPEC 9.2: `process_effective_balance_updates` validated against the interpreter. The fuel
bound grows with the number of validators, because each loop iteration costs fuel. -/
theorem process_effective_balance_updates_valid (h : Heap) (root : Nat)
    (state : Readable.BeaconState) (hd : decState h (.ref root) = some state)
    (_hwf : HeapWF h) (_haw : ArgsWF h [.ref root]) (hw : WTree h [.ref root] peb_fp) :
    ∃ N, ∀ fuel ≥ N,
      ResultMatches gfp peb_fp h [.ref root] (PebExpect h root)
        (interp (env sha) fuel Id.process_effective_balance_updates [.ref root] h)
        (Readable.process_effective_balance_updates state) :=
  ⟨state.validators.length + 26, fun fuel hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    rw [← Nat.add_assoc]
    exact process_effective_balance_updates_run sha k h root state hd hw⟩

end SpecLean.Validation
