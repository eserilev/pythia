import SpecLean.Validation.Common

/-!
# Validation: `decrease_balance` and `saturating_sub`
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Gen SpecLean.Encode

variable (sha : Oracle)

/-- The checked result of `saturating_sub` on two numbers. -/
def satSub (a b : Nat) : Res Nat := if b < a then chkSub a b else chkSub a a

theorem saturating_sub_run (k : Nat) (h : Heap) (a b : Nat) :
    callValue (env sha) (k + 6) (.glob Id.saturating_sub) [.uint gweiTy a, .uint gweiTy b] [] h =
      (fun r => (Value.uint gweiTy r, h)) <$> satSub a b := by
  rw [callValue_fn _ _ _ (g_saturating_sub sha)]
  have rg : resolveUint gweiTy gweiTy = .ok gweiTy := rfl
  simp [callFn, fn_saturating_sub, execBlock, execStmt, evalExpr, evalCmp, evalList, lookupName,
    bindArgs, bindArgs.go, compareOp, cmp_uint (hr := rg), cmpInt, truthyH, truthy,
    binop_sub (hr := rg) (hb := rfl), satSub]
  by_cases hab : b < a
  · simp only [hab, ↓reduceIte]; cases chkSub a b <;> rfl
  · simp only [hab, ↓reduceIte]; cases chkSub a a <;> rfl

theorem saturating_sub_readable (a b : Nat) :
    Readable.saturating_sub (⟨a⟩ : Readable.Gwei) ⟨b⟩ =
      Readable.erase (Readable.Gwei.mk <$> satSub a b) := by
  unfold Readable.saturating_sub satSub
  have hv : ∀ n, Readable.val (Readable.Gwei.mk n) = n := fun _ => rfl
  simp only [hv, uSub_eq]
  by_cases hab : b < a <;> simp only [hab, ↓reduceIte] <;> rfl

/-- `Footprint decrease_balance`: it writes the balances list of the state in place. -/
def decrease_balance_fp : Footprint := [⟨Id.BeaconState, [.exact fBalances]⟩]

/-- The result: `None`, the state decodes to the readable result, the fields of the state that
the readable `BeaconState` leaves out are unchanged, and the plain arguments decode to their
values. -/
def DecreaseBalanceExpect (h : Heap) (vs : List Value) (index : Readable.ValidatorIndex)
    (delta : Readable.Gwei) : Readable.BeaconState → Heap → Value → Prop :=
  fun s' h' v => v = .none ∧ decState h' vs[0]! = some s' ∧ StateRest h h' vs[0]! ∧
    decVidx vs[1]! = some index ∧ decGwei vs[2]! = some delta

theorem decrease_balance_run (k : Nat) (h : Heap) (root : Nat) (state : Readable.BeaconState)
    (index : Readable.ValidatorIndex) (delta : Readable.Gwei)
    (hd : decState h (.ref root) = some state)
    (hix : decVidx (.uint vidxTy index.val) = some index)
    (hdl : decGwei (.uint gweiTy delta.val) = some delta)
    (hw : WTree h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val] FP) :
    ResultMatches decrease_balance_fp h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val]
      (DecreaseBalanceExpect h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val]
        index delta)
      (callName (env sha) (k + 12) Id.decrease_balance
        [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val] h)
      (Readable.decrease_balance state index delta) := by
  obtain ⟨fs, va, ba, vrefs, bs, hroot, hfv, hfb, hova, hmv, hoba, hmb⟩ := decState_some hd
  have hfp : (⟨Id.BeaconState, [PStep.exact fBalances]⟩ : FPat) ∈ FP := by simp [FP]
  have hfp' : (⟨Id.BeaconState, [PStep.exact fBalances]⟩ : FPat) ∈ decrease_balance_fp := by
    simp [decrease_balance_fp]
  have hty : RootTy h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val] 0
      Id.BeaconState := ⟨root, fs, rfl, hroot⟩
  have hm : Matches [PStep.exact fBalances] [fBalances] := ⟨rfl, trivial⟩
  have atb : at? h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val] 0 [fBalances] = some (.ref ba) := by simp [at?, follow, hroot, hfb]
  have hrb : root ≠ ba := wtree_ne hw hfp hty hm atb (q' := []) (k' := 0) (by simp [at?, follow])
    (by simp)
  have hvb : va ≠ ba := wtree_ne hw hfp hty hm atb (q' := [fValidators]) (k' := 0)
    (by simp [at?, follow, hroot, hfv]) (by decide)
  have hrefb : ∀ (j : Nat) r, vrefs[j]? = some (.ref r) → r ≠ ba := fun j r hj =>
    wtree_ne hw hfp hty hm atb (q' := [fValidators, j]) (k' := 0)
      (by simp [at?, follow, hroot, hfv, hova, hj]) (by simp)
  rw [callName, callValue_fn _ _ _ (g_decrease_balance sha)]
  simp [callFn, fn_decrease_balance, execBlock, execStmt, evalExpr, evalList, evalArgs, lookupName,
    bindArgs, bindArgs.go, assignTarget, getAttr_container _ hroot (fi_balances sha), hfb,
    getItem_list hoba, g_saturating_sub]
  simp only [Readable.decrease_balance, Readable.listGet]
  obtain ⟨hlen, hel⟩ := (mapM_some_iff bs state.balances).mp hmb
  cases hb : bs[index.val]? with
  | none =>
    have : state.balances[index.val]? = none := by
      rw [List.getElem?_eq_none_iff] at hb ⊢; omega
    simp [this, ResultMatches, SpecError.fail]
  | some x =>
    have hg := hel index.val x hb
    cases hgb : state.balances[index.val]? with
    | none =>
      have := (List.getElem?_eq_some_iff.mp hb).1
      rw [List.getElem?_eq_none_iff] at hgb; omega
    | some g =>
    rw [hgb] at hg
    obtain ⟨rfl, -⟩ := decGwei_some hg
    simp only [Except.bind_ok', Except.pure_ok']
    rw [show k + 9 = (k + 3) + 6 by omega, saturating_sub_run,
      show g = ⟨g.val⟩ from rfl, saturating_sub_readable]
    cases hs : satSub g.val delta.val with
    | error e =>
      have : e ≠ .outOfFuel := by
        unfold satSub at hs; split at hs <;> exact chkSub_ne_oof hs
      simp [ResultMatches, this]
    | ok r =>
      have hr64 : r < 2 ^ 64 := by unfold satSub at hs; split at hs <;> exact chkSub_lt hs
      have hi : index.val < bs.length := (List.getElem?_eq_some_iff.mp hb).1
      simp [getAttr_container _ hroot (fi_balances sha), hfb,
        setItem_list hoba vidxTy index.val (.uint gweiTy r) (fun _ e => by cases e), coerceElem,
        Readable.listSet, hi, hlen ▸ hi, ResultMatches, DecreaseBalanceExpect]
      have hbsnr : ∀ (j : Nat) y, bs[j]? = some y → ∀ b, y ≠ .ref b := by
        intro j y hy
        have := hel j y hy
        cases hgj : state.balances[j]? with
        | none =>
          have := (List.getElem?_eq_some_iff.mp hy).1
          rw [List.getElem?_eq_none_iff] at hgj; omega
        | some gj => rw [hgj] at this; exact decGwei_nonref this
      have skel : SameSkel (.list .progressiveList (.uint gweiTy) none bs)
          (.list .progressiveList (.uint gweiTy) none (bs.set index.val (.uint gweiTy r))) := by
        refine ⟨rfl, rfl, rfl, by simp, fun j x y hx hy b => ?_⟩
        have hxn := hbsnr j x hx b
        have hyn : y ≠ .ref b := by
          rw [List.getElem?_set] at hy
          split at hy
          · cases hy; intro e; cases e
          · rw [hx] at hy; cases hy; exact hxn
        exact ⟨fun e => absurd e hxn, fun e => absurd e hyn⟩
      refine ⟨⟨?_, ?_, hix, hdl⟩, Frame_set ⟨0, _, [fBalances], hfp', hty, hm, atb⟩,
        Fresh_set hoba, Reach_skel hoba skel _, ?_⟩
      · refine decState_of (vrefs := vrefs) (bs := bs.set index.val (.uint gweiTy r))
          (by simp [hrb, hroot]) hfv hfb (by simp [hvb, hova]) ?_ (by simp)
          (mapM_set hmb index.val _ _ (decGwei_uint r hr64))
        rw [← hmv]
        apply mapM_congr
        intro j x hx
        cases x with
        | ref c => exact decValidator_congr (by simp [hrefb j c hx])
        | _ => rfl
      · intro i q hi1 hi2
        apply follow_set_away
        intro p rr hq hrr hp
        obtain ⟨-, rfl⟩ := hw 0 _ hfp hty [fBalances] hm ba atb 0 p (by simpa [at?] using hp)
        simp at hq; exact hi2 hq.1
      · have := WTree_append_nonref (v := .none) (fun b e => by cases e)
          (WTree_skel hoba skel hw)
        simpa using this

/-- SPEC 9.2: `decrease_balance` validated against the interpreter. -/
theorem decrease_balance_valid (h : Heap) (root : Nat) (state : Readable.BeaconState)
    (index : Readable.ValidatorIndex) (delta : Readable.Gwei)
    (hd : decState h (.ref root) = some state)
    (hix : decVidx (.uint vidxTy index.val) = some index)
    (hdl : decGwei (.uint gweiTy delta.val) = some delta)
    (_hwf : HeapWF h) (_haw : ArgsWF h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val])
    (hw : WTree h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val] FP) :
    ∃ N, ∀ fuel ≥ N,
      ResultMatches decrease_balance_fp h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val]
        (DecreaseBalanceExpect h [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val]
          index delta)
        (interp (env sha) fuel Id.decrease_balance
          [.ref root, .uint vidxTy index.val, .uint gweiTy delta.val] h)
        (Readable.decrease_balance state index delta) :=
  ⟨12, fun fuel hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    exact decrease_balance_run sha k h root state index delta hd hix hdl hw⟩

end SpecLean.Validation
