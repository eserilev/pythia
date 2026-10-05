import SpecLean.Validation.Common

/-!
# Validation: credential checks and `get_max_effective_balance`

These callees do not change the heap. Each `_run` lemma gives the call result for fuel `k + N`.
Callers rewrite with it. The `_valid` theorems state the same in the SPEC 9.2 shape.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Gen SpecLean.Encode

variable (sha : Oracle)

theorem is_compounding_withdrawal_credential_run (k : Nat) (h : Heap) (wc : List UInt8) :
    callValue (env sha) (k + 6) (.glob Id.is_compounding_withdrawal_credential)
      [.bytes Id.Bytes32 wc] [] h =
      .ok (.bool (Readable.is_compounding_withdrawal_credential ⟨wc⟩), h) := by
  rw [callValue_fn _ _ _ (g_is_comp sha)]
  simp [callFn, fn_is_compounding_withdrawal_credential, execBlock, execStmt, evalExpr, evalCmp,
    evalOpt, evalList, lookupName, bindArgs, bindArgs.go, getSlice, sliceRange, toIndex, LibValues.index, Ssz.index, pyIndex,
    sliceBound, compareOp]
  have ht : List.take (min 1 wc.length) wc = List.take 1 wc :=
    List.take_eq_take_iff.mpr (by omega)
  simp only [g_PREFIX, ht, Except.bind_ok', deepEq_bytes]
  simp [Readable.is_compounding_withdrawal_credential, Readable.COMPOUNDING_WITHDRAWAL_PREFIX,
    cmpVal, LibValues.compare, Ssz.compare, pyCmp]
  by_cases he : List.take 1 wc = [2] <;> simp [he]

theorem has_compounding_withdrawal_credential_run (k : Nat) (h : Heap) (r : Nat)
    (x : Readable.Validator) (hx : decValidator h (.ref r) = some x) :
    callValue (env sha) (k + 10) (.glob Id.has_compounding_withdrawal_credential) [.ref r] [] h =
      .ok (.bool (Readable.has_compounding_withdrawal_credential x), h) := by
  obtain ⟨fs, ho, hf⟩ := decValidator_some hx
  obtain ⟨-, -, hwc, -⟩ := decValidatorFields_eb hf
  rw [callValue_fn _ _ _ (g_has_comp sha)]
  simp [callFn, fn_has_compounding_withdrawal_credential, execBlock, execStmt, evalExpr,
    evalList, evalArgs, lookupName, bindArgs, bindArgs.go, getAttr_container _ ho (fi_wc sha), hwc,
    g_is_comp]
  rw [show k + 7 = (k + 1) + 6 by omega, is_compounding_withdrawal_credential_run]
  rfl

theorem get_max_effective_balance_run (k : Nat) (h : Heap) (r : Nat) (x : Readable.Validator)
    (hx : decValidator h (.ref r) = some x) :
    callValue (env sha) (k + 14) (.glob Id.get_max_effective_balance) [.ref r] [] h =
      .ok (.uint gweiTy (Readable.get_max_effective_balance x).val, h) := by
  rw [callValue_fn _ _ _ (g_get_max sha)]
  simp [callFn, fn_get_max_effective_balance, execBlock, execStmt, evalExpr,
    evalList, evalArgs, lookupName, bindArgs, bindArgs.go, g_has_comp]
  rw [show k + 11 = (k + 1) + 10 by omega, has_compounding_withdrawal_credential_run sha _ h r x hx]
  simp [truthy, LibValues.truthy, Ssz.truthy, pyTruthy, Readable.get_max_effective_balance]
  cases Readable.has_compounding_withdrawal_credential x <;> rfl

/-! ## Validation theorems (SPEC 9.2 shape) -/

theorem is_compounding_withdrawal_credential_valid (h : Heap) (wc : List UInt8) :
    ∃ N, ∀ fuel ≥ N,
      ResultMatches [] h [.bytes Id.Bytes32 wc]
        (fun b _ v => v = .bool b)
        (interp (env sha) fuel Id.is_compounding_withdrawal_credential [.bytes Id.Bytes32 wc] h)
        (pure (Readable.is_compounding_withdrawal_credential ⟨wc⟩)) :=
  ⟨6, fun fuel hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    rw [interp, callName, is_compounding_withdrawal_credential_run]
    refine ⟨rfl, pure_result ?_⟩
    rintro k ⟨a, fs, hk, -⟩
    match k with
    | 0 | 1 => simp at hk
    | _ + 2 => simp at hk⟩

theorem get_max_effective_balance_valid (h : Heap) (r : Nat) (x : Readable.Validator)
    (hx : decValidator h (.ref r) = some x) :
    ∃ N, ∀ fuel ≥ N,
      ResultMatches [] h [.ref r]
        (fun g h' v => decGwei v = some g ∧ decValidator h' (.ref r) = some x)
        (interp (env sha) fuel Id.get_max_effective_balance [.ref r] h)
        (pure (Readable.get_max_effective_balance x)) :=
  ⟨14, fun fuel hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    rw [interp, callName, get_max_effective_balance_run sha k h r x hx]
    refine ⟨⟨?_, hx⟩, pure_result ?_⟩
    · unfold Readable.get_max_effective_balance
      split <;> exact decGwei_uint _ (by decide)
    · obtain ⟨vfs, ho, -⟩ := decValidator_some hx
      rintro k ⟨a, fs, hk, hoa⟩
      match k with
      | 0 => simp at hk; subst hk; rw [ho] at hoa; cases hoa
      | 1 => simp at hk
      | _ + 2 => simp at hk⟩

end SpecLean.Validation
