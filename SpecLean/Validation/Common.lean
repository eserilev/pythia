import SpecLean.Bridge
import SpecLean.DecodeLemmas

/-!
# Facts about the generated environment

Each fact holds by `rfl` on the generated data. The translator emits these with the syntax
trees. Here they are written by hand.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Gen SpecLean.Encode SpecLean.Readable

variable (sha : Oracle)

theorem fi_balances : fieldIndex (env sha) Id.BeaconState Id.balances =
    some (fBalances, .list .progressiveList (.uint gweiTy) none) := rfl

theorem fi_validators : fieldIndex (env sha) Id.BeaconState Id.validators =
    some (fValidators, .list .progressiveList (.container Id.Validator) none) := rfl

theorem fi_wc : fieldIndex (env sha) Id.Validator Id.withdrawal_credentials =
    some (fWithdrawalCredentials, .bytes Id.Bytes32 32) := rfl

theorem fi_eb : fieldIndex (env sha) Id.Validator Id.effective_balance =
    some (fEffectiveBalance, .uint gweiTy) := rfl

theorem g_EBI : (env sha).globals.lookup Id.EFFECTIVE_BALANCE_INCREMENT =
    some (.const (.uint gweiTy 1000000000)) := rfl
theorem g_HQ : (env sha).globals.lookup Id.HYSTERESIS_QUOTIENT =
    some (.const (.uint u64Ty 4)) := rfl
theorem g_HDM : (env sha).globals.lookup Id.HYSTERESIS_DOWNWARD_MULTIPLIER =
    some (.const (.uint u64Ty 1)) := rfl
theorem g_HUM : (env sha).globals.lookup Id.HYSTERESIS_UPWARD_MULTIPLIER =
    some (.const (.uint u64Ty 5)) := rfl
theorem g_PREFIX : (env sha).globals.lookup Id.COMPOUNDING_WITHDRAWAL_PREFIX =
    some (.const (.bytes Id.Bytes1 [2])) := rfl
theorem g_UINT64_MAX : (env sha).globals.lookup Id.UINT64_MAX =
    some (.const (.uint u64Ty 18446744073709551615)) := rfl
theorem g_UINT64_MAX_SQRT : (env sha).globals.lookup Id.UINT64_MAX_SQRT =
    some (.const (.uint u64Ty 4294967295)) := rfl

theorem g_is_comp : (env sha).globals.lookup Id.is_compounding_withdrawal_credential =
    some (.fn fn_is_compounding_withdrawal_credential) := rfl
theorem g_has_comp : (env sha).globals.lookup Id.has_compounding_withdrawal_credential =
    some (.fn fn_has_compounding_withdrawal_credential) := rfl
theorem g_get_max : (env sha).globals.lookup Id.get_max_effective_balance =
    some (.fn fn_get_max_effective_balance) := rfl
theorem g_saturating_sub : (env sha).globals.lookup Id.saturating_sub =
    some (.fn fn_saturating_sub) := rfl
theorem g_decrease_balance : (env sha).globals.lookup Id.decrease_balance =
    some (.fn fn_decrease_balance) := rfl
theorem g_peb : (env sha).globals.lookup Id.process_effective_balance_updates =
    some (.fn fn_process_effective_balance_updates) := rfl
theorem g_isqrt : (env sha).globals.lookup Id.integer_squareroot =
    some (.fn fn_integer_squareroot) := rfl
theorem g_Uint64 : (env sha).globals.lookup Id.Uint64 = some (.type (.uint u64Ty)) := rfl
theorem g_min : (env sha).globals.lookup Id.min = some (.builtin .min) := rfl
theorem g_enumerate : (env sha).globals.lookup Id.enumerate = some (.builtin .enumerate) := rfl

theorem call_Uint64 (n : Nat) (w : Value) (h : Heap) :
    callValue (env sha) n (.glob Id.Uint64) [w] [] h =
      applyType (env sha) h (.uint u64Ty) [w] [] := by
  have g : (env sha).globals.lookup Id.Uint64 = some (.type (.uint u64Ty)) := rfl
  rw [callValue.eq_def]; simp only [g]

theorem call_min (n : Nat) (a b : Value) (h : Heap) :
    callValue (env sha) n (.glob Id.min) [a, b] [] h = applyBuiltin (env sha) h .min [a, b] [] := by
  have g : (env sha).globals.lookup Id.min = some (.builtin .min) := rfl
  rw [callValue.eq_def]; simp only [g]

theorem call_enumerate (n : Nat) (a : Value) (h : Heap) :
    callValue (env sha) n (.glob Id.enumerate) [a] [] h =
      applyBuiltin (env sha) h .enumerate [a] [] := by
  have g : (env sha).globals.lookup Id.enumerate = some (.builtin .enumerate) := rfl
  rw [callValue.eq_def]; simp only [g]

/-- A call of a spec function through its global name. -/
theorem callValue_fn {env : Env} (n : Nat) {g : Name} {d : FunctionDef} (vs : List Value)
    (h : Heap) (hg : env.globals.lookup g = some (.fn d)) :
    callValue env n (.glob g) vs [] h = callFn env n d.params (.stmts d.body) Locals.empty vs [] h := by
  rw [callValue.eq_def]; simp only [hg, frame_eq]

end SpecLean.Validation

namespace SpecLean.Validation

open SpecLean SpecLean.Gen SpecLean.Encode

/-! ## Facts used by several proofs -/

/-- `WTree` holds for any arguments with no state among them: every pattern of `FP` is
rooted at `BeaconState`. -/
theorem WTree_noState {h : Heap} {vs : List Value}
    (hn : ∀ k, ¬ RootTy h vs k Id.BeaconState) : WTree h vs FP := by
  intro k pat hk hty
  simp only [FP, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> exact absurd hty (hn k)

/-- The pure-call result: nothing changes, and the result holds no reference. -/
theorem pure_result {h : Heap} {vs : List Value} {fpf : Footprint} {v : Value}
    (hn : ∀ k, ¬ RootTy h (vs ++ [v]) k Id.BeaconState) :
    Frame h h vs fpf ∧ Fresh h h ∧ Reach h h vs ∧ WTree h (vs ++ [v]) FP :=
  ⟨Frame_refl h vs fpf, Fresh_refl h, Reach_refl h vs, WTree_noState hn⟩


/-- Under `WTree`, a footprint object has no second path: another path reaches another
address. -/
theorem wtree_ne {h : Heap} {vs : List Value} {fp : Footprint} (hw : WTree h vs fp)
    {k : Nat} {pat : FPat} (hk : pat ∈ fp) (hty : RootTy h vs k pat.ty) {q : List Nat}
    (hq : Matches pat.steps q)
    {a : Nat} (ha : at? h vs k q = some (.ref a)) {k' : Nat} {q' : List Nat} {a' : Nat}
    (ha' : at? h vs k' q' = some (.ref a')) (hne : ¬ (k' = k ∧ q' = q)) : a' ≠ a := by
  intro e; subst e; exact hne (hw k pat hk hty q hq a' ha k' q' ha')

theorem decValidator_congr {h h' : Heap} {r : Nat} (e : h'.objs r = h.objs r) :
    decValidator h' (.ref r) = decValidator h (.ref r) := by
  simp [decValidator, e]

theorem decGwei_nonref {v : Value} {g : Readable.Gwei} (h : decGwei v = some g) :
    ∀ b, v ≠ .ref b := by
  rw [(decGwei_some h).1]; intro b e; cases e

theorem chkRange_lt {n r : Nat} (h : chkRange n = .ok r) : r < 2 ^ 64 := by
  unfold chkRange at h; split at h <;> cases h; assumption

theorem chkRange_ne_oof {n : Nat} {e : SpecError} (h : chkRange n = .error e) :
    e ≠ .outOfFuel := by
  unfold chkRange at h; split at h <;> cases h; decide

theorem chkSub_lt {a b r : Nat} (h : chkSub a b = .ok r) : r < 2 ^ 64 := by
  unfold chkSub at h; split at h
  · exact chkRange_lt h
  · cases h

theorem chkSub_ne_oof {a b : Nat} {e : SpecError} (h : chkSub a b = .error e) :
    e ≠ .outOfFuel := by
  unfold chkSub at h; split at h
  · exact chkRange_ne_oof h
  · cases h; decide

theorem chkDiv_ne_oof {a b : Nat} {e : SpecError} (h : chkDiv a b = .error e) :
    e ≠ .outOfFuel := by
  unfold chkDiv at h; split at h
  · cases h; decide
  · exact chkRange_ne_oof h

theorem chkAdd_ne_oof {a b : Nat} {e : SpecError} (h : chkAdd a b = .error e) :
    e ≠ .outOfFuel := chkRange_ne_oof h

theorem chkDiv_lt {a b r : Nat} (h : chkDiv a b = .ok r) : r < 2 ^ 64 := by
  unfold chkDiv at h; split at h
  · cases h
  · exact chkRange_lt h

theorem chkMod_ne_oof {a b : Nat} {e : SpecError} (h : chkMod a b = .error e) :
    e ≠ .outOfFuel := by
  unfold chkMod at h; split at h
  · cases h; decide
  · exact chkRange_ne_oof h

end SpecLean.Validation
