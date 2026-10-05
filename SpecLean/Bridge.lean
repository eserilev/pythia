import SpecLean.Lemmas
import SpecLean.Readable

/-!
# Bridge lemmas: interpreter value rules and checked arithmetic

For 64-bit uint classes, each interpreter operator equals one checked operation of `Value.lean`.
The readable operations are the same checked operations with the diagnostic dropped.
-/

namespace SpecLean

open Readable

/-! ## Interpreter side -/

section interp

variable {t : UintTy} (ht : t.bits = 64)
include ht

theorem wrap_nat (n : Nat) : wrapUint t n = (Value.uint t ·) <$> chkRange n := by
  unfold wrapUint chkRange
  rw [ht]
  by_cases hn : n < 2 ^ 64
  · rw [if_pos ⟨Int.natCast_nonneg n, by exact_mod_cast hn⟩, if_pos hn]; rfl
  · rw [if_neg (fun h => hn (by exact_mod_cast h.2)), if_neg hn]; rfl

theorem wrap_add (a b : Nat) : wrapUint t ((a : Int) + b) = (Value.uint t ·) <$> chkAdd a b := by
  rw [show ((a : Int) + b) = ((a + b : Nat) : Int) by omega, wrap_nat ht]; rfl

theorem wrap_mul (a b : Nat) : wrapUint t ((a : Int) * b) = (Value.uint t ·) <$> chkMul a b := by
  rw [show ((a : Int) * b) = ((a * b : Nat) : Int) by simp, wrap_nat ht]; rfl

theorem wrap_sub (a b : Nat) : wrapUint t ((a : Int) - b) = (Value.uint t ·) <$> chkSub a b := by
  unfold chkSub
  by_cases hab : b ≤ a
  · rw [show ((a : Int) - b) = ((a - b : Nat) : Int) by omega, wrap_nat ht, if_pos hab]
  · rw [if_neg hab]; unfold wrapUint
    rw [if_neg (fun h => hab (by omega))]; rfl

theorem wrap_div (a b : Nat) :
    (intArith .floorDiv (a : Int) (b : Int) >>= wrapUint t) =
      (Value.uint t ·) <$> chkDiv a b := by
  unfold chkDiv
  simp only [intArith]
  by_cases hb : b = 0
  · simp [hb]
  · simp only [Int.natCast_eq_zero, hb, ↓reduceIte, Except.bind_ok']
    rw [← Int.ofNat_fdiv]
    exact wrap_nat ht _

theorem wrap_mod (a b : Nat) :
    (intArith .mod (a : Int) (b : Int) >>= wrapUint t) = (Value.uint t ·) <$> chkMod a b := by
  unfold chkMod
  simp only [intArith]
  by_cases hb : b = 0
  · simp [hb]
  · simp only [Int.natCast_eq_zero, hb, ↓reduceIte, Except.bind_ok']
    rw [← Int.ofNat_fmod]
    exact wrap_nat ht _

end interp

section ops

variable {t t' r : UintTy} (hr : resolveUint t t' = .ok r) (hb : r.bits = 64) (a b : Nat)
include hr

theorem binop_uint (op : BinOp) :
    binopVal op (.uint t a) (.uint t' b) = (intArith op a b >>= wrapUint r) := by
  simp [binopVal, hr]

theorem cmp_uint (op : CmpOp) : cmpVal op (.uint t a) (.uint t' b) = .ok (cmpInt op a b) := by
  simp [cmpVal, hr]

include hb

theorem binop_add : binopVal .add (.uint t a) (.uint t' b) = (Value.uint r ·) <$> chkAdd a b := by
  rw [binop_uint hr]; exact wrap_add hb a b

theorem binop_sub : binopVal .sub (.uint t a) (.uint t' b) = (Value.uint r ·) <$> chkSub a b := by
  rw [binop_uint hr]; exact wrap_sub hb a b

theorem binop_mul : binopVal .mul (.uint t a) (.uint t' b) = (Value.uint r ·) <$> chkMul a b := by
  rw [binop_uint hr]; exact wrap_mul hb a b

theorem binop_floorDiv :
    binopVal .floorDiv (.uint t a) (.uint t' b) = (Value.uint r ·) <$> chkDiv a b := by
  rw [binop_uint hr]; exact wrap_div hb a b

theorem binop_mod : binopVal .mod (.uint t a) (.uint t' b) = (Value.uint r ·) <$> chkMod a b := by
  rw [binop_uint hr]; exact wrap_mod hb a b

end ops

/-- A uint and a plain `int`: the `int` takes the class of the uint. -/
theorem binop_uint_int (op : BinOp) (t : UintTy) (a : Nat) (b : Int) :
    binopVal op (.uint t a) (.int b) = (intArith op a b >>= wrapUint t) := by
  simp [binopVal]

theorem div2_int (t : UintTy) (ht : t.bits = 64) (a : Nat) :
    binopVal .floorDiv (.uint t a) (.int 2) = (Value.uint t ·) <$> chkDiv a 2 := by
  rw [binop_uint_int, show (2 : Int) = ((2 : Nat) : Int) from rfl]
  exact wrap_div ht a 2

theorem add1_int (t : UintTy) (ht : t.bits = 64) (a : Nat) :
    binopVal .add (.uint t a) (.int 1) = (Value.uint t ·) <$> chkAdd a 1 := by
  rw [binop_uint_int, show (1 : Int) = ((1 : Nat) : Int) from rfl]
  simp only [intArith, Except.bind_ok']
  exact wrap_add ht a 1

/-! ## Readable side -/

@[simp] theorem erase_ok (x : α) : erase (.ok x : Res α) = .ok x := by
  simp only [erase, Except.mapError]

@[simp] theorem erase_error (e : SpecError) : erase (.error e : Res α) = .error e.fail := by
  simp only [erase, Except.mapError]

section readable

variable {α β : Type} [Uint64Class α] [Uint64Class β] (a b : α)

theorem uAdd_eq : uAdd a b = erase (ofVal <$> chkAdd (val a) (val b)) := by unfold uAdd; rfl
theorem uSub_eq : uSub a b = erase (ofVal <$> chkSub (val a) (val b)) := by unfold uSub; rfl
theorem uMul_eq : uMul a b = erase (ofVal <$> chkMul (val a) (val b)) := by unfold uMul; rfl
theorem uDiv_eq : uDiv a b = erase (ofVal <$> chkDiv (val a) (val b)) := by unfold uDiv; rfl
theorem uMod_eq : uMod a b = erase (ofVal <$> chkMod (val a) (val b)) := by unfold uMod; rfl
theorem toUint_eq : (toUint a : SpecM β) = erase (ofVal <$> chkRange (val a)) := by
  unfold toUint; rfl

end readable

/-! ## Checked operations that cannot fail -/

theorem chkRange_ok {n : Nat} (h : n < 2 ^ 64) : chkRange n = .ok n := by
  unfold chkRange; rw [if_pos h]

theorem chkMod_ok (a c : Nat) (hc : c ≠ 0) (hc' : c < 2 ^ 64) : chkMod a c = .ok (a % c) := by
  unfold chkMod
  rw [if_neg hc, chkRange_ok (by have := Nat.mod_lt a (Nat.pos_of_ne_zero hc); omega)]

theorem chkSub_ok (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 64) : chkSub a b = .ok (a - b) := by
  unfold chkSub; rw [if_pos hb, chkRange_ok (by omega)]

theorem chkSub_self (a : Nat) : chkSub a a = .ok 0 := by
  unfold chkSub; rw [if_pos (Nat.le_refl a), Nat.sub_self, chkRange_ok (by decide)]

theorem chkAdd_ok {a b c : Nat} (h : chkAdd a b = .ok c) : c = a + b ∧ a + b < 2 ^ 64 := by
  unfold chkAdd chkRange at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

end SpecLean
