import SpecLean.Layer4.Examples5

/-!
# Layer 4: step lemmas for generated proofs

Each uint operation, on the denotation side (`dBinop`, `cmpF`) and on the readable side (`uOp`),
in the same `if` form over natural numbers. A generated proof rewrites both sides with these
lemmas and then splits on the same conditions. The conditions never reach `decide`, so no sum
with a literal is evaluated in unary.
-/

namespace SpecLean.Layer4.GenLemmas

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd

attribute [local instance high] LibModel.toLibValues

section den
variable {t t' r : UintTy} (hr : resolveUint t t' = .ok r) (hb : r.bits = 64) (a b : Nat)
include hr hb

theorem d_add : dBinop .add (.val (.uint t a)) (.val (.uint t' b)) =
    some (if a + b < 2 ^ 64 then .ok (.val (.uint r (a + b))) else .error .sszValue) := by
  have h := binop_add hr hb a b
  unfold chkAdd chkRange at h
  by_cases c : a + b < 2 ^ 64
  · rw [if_pos c] at h ⊢; exact dBinop_eval h rfl
  · rw [if_neg c] at h ⊢; exact dBinop_err h (by decide)

theorem d_sub : dBinop .sub (.val (.uint t a)) (.val (.uint t' b)) =
    some (if b ≤ a then (if a - b < 2 ^ 64 then .ok (.val (.uint r (a - b))) else .error .sszValue)
      else .error .sszValue) := by
  have h := binop_sub hr hb a b
  unfold chkSub chkRange at h
  by_cases c : b ≤ a
  · rw [if_pos c] at h ⊢
    by_cases c2 : a - b < 2 ^ 64
    · rw [if_pos c2] at h ⊢; exact dBinop_eval h rfl
    · rw [if_neg c2] at h ⊢; exact dBinop_err h (by decide)
  · rw [if_neg c] at h ⊢; exact dBinop_err h (by decide)

theorem d_mul : dBinop .mul (.val (.uint t a)) (.val (.uint t' b)) =
    some (if a * b < 2 ^ 64 then .ok (.val (.uint r (a * b))) else .error .sszValue) := by
  have h := binop_mul hr hb a b
  unfold chkMul chkRange at h
  by_cases c : a * b < 2 ^ 64
  · rw [if_pos c] at h ⊢; exact dBinop_eval h rfl
  · rw [if_neg c] at h ⊢; exact dBinop_err h (by decide)

theorem d_div : dBinop .floorDiv (.val (.uint t a)) (.val (.uint t' b)) =
    some (if b = 0 then .error .divisionByZero else
      (if a / b < 2 ^ 64 then .ok (.val (.uint r (a / b))) else .error .sszValue)) := by
  have h := binop_floorDiv hr hb a b
  unfold chkDiv chkRange at h
  by_cases c : b = 0
  · rw [if_pos c] at h ⊢; exact dBinop_err h (by decide)
  · rw [if_neg c] at h ⊢
    by_cases c2 : a / b < 2 ^ 64
    · rw [if_pos c2] at h ⊢; exact dBinop_eval h rfl
    · rw [if_neg c2] at h ⊢; exact dBinop_err h (by decide)

theorem d_mod : dBinop .mod (.val (.uint t a)) (.val (.uint t' b)) =
    some (if b = 0 then .error .divisionByZero else
      (if a % b < 2 ^ 64 then .ok (.val (.uint r (a % b))) else .error .sszValue)) := by
  have h := binop_mod hr hb a b
  unfold chkMod chkRange at h
  by_cases c : b = 0
  · rw [if_pos c] at h ⊢; exact dBinop_err h (by decide)
  · rw [if_neg c] at h ⊢
    by_cases c2 : a % b < 2 ^ 64
    · rw [if_pos c2] at h ⊢; exact dBinop_eval h rfl
    · rw [if_neg c2] at h ⊢; exact dBinop_err h (by decide)

end den

section cmp
variable {t t' r : UintTy} (hr : resolveUint t t' = .ok r) (a b : Nat)
include hr

theorem d_cmp (op : CmpOp) (hop : op = .lt ∨ op = .ltE ∨ op = .gt ∨ op = .gtE) :
    cmpF op (.uint t a) (.uint t' b) = some (.ok (cmpInt op a b)) :=
  cmpF_eval (cmp_uint hr a b op) hop

theorem d_eq : cmpF .eq (.uint t a) (.uint t' b) = some (.ok ((a : Int) == (b : Int))) := by
  simp only [cmpF, cmp_uint hr a b, lift_ok]; rfl

theorem d_ne : cmpF .notEq (.uint t a) (.uint t' b) = some (.ok ((a : Int) != (b : Int))) := by
  simp only [cmpF, cmp_uint hr a b, lift_ok, DM.bind, DM.ok]; rfl

end cmp

section rd
variable {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat)
include hb

theorem r_add : (uOp .add (a : Int) (b : Int) : SpecM α) =
    if a + b < 2 ^ 64 then .ok (UintC.ofNat (a + b)) else .error .bug := by
  have h' : (0 : Int) ≤ (a : Int) + b := by omega
  simp only [uOp, erase, intArith, Except.mapError, Except.bind_ok', uOf, hb]
  by_cases c : a + b < 2 ^ 64
  · rw [if_pos ⟨h', by omega⟩, if_pos c, show ((a : Int) + b).toNat = a + b by omega]; rfl
  · rw [if_neg (by omega), if_neg c]; rfl

theorem r_sub : (uOp .sub (a : Int) (b : Int) : SpecM α) =
    if b ≤ a then (if a - b < 2 ^ 64 then .ok (UintC.ofNat (a - b)) else .error .bug) else .error .bug := by
  simp only [uOp, erase, intArith, Except.mapError, Except.bind_ok', uOf, hb]
  by_cases c : b ≤ a
  · rw [if_pos c]
    by_cases c2 : a - b < 2 ^ 64
    · rw [if_pos ⟨by omega, by omega⟩, if_pos c2, show ((a : Int) - b).toNat = a - b by omega]; rfl
    · rw [if_neg (by omega), if_neg c2]; rfl
  · rw [if_neg (by omega), if_neg c]; rfl

theorem r_mul : (uOp .mul (a : Int) (b : Int) : SpecM α) =
    if a * b < 2 ^ 64 then .ok (UintC.ofNat (a * b)) else .error .bug := by
  have hm : ((a : Int) * b) = ((a * b : Nat) : Int) := by push_cast; rfl
  simp only [uOp, erase, intArith, Except.mapError, Except.bind_ok', uOf, hb, hm]
  by_cases c : a * b < 2 ^ 64
  · rw [if_pos ⟨by omega, by omega⟩, if_pos c, Int.toNat_natCast]; rfl
  · rw [if_neg (by omega), if_neg c]; rfl

theorem r_div : (uOp .floorDiv (a : Int) (b : Int) : SpecM α) =
    if b = 0 then .error .bug else (if a / b < 2 ^ 64 then .ok (UintC.ofNat (a / b)) else .error .bug) := by
  by_cases c : b = 0
  · subst c; rfl
  · have hf : (a : Int).fdiv (b : Int) = ((a / b : Nat) : Int) := by
      rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega), Int.natCast_ediv]
    have hb0 : (b : Int) ≠ 0 := by omega
    simp only [uOp, erase, intArith, Except.mapError, if_neg hb0, hf, Except.bind_ok', uOf, hb]
    rw [if_neg c]
    by_cases c2 : a / b < 2 ^ 64
    · rw [if_pos (show (0 : Int) ≤ ((a / b : Nat) : Int) ∧ ((a / b : Nat) : Int) < 2 ^ 64 from
          ⟨Int.natCast_nonneg _, by omega⟩), if_pos c2, Int.toNat_natCast]; rfl
    · rw [if_neg (show ¬ ((0 : Int) ≤ ((a / b : Nat) : Int) ∧ ((a / b : Nat) : Int) < 2 ^ 64) by omega),
        if_neg c2]; rfl

theorem r_mod : (uOp .mod (a : Int) (b : Int) : SpecM α) =
    if b = 0 then .error .bug else (if a % b < 2 ^ 64 then .ok (UintC.ofNat (a % b)) else .error .bug) := by
  by_cases c : b = 0
  · subst c; rfl
  · have hf : (a : Int).fmod (b : Int) = ((a % b : Nat) : Int) := by
      rw [Int.fmod_eq_emod_of_nonneg _ (by omega), Int.natCast_emod]
    have hb0 : (b : Int) ≠ 0 := by omega
    simp only [uOp, erase, intArith, Except.mapError, if_neg hb0, hf, Except.bind_ok', uOf, hb]
    rw [if_neg c]
    by_cases c2 : a % b < 2 ^ 64
    · rw [if_pos ⟨by omega, by omega⟩, if_pos c2, Int.toNat_natCast]; rfl
    · rw [if_neg (by omega), if_neg c2]; rfl

end rd

section lit
variable {t : UintTy} (hb : t.bits = 64) (a k : Nat)
include hb

/-- `uint + int` with a literal that is not negative: the class of the uint. -/
theorem d_add_lit : dBinop .add (.val (.uint t a)) (.val (.int (k : Int))) =
    some (if a + k < 2 ^ 64 then .ok (.val (.uint t (a + k))) else .error .sszValue) := by
  have h : @binopVal LibModel.toLibValues .add (.uint t a) (.int (k : Int)) =
      (Value.uint t ·) <$> chkAdd a k := by
    rw [binop_uint_int]; simp only [intArith, Except.bind_ok']; exact wrap_add hb a k
  unfold chkAdd chkRange at h
  by_cases c : a + k < 2 ^ 64
  · rw [if_pos c] at h ⊢; exact dBinop_eval h rfl
  · rw [if_neg c] at h ⊢; exact dBinop_err h (by decide)

theorem d_sub_lit : dBinop .sub (.val (.uint t a)) (.val (.int (k : Int))) =
    some (if k ≤ a then (if a - k < 2 ^ 64 then .ok (.val (.uint t (a - k))) else .error .sszValue)
      else .error .sszValue) := by
  have h : @binopVal LibModel.toLibValues .sub (.uint t a) (.int (k : Int)) =
      (Value.uint t ·) <$> chkSub a k := by
    rw [binop_uint_int]; simp only [intArith, Except.bind_ok']; exact wrap_sub hb a k
  unfold chkSub chkRange at h
  by_cases c : k ≤ a
  · rw [if_pos c] at h ⊢
    by_cases c2 : a - k < 2 ^ 64
    · rw [if_pos c2] at h ⊢; exact dBinop_eval h rfl
    · rw [if_neg c2] at h ⊢; exact dBinop_err h (by decide)
  · rw [if_neg c] at h ⊢; exact dBinop_err h (by decide)

end lit

/-- A bind on an `if` of a result and an error. -/
theorem dmb_ite {α β : Type} (c : Prop) [Decidable c] (x : Res α) (e : SpecError) (f : α → DM β) :
    DM.bind (some (if c then x else .error e)) f = if c then DM.bind (some x) f else some (.error e) := by
  by_cases h : c <;> simp [h, DM.bind]

theorem dmb_ok {α β : Type} (a : α) (f : α → DM β) : DM.bind (some (.ok a)) f = f a := rfl
theorem dmb_err {α β : Type} (e : SpecError) (f : α → DM β) : DM.bind (some (.error e)) f = some (.error e) := rfl

/-- `dmb_ok` and `dmb_err` as rewrites, not `rfl` lemmas. `simp` uses an `rfl` lemma as a
definitional step, and the kernel then unfolds `den` to check it. -/
theorem dmb_okp {α β : Type} (a : α) (f : α → DM β) : DM.bind (some (.ok a)) f = f a := Eq.trans rfl rfl
theorem dmb_errp {α β : Type} (e : SpecError) (f : α → DM β) :
    DM.bind (some (.error e)) f = some (.error e) := Eq.trans rfl rfl
theorem dmb_okd {α β : Type} (a : α) (f : α → DM β) : DM.bind (DM.ok a) f = f a := Eq.trans rfl rfl

end SpecLean.Layer4.GenLemmas
