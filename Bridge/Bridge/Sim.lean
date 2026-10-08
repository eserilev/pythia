import SpecLean.Rd.Prelude
import Bridge.Attr
import EpochProofs.Spec.Block.Block

/-!
# The bridge relation

`Sim f r h`: the readable computation `r` and the hand computation `h` give the same result up
to `f`, or errors of the same class. A bridge theorem is `Sim abs (Gen.g x) (Hand.g (abs x))`.

The lemmas below step through both `do` blocks one bind at a time. A `simp` that unfolds `bind`
makes the kernel fail with deep recursion, so the proofs do not do that.
-/

namespace Pythia.Bridge

open SpecLean SpecLean.Rd

/-- The preset of the bridge: minimal. -/
abbrev Hand := EpochProofs.Spec.Preset.minimal

abbrev HM := EpochProofs.Spec.SpecM

def errClass : EpochProofs.Spec.SpecError → Fail
  | .indexOutOfRange | .assertionFailed => .invalid
  | .overflow | .divisionByZero => .bug

/-- A byte list as a vector of length `n`. Missing bytes are 0, extra bytes are dropped. -/
def toVec (n : Nat) (l : List UInt8) : Vector UInt8 n := Vector.ofFn fun i => l.getD i 0

theorem toVec_toList (n : Nat) (l : List UInt8) (h : l.length = n) : (toVec n l).toList = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- A 32-byte vector with its first byte replaced, as the hand spec writes it. -/
theorem toVec_prefix (p : UInt8) (l : List UInt8) (hl : l.length = 32) (h : 1 + (min 32 32 - 1) = 32) :
    toVec 32 ([p] ++ l.drop 1) = (#v[p] ++ (toVec 32 l).extract 1 32).cast h := by
  apply Vector.toList_inj.mp
  rw [toVec_toList _ _ (by simp [hl])]
  simp [Vector.toList_cast, Vector.toList_append, Vector.toList_extract, toVec_toList _ _ hl]
  rw [List.take_of_length_le (by simp [hl])]

theorem bytesOf_ok {β : Type} [BytesC β] (b : List UInt8) (h : b.length = BytesC.len β) :
    (bytesOf β b : SpecM β) = .ok (BytesC.ofBytes b) := by
  unfold bytesOf; rw [if_pos h]; rfl

def Sim {α β : Type} (f : α → β) (r : SpecM α) (h : HM β) : Prop :=
  r.map f = h.mapError errClass

/-! ## Monad steps -/

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem err_bind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e :=
  rfl

theorem mapError_ok {ε ε' α : Type} (g : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError g = .ok a := rfl

/-- `r` succeeds only with values that satisfy `P`. -/
def Post {α : Type} (P : α → Prop) (r : SpecM α) : Prop := ∀ x, r = .ok x → P x

/-- `Sim` and a range fact on the readable result. The bridge statements use it. -/
def SimI {α β : Type} (P : α → Prop) (f : α → β) (r : SpecM α) (h : HM β) : Prop :=
  Sim f r h ∧ Post P r

theorem simI_sim {α β : Type} {P : α → Prop} {f : α → β} {r : SpecM α} {h : HM β}
    (hs : SimI P f r h) : Sim f r h := hs.1

theorem simI_post {α β : Type} {P : α → Prop} {f : α → β} {r : SpecM α} {h : HM β}
    (hs : SimI P f r h) {x : α} (hx : r = .ok x) : P x := hs.2 x hx

theorem simI_intro {α β : Type} {P : α → Prop} {f : α → β} {r : SpecM α} {h : HM β}
    (hs : Sim f r h) (hp : Post P r) : SimI P f r h := ⟨hs, hp⟩

theorem post_true {α : Type} (r : SpecM α) : Post (fun _ => True) r := fun _ _ => trivial

theorem post_pure {α : Type} {P : α → Prop} (a : α) (h : P a) : Post P (pure a) := by
  intro x hx; cases hx; exact h

theorem post_bind {α β : Type} {P : β → Prop} {A : SpecM α} {K : α → SpecM β}
    (h : ∀ y, A = .ok y → Post P (K y)) : Post P (A >>= K) := by
  intro x hx
  cases hA : A with
  | error e => rw [hA] at hx; cases hx
  | ok y => rw [hA, ok_bind] at hx; exact h y hA x hx

theorem post_ite {α : Type} {P : α → Prop} (c : Prop) {_ : Decidable c} {A B : SpecM α}
    (h1 : c → Post P A) (h2 : ¬c → Post P B) : Post P (if c then A else B) := by
  by_cases h : c
  · rw [if_pos h]; exact h1 h
  · rw [if_neg h]; exact h2 h

theorem post_throw {α : Type} {P : α → Prop} (e : Fail) : Post P (throw e : SpecM α) := by
  intro x hx; cases hx

theorem post_simI {α β : Type} {P : α → Prop} {f : α → β} {r : SpecM α} {h : HM β}
    (hs : SimI P f r h) : Post P r := hs.2

theorem sim_pure {α β : Type} (f : α → β) (a : α) (b : β) (h : f a = b) :
    Sim f (pure a) (pure b) := by
  subst h; rfl

theorem sim_ok {α β : Type} (f : α → β) (a : α) (b : β) (h : f a = b) :
    Sim f (.ok a) (pure b) := by
  subst h; rfl

theorem sim_bind {α α' β β' : Type} {f : α → α'} {g : β → β'} {A : SpecM α} {B : HM α'}
    {K : α → SpecM β} {L : α' → HM β'} (hA : Sim f A B)
    (hK : ∀ x, A = .ok x → Sim g (K x) (L (f x))) : Sim g (A >>= K) (B >>= L) := by
  unfold Sim at *
  cases A with
  | error e =>
    cases B with
    | error e' =>
      rw [err_bind, err_bind]
      simp only [Except.map, Except.mapError] at hA ⊢
      cases hA; rfl
    | ok b => cases hA
  | ok a =>
    cases B with
    | error e' => cases hA
    | ok b =>
      cases hA
      rw [ok_bind, ok_bind]
      exact hK a rfl

/-- A readable bind whose hand side is a plain value (a hand function that cannot fail). -/
theorem sim_bind_val {α α' β β' : Type} {f : α → α'} {g : β → β'} {A : SpecM α} {b : α'}
    {K : α → SpecM β} {H : HM β'} (hA : Sim f A (pure b))
    (hK : ∀ x, A = .ok x → f x = b → Sim g (K x) H) : Sim g (A >>= K) H := by
  unfold Sim at hA
  cases A with
  | error e => cases hA
  | ok a =>
    cases hA
    exact hK a rfl rfl

/-- A readable step that cannot fail. -/
theorem sim_bind_l {α β β' : Type} {g : β → β'} {A : SpecM α} (a : α) {K : α → SpecM β}
    {H : HM β'} (hA : A = .ok a) (hK : Sim g (K a) H) : Sim g (A >>= K) H := by
  subst hA; exact hK

/-- A hand step that cannot fail. -/
theorem sim_bind_r {α β β' : Type} {g : β → β'} {B : HM α} (b : α) {L : α → HM β'}
    {R : SpecM β} (hB : B = .ok b) (hK : Sim g R (L b)) : Sim g R (B >>= L) := by
  subst hB; exact hK

theorem sim_ite {α β : Type} {f : α → β} (c c' : Prop) {_ : Decidable c} {_ : Decidable c'}
    {A B : SpecM α} {A' B' : HM β} (hc : c ↔ c') (h1 : c → c' → Sim f A A')
    (h2 : ¬c → ¬c' → Sim f B B') : Sim f (if c then A else B) (if c' then A' else B') := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact h1 h (hc.mp h)
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact h2 h (fun h' => h (hc.mpr h'))

theorem sim_congr {α β : Type} {f g : α → β} {r : SpecM α} {h : HM β} (hfg : ∀ x, f x = g x)
    (hs : Sim f r h) : Sim g r h := by
  have : f = g := funext hfg
  subst this; exact hs

theorem sim_bind_pure {α β : Type} {f : α → β} {A : SpecM α} {H : HM β} (hs : Sim f A H) :
    Sim f (A >>= pure) H := by
  have : (A >>= pure) = A := by cases A <;> rfl
  rw [this]; exact hs

theorem sim_bind_pure_r {α β : Type} {f : α → β} {A : SpecM α} {H : HM β} (hs : Sim f A H) :
    Sim f A (H >>= pure) := by
  have : (H >>= pure) = H := by cases H <;> rfl
  rw [this]; exact hs

theorem sim_pure_ite {α β : Type} {f : α → β} {R : SpecM α} (c : Prop) {_ : Decidable c}
    (a b : β) (hs : Sim f R (if c then pure a else pure b)) : Sim f R (pure (if c then a else b)) := by
  by_cases h : c
  · rw [if_pos h] at hs ⊢; exact hs
  · rw [if_neg h] at hs ⊢; exact hs

theorem sim_pure_or {α : Type} {f : α → Bool} {R : SpecM α} (a b : Bool)
    (hs : Sim f R (if a = true then pure true else pure b)) : Sim f R (pure (a || b)) := by
  cases a <;> simpa using hs

theorem sim_pure_and {α : Type} {f : α → Bool} {R : SpecM α} (a b : Bool)
    (hs : Sim f R (if a = true then pure b else pure false)) : Sim f R (pure (a && b)) := by
  cases a <;> simpa using hs

/-- A readable `assert c` against the hand `if ¬P then throw .assertionFailed`. -/
theorem sim_assert {β β' : Type} {g : β → β'} (c : Bool) (P : Prop) {_ : Decidable P}
    {K : Unit → SpecM β} {L : PUnit → HM β'} (hc : c = true ↔ P) (hK : P → Sim g (K ()) (L ())) :
    Sim g (assert c >>= K)
      (if ¬P then (throw .assertionFailed >>= L) else (pure PUnit.unit >>= L)) := by
  by_cases h : P
  · rw [if_neg (fun hn => hn h)]
    have hc' : c = true := hc.mpr h
    subst hc'
    exact hK h
  · rw [if_pos h]
    have hc' : c = false := by cases c <;> simp_all
    subst hc'
    rfl

/-! ## Uint arithmetic -/

theorem uOf_ok {α : Type} [UintC α] (n : Nat) (hb : UintC.bits α = 64) (hn : n < 2 ^ 64) :
    (uOf α (n : Int) : SpecM α) = .ok (UintC.ofNat n) := by
  unfold uOf
  rw [if_pos ⟨Int.natCast_nonneg n, by rw [hb]; exact_mod_cast hn⟩]
  rfl

theorem uOf_okB {α : Type} [UintC α] (n : Nat) (hn : n < 2 ^ UintC.bits α) :
    (uOf α (n : Int) : SpecM α) = .ok (UintC.ofNat n) := by
  unfold uOf
  rw [if_pos ⟨Int.natCast_nonneg n, by exact_mod_cast hn⟩]
  rfl

theorem uOf_neg {α : Type} [UintC α] (z : Int) (hb : UintC.bits α = 64)
    (hz : ¬ (0 ≤ z ∧ z < 2 ^ 64)) : (uOf α z : SpecM α) = .error .bug := by
  unfold uOf
  rw [if_neg (by rw [hb]; exact hz)]
  rfl

theorem uOf_range {α : Type} [UintC α] (z : Int) (x : α) (h : (uOf α z : SpecM α) = .ok x) :
    UintC.val x < 2 ^ UintC.bits α := by
  unfold uOf at h
  split at h
  · rename_i hc
    cases h
    rw [UintC.val_ofNat]
    have h2 : ((2 : Int) ^ UintC.bits α) = ((2 ^ UintC.bits α : Nat) : Int) := by push_cast; rfl
    omega
  · cases h

theorem map_val_ofNat {α : Type} [UintC α] (n : Nat) :
    Except.map UintC.val (Except.ok (UintC.ofNat n : α) : SpecM α) = .ok n := by
  show Except.ok _ = _
  rw [UintC.val_ofNat]

theorem sim_uOf_pure {α : Type} [UintC α] (hb : UintC.bits α = 64) (z : Int) (n : Nat)
    (hz : z = n) (hn : n < 2 ^ 64) : Sim UintC.val (uOf α z) (pure n) := by
  subst hz
  unfold Sim
  rw [uOf_ok n hb hn, map_val_ofNat]
  rfl

theorem sim_uCast_pure {α β : Type} [UintC α] [UintC β] (hb : UintC.bits β = 64) (x : α) (n : Nat)
    (hx : UintC.val x = n) (hn : n < 2 ^ 64) : Sim UintC.val (uCast β x) (pure n) := by
  unfold uCast
  exact sim_uOf_pure hb _ n (by rw [uv, hx]) hn

theorem sim_uOp_add {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) :
    Sim UintC.val (uOp .add (a : Int) (b : Int) : SpecM α) (EpochProofs.Spec.uint64Add a b) := by
  unfold uOp EpochProofs.Spec.uint64Add EpochProofs.Spec.UINT64_SIZE
  simp only [erase, intArith, mapError_ok, ok_bind]
  unfold Sim
  rw [show (a : Int) + (b : Int) = ((a + b : Nat) : Int) by push_cast; rfl]
  by_cases h : a + b < 2 ^ 64
  · rw [uOf_ok (a + b) hb h, if_pos h, map_val_ofNat]; rfl
  · rw [uOf_neg _ hb (by omega), if_neg h]
    rfl

theorem sim_uOp_sub {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) (ha : a < 2 ^ 64) :
    Sim UintC.val (uOp .sub (a : Int) (b : Int) : SpecM α) (EpochProofs.Spec.uint64Sub a b) := by
  unfold uOp EpochProofs.Spec.uint64Sub
  simp only [erase, intArith, mapError_ok, ok_bind]
  unfold Sim
  by_cases h : b ≤ a
  · rw [show (a : Int) - (b : Int) = ((a - b : Nat) : Int) by omega,
      uOf_ok (a - b) hb (by omega), if_pos h, map_val_ofNat]; rfl
  · rw [uOf_neg _ hb (by omega), if_neg h]
    rfl

theorem sim_uOp_mul {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) :
    Sim UintC.val (uOp .mul (a : Int) (b : Int) : SpecM α) (EpochProofs.Spec.uint64Mul a b) := by
  unfold uOp EpochProofs.Spec.uint64Mul EpochProofs.Spec.UINT64_SIZE
  simp only [erase, intArith, mapError_ok, ok_bind]
  unfold Sim
  by_cases h : a * b < 2 ^ 64
  · rw [show (a : Int) * (b : Int) = ((a * b : Nat) : Int) by push_cast; rfl,
      uOf_ok (a * b) hb h, if_pos h, map_val_ofNat]; rfl
  · rw [show (a : Int) * (b : Int) = ((a * b : Nat) : Int) by push_cast; rfl,
      uOf_neg _ hb (by omega), if_neg h]
    rfl

theorem sim_uOp_sub_pure {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Int) (n m : Nat)
    (han : a = n) (hbm : b = m) (hle : m ≤ n) (hn : n < 2 ^ 64) :
    Sim UintC.val (uOp .sub a b : SpecM α) (pure (n - m)) := by
  subst han hbm
  unfold uOp Sim
  simp only [erase, intArith, mapError_ok, ok_bind]
  rw [show (n : Int) - (m : Int) = ((n - m : Nat) : Int) by omega,
    uOf_ok _ hb (by omega), map_val_ofNat]
  rfl

theorem sim_uOp_add_pure {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Int) (n m : Nat)
    (han : a = n) (hbm : b = m) (hs : n + m < 2 ^ 64) :
    Sim UintC.val (uOp .add a b : SpecM α) (pure (n + m)) := by
  subst han hbm
  unfold uOp Sim
  simp only [erase, intArith, mapError_ok, ok_bind]
  rw [show (n : Int) + (m : Int) = ((n + m : Nat) : Int) by omega,
    uOf_ok _ hb hs, map_val_ofNat]
  rfl

theorem sim_uOp_and_pure {α : Type} [UintC α] (a b : Int) (n m : Nat)
    (han : a = n) (hbm : b = m) (hn : n < 2 ^ UintC.bits α) :
    Sim UintC.val (uOp .bitAnd a b : SpecM α) (pure (n &&& m)) := by
  subst han hbm
  unfold uOp Sim
  simp only [erase, intArith, mapError_ok, ok_bind]
  show Except.map UintC.val (uOf α (pyAnd (Int.ofNat n) (Int.ofNat m))) = _
  simp only [pyAnd]
  rw [show (Int.ofNat (n &&& m)) = ((n &&& m : Nat) : Int) from rfl,
    uOf_okB _ (Nat.lt_of_le_of_lt Nat.and_le_left hn), map_val_ofNat]
  rfl

theorem xor_and_eq (a b : Nat) (ha : a < 2 ^ 64) : a ^^^ (a &&& b) = a &&& (2 ^ 64 - 1 ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · cases a.testBit i <;> cases b.testBit i <;> simp [hi]
  · have : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this, hi]

/-- `x & ~m` on a Python `int`: the readable `Int.not` against the hand `UINT64_MAX ^^^ m`. -/
theorem sim_uOp_andnot_pure {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Int) (n m : Nat)
    (han : a = n) (hbm : b = m) (hn : n < 2 ^ 64) :
    Sim UintC.val (uOp .bitAnd a b.not : SpecM α) (pure (n &&& (2 ^ 64 - 1 ^^^ m))) := by
  subst han hbm
  unfold uOp Sim
  simp only [erase, intArith, mapError_ok, ok_bind]
  show Except.map UintC.val (uOf α (pyAnd (Int.ofNat n) (Int.negSucc m))) = _
  simp only [pyAnd]
  rw [show (Int.ofNat (n ^^^ (n &&& m))) = ((n ^^^ (n &&& m) : Nat) : Int) from rfl, xor_and_eq n m hn,
    uOf_okB _ (by rw [hb]; exact Nat.lt_of_le_of_lt Nat.and_le_left hn), map_val_ofNat]
  rfl

theorem sim_uOp_or_pure {α : Type} [UintC α] (a b : Int) (n m : Nat)
    (han : a = n) (hbm : b = m) (hn : n < 2 ^ UintC.bits α) (hm : m < 2 ^ UintC.bits α) :
    Sim UintC.val (uOp .bitOr a b : SpecM α) (pure (n ||| m)) := by
  subst han hbm
  unfold uOp Sim
  simp only [erase, intArith, mapError_ok, ok_bind]
  show Except.map UintC.val (uOf α (pyOr (Int.ofNat n) (Int.ofNat m))) = _
  simp only [pyOr]
  rw [show (Int.ofNat (n ||| m)) = ((n ||| m : Nat) : Int) from rfl,
    uOf_okB _ (Nat.or_lt_two_pow hn hm), map_val_ofNat]
  rfl

theorem fdiv_nat (a b : Nat) : (a : Int).fdiv (b : Int) = ((a / b : Nat) : Int) := by
  rw [Int.fdiv_eq_ediv, if_pos (.inl (Int.natCast_nonneg b))]
  simp only [Int.sub_zero]
  exact (Int.natCast_ediv a b).symm

theorem fmod_nat (a b : Nat) : (a : Int).fmod (b : Int) = ((a % b : Nat) : Int) := by
  rw [Int.fmod_eq_emod_of_nonneg _ (Int.natCast_nonneg b)]
  exact (Int.natCast_emod a b).symm

theorem sim_uOp_div {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) (ha : a < 2 ^ 64) :
    Sim UintC.val (uOp .floorDiv (a : Int) (b : Int) : SpecM α)
      (EpochProofs.Spec.uint64Div a b) := by
  unfold uOp EpochProofs.Spec.uint64Div
  simp only [erase, intArith]
  unfold Sim
  by_cases h : b = 0
  · subst h
    rw [if_pos (by simp), if_pos rfl]; rfl
  · rw [if_neg (by omega), if_neg h, mapError_ok, ok_bind, fdiv_nat,
      uOf_ok (a / b) hb (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha), map_val_ofNat]; rfl

theorem sim_uOp_mod {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) (ha : a < 2 ^ 64) :
    Sim UintC.val (uOp .mod (a : Int) (b : Int) : SpecM α) (EpochProofs.Spec.uint64Mod a b) := by
  unfold uOp EpochProofs.Spec.uint64Mod
  simp only [erase, intArith]
  unfold Sim
  by_cases h : b = 0
  · subst h
    rw [if_pos (by simp), if_pos rfl]; rfl
  · rw [if_neg (by omega), if_neg h, mapError_ok, ok_bind, fmod_nat,
      uOf_ok (a % b) hb (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha), map_val_ofNat]; rfl

theorem uOp_mod_ok {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) (hb0 : b ≠ 0)
    (ha : a < 2 ^ 64) : (uOp .mod (a : Int) (b : Int) : SpecM α) = .ok (UintC.ofNat (a % b)) := by
  unfold uOp
  simp only [erase, intArith]
  rw [if_neg (by omega), mapError_ok, ok_bind, fmod_nat,
    uOf_ok (a % b) hb (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem uOp_div_ok {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) (hb0 : b ≠ 0)
    (ha : a < 2 ^ 64) : (uOp .floorDiv (a : Int) (b : Int) : SpecM α) = .ok (UintC.ofNat (a / b)) := by
  unfold uOp
  simp only [erase, intArith]
  rw [if_neg (by omega), mapError_ok, ok_bind, fdiv_nat,
    uOf_ok (a / b) hb (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem uint64Mod_ok (a b : Nat) (hb0 : b ≠ 0) : EpochProofs.Spec.uint64Mod a b = .ok (a % b) := by
  unfold EpochProofs.Spec.uint64Mod; rw [if_neg hb0]; rfl

theorem uint64Div_ok (a b : Nat) (hb0 : b ≠ 0) : EpochProofs.Spec.uint64Div a b = .ok (a / b) := by
  unfold EpochProofs.Spec.uint64Div; rw [if_neg hb0]; rfl

theorem iOp_pow2 (k : Int) (hk : 0 ≤ k) :
    iOp .pow 2 k = if k < 2 ^ 32 then .ok (((2 ^ k.toNat : Nat)) : Int) else .error .bug := by
  simp only [iOp, intArith, erase]
  rw [if_neg (by omega)]
  by_cases h : k < 2 ^ 32
  · rw [if_pos (Or.inr h), if_pos h]
    push_cast; rfl
  · rw [if_neg (by simp; omega), if_neg h]
    rfl

/-- `uOf α (2 ** k)` for an 8-bit class against the hand `if 2 ^ k < 256 then … else throw`. -/
theorem sim_pow_uOf {α β β' : Type} [UintC α] {g : β → β'} (hb : UintC.bits α = 8) (k : Int)
    (hk : 0 ≤ k) {K : α → SpecM β} {H : HM β'}
    (hK : 2 ^ k.toNat < 256 → Sim g (K (UintC.ofNat (2 ^ k.toNat))) H) :
    Sim g (iOp .pow 2 k >>= fun z => uOf α z >>= K)
      (if 2 ^ k.toNat < 256 then H else throw .overflow) := by
  rw [iOp_pow2 k hk]
  by_cases h32 : k < 2 ^ 32
  · rw [if_pos h32, ok_bind]
    by_cases h8 : 2 ^ k.toNat < 256
    · rw [if_pos h8]
      unfold uOf
      rw [if_pos ⟨Int.natCast_nonneg _, by rw [hb]; exact_mod_cast h8⟩]
      show Sim g (K (UintC.ofNat (((2 ^ k.toNat : Nat) : Int)).toNat)) H
      rw [Int.toNat_natCast]
      exact hK h8
    · rw [if_neg h8]
      unfold uOf
      rw [if_neg (by rw [hb]; intro ⟨_, h⟩; exact h8 (by exact_mod_cast h))]
      rfl
  · have h8 : ¬ 2 ^ k.toNat < 256 := by
      have : 8 ≤ k.toNat := by omega
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) this
      omega
    rw [if_neg h32, err_bind, if_neg h8]
    rfl

@[bridge_cast] theorem uint8_and (a b : Nat) (ha : a < 256) (hb : b < 256) :
    UInt8.ofNat a &&& UInt8.ofNat b = UInt8.ofNat (a &&& b) := by
  apply UInt8.toNat.inj
  simp [UInt8.toNat_and, UInt8.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left ha)]

@[bridge_cast] theorem uint8_or (a b : Nat) (ha : a < 256) (hb : b < 256) :
    UInt8.ofNat a ||| UInt8.ofNat b = UInt8.ofNat (a ||| b) := by
  apply UInt8.toNat.inj
  have : a ||| b < 2 ^ 8 := Nat.or_lt_two_pow ha hb
  simp [UInt8.toNat_or, UInt8.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (show a ||| b < 256 from this)]

@[bridge_cast] theorem uint8_beq (a b : Nat) (ha : a < 256) (hb : b < 256) :
    (UInt8.ofNat a == UInt8.ofNat b) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    simpa [UInt8.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · intro h; subst h; rfl

@[bridge_cast] theorem uint8_and_beq (a b : Nat) (ha : a < 256) (hb : b < 256) :
    (UInt8.ofNat a &&& UInt8.ofNat b == UInt8.ofNat b) = (a &&& b == b) := by
  rw [uint8_and a b ha hb, uint8_beq _ _ (Nat.lt_of_le_of_lt Nat.and_le_left ha) hb]

/-! ## Lists -/

@[bridge_cast] theorem int_beq_nat (a b : Nat) : ((a : Int) == (b : Int)) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega

@[bridge_cast] theorem int_bne_nat (a b : Nat) : ((a : Int) != (b : Int)) = (a != b) := by
  rw [bne, bne, int_beq_nat]

@[bridge_cast] theorem int_beq_zero (a : Nat) : ((a : Int) == 0) = (a == 0) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega

@[bridge_cast] theorem int_bne_zero (a : Nat) : ((a : Int) != 0) = (a != 0) := by
  rw [bne, bne, int_beq_zero]

@[bridge_cast] theorem decide_int_lt (a b : Nat) : decide ((a : Int) < (b : Int)) = decide (a < b) := by
  simp

@[bridge_cast] theorem decide_int_le (a b : Nat) : decide ((a : Int) ≤ (b : Int)) = decide (a ≤ b) := by
  simp

theorem lslice_take {α : Type} (xs : List α) (n : Nat) :
    lslice xs none (some (n : Int)) = xs.take n := by
  unfold lslice sliceBound'
  simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, List.drop_zero]
  rw [if_neg (by omega)]
  simp [Int.toNat_natCast]

theorem lslice_drop {α : Type} (xs : List α) (n : Nat) :
    lslice xs (some (n : Int)) none = xs.drop n := by
  unfold lslice sliceBound'
  simp only [Option.map_some, Option.getD_some, Option.map_none, Option.getD_none]
  rw [if_neg (by omega)]
  simp only [Int.toNat_natCast]
  rw [List.take_of_length_le (by simp <;> omega)]
  by_cases h : n ≤ xs.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_of_length_le (by omega)]

theorem lslice_drop_one {α : Type} (xs : List α) : lslice xs (some 1) none = xs.drop 1 :=
  lslice_drop xs 1

theorem lappend_none {α : Type} (xs : List α) (x : α) : lappend xs x none = .ok (xs ++ [x]) := rfl

theorem lfrom_none {α : Type} (xs : List α) : lfrom .progressiveList none xs = .ok xs := rfl

theorem lslice_take_one {α : Type} (xs : List α) : lslice xs none (some 1) = xs.take 1 :=
  lslice_take xs 1


theorem sim_lget {α β : Type} (g : α → β) (xs : List α) (i : Nat) :
    Sim g (lget xs (i : Int)) (EpochProofs.Spec.listGet (xs.map g) i) := by
  unfold Sim lget Rd.pyIndex EpochProofs.Spec.listGet
  rw [if_neg (by omega)]
  by_cases h : i < xs.length
  · rw [if_pos (by omega)]
    simp [h]; rfl
  · rw [if_neg (by omega)]
    simp [List.getElem?_eq_none (by simpa using h)]; rfl

theorem sim_lset {α β : Type} (g : α → β) (xs : List α) (i : Nat) (x : α) (y : β)
    (hy : g x = y) :
    Sim (List.map g) (lset xs (i : Int) x) (EpochProofs.Spec.listSet (xs.map g) i y) := by
  subst hy
  unfold Sim lset Rd.pyIndex EpochProofs.Spec.listSet
  rw [if_neg (by omega)]
  by_cases h : i < xs.length
  · rw [if_pos (by omega), if_pos (by simpa using h)]
    show Except.ok _ = Except.ok _
    rw [List.map_set, Int.toNat_natCast]
  · rw [if_neg (by omega), if_neg (by simpa using h)]
    rfl

end Pythia.Bridge
