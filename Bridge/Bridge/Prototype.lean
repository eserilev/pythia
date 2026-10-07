import SpecLean.Gen.Readable
import EpochProofs.Spec.Slashings

/-!
# Step 6 prototype: the hand-written spec equals the readable Lean

Two functions: `get_current_epoch` and `decrease_balance`. `EpochProofs.Spec` is the hand-written
spec that the Lighthouse epoch proofs use (v1.7.0-beta.2). `Gen` is the readable Lean that Pythia
generates (889a389f9, minimal preset). `Hand` is the minimal preset of the hand-written spec.

The hand spec keeps four error classes. The readable Lean keeps two (`Fail`). `errClass` maps
the first to the second, as `SpecError.fail` does for the interpreter.
-/

namespace Pythia.Bridge

open SpecLean SpecLean.Rd

abbrev Hand := EpochProofs.Spec.Preset.minimal

def errClass : EpochProofs.Spec.SpecError → Fail
  | .indexOutOfRange | .assertionFailed => .invalid
  | .overflow | .divisionByZero => .bug

variable [Spec] [Gen.Cfg]

theorem fdiv_nat (a b : Nat) : (a : Int).fdiv (b : Int) = ((a / b : Nat) : Int) := by
  rw [Int.fdiv_eq_ediv, if_pos (.inl (Int.natCast_nonneg b))]
  simp only [Int.sub_zero]
  exact (Int.natCast_ediv a b).symm

theorem uOf_ok {α : Type} [UintC α] (n : Nat) (hb : UintC.bits α = 64) (hn : n < 2 ^ 64) :
    (uOf α (n : Int) : SpecM α) = .ok (UintC.ofNat n) := by
  unfold uOf
  rw [if_pos ⟨Int.natCast_nonneg n, by rw [hb]; exact_mod_cast hn⟩]
  rfl

-- Unfolding `bind` with `simp` makes the kernel fail with deep recursion. These `rfl` lemmas
-- rewrite one bind at a time.
theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem mapError_ok {ε ε' α : Type} (g : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError g = .ok a := rfl

theorem err_bind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e :=
  rfl

theorem rd_compute_epoch_at_slot (n : Nat) (hn : n < 2 ^ 64) :
    Gen.compute_epoch_at_slot ⟨n⟩ = .ok ⟨n / 8⟩ := by
  have h8 : n / 8 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  simp only [Gen.compute_epoch_at_slot, uOp, erase, intArith, uv, Gen.SLOTS_PER_EPOCH, uCast,
    UintC.val]
  rw [if_neg (by decide), fdiv_nat]
  rw [mapError_ok, ok_bind]
  rw [uOf_ok (α := Gen.Slot) (n / 8) rfl h8]
  simp only [UintC.ofNat]
  rw [ok_bind]
  dsimp only
  rw [uOf_ok (α := Gen.Epoch) (n / 8) rfl h8]
  rfl

theorem get_current_epoch_eq (s : EpochProofs.Spec.BeaconState) (r : Gen.BeaconState)
    (hslot : r.slot.val = s.slot) (hs : s.slot < 2 ^ 64) :
    (Gen.get_current_epoch r).map (·.val) =
      (EpochProofs.Spec.get_current_epoch Hand s).mapError errClass := by
  have hr : r.slot = ⟨s.slot⟩ := by rw [← hslot]
  simp only [Gen.get_current_epoch, hr, rd_compute_epoch_at_slot _ hs]
  rfl

theorem lget_ok {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    lget xs (i : Int) = .ok xs[i] := by
  unfold lget Rd.pyIndex
  rw [if_neg (by omega), if_pos (by omega)]
  simp [h]
  rfl

theorem lget_err {α : Type} (xs : List α) (i : Nat) (h : ¬ i < xs.length) :
    lget xs (i : Int) = .error .invalid := by
  unfold lget Rd.pyIndex
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

theorem lset_ok {α : Type} (xs : List α) (i : Nat) (x : α) (h : i < xs.length) :
    lset xs (i : Int) x = .ok (xs.set i x) := by
  unfold lset Rd.pyIndex
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [Int.toNat_natCast]
  rfl

theorem rd_saturating_sub (a d : Nat) (ha : a < 2 ^ 64) :
    Gen.saturating_sub ⟨a⟩ (d : Int) = .ok ⟨EpochProofs.Spec.saturating_sub a d⟩ := by
  unfold Gen.saturating_sub EpochProofs.Spec.saturating_sub
  simp only [uOp, erase, intArith, uv, UintC.val]
  by_cases hgt : a > d
  · rw [if_pos (by simp; omega), if_pos hgt, mapError_ok, ok_bind,
      show (a : Int) - (d : Int) = ((a - d : Nat) : Int) by omega,
      uOf_ok (α := Gen.Uint64) (a - d) rfl (by omega)]
    rfl
  · rw [if_neg (by simp; omega), if_neg hgt, mapError_ok, ok_bind,
      show (a : Int) - (a : Int) = ((a - a : Nat) : Int) by omega,
      uOf_ok (α := Gen.Uint64) (a - a) rfl (by omega)]
    rfl

/-- `decrease_balance`: the readable Lean equals the hand spec on the balances, and keeps the
other fields. The balances are below `2 ^ 64`, as in any state that SSZ can decode. -/
theorem decrease_balance_eq (r : Gen.BeaconState) (i d : Nat)
    (hb : ∀ b ∈ r.balances, b.val < 2 ^ 64) :
    Gen.decrease_balance r ⟨i⟩ ⟨d⟩ =
      ((EpochProofs.Spec.decrease_balance (r.balances.map (·.val)) i d).mapError errClass).map
        fun bs => { r with balances := bs.map Gen.Gwei.mk } := by
  unfold Gen.decrease_balance EpochProofs.Spec.decrease_balance
  simp only [uv, UintC.val]
  by_cases hi : i < r.balances.length
  · have hbi : r.balances[i].val < 2 ^ 64 := hb _ (List.getElem_mem hi)
    have hi' : i < (r.balances.map (·.val)).length := by simpa using hi
    have hg : EpochProofs.Spec.listGet (r.balances.map (·.val)) i = .ok r.balances[i].val := by
      unfold EpochProofs.Spec.listGet
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    have hs : ∀ v, EpochProofs.Spec.listSet (r.balances.map (·.val)) i v =
        .ok ((r.balances.map (·.val)).set i v) := fun v => by
      unfold EpochProofs.Spec.listSet
      rw [if_pos hi']
      rfl
    rw [lget_ok _ _ hi, ok_bind, rd_saturating_sub _ _ hbi, ok_bind, lset_ok _ _ _ hi, ok_bind,
      hg, ok_bind, hs]
    show Except.ok _ = Except.ok _
    congr
    rw [List.map_set, List.map_map]
    have hid : (Gen.Gwei.mk ∘ fun x : Gen.Gwei => x.val) = id := rfl
    rw [hid, List.map_id]
  · have hg : EpochProofs.Spec.listGet (r.balances.map (·.val)) i = .error .indexOutOfRange := by
      unfold EpochProofs.Spec.listGet
      rw [List.getElem?_eq_none (by simpa using hi)]
      rfl
    rw [lget_err _ _ hi, err_bind, hg, err_bind]
    rfl

end Pythia.Bridge
