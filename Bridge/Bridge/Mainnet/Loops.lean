import Bridge.GenMainnet.Specs

/-!
# Bridge proofs of functions with a loop (mainnet)

Hand-written proofs of `spec_f` for functions whose readable Lean has a loop. Each theorem is
`loop_f : spec_f`. `tools/gen_bridge.py` reads the names and uses them in `Eqs.lean`.
-/

namespace Pythia.Bridge.Mainnet

open Pythia.Bridge SpecLean SpecLean.Rd

attribute [local instance] GenMainnet.Cfg.default
set_option linter.unusedSectionVars false

variable [Spec]

/-- `y + n / y ≤ n + 1` for `1 ≤ y ≤ n`: the sum in the square-root loop does not overflow. -/
theorem add_div_le (n y : Nat) (h1 : 1 ≤ y) (h2 : y ≤ n) : y + n / y ≤ n + 1 := by
  have hq := Nat.div_mul_le_self n y
  generalize n / y = q at hq ⊢
  cases q with
  | zero => omega
  | succ q =>
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    simp only [Nat.succ_mul, Nat.mul_succ] at hq
    omega

theorem isqrt_loop_ok (n : GenMainnet.Uint64) (hn : n.val + 1 < 2 ^ 64) (x y : GenMainnet.Uint64)
    (hx : x.val ≤ n.val) (hy : y.val < 2 ^ 64) (hy1 : 1 ≤ n.val → 1 ≤ y.val) :
    ∃ b, GenMainnet.integer_squareroot.loop1 n x y =
      .ok (⟨EpochProofs.Spec.integer_squareroot.loop n.val x.val y.val⟩, b) := by
  rw [GenMainnet.integer_squareroot.loop1, EpochProofs.Spec.integer_squareroot.loop]
  by_cases hyx : y.val < x.val
  · have h1 : 1 ≤ y.val := hy1 (by omega)
    have hd : (uOp .floorDiv (uv n) (uv y) : SpecM GenMainnet.Uint64) = .ok ⟨n.val / y.val⟩ :=
      uOp_div_ok (α := GenMainnet.Uint64) rfl n.val y.val (by omega) (by omega)
    have hs : y.val + n.val / y.val ≤ n.val + 1 := add_div_le n.val y.val h1 (by omega)
    have ha : (uOp .add (uv y) (uv (⟨n.val / y.val⟩ : GenMainnet.Uint64)) : SpecM GenMainnet.Uint64) =
        .ok ⟨y.val + n.val / y.val⟩ := by
      rw [show uv y = ((y.val : Nat) : Int) from rfl, show uv (⟨n.val / y.val⟩ : GenMainnet.Uint64) = ((n.val / y.val : Nat) : Int) from rfl,
        uOp_add_nat (α := GenMainnet.Uint64) rfl, if_pos (by omega)]; rfl
    have h2 : (uOp .floorDiv (uv (⟨y.val + n.val / y.val⟩ : GenMainnet.Uint64)) 2 : SpecM GenMainnet.Uint64) =
        .ok ⟨(y.val + n.val / y.val) / 2⟩ :=
      uOp_div_ok (α := GenMainnet.Uint64) rfl _ 2 (by omega) (by show y.val + n.val / y.val < 2 ^ 64; omega)
    obtain ⟨b, hb⟩ := isqrt_loop_ok n hn y ⟨(y.val + n.val / y.val) / 2⟩ (by omega) (by simp; omega)
      (fun hn1 => by
        show 1 ≤ (y.val + n.val / y.val) / 2
        rcases Nat.lt_or_ge 1 y.val with h | h
        · generalize n.val / y.val = q; omega
        · have : y.val = 1 := by omega
          rw [this, Nat.div_one]; omega)
    refine ⟨b, ?_⟩
    rw [if_neg (by simp [uv]; omega), if_pos hyx]
    simp only [pure_bind]
    rw [hd, ok_bind, ha, ok_bind, h2, ok_bind, dif_pos (by show y.val < x.val; exact hyx)]
    exact hb
  · refine ⟨y, ?_⟩
    rw [if_pos (by simp [uv]; omega), if_neg hyx]
    rfl
termination_by x.val
decreasing_by all_goals (simp_wf; omega)

theorem isqrt_loop_le (n x y : Nat) : EpochProofs.Spec.integer_squareroot.loop n x y ≤ x := by
  rw [EpochProofs.Spec.integer_squareroot.loop]
  split
  · have := isqrt_loop_le n y ((y + n / y) / 2); omega
  · exact Nat.le_refl _
termination_by x

theorem loop_integer_squareroot : spec_integer_squareroot := by
  intro n hn
  unfold GenMainnet.integer_squareroot EpochProofs.Spec.integer_squareroot
  by_cases hm : n.val = 18446744073709551615
  · have e : (uv n == uv GenMainnet.UINT64_MAX) = true := by simp [uv, hm, GenMainnet.UINT64_MAX]
    rw [if_pos e]
    have e2 : (n.val == EpochProofs.Spec.UINT64_MAX) = true := by
      simp [hm, EpochProofs.Spec.UINT64_MAX]
    rw [if_pos e2]
    exact ⟨rfl, fun x hx => by cases hx; decide⟩
  · have e : ¬ (uv n == uv GenMainnet.UINT64_MAX) = true := by simp [uv, GenMainnet.UINT64_MAX]; omega
    rw [if_neg e]
    have e2 : ¬ (n.val == EpochProofs.Spec.UINT64_MAX) = true := by
      simp [hm, EpochProofs.Spec.UINT64_MAX]
    rw [if_neg e2]
    have hn' : n.val + 1 < 2 ^ 64 := by omega
    have ha : (uOp .add (uv n) 1 : SpecM GenMainnet.Uint64) = .ok ⟨n.val + 1⟩ := by
      rw [show uv n = ((n.val : Nat) : Int) from rfl, show (1 : Int) = ((1 : Nat) : Int) from rfl,
        uOp_add_nat (α := GenMainnet.Uint64) rfl, if_pos hn']; rfl
    have hd : (uOp .floorDiv (uv (⟨n.val + 1⟩ : GenMainnet.Uint64)) 2 : SpecM GenMainnet.Uint64) =
        .ok ⟨(n.val + 1) / 2⟩ :=
      uOp_div_ok (α := GenMainnet.Uint64) rfl _ 2 (by omega) hn'
    obtain ⟨b, hb⟩ := isqrt_loop_ok n hn' n ⟨(n.val + 1) / 2⟩ (Nat.le_refl _) (by show (n.val + 1) / 2 < 2 ^ 64; omega)
      (fun h1 => by show 1 ≤ (n.val + 1) / 2; omega)
    simp only [pure_bind]
    rw [ha, ok_bind, hd, ok_bind, hb, ok_bind]
    refine ⟨rfl, fun x hx => ?_⟩
    cases hx
    have := isqrt_loop_le n.val n.val ((n.val + 1) / 2)
    show EpochProofs.Spec.integer_squareroot.loop n.val n.val ((n.val + 1) / 2) < 2 ^ 64
    omega

end Pythia.Bridge.Mainnet
