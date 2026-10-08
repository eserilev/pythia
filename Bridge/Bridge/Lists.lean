import Bridge.Sim

/-!
# List steps of the bridge

`mapM` on both sides, and the readable `sumU` against the hand `uint64Sum`.
-/

namespace Pythia.Bridge

open SpecLean SpecLean.Rd

theorem sim_mapM {α β γ δ : Type} (g : β → δ) (h : α → γ) (F : α → SpecM β) (G : γ → HM δ)
    (xs : List α) (hF : ∀ x ∈ xs, Sim g (F x) (G (h x))) :
    Sim (List.map g) (xs.mapM F) ((xs.map h).mapM G) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.map_cons, List.mapM_cons]
    apply sim_bind (hF x (List.mem_cons_self ..))
    intro y _
    apply sim_bind (ih fun x' hx' => hF x' (List.mem_cons_of_mem _ hx'))
    intro ys _
    exact sim_pure _ _ _ rfl

theorem uOp_add_nat {α : Type} [UintC α] (hb : UintC.bits α = 64) (a b : Nat) :
    (uOp .add (a : Int) (b : Int) : SpecM α) =
      if a + b < 2 ^ 64 then .ok (UintC.ofNat (a + b)) else .error .bug := by
  unfold uOp
  simp only [erase, intArith, mapError_ok, ok_bind]
  rw [show (a : Int) + (b : Int) = ((a + b : Nat) : Int) by push_cast; rfl]
  by_cases h : a + b < 2 ^ 64
  · rw [uOf_ok _ hb h, if_pos h]
  · rw [uOf_neg _ hb (by omega), if_neg h]

theorem foldlM_add {α : Type} [UintC α] (hb : UintC.bits α = 64) (xs : List α) (a : Nat)
    (ha : a < 2 ^ 64) :
    xs.foldlM (fun (acc x : α) => (uOp .add (uv acc) (uv x) : SpecM α)) (UintC.ofNat a) =
      if a + (xs.map UintC.val).sum < 2 ^ 64 then .ok (UintC.ofNat (a + (xs.map UintC.val).sum))
      else .error .bug := by
  induction xs generalizing a with
  | nil => simp [ha]; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons, show uv (UintC.ofNat a : α) = (a : Int) by simp [uv, UintC.val_ofNat],
      show uv x = (UintC.val x : Int) from rfl, uOp_add_nat hb]
    by_cases h : a + UintC.val x < 2 ^ 64
    · rw [if_pos h, ok_bind, ih _ h]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]
    · rw [if_neg h, err_bind]
      simp only [List.map_cons, List.sum_cons]
      rw [if_neg (by omega)]

theorem sim_sumU {α : Type} [UintC α] (hb : UintC.bits α = 64) (s : α) (hs : UintC.val s = 0)
    (xs : List α) :
    Sim UintC.val (sumU s xs) (EpochProofs.Spec.uint64Sum (xs.map UintC.val)) := by
  have hs' : s = UintC.ofNat 0 := by rw [← hs, UintC.ofNat_val]
  subst hs'
  unfold sumU Prim.sum EpochProofs.Spec.uint64Sum EpochProofs.Spec.UINT64_SIZE Sim
  rw [foldlM_add hb xs 0 (by decide)]
  simp only [Nat.zero_add]
  by_cases h : (xs.map UintC.val).sum < 2 ^ 64
  · rw [if_pos h, if_pos h, map_val_ofNat]; rfl
  · rw [if_neg h, if_neg h]; rfl

theorem sim_pyMax2 {α : Type} [UintC α] [PyOrd α] (hlt : ∀ a b : α, PyOrd.lt a b = decide (UintC.val a < UintC.val b))
    (a b : α) : Sim UintC.val (pyMax [a, b]) (pure (max (UintC.val a) (UintC.val b))) := by
  unfold Sim
  show Except.ok (UintC.val (if PyOrd.lt a b = true then b else a)) =
    Except.ok (max (UintC.val a) (UintC.val b))
  rw [hlt]
  by_cases h : UintC.val a < UintC.val b
  · rw [if_pos (by simpa using h), Nat.max_eq_right (Nat.le_of_lt h)]
  · rw [if_neg (by simpa using h), Nat.max_eq_left (by omega)]

end Pythia.Bridge
