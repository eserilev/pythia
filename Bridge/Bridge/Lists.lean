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

/-- A comprehension over `enumerate(xs)` that keeps the indices whose item passes a test: the
readable `filterMapM` against the hand `filter` then `map (·.2)`. -/
theorem sim_filterMapM_zipIdx {α β δ : Type} [UintC δ] (g : α → β) (M : α × Nat → Int × α)
    (hM : ∀ v i, M (v, i) = ((i : Int), v)) (F : Int × α → SpecM (Option δ))
    (p : β × Nat → Bool) (xs : List α) (n : Nat)
    (hF : ∀ v i, n ≤ i → i < n + xs.length → v ∈ xs →
      Sim (Option.map UintC.val) (F ((i : Int), v)) (pure (if p (g v, i) then some i else none))) :
    Sim (List.map UintC.val) (((xs.zipIdx n).map M).filterMapM F)
      (pure (((xs.map g).zipIdx n |>.filter p).map (·.2))) := by
  revert n
  induction xs with
  | nil => intro n _; rfl
  | cons v xs ih =>
    intro n hF
    have h1 := hF v n (Nat.le_refl n) (by simp) (List.mem_cons_self ..)
    have ih' := ih (n + 1) (fun v' i h1 h2 hm =>
      hF v' i (by omega) (by simp only [List.length_cons]; omega) (List.mem_cons_of_mem _ hm))
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, List.zipIdx_cons, hM, List.filterMapM_cons]
    unfold Sim at h1 ih' ⊢
    cases hF0 : F ((n : Int), v) with
    | error e => rw [hF0] at h1; cases h1
    | ok o =>
      rw [hF0] at h1
      rw [ok_bind]
      rw [List.filter_cons]
      cases hp : p (g v, n) with
      | false =>
        rw [hp] at h1
        cases o with
        | none => exact ih'
        | some y => cases h1
      | true =>
        rw [hp] at h1
        cases o with
        | none => cases h1
        | some y =>
          have hy : UintC.val y = n := by
            simp only [Except.map, Option.map_some] at h1
            exact Option.some.inj (Except.ok.inj h1)
          simp only [if_true, List.map_cons]
          cases hr : List.filterMapM F ((List.zipIdx xs (n + 1)).map M) with
          | error e =>
            rw [hr] at ih'
            cases ih'
          | ok ys =>
            rw [hr] at ih'
            rw [ok_bind]
            simp only [Except.map, Except.mapError, pure, Except.pure] at ih' ⊢
            rw [List.map_cons, hy, Except.ok.inj ih']

/-- The items of a `filterMapM` result come from `some` results of the step. -/
theorem post_filterMapM {γ δ : Type} (R : δ → Prop) (F : γ → SpecM (Option δ)) (L : List γ)
    (hF : ∀ x ∈ L, Post (fun o => ∀ y ∈ o, R y) (F x)) :
    Post (fun ys => ys.length ≤ L.length ∧ ∀ y ∈ ys, R y) (L.filterMapM F) := by
  induction L with
  | nil =>
    intro ys h
    cases h
    exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | cons a L ih =>
    have ih' := ih (fun x hx => hF x (List.mem_cons_of_mem _ hx))
    intro ys h
    rw [List.filterMapM_cons] at h
    cases hFa : F a with
    | error e => rw [hFa] at h; cases h
    | ok o =>
      rw [hFa, ok_bind] at h
      cases o with
      | none =>
        have := ih' ys h
        exact ⟨by simp only [List.length_cons]; omega, this.2⟩
      | some b =>
        dsimp only at h
        cases hr : List.filterMapM F L with
        | error e => rw [hr, err_bind] at h; cases h
        | ok rs =>
          rw [hr, ok_bind] at h
          cases h
          have := ih' rs hr
          have hb : R b := hF a (List.mem_cons_self ..) (some b) hFa b rfl
          refine ⟨by simp only [List.length_cons]; omega, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with h1 | h1
          · subst h1; exact hb
          · exact this.2 y h1

theorem post_filterMapM_ir {γ δ : Type} (R : δ → Prop) (F : γ → SpecM (Option δ)) (L : List γ)
    (hL : L.length < 2 ^ 64) (hF : ∀ x ∈ L, Post (fun o => ∀ y ∈ o, R y) (F x)) :
    Post (fun ys => ys.length < 2 ^ 64 ∧ ∀ y ∈ ys, R y) (L.filterMapM F) := by
  intro ys h
  have := post_filterMapM R F L hF ys h
  exact ⟨by omega, this.2⟩

end Pythia.Bridge
