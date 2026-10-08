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

theorem sim_pyMin2 {α : Type} [UintC α] [PyOrd α] (hlt : ∀ a b : α, PyOrd.lt a b = decide (UintC.val a < UintC.val b))
    (a b : α) : Sim UintC.val (pyMin [a, b]) (pure (min (UintC.val a) (UintC.val b))) := by
  unfold Sim
  show Except.ok (UintC.val (if PyOrd.lt b a = true then b else a)) =
    Except.ok (min (UintC.val a) (UintC.val b))
  rw [hlt]
  by_cases h : UintC.val b < UintC.val a
  · rw [if_pos (by simpa using h), Nat.min_eq_right (Nat.le_of_lt h)]
  · rw [if_neg (by simpa using h), Nat.min_eq_left (by omega)]

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

/-- `dedup` keeps a list with no duplicates. -/
theorem dedup_of_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (h : xs.Nodup) :
    dedup xs = xs := by
  have key : ∀ acc : List α, (acc ++ xs).Nodup →
      xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc = acc ++ xs := by
    clear h
    induction xs with
    | nil => intro acc _; simp
    | cons x xs ih =>
      intro acc hn
      rw [List.foldl_cons]
      have hx : x ∉ acc := by
        intro hm
        have := List.nodup_append.mp hn
        exact this.2.2 x hm x (List.mem_cons_self ..) rfl
      rw [if_neg (by simpa using hx)]
      have := ih (acc ++ [x]) (by simpa using hn)
      simpa using this
  unfold dedup
  simpa using key [] (by simpa using h)

theorem nodup_filter_zipIdx_snd {β : Type} (xs : List β) (p : β × Nat → Bool) :
    ((xs.zipIdx.filter p).map (·.2)).Nodup := by
  have h1 : (xs.zipIdx.map (·.2)).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  exact (List.Sublist.map _ List.filter_sublist).nodup h1
theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map] at h
  exact h.imp fun hne heq => hne (congrArg f heq)

theorem nodup_get_active (s : EpochProofs.Spec.BeaconState) (e : Nat) :
    (EpochProofs.Spec.get_active_validator_indices s e).Nodup :=
  nodup_filter_zipIdx_snd _ _

/-- The items of `dedup xs` are items of `xs`, and there are not more of them. -/
theorem dedup_facts {α : Type} [BEq α] (xs : List α) :
    (dedup xs).length ≤ xs.length ∧ ∀ z ∈ dedup xs, z ∈ xs := by
  have key : ∀ acc : List α,
      (xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).length ≤
        acc.length + xs.length ∧
      ∀ z ∈ xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc,
        z ∈ acc ∨ z ∈ xs := by
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih =>
      intro acc
      rw [List.foldl_cons]
      split
      · have := ih acc
        refine ⟨by simp only [List.length_cons]; omega, fun z hz => ?_⟩
        rcases this.2 z hz with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · have := ih (acc ++ [x])
        refine ⟨by simp only [List.length_cons, List.length_append, List.length_nil] at this ⊢; omega,
          fun z hz => ?_⟩
        rcases this.2 z hz with h | h
        · rcases List.mem_append.mp h with h' | h'
          · exact Or.inl h'
          · simp only [List.mem_singleton] at h'; subst h'; exact Or.inr (List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ h)
  have := key []
  unfold dedup
  refine ⟨by simpa using this.1, fun z hz => ?_⟩
  rcases this.2 z hz with h | h
  · cases h
  · exact h

theorem ir_dedup {α : Type} [BEq α] {P : α → Prop} {xs : List α}
    (h : xs.length < 2 ^ 64 ∧ ∀ z ∈ xs, P z) : (dedup xs).length < 2 ^ 64 ∧ ∀ z ∈ dedup xs, P z :=
  ⟨Nat.lt_of_le_of_lt (dedup_facts xs).1 h.1, fun z hz => h.2 z ((dedup_facts xs).2 z hz)⟩
/-! ## Membership and index in a list of byte values -/

theorem bytes_data_inj {β : Type} [BytesC β] {x y : β} (h : BytesC.data x = BytesC.data y) : x = y := by
  rw [← BytesC.ofBytes_data x, ← BytesC.ofBytes_data y, h]

theorem mem_map_bytes {α β : Type} [BytesC β] (x : β) (vs : List α) (g : α → β) :
    x ∈ vs.map g ↔ BytesC.data x ∈ vs.map (fun v => BytesC.data (g v)) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, bytes_data_inj h⟩

theorem mem_map_toVec {α : Type} (n : Nat) (vs : List α) (f : α → List UInt8) (b : List UInt8)
    (hb : b.length = n) (hvs : ∀ y ∈ vs, (f y).length = n) :
    toVec n b ∈ vs.map (fun y => toVec n (f y)) ↔ b ∈ vs.map f := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, (toVec_inj (hvs a ha) hb).mp h⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, by rw [h]⟩

theorem idxOf_map_of_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β) (xs : List α) (x : α)
    (hinj : ∀ y ∈ xs, f y = f x → y = x) : (xs.map f).idxOf (f x) = xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons]
    have ih' := ih (fun y hy => hinj y (List.mem_cons_of_mem _ hy))
    by_cases h : a = x
    · subst h; simp
    · have hf : f a ≠ f x := fun e => h (hinj a (List.mem_cons_self ..) e)
      have e1 : (f a == f x) = false := beq_eq_false_iff_ne.mpr hf
      have e2 : (a == x) = false := beq_eq_false_iff_ne.mpr h
      rw [e1, e2, ih']

theorem idxOf_map_bytes {α β : Type} [BytesC β] [BEq β] [LawfulBEq β] (x : β) (vs : List α) (g : α → β) :
    (vs.map g).idxOf x = (vs.map (fun v => BytesC.data (g v))).idxOf (BytesC.data x) := by
  have := idxOf_map_of_inj (BytesC.data (α := β)) (vs.map g) x (fun y _ h => bytes_data_inj h)
  rw [List.map_map] at this
  rw [← this]
  rfl

theorem idxOf_map_toVec {α : Type} (n : Nat) (vs : List α) (f : α → List UInt8) (b : List UInt8)
    (hb : b.length = n) (hvs : ∀ y ∈ vs, (f y).length = n) :
    (vs.map (fun y => toVec n (f y))).idxOf (toVec n b) = (vs.map f).idxOf b := by
  have h := idxOf_map_of_inj (toVec n) (vs.map f) b (fun y hy e => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    exact (toVec_inj (hvs a ha) hb).mp e)
  rw [List.map_map] at h
  exact h

theorem lindex_ok {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (x : α) (h : x ∈ xs) :
    lindex xs x = .ok ((xs.idxOf x : Nat) : Int) := by
  unfold lindex
  have : xs.findIdx? (· == x) = some (xs.idxOf x) := by
    rw [List.findIdx?_eq_some_iff_findIdx_eq]
    exact ⟨List.idxOf_lt_length_of_mem h, rfl⟩
  rw [this]; rfl
theorem toVec_bne {n : Nat} (a b : List UInt8) (ha : a.length = n) (hb : b.length = n) :
    (toVec n a != toVec n b) = (a != b) := by
  rw [bne, bne, toVec_beq a b ha hb]

/-- `xs[-1]`: the last item, against the hand `listGet` at `length - 1`. -/
theorem sim_lget_last {α β : Type} (g : α → β) (xs : List α) :
    Sim g (lget xs (-1)) (EpochProofs.Spec.listGet (xs.map g) ((xs.map g).length - 1)) := by
  rw [List.length_map]
  cases xs with
  | nil => rfl
  | cons x xs =>
    have := sim_lget g (x :: xs) ((x :: xs).length - 1)
    unfold Sim lget Rd.pyIndex at *
    simp only [List.length_cons] at *
    rw [if_pos (by omega), if_pos (by omega)]
    rw [if_neg (by omega), if_pos (by omega)] at this
    have e : ((-1 : Int) + ((xs.length + 1 : Nat) : Int)).toNat = ((xs.length + 1 - 1 : Nat) : Int).toNat := by omega
    rw [e]
    exact this
/-- `max` and `min` pick one of their arguments. -/
theorem pick_mem {α : Type} (better : α → α → Id Bool) (best : α) (xs : List α) :
    Id.run (Prim.pick better best xs) ∈ best :: xs := by
  induction xs generalizing best with
  | nil => exact List.mem_cons_self ..
  | cons x xs ih =>
    simp only [Prim.pick]
    show Id.run (Prim.pick better (if Id.run (better x best) then x else best) xs) ∈ best :: x :: xs
    by_cases hb : Id.run (better x best) = true
    · rw [if_pos hb]
      rcases List.mem_cons.mp (ih x) with h | h
      · rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    · rw [if_neg hb]
      rcases List.mem_cons.mp (ih best) with h | h
      · rw [h]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem pyMax_mem {α : Type} [PyOrd α] {xs : List α} {x : α} (h : pyMax xs = .ok x) : x ∈ xs := by
  cases xs with
  | nil => cases h
  | cons a xs =>
    unfold pyMax at h
    cases h
    exact pick_mem _ _ _

theorem pyMin_mem {α : Type} [PyOrd α] {xs : List α} {x : α} (h : pyMin xs = .ok x) : x ∈ xs := by
  cases xs with
  | nil => cases h
  | cons a xs =>
    unfold pyMin at h
    cases h
    exact pick_mem _ _ _
theorem pyMax2_val {α : Type} [PyOrd α] [UintC α] {a b x : α} (h : pyMax [a, b] = .ok x) :
    UintC.val x = UintC.val a ∨ UintC.val x = UintC.val b := by
  rcases List.mem_cons.mp (pyMax_mem h) with h1 | h1
  · exact Or.inl (h1 ▸ rfl)
  · exact Or.inr ((List.mem_singleton.mp h1) ▸ rfl)

theorem pyMin2_val {α : Type} [PyOrd α] [UintC α] {a b x : α} (h : pyMin [a, b] = .ok x) :
    UintC.val x = UintC.val a ∨ UintC.val x = UintC.val b := by
  rcases List.mem_cons.mp (pyMin_mem h) with h1 | h1
  · exact Or.inl (h1 ▸ rfl)
  · exact Or.inr ((List.mem_singleton.mp h1) ▸ rfl)

/-- `range(a, b)` and a list comprehension over it. -/
theorem pyRange_nat (a b : Nat) :
    pyRange (a : Int) (b : Int) 1 = .ok ((List.range' a (b - a)).map fun i : Nat => (i : Int)) := by
  unfold pyRange
  rw [if_neg (by decide)]
  show Except.ok _ = Except.ok _
  congr 1
  have : (((b : Int) - a + 1 - 1) / 1).toNat = b - a := by omega
  simp only [gt_iff_lt, show (1 : Int) > 0 from by decide, ↓reduceIte, this]
  rw [List.range'_eq_map_range]
  simp [List.map_map, Function.comp_def]

theorem sim_mapM_range {β δ : Type} (g : β → δ) (a b : Nat) (F : Int → SpecM β) (G : Nat → HM δ)
    (hF : ∀ i, a ≤ i → i < b → Sim g (F i) (G i)) :
    Sim (List.map g) (((List.range' a (b - a)).map fun i : Nat => (i : Int)).mapM F)
      ((List.range' a (b - a)).mapM G) := by
  have h := sim_mapM g Int.toNat F G ((List.range' a (b - a)).map fun i : Nat => (i : Int))
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have := List.mem_range'_1.mp hi
      rw [Int.toNat_natCast]
      exact hF i this.1 (by omega))
  rw [List.map_map] at h
  have e : ((List.range' a (b - a)).map (Int.toNat ∘ fun i : Nat => (i : Int))) = List.range' a (b - a) := by
    simp [Function.comp_def]
  rw [e] at h
  exact h

theorem post_mapM_ir {γ δ : Type} (R : δ → Prop) (F : γ → SpecM δ) (L : List γ)
    (hL : L.length < 2 ^ 64) (hF : ∀ x ∈ L, Post R (F x)) :
    Post (fun ys => ys.length < 2 ^ 64 ∧ ∀ y ∈ ys, R y) (L.mapM F) := by
  have key : ∀ ys, L.mapM F = .ok ys → ys.length = L.length ∧ ∀ y ∈ ys, R y := by
    induction L with
    | nil => intro ys h; cases h; exact ⟨rfl, fun _ h => nomatch h⟩
    | cons x L ih =>
      intro ys h
      rw [List.mapM_cons] at h
      cases hx : F x with
      | error e => rw [hx] at h; cases h
      | ok y =>
        rw [hx, ok_bind] at h
        cases hr : L.mapM F with
        | error e => rw [hr, err_bind] at h; cases h
        | ok rs =>
          rw [hr, ok_bind] at h
          cases h
          have := ih (by simp at hL; omega) (fun z hz => hF z (List.mem_cons_of_mem _ hz)) rs hr
          refine ⟨by simp [this.1], fun z hz => ?_⟩
          rcases List.mem_cons.mp hz with h1 | h1
          · rw [h1]; exact hF x (List.mem_cons_self ..) y hx
          · exact this.2 z h1
  intro ys h
  have := key ys h
  exact ⟨by omega, this.2⟩
theorem pyRange_uv_len {α β : Type} [UintC α] [UintC β] {a : α} {b : β} {y : List Int}
    (h : pyRange (uv a) (uv b) 1 = .ok y) : y.length ≤ UintC.val b := by
  rw [show uv a = ((UintC.val a : Nat) : Int) from rfl, show uv b = ((UintC.val b : Nat) : Int) from rfl,
    pyRange_nat] at h
  cases h
  simp

end Pythia.Bridge
