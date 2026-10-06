import SpecLean.Rd.Prelude
import SpecLean.Validation.Attr

/-!
# Decode facts for the generated proofs

A decoded argument gives facts about the heap: its object, and the value of each field. Each
lemma here states a decoder result as the value that it reads.
-/

namespace SpecLean.Validation.Decode

open SpecLean SpecLean.Rd

theorem containerFieldsT_eq {ty : Name} {h : Heap} {v : Value} {fs : List Value} :
    containerFieldsT ty h v = some fs ↔ ∃ r, v = .ref r ∧ h.objs r = some (.container ty fs) := by
  constructor
  · intro e
    unfold containerFieldsT at e
    split at e
    · rename_i r
      split at e
      · rename_i ty' fs' ho
        split at e
        · cases e; subst_vars; exact ⟨r, rfl, ho⟩
        · cases e
      · cases e
    · cases e
  · rintro ⟨r, rfl, ho⟩
    simp [containerFieldsT, ho]

theorem decUintT_eq {α : Type} [UintC α] {t : UintTy} {h : Heap} {v : Value} {x : α} :
    decUintT t h v = some x ↔ v = .uint t (UintC.val x) ∧ UintC.val x < 2 ^ UintC.bits α := by
  constructor
  · intro e
    unfold decUintT at e
    split at e
    · split at e
      · rename_i hc; cases e; obtain ⟨rfl, hr⟩ := hc; simp [UintC.val_ofNat, hr]
      · cases e
    · cases e
  · rintro ⟨rfl, hr⟩
    simp [decUintT, UintC.ofNat_val, hr]

theorem decBytesT_eq {α : Type} [BytesC α] {cls : Name} {h : Heap} {v : Value} {x : α} :
    decBytesT cls h v = some x ↔
      v = .bytes cls (BytesC.data x) ∧ (BytesC.data x).length = BytesC.len α := by
  constructor
  · intro e
    unfold decBytesT at e
    split at e
    · split at e
      · rename_i hc; cases e; obtain ⟨rfl, hl⟩ := hc; simp [BytesC.data_ofBytes, hl]
      · cases e
    · cases e
  · rintro ⟨rfl, hl⟩
    simp [decBytesT, BytesC.ofBytes_data, hl]

theorem decBooleanV_eq {h : Heap} {v : Value} {x : Boolean} :
    decBooleanV h v = some x ↔ v = .boolean x.val := by
  constructor
  · intro e
    unfold decBooleanV at e
    split at e
    · cases e; rfl
    · cases e
  · rintro rfl
    rfl

theorem decListV_eq {α : Type} {f : Dec α} {h : Heap} {v : Value} {ys : List α} :
    decListV f h v = some ys ↔
      ∃ a k e l xs, v = .ref a ∧ h.objs a = some (.list k e l xs) ∧ xs.mapM (f h) = some ys := by
  constructor
  · intro e
    unfold decListV at e
    split at e
    · rename_i a
      split at e
      · rename_i k el l xs ho
        exact ⟨a, k, el, l, xs, rfl, ho, e⟩
      · cases e
    · cases e
  · rintro ⟨a, k, e, l, xs, rfl, ho, hm⟩
    simp [decListV, ho, hm]

theorem decListT_eq {α : Type} {k : ListKind} {e : SszTy} {l : Option Nat} {f : Dec α} {h : Heap}
    {v : Value} {ys : List α} :
    decListT k e l f h v = some ys ↔
      ∃ a xs, v = .ref a ∧ h.objs a = some (.list k e l xs) ∧ xs.mapM (f h) = some ys := by
  constructor
  · intro hd
    unfold decListT at hd
    split at hd
    · rename_i a
      split at hd
      · rename_i k' e' l' xs ho
        split at hd
        · rename_i hc
          obtain ⟨rfl, rfl, rfl⟩ := hc
          exact ⟨a, xs, rfl, ho, hd⟩
        · cases hd
      · cases hd
    · cases hd
  · rintro ⟨a, xs, rfl, ho, hm⟩
    simp [decListT, ho, hm]

/-- A list of scalars decodes element by element: it is the list of encodings. -/
theorem mapM_eq_map {α : Type} {f : Value → Option α} {g : α → Value}
    (hf : ∀ v y, f v = some y ↔ v = g y) :
    ∀ {xs : List Value} {ys : List α}, xs.mapM f = some ys ↔ xs = ys.map g
  | [], ys => by cases ys <;> simp
  | x :: xs, ys => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    constructor
    · rintro ⟨y', hy', ys', hys', rfl⟩
      simp [(hf _ _).1 hy', (mapM_eq_map hf).1 hys']
    · intro e
      cases ys with
      | nil => cases e
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at e
        exact ⟨y, (hf _ _).2 e.1, ys, (mapM_eq_map hf).2 e.2, rfl⟩

/-- `mapM_eq_map` for a decoder with a check on the decoded value, such as a range. -/
theorem mapM_eq_map_P {α : Type} {f : Value → Option α} {g : α → Value} {P : α → Prop}
    (hf : ∀ v y, f v = some y ↔ v = g y ∧ P y) :
    ∀ {xs : List Value} {ys : List α}, xs.mapM f = some ys ↔ xs = ys.map g ∧ ∀ y ∈ ys, P y
  | [], ys => by cases ys <;> simp
  | x :: xs, ys => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    constructor
    · rintro ⟨y', hy', ys', hys', rfl⟩
      obtain ⟨e1, p1⟩ := (hf _ _).1 hy'
      obtain ⟨e2, p2⟩ := (mapM_eq_map_P hf).1 hys'
      refine ⟨by simp [e1, e2], fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact p1
      · exact p2 y hy
    · rintro ⟨e, hp⟩
      cases ys with
      | nil => cases e
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at e
        exact ⟨y, (hf _ _).2 ⟨e.1, hp y (by simp)⟩, ys,
          (mapM_eq_map_P hf).2 ⟨e.2, fun z hz => hp z (by simp [hz])⟩, rfl⟩

theorem mapM_decUintT {α : Type} [UintC α] {t : UintTy} {h : Heap} {xs : List Value}
    {ys : List α} :
    xs.mapM (decUintT t h) = some ys ↔ xs = ys.map (fun y => .uint t (UintC.val y)) ∧
      ∀ y ∈ ys, UintC.val y < 2 ^ UintC.bits α :=
  mapM_eq_map_P (fun _ _ => decUintT_eq)

theorem mapM_decBytesT {α : Type} [BytesC α] {cls : Name} {h : Heap} {xs : List Value}
    {ys : List α} :
    xs.mapM (decBytesT cls h) = some ys ↔ xs = ys.map (fun y => .bytes cls (BytesC.data y)) ∧
      ∀ y ∈ ys, (BytesC.data y).length = BytesC.len α :=
  mapM_eq_map_P (fun _ _ => decBytesT_eq)

theorem mapM_decBooleanV {h : Heap} {xs : List Value} {ys : List Boolean} :
    xs.mapM (decBooleanV h) = some ys ↔ xs = ys.map (fun y => .boolean y.val) :=
  mapM_eq_map (fun _ _ => decBooleanV_eq)

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.length = ys.length
  | [], ys, e => by simp at e; subst e; rfl
  | x :: xs, ys, e => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at e
    obtain ⟨y, -, ys', hys, rfl⟩ := e
    simp [mapM_length hys]

/-- An index into a decoded list: both lists miss it, or both hold it and the item decodes. -/
theorem mapM_getElem? {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ k : Nat,
      (xs[k]? = none ∧ ys[k]? = none) ∨ ∃ v y, xs[k]? = some v ∧ ys[k]? = some y ∧ f v = some y
  | [], ys, e, k => by simp at e; subst e; simp
  | x :: xs, ys, e, k => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at e
    obtain ⟨y, hy, ys', hys, rfl⟩ := e
    cases k with
    | zero => exact .inr ⟨x, y, rfl, rfl, hy⟩
    | succ k => simpa using mapM_getElem? hys k

/-- A write into a list of encodings, decoded: the decoded list with the item replaced. -/
theorem mapM_map_of {α : Type} {f : Value → Option α} {g : α → Value} :
    ∀ (ys : List α), (∀ y ∈ ys, f (g y) = some y) → (ys.map g).mapM f = some ys
  | [], _ => rfl
  | y :: ys, hfg => by
    simp [List.mapM_cons, hfg y (by simp),
      mapM_map_of ys (fun z hz => hfg z (by simp [hz]))]

/-- A write into a list of encodings, decoded: the decoded list with the item replaced. -/
theorem mapM_set_map {α : Type} {f : Value → Option α} {g : α → Value} :
    ∀ (ys : List α), (∀ y ∈ ys, f (g y) = some y) → ∀ (k : Nat) (v : Value),
      ((ys.map g).set k v).mapM f = if k < ys.length then (f v).map (ys.set k ·) else some ys
  | [], _, k, v => by simp
  | y :: ys, hfg, 0, v => by
    simp only [List.map_cons, List.set_cons_zero, List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def, List.length_cons, Nat.zero_lt_succ, if_true, List.set_cons_zero]
    have hm : (ys.map g).mapM f = some ys := mapM_map_of ys (fun z hz => hfg z (by simp [hz]))
    cases f v <;> simp [hm]
  | y :: ys, hfg, k + 1, v => by
    simp only [List.map_cons, List.set_cons_succ, List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def, List.length_cons, Nat.add_lt_add_iff_right, hfg y (by simp),
      Option.bind_some, mapM_set_map ys (fun z hz => hfg z (by simp [hz])) k v]
    split <;> (try cases f v) <;> simp

theorem mapM_map_decUintT {α : Type} [UintC α] {t : UintTy} {h : Heap} (ys : List α)
    (hr : ∀ y ∈ ys, UintC.val y < 2 ^ UintC.bits α) :
    (ys.map (fun y => Value.uint t (UintC.val y))).mapM (decUintT t h) = some ys :=
  mapM_decUintT.2 ⟨rfl, hr⟩

theorem mapM_map_decBytesT {α : Type} [BytesC α] {cls : Name} {h : Heap} (ys : List α)
    (hl : ∀ y ∈ ys, (BytesC.data y).length = BytesC.len α) :
    (ys.map (fun y => Value.bytes cls (BytesC.data y))).mapM (decBytesT cls h) = some ys :=
  mapM_decBytesT.2 ⟨rfl, hl⟩

theorem mapM_map_decBooleanV {h : Heap} (ys : List Boolean) :
    (ys.map (fun y => Value.boolean y.val)).mapM (decBooleanV h) = some ys :=
  mapM_decBooleanV.2 rfl

theorem mapM_set_map_decUintT {α : Type} [UintC α] {t : UintTy} {h : Heap} (ys : List α)
    (hr : ∀ y ∈ ys, UintC.val y < 2 ^ UintC.bits α) (k : Nat) (v : Value) :
    ((ys.map (fun y => Value.uint t (UintC.val y))).set k v).mapM (decUintT t h) =
      if k < ys.length then (decUintT t h v).map (ys.set k ·) else some ys :=
  mapM_set_map ys (fun y hy => decUintT_eq.2 ⟨rfl, hr y hy⟩) k v

theorem mapM_set_map_decBytesT {α : Type} [BytesC α] {cls : Name} {h : Heap} (ys : List α)
    (hl : ∀ y ∈ ys, (BytesC.data y).length = BytesC.len α) (k : Nat) (v : Value) :
    ((ys.map (fun y => Value.bytes cls (BytesC.data y))).set k v).mapM (decBytesT cls h) =
      if k < ys.length then (decBytesT cls h v).map (ys.set k ·) else some ys :=
  mapM_set_map ys (fun y hy => decBytesT_eq.2 ⟨rfl, hl y hy⟩) k v

theorem mapM_set_map_decBooleanV {h : Heap} (ys : List Boolean) (k : Nat) (v : Value) :
    ((ys.map (fun y => Value.boolean y.val)).set k v).mapM (decBooleanV h) =
      if k < ys.length then (decBooleanV h v).map (ys.set k ·) else some ys :=
  mapM_set_map ys (fun _ _ => decBooleanV_eq.2 rfl) k v

attribute [rd_simp] containerFieldsT_eq decUintT_eq decBytesT_eq decBooleanV_eq decListV_eq decListT_eq
  mapM_decUintT mapM_decBytesT mapM_decBooleanV

end SpecLean.Validation.Decode

namespace SpecLean.Validation.Decode

open SpecLean.Rd

-- The width and the length of a class are literals in the proofs.
attribute [rd_simp] UintC.bits BytesC.len

end SpecLean.Validation.Decode

namespace SpecLean.Validation.Decode

/-- A range check that the context proves: the proofs discharge `n < m` by `omega`. -/
theorem ite_lt_of {α : Type} {n m : Nat} {a b : α} (h : n < m) : (if n < m then a else b) = a :=
  if_pos h

end SpecLean.Validation.Decode

namespace SpecLean.Validation.Decode

/-- An item of a decoded list, at an index below the length: it decodes to the item of the
decoded list. -/
theorem mapM_getElem_some {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (hm : xs.mapM f = some ys) (i : Nat) (hi : i < xs.length) :
    ∃ y, ys[i]? = some y ∧ f xs[i] = some y := by
  rcases mapM_getElem? hm i with ⟨h1, -⟩ | ⟨v, y, h1, h2, h3⟩
  · rw [List.getElem?_eq_none_iff] at h1; omega
  · rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h1
    exact ⟨y, h2, h1 ▸ h3⟩

end SpecLean.Validation.Decode

namespace SpecLean.Validation.Decode

theorem mapM_drop {α β : Type} {f : α → Option β} :
    ∀ (n : Nat) {xs : List α} {ys : List β}, xs.mapM f = some ys →
      (xs.drop n).mapM f = some (ys.drop n)
  | 0, _, _, hm => by simpa using hm
  | n + 1, [], ys, hm => by simp at hm; subst hm; rfl
  | n + 1, x :: xs, ys, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hm
    obtain ⟨y, -, ys', hys', rfl⟩ := hm
    simpa using mapM_drop n hys'

theorem mapM_take {α β : Type} {f : α → Option β} :
    ∀ (n : Nat) {xs : List α} {ys : List β}, xs.mapM f = some ys →
      (xs.take n).mapM f = some (ys.take n)
  | 0, _, _, _ => rfl
  | n + 1, [], ys, hm => by simp at hm; subst hm; rfl
  | n + 1, x :: xs, ys, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hm
    obtain ⟨y, hy, ys', hys', rfl⟩ := hm
    simp [List.mapM_cons, hy, mapM_take n hys']

end SpecLean.Validation.Decode

namespace SpecLean.Validation.Decode

/-- A length check that the context proves: the proofs discharge `n = m` by `omega`. -/
theorem ite_eq_nat_of {α : Type} {n m : Nat} {a b : α} (h : n = m) :
    (if n = m then a else b) = a :=
  if_pos h

end SpecLean.Validation.Decode
