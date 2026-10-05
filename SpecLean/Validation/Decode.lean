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
    decUintT t h v = some x ↔ v = .uint t (UintC.val x) := by
  constructor
  · intro e
    unfold decUintT at e
    split at e
    · split at e
      · cases e; subst_vars; simp [UintC.val_ofNat]
      · cases e
    · cases e
  · rintro rfl
    simp [decUintT, UintC.ofNat_val]

theorem decBytesT_eq {α : Type} [BytesC α] {cls : Name} {h : Heap} {v : Value} {x : α} :
    decBytesT cls h v = some x ↔ v = .bytes cls (BytesC.data x) := by
  constructor
  · intro e
    unfold decBytesT at e
    split at e
    · split at e
      · cases e; subst_vars; simp [BytesC.data_ofBytes]
      · cases e
    · cases e
  · rintro rfl
    simp [decBytesT, BytesC.ofBytes_data]

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

theorem mapM_decUintT {α : Type} [UintC α] {t : UintTy} {h : Heap} {xs : List Value}
    {ys : List α} :
    xs.mapM (decUintT t h) = some ys ↔ xs = ys.map (fun y => .uint t (UintC.val y)) :=
  mapM_eq_map (fun _ _ => decUintT_eq)

theorem mapM_decBytesT {α : Type} [BytesC α] {cls : Name} {h : Heap} {xs : List Value}
    {ys : List α} :
    xs.mapM (decBytesT cls h) = some ys ↔ xs = ys.map (fun y => .bytes cls (BytesC.data y)) :=
  mapM_eq_map (fun _ _ => decBytesT_eq)

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
theorem mapM_set_map {α : Type} {f : Value → Option α} {g : α → Value}
    (hfg : ∀ y, f (g y) = some y) :
    ∀ (ys : List α) (k : Nat) (v : Value), ((ys.map g).set k v).mapM f =
      if k < ys.length then (f v).map (ys.set k ·) else some ys
  | [], k, v => by simp
  | y :: ys, 0, v => by
    simp only [List.map_cons, List.set_cons_zero, List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def, List.length_cons, Nat.zero_lt_succ, if_true, List.set_cons_zero]
    have hm : (ys.map g).mapM f = some ys := by
      have := mapM_set_map hfg ys ys.length (g y)
      simp only [List.set_eq_of_length_le (by simp : (ys.map g).length ≤ ys.length),
        Nat.lt_irrefl, if_false] at this
      exact this
    cases f v <;> simp [hm]
  | y :: ys, k + 1, v => by
    simp only [List.map_cons, List.set_cons_succ, List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def, List.length_cons, Nat.add_lt_add_iff_right, hfg, Option.bind_some,
      mapM_set_map hfg ys k v]
    split <;> (try cases f v) <;> simp

theorem mapM_map_of {α : Type} {f : Value → Option α} {g : α → Value}
    (hfg : ∀ y, f (g y) = some y) : ∀ (ys : List α), (ys.map g).mapM f = some ys
  | [] => rfl
  | y :: ys => by simp [List.mapM_cons, hfg, mapM_map_of hfg ys]

theorem mapM_map_decUintT {α : Type} [UintC α] {t : UintTy} {h : Heap} (ys : List α) :
    (ys.map (fun y => Value.uint t (UintC.val y))).mapM (decUintT t h) = some ys :=
  mapM_decUintT.2 rfl

theorem mapM_map_decBytesT {α : Type} [BytesC α] {cls : Name} {h : Heap} (ys : List α) :
    (ys.map (fun y => Value.bytes cls (BytesC.data y))).mapM (decBytesT cls h) = some ys :=
  mapM_decBytesT.2 rfl

theorem mapM_map_decBooleanV {h : Heap} (ys : List Boolean) :
    (ys.map (fun y => Value.boolean y.val)).mapM (decBooleanV h) = some ys :=
  mapM_decBooleanV.2 rfl

theorem mapM_set_map_decUintT {α : Type} [UintC α] {t : UintTy} {h : Heap} (ys : List α)
    (k : Nat) (v : Value) :
    ((ys.map (fun y => Value.uint t (UintC.val y))).set k v).mapM (decUintT t h) =
      if k < ys.length then (decUintT t h v).map (ys.set k ·) else some ys :=
  mapM_set_map (fun _ => decUintT_eq.2 rfl) ys k v

theorem mapM_set_map_decBytesT {α : Type} [BytesC α] {cls : Name} {h : Heap} (ys : List α)
    (k : Nat) (v : Value) :
    ((ys.map (fun y => Value.bytes cls (BytesC.data y))).set k v).mapM (decBytesT cls h) =
      if k < ys.length then (decBytesT cls h v).map (ys.set k ·) else some ys :=
  mapM_set_map (fun _ => decBytesT_eq.2 rfl) ys k v

theorem mapM_set_map_decBooleanV {h : Heap} (ys : List Boolean) (k : Nat) (v : Value) :
    ((ys.map (fun y => Value.boolean y.val)).set k v).mapM (decBooleanV h) =
      if k < ys.length then (decBooleanV h v).map (ys.set k ·) else some ys :=
  mapM_set_map (fun _ => decBooleanV_eq.2 rfl) ys k v

attribute [rd_simp] containerFieldsT_eq decUintT_eq decBytesT_eq decBooleanV_eq decListV_eq decListT_eq
  mapM_decUintT mapM_decBytesT mapM_decBooleanV

end SpecLean.Validation.Decode
