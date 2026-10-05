import SpecLean.Validation.Decode
import SpecLean.Validation.Where

/-!
# Decoders read only the objects that they reach

`LocalDec f`: if two heaps hold the same objects at every address that `v` reaches, `f`
decodes `v` the same in both. Each decoder of the readable Lean has an instance: the scalar
ones read no object, a list reads its object and its items, a container its object and its
fields.
-/

namespace SpecLean.Validation.Local

open SpecLean SpecLean.Rd SpecLean.Encode

/-- `h'` holds the objects of `h` at every address that `v` reaches in `h`. -/
def Same (h h' : Heap) (v : Value) : Prop :=
  ∀ q c, follow h v q = some (.ref c) → h'.objs c = h.objs c

class LocalDec {α : Type} (f : Dec α) : Prop where
  local_same : ∀ h h' v, Same h h' v → f h' v = f h v

theorem Same.self {h h' : Heap} {a : Nat} (hp : Same h h' (.ref a)) : h'.objs a = h.objs a :=
  hp [] a (by simp [follow])

theorem Same.field {h h' : Heap} {a : Nat} {ty : Name} {fs : List Value} {i : Nat} {x : Value}
    (hp : Same h h' (.ref a)) (ho : h.objs a = some (.container ty fs)) (hx : fs[i]? = some x) :
    Same h h' x := fun q c e => hp (i :: q) c (by simp [follow, ho, hx, e])

theorem Same.item {h h' : Heap} {a : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} {j : Nat} {x : Value}
    (hp : Same h h' (.ref a)) (ho : h.objs a = some (.list k e l xs)) (hx : xs[j]? = some x) :
    Same h h' x := fun q c e' => hp (j :: q) c (by simp [follow, ho, hx, e'])

instance {α : Type} [UintC α] (t : UintTy) : LocalDec (decUintT (α := α) t) :=
  ⟨fun _ _ v _ => by unfold decUintT; split <;> rfl⟩

instance {α : Type} [BytesC α] (cls : Name) : LocalDec (decBytesT (α := α) cls) :=
  ⟨fun _ _ v _ => by unfold decBytesT; split <;> rfl⟩

instance : LocalDec decBooleanV := ⟨fun _ _ v _ => by unfold decBooleanV; split <;> rfl⟩

theorem mapM_local {α : Type} {f : Dec α} [LocalDec f] {h h' : Heap} {a : Nat} {k : ListKind}
    {e : SszTy} {l : Option Nat} {xs : List Value}
    (hp : Same h h' (.ref a)) (ho : h.objs a = some (.list k e l xs)) :
    ∀ (ys : List Value), (∀ (j : Nat) x, ys[j]? = some x → ∃ i : Nat, xs[i]? = some x) →
      ys.mapM (f h') = ys.mapM (f h)
  | [], _ => rfl
  | y :: ys, hs => by
    obtain ⟨i, h0⟩ := hs 0 y rfl
    simp only [List.mapM_cons, LocalDec.local_same h h' y (hp.item ho h0)]
    rw [mapM_local hp ho ys (fun j x hj => hs (j + 1) x (by simpa using hj))]

instance {α : Type} (k : ListKind) (e : SszTy) (l : Option Nat) (f : Dec α) [LocalDec f] :
    LocalDec (decListT k e l f) := by
  refine ⟨fun h h' v hp => ?_⟩
  cases v with
  | ref a =>
    simp only [decListT, hp.self]
    split
    · rename_i k' e' l' xs ho
      split
      · rename_i hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact mapM_local hp ho xs (fun j _ hj => ⟨j, hj⟩)
      · rfl
    · rfl
  | _ => rfl

/-- The fields of a container read the same in a heap that agrees on what they reach. -/
theorem field_local {α : Type} {f : Dec α} [LocalDec f] {h h' : Heap} {a : Nat} {ty : Name}
    {fs : List Value} (hp : Same h h' (.ref a)) (ho : h.objs a = some (.container ty fs))
    (i : Nat) : (fs[i]?.bind (f h')) = (fs[i]?.bind (f h)) := by
  cases hx : fs[i]? with
  | none => rfl
  | some x => exact LocalDec.local_same h h' x (hp.field ho hx)

theorem containerFieldsT_local {ty : Name} {h h' : Heap} {a : Nat} (hp : Same h h' (.ref a)) :
    containerFieldsT ty h' (.ref a) = containerFieldsT ty h (.ref a) := by
  simp [containerFieldsT, hp.self]

/-- A list of items that the heaps agree on decodes the same. -/
theorem mapM_same {α : Type} {f : Dec α} [LocalDec f] {h h' : Heap} {xs : List Value}
    (hall : ∀ (j : Nat) x, xs[j]? = some x → ∀ q c, follow h x q = some (.ref c) →
      h'.objs c = h.objs c) :
    xs.mapM (f h') = xs.mapM (f h) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.mapM_cons, LocalDec.local_same h h' y (hall 0 y rfl)]
    rw [ih (fun j x hj => hall (j + 1) x (by simpa using hj))]

/-- A decoded list of items that the heaps agree on decodes the same in the new heap. -/
theorem mapM_same_of {α : Type} {f : Dec α} [LocalDec f] {h h' : Heap} {xs : List Value}
    {ys : List α} (hm : xs.mapM (f h) = some ys)
    (hall : ∀ (j : Nat) x, xs[j]? = some x → ∀ q c, follow h x q = some (.ref c) →
      h'.objs c = h.objs c) :
    xs.mapM (f h') = some ys := by
  rw [mapM_same hall, hm]

end SpecLean.Validation.Local

open SpecLean.Validation.Local SpecLean.Validation.Decode in
/-- The `LocalDec` instance of a container decoder: its object, then each field. -/
macro "rd_local" d:ident : tactic => `(tactic| (
  refine ⟨fun h h' v hp => ?_⟩
  cases v with
  | ref a =>
    simp only [$d:ident, Option.bind_eq_bind, containerFieldsT_local hp]
    cases hf : SpecLean.Rd.containerFieldsT _ h (.ref a) with
    | none => rfl
    | some fs =>
      obtain ⟨r, hr, ho⟩ := containerFieldsT_eq.1 hf
      cases hr
      simp only [Option.bind_some, field_local hp ho]
  | _ => simp [$d:ident, SpecLean.Rd.containerFieldsT]))
