import SpecLean.Validation.Decode
import SpecLean.Validation.Where

/-!
# Decoders read only the objects that they reach

`LocalDec f`: a write to an object that `f` does not reach from `v` leaves `f v` unchanged.
Each decoder of the readable Lean has an instance: the scalar ones read no object, a list reads
its object and its items, a container its object and its fields.
-/

namespace SpecLean.Validation.Local

open SpecLean SpecLean.Rd SpecLean.Encode

/-- No object that `v` reaches is at address `w`. -/
def Away (h : Heap) (v : Value) (w : Nat) : Prop :=
  ∀ q c, follow h v q = some (.ref c) → c ≠ w

class LocalDec {α : Type} (f : Dec α) : Prop where
  local_set : ∀ h w o v, Away h v w → f (h.set w o) v = f h v

theorem Away.self {h : Heap} {a w : Nat} (hp : Away h (.ref a) w) : a ≠ w :=
  hp [] a (by simp [follow])

theorem Away.field {h : Heap} {a w : Nat} {ty : Name} {fs : List Value} {i : Nat} {x : Value}
    (hp : Away h (.ref a) w) (ho : h.objs a = some (.container ty fs)) (hx : fs[i]? = some x) :
    Away h x w := fun q c e => hp (i :: q) c (by simp [follow, ho, hx, e])

theorem Away.item {h : Heap} {a w : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} {j : Nat} {x : Value}
    (hp : Away h (.ref a) w) (ho : h.objs a = some (.list k e l xs)) (hx : xs[j]? = some x) :
    Away h x w := fun q c e' => hp (j :: q) c (by simp [follow, ho, hx, e'])

instance {α : Type} [UintC α] (t : UintTy) : LocalDec (decUintT (α := α) t) :=
  ⟨fun _ _ _ v _ => by unfold decUintT; split <;> rfl⟩

instance {α : Type} [BytesC α] (cls : Name) : LocalDec (decBytesT (α := α) cls) :=
  ⟨fun _ _ _ v _ => by unfold decBytesT; split <;> rfl⟩

instance : LocalDec decBooleanV := ⟨fun _ _ _ v _ => by unfold decBooleanV; split <;> rfl⟩

theorem mapM_local {α : Type} {f : Dec α} [LocalDec f] {h : Heap} {w : Nat} {o : HeapObj}
    {a : Nat} {k : ListKind} {e : SszTy} {l : Option Nat} {xs : List Value}
    (hp : Away h (.ref a) w) (ho : h.objs a = some (.list k e l xs)) :
    ∀ (ys : List Value), (∀ (j : Nat) x, ys[j]? = some x → ∃ i : Nat, xs[i]? = some x) →
      ys.mapM (f (h.set w o)) = ys.mapM (f h)
  | [], _ => rfl
  | y :: ys, hs => by
    obtain ⟨i, h0⟩ := hs 0 y rfl
    have hy : Away h y w := hp.item ho h0
    simp only [List.mapM_cons, LocalDec.local_set h w o y hy]
    have := mapM_local (f := f) (o := o) hp ho ys (fun j x hj => hs (j + 1) x (by simpa using hj))
    rw [this]

instance {α : Type} (k : ListKind) (e : SszTy) (l : Option Nat) (f : Dec α) [LocalDec f] :
    LocalDec (decListT k e l f) := by
  refine ⟨fun h w o v hp => ?_⟩
  cases v with
  | ref a =>
    have ha : a ≠ w := hp.self
    simp only [decListT, Heap.set_objs, if_neg ha]
    split
    · rename_i k' e' l' xs ho
      split
      · rename_i hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact mapM_local hp ho xs (fun j _ hj => ⟨j, hj⟩)
      · rfl
    · rfl
  | _ => rfl

/-- The fields of a container read the same after a write away from it. -/
theorem field_local {α : Type} {f : Dec α} [LocalDec f] {h : Heap} {w : Nat} {o : HeapObj}
    {a : Nat} {ty : Name} {fs : List Value} (hp : Away h (.ref a) w)
    (ho : h.objs a = some (.container ty fs)) (i : Nat) :
    (fs[i]?.bind (f (h.set w o))) = (fs[i]?.bind (f h)) := by
  cases hx : fs[i]? with
  | none => rfl
  | some x => exact LocalDec.local_set h w o x (hp.field ho hx)

theorem containerFieldsT_local {ty : Name} {h : Heap} {w : Nat} {o : HeapObj} {a : Nat}
    (hp : Away h (.ref a) w) :
    containerFieldsT ty (h.set w o) (.ref a) = containerFieldsT ty h (.ref a) := by
  simp [containerFieldsT, hp.self]

/-- A list of items that no write reaches decodes the same. -/
theorem mapM_set_away {α : Type} {f : Dec α} [LocalDec f] {h : Heap} {w : Nat} {o : HeapObj}
    {xs : List Value} (hall : ∀ (j : Nat) x, xs[j]? = some x → Away h x w) :
    xs.mapM (f (h.set w o)) = xs.mapM (f h) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.mapM_cons, LocalDec.local_set h w o y (hall 0 y rfl)]
    rw [ih (fun j x hj => hall (j + 1) x (by simpa using hj))]

end SpecLean.Validation.Local

open SpecLean.Validation.Local SpecLean.Validation.Decode in
/-- The `LocalDec` instance of a container decoder: its object, then each field. -/
macro "rd_local" d:ident : tactic => `(tactic| (
  refine ⟨fun h w o v hp => ?_⟩
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
