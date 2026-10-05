import SpecLean.Validation.Where

/-!
# Writes that only add new objects keep `Reach`

`Grows h h' n`: every old object of `h'` (below `n`) holds, at each position, the reference of
`h` there or a new reference (at or above `n`), and every new object holds only new references.
A path of `h'` then reaches an old object only where `h` reached it. A write of a value, a new
object, or an append of a new object grows the heap. A list slice does not: it moves old items.
-/

namespace SpecLean.Validation.Grow

open SpecLean SpecLean.Encode

/-- The item at position `i` of an object that `follow` reads. -/
def item : HeapObj → Nat → Option Value
  | .container _ fs, i => fs[i]?
  | .list _ _ _ xs, i => xs[i]?
  | _, _ => none

/-- Each reference of `o'` is the reference of `o` at its position, or a new one. -/
def ObjGrows (n : Nat) (o o' : HeapObj) : Prop :=
  ∀ i b, item o' i = some (.ref b) → item o i = some (.ref b) ∨ n ≤ b

/-- A new object holds only new references. -/
def NewObj (n : Nat) (o : HeapObj) : Prop := ∀ i b, item o i = some (.ref b) → n ≤ b

def Grows (h h' : Heap) (n : Nat) : Prop :=
  ∀ a o', h'.objs a = some o' →
    (a < n → ∃ o, h.objs a = some o ∧ ObjGrows n o o') ∧ (n ≤ a → NewObj n o')

theorem follow_cons (h : Heap) (a : Nat) (i : Nat) (q : List Nat) :
    follow h (.ref a) (i :: q) =
      (match h.objs a with
       | some o => (item o i).bind (follow h · q)
       | none => none) := by
  simp only [follow]
  cases h.objs a with
  | none => rfl
  | some o => cases o <;> rfl

theorem follow_nonref' {h : Heap} {v : Value} (hv : ∀ b, v ≠ .ref b) {q : List Nat} {b : Nat}
    (e : follow h v q = some (.ref b)) : False := by
  cases q with
  | nil => simp [follow] at e; exact hv b e
  | cons i q => rw [follow_nonref hv] at e; cases e

/-- From a new object, every path reaches new objects. -/
theorem follow_new {h h' : Heap} {n : Nat} (hg : Grows h h' n) :
    ∀ (q : List Nat) (a b : Nat), n ≤ a → follow h' (.ref a) q = some (.ref b) → n ≤ b
  | [], a, b, ha, e => by simp [follow] at e; omega
  | i :: q, a, b, ha, e => by
    rw [follow_cons] at e
    cases ho : h'.objs a with
    | none => rw [ho] at e; cases e
    | some o' =>
      rw [ho] at e
      simp only at e
      cases hi : item o' i with
      | none => rw [hi] at e; cases e
      | some x =>
        rw [hi] at e
        simp only [Option.bind_some] at e
        by_cases hx : ∃ c, x = .ref c
        · obtain ⟨c, rfl⟩ := hx
          exact follow_new hg q c b ((hg a o' ho).2 ha i c hi) e
        · exact (follow_nonref' (fun c hc => hx ⟨c, hc⟩) e).elim

/-- A path of `h'` from an old object reaches what `h` reaches there, or a new object. -/
theorem follow_grows {h h' : Heap} {n : Nat} (hg : Grows h h' n) :
    ∀ (q : List Nat) (a b : Nat), a < n → follow h' (.ref a) q = some (.ref b) →
      follow h (.ref a) q = some (.ref b) ∨ n ≤ b
  | [], a, b, _, e => by simp [follow] at e ⊢; exact .inl e
  | i :: q, a, b, ha, e => by
    rw [follow_cons] at e
    cases ho : h'.objs a with
    | none => rw [ho] at e; cases e
    | some o' =>
      rw [ho] at e
      simp only at e
      obtain ⟨o, hoh, hgo⟩ := (hg a o' ho).1 ha
      cases hi : item o' i with
      | none => rw [hi] at e; cases e
      | some x =>
        rw [hi] at e
        simp only [Option.bind_some] at e
        by_cases hx : ∃ c, x = .ref c
        · obtain ⟨c, rfl⟩ := hx
          rcases hgo i c hi with hs | hn
          · by_cases hc : c < n
            · rcases follow_grows hg q c b hc e with e2 | e2
              · left
                rw [follow_cons, hoh]
                simp [hs, e2]
              · exact .inr e2
            · exact .inr (follow_new hg q c b (by omega) e)
          · exact .inr (follow_new hg q c b hn e)
        · exact (follow_nonref' (fun c hc => hx ⟨c, hc⟩) e).elim

/-- A grown heap keeps `Reach`. -/
theorem reach_of_grows {h h' : Heap} {vs : List Value} (hwf : HeapWF h) (haw : ArgsWF h vs)
    (hg : Grows h h' h.next) : Reach h h' vs := by
  intro k q b e
  unfold at? at e ⊢
  cases hk : vs[k]? with
  | none => rw [hk] at e; cases e
  | some v =>
    rw [hk] at e
    simp only [Option.bind_some] at e ⊢
    by_cases hv : ∃ a, v = .ref a
    · obtain ⟨a, rfl⟩ := hv
      have ha : a < h.next := by
        apply Nat.lt_of_not_le; intro hle
        exact haw k [] a (by simp [at?, hk, follow]) (hwf a hle)
      exact follow_grows hg q a b ha e
    · exact (follow_nonref' (fun c hc => hv ⟨c, hc⟩) e).elim

/-! ## Each write grows the heap -/

theorem grows_refl (h : Heap) (n : Nat) (hwf : HeapWF h) (hn : h.next ≤ n) : Grows h h n := by
  intro a o' ho
  refine ⟨fun _ => ⟨o', ho, fun i b hi => .inl hi⟩, fun ha => ?_⟩
  rw [hwf a (by omega)] at ho; cases ho

/-- A write of an object that grows the old one. -/
theorem grows_set {h h1 : Heap} {n a : Nat} {o o' : HeapObj} (hg : Grows h h1 n)
    (ho : h1.objs a = some o) (hgo : ObjGrows n o o') (hnew : n ≤ a → NewObj n o') :
    Grows h (h1.set a o') n := by
  intro b ob hb
  by_cases hab : b = a
  · subst hab
    simp only [Heap.set_objs, if_true, Option.some.injEq] at hb
    subst hb
    refine ⟨fun hlt => ?_, hnew⟩
    obtain ⟨o0, h0, hg0⟩ := (hg b o ho).1 hlt
    refine ⟨o0, h0, fun i c hi => ?_⟩
    rcases hgo i c hi with e | e
    · exact hg0 i c e
    · exact .inr e
  · simp only [Heap.set_objs, if_neg hab] at hb
    exact hg b ob hb

/-- A new object with only new references. -/
theorem grows_alloc {h h1 : Heap} {n : Nat} {o : HeapObj} (hg : Grows h h1 n) (hn : n ≤ h1.next)
    (hwf : HeapWF h1) (hnew : NewObj n o) : Grows h (h1.alloc o).2 n := by
  intro b ob hb
  by_cases hbn : b = h1.next
  · subst hbn
    rw [Where.objs_alloc_self] at hb; cases hb
    exact ⟨fun hlt => by omega, fun _ => hnew⟩
  · rw [Where.objs_alloc_ne hbn] at hb
    exact hg b ob hb

/-- A value is not a reference, or a new one. -/
def NewVal (n : Nat) (v : Value) : Prop := ∀ b, v = .ref b → n ≤ b

theorem newVal_of_ge {n b : Nat} (h : n ≤ b) : NewVal n (.ref b) := fun c e => by cases e; exact h
theorem newVal_uint (n : Nat) (t : UintTy) (m : Nat) : NewVal n (.uint t m) := fun _ e => by cases e
theorem newVal_bytes (n : Nat) (c : Name) (b : List UInt8) : NewVal n (.bytes c b) :=
  fun _ e => by cases e
theorem newVal_boolean (n : Nat) (b : Bool) : NewVal n (.boolean b) := fun _ e => by cases e

theorem item_set_of {xs : List Value} {i j : Nat} {v x : Value} (hx : (xs.set i v)[j]? = some x) :
    xs[j]? = some x ∨ x = v := by
  rw [List.getElem?_set] at hx
  split at hx
  · split at hx
    · cases hx; exact .inr rfl
    · cases hx
  · exact .inl hx

theorem objGrows_list_set {n : Nat} {k : ListKind} {e : SszTy} {l : Option Nat} {xs : List Value}
    {i : Nat} {v : Value} (hv : NewVal n v) :
    ObjGrows n (.list k e l xs) (.list k e l (xs.set i v)) := by
  intro j b hj
  simp only [item] at hj ⊢
  rcases item_set_of hj with h1 | h1
  · exact .inl h1
  · exact .inr (hv b h1.symm)

theorem objGrows_container_set {n : Nat} {ty : Name} {fs : List Value} {i : Nat} {v : Value}
    (hv : NewVal n v) : ObjGrows n (.container ty fs) (.container ty (fs.set i v)) := by
  intro j b hj
  simp only [item] at hj ⊢
  rcases item_set_of hj with h1 | h1
  · exact .inl h1
  · exact .inr (hv b h1.symm)

theorem objGrows_list_append {n : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs ys : List Value} (hys : ∀ y ∈ ys, NewVal n y) :
    ObjGrows n (.list k e l xs) (.list k e l (xs ++ ys)) := by
  intro j b hj
  simp only [item] at hj ⊢
  rw [List.getElem?_append] at hj
  split at hj
  · exact .inl (by rw [List.getElem?_eq_getElem (by omega)] at hj ⊢; exact hj)
  · exact .inr (hys _ (List.mem_of_getElem? hj) b rfl)

theorem newObj_container {n : Nat} {ty : Name} {fs : List Value} (hfs : ∀ x ∈ fs, NewVal n x) :
    NewObj n (.container ty fs) := by
  intro i b hi
  simp only [item] at hi
  exact hfs _ (List.mem_of_getElem? hi) b rfl

theorem newObj_list {n : Nat} {k : ListKind} {e : SszTy} {l : Option Nat} {xs : List Value}
    (hxs : ∀ x ∈ xs, NewVal n x) : NewObj n (.list k e l xs) := by
  intro i b hi
  simp only [item] at hi
  exact hxs _ (List.mem_of_getElem? hi) b rfl

theorem newVals_map_uint {α : Type} (n : Nat) (t : UintTy) (f : α → Nat) (ys : List α) :
    ∀ x ∈ ys.map (fun y => Value.uint t (f y)), NewVal n x := by
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact newVal_uint _ _ _

theorem newVals_map_bytes {α : Type} (n : Nat) (c : Name) (f : α → List UInt8) (ys : List α) :
    ∀ x ∈ ys.map (fun y => Value.bytes c (f y)), NewVal n x := by
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact newVal_bytes _ _ _

theorem newVals_map_boolean {α : Type} (n : Nat) (f : α → Bool) (ys : List α) :
    ∀ x ∈ ys.map (fun y => Value.boolean (f y)), NewVal n x := by
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact newVal_boolean _ _

theorem newVals_nil (n : Nat) : ∀ y ∈ ([] : List Value), NewVal n y := by simp

theorem newVals_cons {n : Nat} {x : Value} {xs : List Value} (hx : NewVal n x)
    (hxs : ∀ y ∈ xs, NewVal n y) : ∀ y ∈ x :: xs, NewVal n y := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact hxs y hy

theorem newVals_append {n : Nat} {xs ys : List Value} (hxs : ∀ y ∈ xs, NewVal n y)
    (hys : ∀ y ∈ ys, NewVal n y) : ∀ y ∈ xs ++ ys, NewVal n y := by
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · exact hxs y hy
  · exact hys y hy

theorem old_not_new {h : Heap} {vs : List Value} (hwf : HeapWF h) (haw : ArgsWF h vs)
    {k : Nat} {q : List Nat} {a : Nat} (e : at? h vs k q = some (.ref a)) {P : Prop} :
    h.next ≤ a → P := fun hle => absurd (reached_old hwf haw e) (Nat.not_lt_of_le hle)

end SpecLean.Validation.Grow
