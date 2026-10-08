import SpecLean.Paths
import SpecLean.Compose

/-!
# Paths to the objects that a proof reads and writes

A decode hypothesis says where each object of an argument sits: the root, then one field or
item at a time. `at_root`, `at_field` and `at_item` build `at?` facts along that way. Under
`WTree`, an object at a footprint path has no second path (`wtree_ne`): two objects at
different paths are different objects.
-/

namespace SpecLean.Validation.Where

open SpecLean SpecLean.Encode

theorem at_root {h : Heap} {vs : List Value} {k : Nat} {v : Value} (hv : vs[k]? = some v) :
    at? h vs k [] = some v := by
  simp [at?, hv, follow]

theorem follow_append {h : Heap} :
    ∀ (v : Value) (q r : List Nat), follow h v (q ++ r) = (follow h v q).bind (follow h · r)
  | v, [], r => by simp [follow]
  | .ref a, i :: q, r => by
    simp only [List.cons_append, follow]
    split
    · rename_i fs _
      cases fs[i]? with
      | none => rfl
      | some x => exact follow_append x q r
    · rename_i xs _
      cases xs[i]? with
      | none => rfl
      | some x => exact follow_append x q r
    · rfl
  | .int _, _ :: _, _ | .bool _, _ :: _, _ | .lib _, _ :: _, _ | .str _, _ :: _, _
  | .none, _ :: _, _ | .bytes _ _, _ :: _, _ | .tuple _, _ :: _, _
  | .frozenDict _, _ :: _, _ | .enumView _, _ :: _, _ | .zipView _ _, _ :: _, _
  | .glob _, _ :: _, _ | .member _ _, _ :: _, _ => rfl

theorem at_field {h : Heap} {vs : List Value} {k : Nat} {q : List Nat} {p : Nat} {ty : Name}
    {fs : List Value} {i : Nat} {v : Value} (hp : at? h vs k q = some (.ref p))
    (ho : h.objs p = some (.container ty fs)) (hi : fs[i]? = some v) :
    at? h vs k (q ++ [i]) = some v := by
  simp only [at?] at hp ⊢
  cases hk : vs[k]? with
  | none => simp [hk] at hp
  | some w =>
    simp only [hk, Option.bind_some] at hp ⊢
    rw [follow_append, hp]
    simp [follow, ho, hi]

theorem at_item {h : Heap} {vs : List Value} {k : Nat} {q : List Nat} {p : Nat} {kd : ListKind}
    {e : SszTy} {l : Option Nat} {xs : List Value} {j : Nat} {v : Value}
    (hp : at? h vs k q = some (.ref p)) (ho : h.objs p = some (.list kd e l xs))
    (hj : xs[j]? = some v) : at? h vs k (q ++ [j]) = some v := by
  simp only [at?] at hp ⊢
  cases hk : vs[k]? with
  | none => simp [hk] at hp
  | some w =>
    simp only [hk, Option.bind_some] at hp ⊢
    rw [follow_append, hp]
    simp [follow, ho, hj]

theorem at_follow {h : Heap} {vs : List Value} {k : Nat} {q r : List Nat} {x v : Value}
    (hx : at? h vs k q = some x) (hf : follow h x r = some v) : at? h vs k (q ++ r) = some v := by
  simp only [at?] at hx ⊢
  cases hk : vs[k]? with
  | none => simp [hk] at hx
  | some w =>
    simp only [hk, Option.bind_some] at hx ⊢
    rw [follow_append, hx]
    simpa using hf

/-- Under `WTree`, an object at a footprint path has no second path. -/
theorem wtree_ne {h : Heap} {vs : List Value} {fp : Footprint} (hw : WTree h vs fp)
    {k : Nat} {pat : FPat} (hk : pat ∈ fp) (hty : RootTy h vs k pat.ty) {q : List Nat}
    (hq : Matches pat.steps q)
    {a : Nat} (ha : at? h vs k q = some (.ref a)) {k' : Nat} {q' : List Nat} {a' : Nat}
    (ha' : at? h vs k' q' = some (.ref a')) (hne : ¬ (k' = k ∧ q' = q)) : a' ≠ a := by
  intro e; subst e; exact hne (hw k pat hk hty q hq a' ha k' q' ha')

theorem rootTy_of {h : Heap} {vs : List Value} {k : Nat} {a : Nat} {ty : Name} {fs : List Value}
    (hv : vs[k]? = some (.ref a)) (ho : h.objs a = some (.container ty fs)) :
    RootTy h vs k ty := rootTy_container hv ho

theorem atFp_of {h : Heap} {vs : List Value} {fp : Footprint} {k : Nat} {pat : FPat}
    (hk : pat ∈ fp) (hty : RootTy h vs k pat.ty) {q : List Nat} (hq : Matches pat.steps q)
    {a : Nat} (ha : at? h vs k q = some (.ref a)) : AtFp h vs fp a :=
  ⟨k, pat, q, hk, hty, hq, ha⟩

theorem normIndex_lt {n : Nat} {i : Int} {k : Nat} (e : normIndex n i = some k) : k < n := by
  unfold normIndex at e
  split at e
  · split at e
    · cases e; omega
    · cases e
  · split at e
    · cases e; omega
    · cases e

theorem objs_set_ne {h : Heap} {a b : Nat} {o : HeapObj} (hne : b ≠ a) :
    (h.set a o).objs b = h.objs b := by
  simp [hne]

theorem objs_set_self {h : Heap} {a : Nat} {o : HeapObj} : (h.set a o).objs a = some o := by
  simp

/-! ## New objects -/

theorem alloc_fst (h : Heap) (o : HeapObj) : (h.alloc o).1 = h.next := rfl

theorem alloc_next (h : Heap) (o : HeapObj) : (h.alloc o).2.next = h.next + 1 := rfl

theorem set_next (h : Heap) (a : Nat) (o : HeapObj) : (h.set a o).next = h.next := rfl

theorem objs_alloc_ne {h : Heap} {o : HeapObj} {b : Nat} (hb : b ≠ h.next) :
    (h.alloc o).2.objs b = h.objs b := by
  simp [Heap.alloc, hb]

theorem objs_alloc_self {h : Heap} {o : HeapObj} : (h.alloc o).2.objs h.next = some o := by
  simp [Heap.alloc]

theorem objs_alloc_at {h : Heap} {o : HeapObj} {b : Nat} (hb : b = h.next) :
    (h.alloc o).2.objs b = some o := by
  subst hb; exact objs_alloc_self

/-- An argument object is below `next`. -/
theorem ne_next_of_at {h : Heap} {vs : List Value} (hwf : HeapWF h) (haw : ArgsWF h vs)
    {k : Nat} {q : List Nat} {b : Nat} (e : at? h vs k q = some (.ref b)) (c : Nat) :
    b ≠ h.next + c := by
  have := reached_old hwf haw e; omega

/-! ## The frame of a run of writes -/

theorem frame_set {h h1 : Heap} {vs : List Value} {fp : Footprint} {a : Nat} {o : HeapObj}
    (hf : Frame h h1 vs fp) (hat : AtFp h vs fp a) : Frame h (h1.set a o) vs fp := by
  intro b hn hb
  have : b ≠ a := fun e => by subst e; exact hb hat
  simp [this, hf b hn hb]

theorem frame_alloc {h h1 : Heap} {vs : List Value} {fp : Footprint} {o : HeapObj}
    (hf : Frame h h1 vs fp) (hwf : HeapWF h) (hfr : Fresh h h1) :
    Frame h (h1.alloc o).2 vs fp := by
  intro b hn hb
  have hlt : b < h.next := Nat.lt_of_not_le fun hle => hn (hwf b hle)
  have : b ≠ h1.next := by have := hfr.1; omega
  rw [objs_alloc_ne this, hf b hn hb]

theorem frame_set_fresh {h h1 : Heap} {vs : List Value} {fp : Footprint} {a : Nat}
    {o : HeapObj} (hf : Frame h h1 vs fp) (hwf : HeapWF h) (ha : h.next ≤ a) :
    Frame h (h1.set a o) vs fp := by
  intro b hn hb
  have hlt : b < h.next := Nat.lt_of_not_le fun hle => hn (hwf b hle)
  have : b ≠ a := by omega
  simp [this, hf b hn hb]

theorem heapWF_of_fresh {h h1 : Heap} (hwf : HeapWF h) (hf : Fresh h h1) : HeapWF h1 := hf.2 hwf

theorem fresh_alloc {h h1 : Heap} {o : HeapObj} (hf : Fresh h h1) : Fresh h (h1.alloc o).2 := by
  refine ⟨by simp [alloc_next]; have := hf.1; omega, fun hwf => ?_⟩
  have hw1 := hf.2 hwf
  intro b hb
  simp only [alloc_next] at hb
  rw [objs_alloc_ne (by omega)]
  exact hw1 b (by omega)

theorem fresh_set {h h1 : Heap} {a : Nat} {o o0 : HeapObj} (hf : Fresh h h1)
    (ho : h1.objs a = some o0) : Fresh h (h1.set a o) :=
  Fresh_trans hf (Fresh_set ho)

theorem reach_set {h h1 : Heap} {vs : List Value} {a : Nat} {o o0 : HeapObj}
    (hr : Reach h h1 vs) (hf : Fresh h h1) (ho : h1.objs a = some o0) (hs : SameSkel o0 o) :
    Reach h (h1.set a o) vs :=
  Reach_trans hf hr (Reach_skel ho hs vs)

/-- A value that holds no reference. -/
def NoRef (v : Value) : Prop := ∀ b, v ≠ .ref b

theorem refEq_noRef {x y : Value} (hx : NoRef x) (hy : NoRef y) : RefEq x y :=
  fun b => ⟨fun e => absurd e (hx b), fun e => absurd e (hy b)⟩

/-- A write of a value with no reference over an item with no reference keeps the shape. -/
theorem sameSkel_list_set {k : ListKind} {e : SszTy} {l : Option Nat} {xs : List Value} {i : Nat}
    {v : Value} (hxs : ∀ x ∈ xs, NoRef x) (hv : NoRef v) :
    SameSkel (.list k e l xs) (.list k e l (xs.set i v)) := by
  refine ⟨rfl, rfl, rfl, by simp, fun j x y hx hy => ?_⟩
  have hx' : NoRef x := hxs x (List.mem_of_getElem? hx)
  rw [List.getElem?_set] at hy
  split at hy
  · split at hy
    · cases hy; exact refEq_noRef hx' hv
    · cases hy
  · exact refEq_noRef hx' (hxs y (List.mem_of_getElem? (by simpa using hy)))

theorem sameSkel_container_set {ty : Name} {fs : List Value} {i : Nat} {v : Value}
    (hi : ∀ x, fs[i]? = some x → NoRef x) (hv : NoRef v) :
    SameSkel (.container ty fs) (.container ty (fs.set i v)) := by
  refine ⟨rfl, by simp, fun j x y hx hy => ?_⟩
  rw [List.getElem?_set] at hy
  split at hy
  · rename_i hj
    split at hy
    · cases hy; subst hj; exact refEq_noRef (hi x hx) hv
    · cases hy
  · rw [hy] at hx; cases hx; exact RefEq.refl _

theorem noRef_uint (t : UintTy) (n : Nat) : NoRef (.uint t n) := fun _ e => by cases e
theorem noRef_bytes (c : Name) (b : List UInt8) : NoRef (.bytes c b) := fun _ e => by cases e
theorem noRef_boolean (b : Bool) : NoRef (.boolean b) := fun _ e => by cases e
theorem noRef_map_uint {α : Type} (t : UintTy) (f : α → Nat) (ys : List α) :
    ∀ x ∈ ys.map (fun y => Value.uint t (f y)), NoRef x := by
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact noRef_uint _ _
theorem noRef_map_bytes {α : Type} (c : Name) (f : α → List UInt8) (ys : List α) :
    ∀ x ∈ ys.map (fun y => Value.bytes c (f y)), NoRef x := by
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact noRef_bytes _ _
theorem noRef_map_boolean {α : Type} (f : α → Bool) (ys : List α) :
    ∀ x ∈ ys.map (fun y => Value.boolean (f y)), NoRef x := by
  intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact noRef_boolean _

end SpecLean.Validation.Where
