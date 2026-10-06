import SpecLean.Validation.Comp
import SpecLean.Validation.Local

/-!
# New list objects (SPEC 9.2)

A comprehension result goes through `allocPyList`, and an SSZ list constructor through
`newList`. Both put one new object at `h.next`. The arguments reach no free address, so they
do not reach the new object: every path from them reads the same (`at?_alloc`), and the run has
the whole contract (`alloc_contract`). The new list decodes to the readable items when its items
reach only objects of the old heap (`decListV_alloc`, `decListT_alloc`).
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Rd SpecLean.Encode SpecLean.Validation.Local SpecLean.Validation.Where

/-- From a value that reaches only objects of the heap, every path reads the same after an
allocation. -/
theorem follow_alloc {h : Heap} {o : HeapObj} (hwf : HeapWF h) :
    ∀ (q : List Nat) (v : Value), (∀ p c, follow h v p = some (.ref c) → h.objs c ≠ none) →
      follow (h.alloc o).2 v q = follow h v q
  | [], _, _ => rfl
  | i :: p, v, hv => by
    cases v with
    | ref a =>
      have ha : h.objs a ≠ none := hv [] a rfl
      have hne : a ≠ h.next := fun e => ha (hwf a (by omega))
      simp only [follow, objs_alloc_ne hne]
      split
      · rename_i fs ho
        cases hx : fs[i]? with
        | none => rfl
        | some x =>
          simp only [Option.bind_some]
          exact follow_alloc hwf p x fun p' c e => hv (i :: p') c (by simp [follow, ho, hx, e])
      · rename_i k e l xs ho
        cases hx : xs[i]? with
        | none => rfl
        | some x =>
          simp only [Option.bind_some]
          exact follow_alloc hwf p x fun p' c e' => hv (i :: p') c (by simp [follow, ho, hx, e'])
      · rfl
    | _ => rfl

/-- An allocation changes no path from the arguments. -/
theorem at?_alloc {h : Heap} {vs : List Value} {o : HeapObj} (hwf : HeapWF h) (haw : ArgsWF h vs)
    (k : Nat) (q : List Nat) : at? (h.alloc o).2 vs k q = at? h vs k q := by
  unfold at?
  cases hk : vs[k]? with
  | none => rfl
  | some v =>
    simp only [Option.bind_some]
    exact follow_alloc hwf q v fun p c e => haw k p c (by simp [at?, hk, e])

/-- An allocation has the whole contract: frame, fresh address, no new paths, `FreshOnce` and
the roots kept. -/
theorem alloc_contract (gfp fpf : Footprint) {h : Heap} {vs : List Value} (o : HeapObj)
    (hwf : HeapWF h) (haw : ArgsWF h vs) : CContract gfp fpf vs h (h.alloc o).2 := by
  have hat := at?_alloc (o := o) hwf haw
  refine ⟨⟨frame_alloc (Frame_refl _ _ _) hwf (Fresh_refl _), fresh_alloc (Fresh_refl _),
    noNewPaths_of_reach fun k q b e => .inl (by rw [← hat]; exact e), ?_⟩, ?_⟩
  · rintro k ty ⟨a, fs, hk, ho⟩
    have e : at? h vs k [] = some (.ref a) := by simp [at?, hk, follow]
    have hne : a ≠ h.next := fun ea => haw k [] a e (hwf a (by omega))
    rw [objs_alloc_ne hne] at ho
    exact ⟨a, fs, hk, ho⟩
  · intro k q k' q' b hb e _
    rw [hat] at e
    exact absurd (hwf b hb) (haw k q b e)

/-- `allocPyList` gives a reference to the new object. -/
theorem allocPyList_eq (h : Heap) (vals : List Value) :
    allocPyList h vals = (.ref h.next, (h.alloc (.list .pyList .any none vals)).2) := rfl

/-- Items that reach only objects of the heap decode the same after an allocation. -/
theorem mapM_alloc {α : Type} {f : Dec α} [LocalDec f] {h : Heap} {o : HeapObj}
    {vals : List Value} {ys : List α} (hwf : HeapWF h) (hm : vals.mapM (f h) = some ys)
    (hold : ∀ (j : Nat) x, vals[j]? = some x → ∀ q c, follow h x q = some (.ref c) → h.objs c ≠ none) :
    vals.mapM (f (h.alloc o).2) = some ys :=
  mapM_same_of hm fun j x hx q c e =>
    objs_alloc_ne fun ec => hold j x hx q c e (hwf c (by omega))

/-- The new Python list decodes to the readable items. -/
theorem decListV_alloc {α : Type} {f : Dec α} [LocalDec f] {h : Heap} {vals : List Value}
    {ys : List α} (hwf : HeapWF h) (hm : vals.mapM (f h) = some ys)
    (hold : ∀ (j : Nat) x, vals[j]? = some x → ∀ q c, follow h x q = some (.ref c) → h.objs c ≠ none) :
    decListV f (allocPyList h vals).2 (allocPyList h vals).1 = some ys := by
  simp only [allocPyList_eq, decListV, objs_alloc_self]
  exact mapM_alloc hwf hm hold

/-- A new SSZ list of type `.list k e l` decodes with the typed decoder. -/
theorem decListT_alloc {α : Type} {f : Dec α} [LocalDec f] {h : Heap} {k : ListKind}
    {e : SszTy} {l : Option Nat} {vals : List Value} {ys : List α} (hwf : HeapWF h)
    (hm : vals.mapM (f h) = some ys)
    (hold : ∀ (j : Nat) x, vals[j]? = some x → ∀ q c, follow h x q = some (.ref c) → h.objs c ≠ none) :
    decListT k e l f (h.alloc (.list k e l vals)).2 (.ref h.next) = some ys := by
  simp only [decListT, objs_alloc_self, and_self, ↓reduceIte]
  exact mapM_alloc hwf hm hold

/-- A value that is not a reference reaches no object. -/
theorem hold_noRef {h : Heap} {vals : List Value} (hn : ∀ x ∈ vals, NoRef x) :
    ∀ (j : Nat) x, vals[j]? = some x → ∀ q c, follow h x q = some (.ref c) → h.objs c ≠ none := by
  intro j x hx q c e
  have hxm : x ∈ vals := List.mem_of_getElem? hx
  cases q with
  | nil => simp [follow] at e; exact absurd e (hn x hxm c)
  | cons i p =>
    cases x with
    | ref b => exact absurd rfl (hn _ hxm b)
    | _ => simp [follow] at e

/-! ## SSZ list constructors -/

/-- `newList` on items that the coercion keeps: a new list at `h.next`. -/
theorem newList_keep (env : Env) (d : Nat) (h : Heap) (k : ListKind) (e : SszTy)
    (l : Option Nat) (vals : List Value) (hl : Ssz.checkLength k l vals.length = .ok ())
    (hc : (match k, e with
      | .list, .uint (.width 8) => (·, h) <$> vals.mapM coerceByte
      | _, _ => Ssz.coerceAll env d h e vals) = .ok (vals, h)) :
    Ssz.newList env d h k e l vals = .ok (.ref h.next, (h.alloc (.list k e l vals)).2) := by
  rw [Ssz.newList]
  simp only [hl, Except.bind_ok']
  split <;> split at hc <;> simp_all <;> rfl

/-- The coercion keeps uints of the exact element class. -/
theorem coerceAll_uint_self (env : Env) (d : Nat) (h : Heap) (t : UintTy) :
    ∀ ns : List Nat, Ssz.coerceAll env (d + 1) h (.uint t) (ns.map (Value.uint t)) =
      .ok (ns.map (Value.uint t), h)
  | [] => by simp only [List.map_nil]; rw [Ssz.coerceAll]
  | n :: ns => by
    rw [List.map_cons, Ssz.coerceAll, coerceH_plain env false d h t _ (fun _ e => by cases e)]
    simp only [coerceElem, ↓reduceIte, Except.bind_ok', Except.pure_ok', Except.map_ok', if_true,
      Bool.false_eq_true]
    rw [coerceAll_uint_self env d h t ns]
    rfl

end SpecLean.Validation
