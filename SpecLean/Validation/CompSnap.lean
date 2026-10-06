import SpecLean.Validation.Comp

/-!
# Comprehensions over a snapshot (SPEC 9.3)

`range(...)`, a tuple, `sorted(...)` and a slice give a snapshot, not a live list: `iterSource`
gives `.seq (.snap xs)`. The items are the items of `xs`, so `comp_sim` needs no length invariant.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Encode

theorem iterItem_snap (h : Heap) (xs : List Value) (i : Nat) :
    iterItem h (.seq (.snap xs)) i = .ok xs[i]? := rfl

theorem iterSource_tuple (h : Heap) (xs : List Value) :
    iterSource h (.tuple xs) = .ok (.seq (.snap xs)) := rfl

/-- `range(n)` for a natural `n` is the tuple of `0, ..., n - 1`. -/
theorem range_nat (env : Env) (h : Heap) (n : Nat) :
    applyBuiltin env h .range [.int (n : Int)] [] =
      .ok (.tuple ((List.range n).map fun (i : Nat) => .int (i : Int)), h) := by
  simp [applyBuiltin, LibModel.builtin, Ssz.builtin, Ssz.toIndex_int]

/-- `comp_sim` over a snapshot `xs` with one item per readable item. -/
theorem comp_snap_sim {α β : Type} (env : Env) (t : Target) (ifs : List Expr) (elt : Expr)
    (xs : List Value) (Kf : Nat) (ys : List α) (hlen : xs.length = ys.length)
    (f : α → Except Fail (Option β)) (E : Value → β → Heap → Prop)
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (Q : Nat → Locals → Heap → Prop)
    (hstep : ∀ n i L h x y, Q i L h → ys[i]? = some y → xs[i]? = some x →
      ItemRel (CContract gfp fpf vs h) (Q (i + 1)) E (compItem env (n + Kf) L h t ifs elt x)
        (f y))
    (hE : ∀ v b h h', E v b h → CContract gfp fpf vs h h' → E v b h') :
    ∀ n i L h, Q i L h → CContract gfp fpf vs h0 h → ys.length - i ≤ n →
      CompOut (fun h' => CContract gfp fpf vs h0 h' ∧ (∀ v b, E v b h → E v b h') ∧
          ∃ j L', Q j L' h' ∧ ys.length ≤ j) E
        (compItems env (n + Kf + 1) L h t ifs [] elt none (.seq (.snap xs)) i)
        ((ys.drop i).filterMapM f) :=
  comp_sim env t ifs elt (.seq (.snap xs)) Kf ys f E hsub hwf Q
    (fun i _ _ _ hi => ⟨xs[i]'(by omega), by rw [iterItem_snap, List.getElem?_eq_getElem]⟩)
    (fun i _ _ _ hi => by rw [iterItem_snap, List.getElem?_eq_none_iff.mpr (by omega)])
    (fun n i L h x y hq hy hx => hstep n i L h x y hq hy (by rw [iterItem_snap] at hx; exact Except.ok.inj hx))
    hE

end SpecLean.Validation
