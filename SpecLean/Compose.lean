import SpecLean.Paths

/-!
# The composition lemma (SPEC 9.2, 9.4)

A function takes `WTree` over its own footprint, and promises `Reach` on its result, not
`WTree`. The lemma here gives `WTree` back over any footprint: a run that reaches no old object
by a new path, and that reaches each new object by one path, creates no sharing. So `WTree`
over `FP` at the entry of the state transition gives `WTree` over `FP` at its exit.
-/

namespace SpecLean.Encode

open SpecLean

/-- Each new object that the arguments reach is reached by one path. -/
def FreshOnce (h h' : Heap) (vs : List Value) : Prop :=
  ∀ k q k' q' b, h.next ≤ b → at? h' vs k q = some (.ref b) → at? h' vs k' q' = some (.ref b) →
    k' = k ∧ q' = q

/-- The root objects keep their container class. -/
def RootsKept (h h' : Heap) (vs : List Value) : Prop :=
  ∀ k ty, RootTy h' vs k ty → RootTy h vs k ty

/-- An object that the arguments reach in a well-formed heap is below `next`. -/
theorem reached_old {h : Heap} {vs : List Value} (hwf : HeapWF h) (haw : ArgsWF h vs)
    {k : Nat} {q : List Nat} {b : Nat} (e : at? h vs k q = some (.ref b)) : b < h.next := by
  apply Nat.lt_of_not_le
  intro hle
  exact haw k q b e (hwf b hle)

/-- The composition lemma. Old objects keep their paths (`Reach`), new objects have one path
each (`FreshOnce`), and the roots keep their class. Then `WTree` carries over, for any
footprint. -/
theorem wtree_compose {h h' : Heap} {vs : List Value} {fp : Footprint}
    (hw : WTree h vs fp) (hwf : HeapWF h) (haw : ArgsWF h vs)
    (hr : Reach h h' vs) (hf : FreshOnce h h' vs) (hk : RootsKept h h' vs) :
    WTree h' vs fp := by
  intro k pat hpat hty q hq a ha k' q' ha'
  rcases hr k q a ha with ho | hn
  · rcases hr k' q' a ha' with ho' | hn'
    · exact hw k pat hpat (hk k pat.ty hty) q hq a ho k' q' ho'
    · exact absurd hn' (Nat.not_le_of_lt (reached_old hwf haw ho))
  · exact hf k q k' q' a hn ha ha'

/-- `Reach` composes along a run whose heap only grows. -/
theorem Reach_trans {h1 h2 h3 : Heap} {vs : List Value} (f : Fresh h1 h2)
    (a : Reach h1 h2 vs) (b : Reach h2 h3 vs) : Reach h1 h3 vs := by
  intro k q c e
  rcases b k q c e with e2 | n2
  · exact a k q c e2
  · exact .inr (Nat.le_trans f.1 n2)

end SpecLean.Encode
