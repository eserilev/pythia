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

/-- The composition lemma. Old objects gain no path (`NoNewPaths`), new objects have one path
each (`FreshOnce`), and the roots keep their class. Then `WTree` carries over. -/
theorem wtree_compose {h h' : Heap} {vs : List Value} {fp : Footprint}
    (hw : WTree h vs fp) (hwf : HeapWF h) (haw : ArgsWF h vs)
    (hn : NoNewPaths h h' vs fp) (hf : FreshOnce h h' vs) (hk : RootsKept h h' vs) :
    WTree h' vs fp := by
  intro k pat hpat hty q hq a ha k' q' ha'
  by_cases hold : a < h.next
  · obtain ⟨φ, hφ⟩ := hn
    obtain ⟨e1, hpres, hinj⟩ := hφ k q a ha hold
    obtain ⟨e2, -, -⟩ := hφ k' q' a ha' hold
    have := hw k pat hpat (hk k pat.ty hty) (φ k q) (hpres pat hpat hq) a e1 k' (φ k' q') e2
    obtain ⟨hkk, hq'⟩ := this
    exact ⟨hkk, hinj k' q' ha' hkk (by subst hkk; exact hq')⟩
  · exact hf k q k' q' a (Nat.le_of_not_lt hold) ha ha'

/-- `NoNewPaths` composes along a run whose heap only grows. -/
theorem NoNewPaths_trans {h1 h2 h3 : Heap} {vs : List Value} {fp : Footprint} (f : Fresh h1 h2)
    (a : NoNewPaths h1 h2 vs fp) (b : NoNewPaths h2 h3 vs fp) : NoNewPaths h1 h3 vs fp := by
  obtain ⟨φ1, h1φ⟩ := a
  obtain ⟨φ2, h2φ⟩ := b
  refine ⟨fun k q => φ1 k (φ2 k q), fun k q c e hc => ?_⟩
  have hc2 : c < h2.next := Nat.lt_of_lt_of_le hc f.1
  obtain ⟨e2, p2, i2⟩ := h2φ k q c e hc2
  obtain ⟨e1, p1, i1⟩ := h1φ k _ c e2 hc
  refine ⟨e1, fun pat hp hm => p1 pat hp (p2 pat hp hm), fun k' q' e' hk heq => ?_⟩
  subst hk
  obtain ⟨e2', -, -⟩ := h2φ k' q' c e' hc2
  exact i2 k' q' e' rfl (i1 k' _ e2' rfl heq)

/-- Paths kept in place: no old object gains a path. -/
theorem noNewPaths_of_reach {h h' : Heap} {vs : List Value} {fp : Footprint}
    (hr : Reach h h' vs) : NoNewPaths h h' vs fp := by
  refine ⟨fun _ q => q, fun k q a e hlt => ?_⟩
  rcases hr k q a e with e0 | hn
  · exact ⟨e0, fun _ _ hm => hm, fun _ _ _ _ heq => heq⟩
  · exact absurd hlt (Nat.not_lt_of_le hn)

theorem NoNewPaths_refl (h : Heap) (vs : List Value) (fp : Footprint) : NoNewPaths h h vs fp :=
  noNewPaths_of_reach (Reach_refl h vs)

/-- `Reach` composes along a run whose heap only grows. -/
theorem Reach_trans {h1 h2 h3 : Heap} {vs : List Value} (f : Fresh h1 h2)
    (a : Reach h1 h2 vs) (b : Reach h2 h3 vs) : Reach h1 h3 vs := by
  intro k q c e
  rcases b k q c e with e2 | n2
  · exact a k q c e2
  · exact .inr (Nat.le_trans f.1 n2)

end SpecLean.Encode
