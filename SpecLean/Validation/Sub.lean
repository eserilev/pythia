import SpecLean.Paths
import SpecLean.Compose

/-!
# The write condition at a call

A caller passes some of its arguments to a callee. Each `ref` argument of the callee is a `ref`
argument of the caller, at a position `σ k`. Then the paths of the callee are paths of the
caller, and `WTree` and `ArgsWF` carry over to the callee, for a part of the caller's footprint.
-/

namespace SpecLean.Encode

open SpecLean

deriving instance DecidableEq for PStep
deriving instance DecidableEq for FPat

/-- Each `ref` argument of `vs'` is the argument `σ k` of `vs`. -/
def SubArgs (vs' vs : List Value) (σ : Nat → Nat) : Prop :=
  ∀ k a, vs'[k]? = some (.ref a) → vs[σ k]? = some (.ref a)

/-- A path of the callee is a path of the caller. -/
theorem at?_sub {h : Heap} {vs' vs : List Value} {σ : Nat → Nat} (hs : SubArgs vs' vs σ)
    {k : Nat} {q : List Nat} {b : Nat} (e : at? h vs' k q = some (.ref b)) :
    at? h vs (σ k) q = some (.ref b) := by
  unfold at? at e ⊢
  cases hk : vs'[k]? with
  | none => rw [hk] at e; cases e
  | some v =>
    rw [hk] at e
    simp only [Option.bind_some] at e
    by_cases hv : ∃ a, v = .ref a
    · obtain ⟨a, rfl⟩ := hv
      rw [hs k a hk]
      exact e
    · cases q with
      | nil =>
        simp [follow] at e
        exact absurd ⟨b, e⟩ hv
      | cons i q =>
        rw [follow_nonref (fun c hc => hv ⟨c, hc⟩)] at e
        cases e

theorem rootTy_sub {h : Heap} {vs' vs : List Value} {σ : Nat → Nat} (hs : SubArgs vs' vs σ)
    {k : Nat} {ty : Name} (hr : RootTy h vs' k ty) : RootTy h vs (σ k) ty := by
  obtain ⟨a, fs, hk, ho⟩ := hr
  exact ⟨a, fs, hs k a hk, ho⟩

/-- `WTree` of the caller gives `WTree` of the callee over a part of the footprint. `σ` must be
one to one on the `ref` arguments of the callee. -/
theorem WTree_sub {h : Heap} {vs' vs : List Value} {fp' fp : Footprint} {σ : Nat → Nat}
    (hw : WTree h vs fp) (hs : SubArgs vs' vs σ) (hfp : ∀ p ∈ fp', p ∈ fp)
    (hinj : ∀ k k' a a', vs'[k]? = some (.ref a) → vs'[k']? = some (.ref a') → σ k = σ k' →
      k = k') :
    WTree h vs' fp' := by
  intro k pat hpat hty q hq a ha k' q' ha'
  obtain ⟨hkk, hqq⟩ := hw (σ k) pat (hfp pat hpat) (rootTy_sub hs hty) q hq a (at?_sub hs ha)
    (σ k') q' (at?_sub hs ha')
  refine ⟨?_, hqq⟩
  -- Both paths start at a `ref` argument.
  have refOf : ∀ {j : Nat} {p : List Nat}, at? h vs' j p = some (.ref a) →
      ∃ c, vs'[j]? = some (.ref c) := by
    intro j p e
    unfold at? at e
    cases hj : vs'[j]? with
    | none => rw [hj] at e; cases e
    | some v =>
      rw [hj] at e
      simp only [Option.bind_some] at e
      by_cases hv : ∃ c, v = .ref c
      · obtain ⟨c, rfl⟩ := hv; exact ⟨c, rfl⟩
      · cases p with
        | nil => simp [follow] at e; exact absurd ⟨a, e⟩ hv
        | cons i p => rw [follow_nonref (fun c hc => hv ⟨c, hc⟩)] at e; cases e
  obtain ⟨c, hc⟩ := refOf ha
  obtain ⟨c', hc'⟩ := refOf ha'
  exact (hinj k k' c c' hc hc' hkk.symm).symm

theorem ArgsWF_sub {h : Heap} {vs' vs : List Value} {σ : Nat → Nat} (haw : ArgsWF h vs)
    (hs : SubArgs vs' vs σ) : ArgsWF h vs' :=
  fun k q a e => haw (σ k) q a (at?_sub hs e)

/-- A write that keeps the shape of the object keeps `ArgsWF`. -/
theorem ArgsWF_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') {vs : List Value} (haw : ArgsWF h vs) : ArgsWF (h.set a o') vs := by
  intro k q b e
  have e0 := (at?_skel ho hs vs k q b).mp e
  simp only [Heap.set_objs]
  split
  · simp
  · exact haw k q b e0

theorem AtFp_mono_fp {h : Heap} {vs : List Value} {fp fp' : Footprint} {a : Nat}
    (hsub : ∀ p ∈ fp', p ∈ fp) (ha : AtFp h vs fp' a) : AtFp h vs fp a := by
  obtain ⟨k, pat, q, hp, hty, hm, e⟩ := ha
  exact ⟨k, pat, q, hsub pat hp, hty, hm, e⟩

/-- A frame over a part of the footprint is a frame over all of it. -/
theorem Frame_mono_fp {h h' : Heap} {vs : List Value} {fp fp' : Footprint}
    (hf : Frame h h' vs fp') (hsub : ∀ p ∈ fp', p ∈ fp) : Frame h h' vs fp :=
  fun a hn ha => hf a hn (fun h' => ha (AtFp_mono_fp hsub h'))

/-- A write that keeps the shape of the object keeps the footprint paths. -/
theorem AtFp_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') {vs : List Value} {fp : Footprint} {b : Nat} :
    AtFp (h.set a o') vs fp b → AtFp h vs fp b := by
  rintro ⟨k, pat, q, hp, hty, hm, e⟩
  exact ⟨k, pat, q, hp, (rootTy_skel ho hs vs k pat.ty).mp hty, hm, (at?_skel ho hs vs k q b).mp e⟩

end SpecLean.Encode
