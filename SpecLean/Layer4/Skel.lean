import SpecLean.Layer4.Den
import SpecLean.Layer4.Inv

/-!
# Layer 4: runs that keep the shape of the heap

The fragment writes only flat values over flat values. So a run changes objects, but every
old object keeps its shape (`SameSkel`). New objects come only at free addresses (`Skel`).
Then every heap path to a reference reads the same, from a value that reaches only old objects
(`Below`), so a caller's places stay valid across a call. `Ext` is the run that changes no old
object: a read, or a call of a function that writes nothing.

`dec_graft`: after a call, the caller's tree of an argument is its old tree with the callee's
tree put in at the place of the call argument. It needs that every changed object that the
caller's argument reaches is below that place.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode SpecLean.Validation.Where

/-- No old object changes. New objects come at free addresses. -/
def Ext (h h' : Heap) : Prop :=
  h.next ≤ h'.next ∧ (HeapWF h → HeapWF h') ∧ ∀ a, a < h.next → h'.objs a = h.objs a

/-- Every reference that `v` reaches is below `next`. -/
abbrev Below (h : Heap) (v : Value) : Prop := ∀ q a, follow h v q = some (.ref a) → a < h.next

theorem follow_nonref_ref {h : Heap} {v : Value} (hv : ∀ b, v ≠ .ref b) {q : List Nat} {b : Nat}
    (e : follow h v q = some (.ref b)) : False := by
  cases q with
  | nil => simp [follow] at e; exact hv b e
  | cons i q => rw [follow_nonref hv] at e; cases e

theorem Ext_refl (h : Heap) : Ext h h := ⟨Nat.le_refl _, id, fun _ _ => rfl⟩

theorem Ext_trans {h1 h2 h3 : Heap} (a : Ext h1 h2) (b : Ext h2 h3) : Ext h1 h3 :=
  ⟨Nat.le_trans a.1 b.1, fun w => b.2.1 (a.2.1 w),
    fun x hx => (b.2.2 x (Nat.lt_of_lt_of_le hx a.1)).trans (a.2.2 x hx)⟩

theorem refEq_trans {x y z : Value} (a : RefEq x y) (b : RefEq y z) : RefEq x z :=
  fun c => (a c).trans (b c)

theorem refEq_symm {x y : Value} (a : RefEq x y) : RefEq y x := fun c => (a c).symm

theorem skelList_trans {xs ys zs : List Value} (l1 : xs.length = ys.length)
    (r1 : ∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → RefEq x y)
    (l2 : ys.length = zs.length)
    (r2 : ∀ (i : Nat) x y, ys[i]? = some x → zs[i]? = some y → RefEq x y) :
    ∀ (i : Nat) x z, xs[i]? = some x → zs[i]? = some z → RefEq x z := by
  intro i x z hx hz
  have hi : i < ys.length := by
    have := (List.getElem?_eq_some_iff.mp hx).1; omega
  exact refEq_trans (r1 i x _ hx (List.getElem?_eq_getElem hi)) (r2 i _ z (List.getElem?_eq_getElem hi) hz)

theorem sameSkel_trans {o o' o'' : HeapObj} (a : SameSkel o o') (b : SameSkel o' o'') :
    SameSkel o o'' := by
  cases o <;> cases o' <;> simp only [SameSkel] at a <;> (try exact a.elim) <;>
    cases o'' <;> simp only [SameSkel] at b ⊢ <;> (try exact b.elim)
  · exact ⟨a.1.trans b.1, a.2.1.trans b.2.1, a.2.2.1.trans b.2.2.1, a.2.2.2.1.trans b.2.2.2.1,
      skelList_trans a.2.2.2.1 a.2.2.2.2 b.2.2.2.1 b.2.2.2.2⟩
  · exact ⟨a.1.trans b.1, a.2.1.trans b.2.1, skelList_trans a.2.1 a.2.2 b.2.1 b.2.2⟩

theorem Ext_alloc (h : Heap) (o : HeapObj) : Ext h (h.alloc o).2 := by
  refine ⟨by simp [Heap.alloc], fun hwf b hb => ?_, fun b hb => ?_⟩
  · simp only [Heap.alloc] at hb ⊢
    have : b ≠ h.next := by omega
    simp [this, hwf b (by omega)]
  · simp [Heap.alloc, Nat.ne_of_lt hb]

theorem below_child {h : Heap} {c : Nat} {xs : List Value} (hk : okids (h.objs c) = some xs)
    {j : Nat} {x : Value} (hx : xs[j]? = some x) (hb : Below h (.ref c)) : Below h x :=
  fun q a e => hb (j :: q) a (by rw [follow_ref_cons, hk]; simp [hx, e])

/-- The arguments reach only objects below `next`. -/
abbrev BelowArgs (h : Heap) (vs : List Value) : Prop := ∀ (k : Nat) (v : Value), vs[k]? = some v → Below h v


/-- Every reference that `v` reaches in `h` is new (at `lo` or above) and below `next`. -/
def NewIn (lo : Nat) (h : Heap) (v : Value) : Prop :=
  ∀ q b, follow h v q = some (.ref b) → lo ≤ b ∧ b < h.next

/-- An old object after a run: the same shape and the same references, but a list may grow at
its end, by items that reach only objects new from `lo`. -/
def GrowSkel (lo : Nat) (h' : Heap) : HeapObj → HeapObj → Prop
  | .container ty fs, .container ty' fs' =>
    ty = ty' ∧ fs.length = fs'.length ∧ ∀ (i : Nat) x y, fs[i]? = some x → fs'[i]? = some y → RefEq x y
  | .list k e l xs, .list k' e' l' xs' =>
    k = k' ∧ e = e' ∧ l = l' ∧ xs.length ≤ xs'.length ∧
      (∀ (i : Nat) x y, xs[i]? = some x → xs'[i]? = some y → RefEq x y) ∧
      ∀ (i : Nat) y, xs.length ≤ i → xs'[i]? = some y → NewIn lo h' y
  | _, _ => False

/-- Every old object keeps its shape, or a list of it grows by new items (new from `lo`). New
objects come at free addresses. -/
def SkelL (lo : Nat) (h h' : Heap) : Prop :=
  h.next ≤ h'.next ∧ (HeapWF h → HeapWF h') ∧ ∀ a, a < h.next → h'.objs a = h.objs a ∨
    ∃ o o', h.objs a = some o ∧ h'.objs a = some o' ∧ GrowSkel lo h' o o'

/-- A run from `h`: lists may grow by objects that the run made. -/
abbrev Skel (h h' : Heap) : Prop := SkelL h.next h h'

theorem follow_refEq {h : Heap} {v w : Value} (hvw : RefEq v w) :
    ∀ q b, follow h v q = some (.ref b) ↔ follow h w q = some (.ref b) := by
  intro q b
  by_cases hv : ∃ c, v = .ref c
  · obtain ⟨c, rfl⟩ := hv
    have hw : w = .ref c := (hvw c).mp rfl
    subst hw; exact Iff.rfl
  · have hv' : ∀ c, v ≠ .ref c := fun c e => hv ⟨c, e⟩
    have hw' : ∀ c, w ≠ .ref c := fun c e => hv' c ((hvw c).mpr e)
    cases q with
    | nil => simp only [follow, Option.some.injEq]; exact hvw b
    | cons j q => rw [follow_nonref hv', follow_nonref hw']

theorem newIn_mono {lo lo' : Nat} {h : Heap} {v : Value} (hle : lo' ≤ lo) (hv : NewIn lo h v) :
    NewIn lo' h v := fun q b e => ⟨Nat.le_trans hle (hv q b e).1, (hv q b e).2⟩

theorem growSkel_mono {lo lo' : Nat} {h' : Heap} {o o' : HeapObj} (hle : lo' ≤ lo)
    (hs : GrowSkel lo h' o o') : GrowSkel lo' h' o o' := by
  cases o <;> cases o' <;> simp only [GrowSkel] at hs ⊢ <;> try exact hs
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
    fun i y hi hy => newIn_mono hle (hs.2.2.2.2.2 i y hi hy)⟩

theorem growSkel_of_same {lo : Nat} {h' : Heap} {o o' : HeapObj} (hs : SameSkel o o') :
    GrowSkel lo h' o o' := by
  cases o <;> cases o' <;> simp only [SameSkel, GrowSkel] at hs ⊢ <;> try exact hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, Nat.le_of_eq hs.2.2.2.1, hs.2.2.2.2, fun i y hi hy => ?_⟩
  have := (List.getElem?_eq_some_iff.mp hy).1; omega

/-- The children of an old object before and after: a prefix with the same references, and new
items at the end. -/
def KidsGrow (lo : Nat) (h' : Heap) (xs ys : List Value) : Prop :=
  xs.length ≤ ys.length ∧ (∀ (i : Nat) x y, xs[i]? = some x → ys[i]? = some y → RefEq x y) ∧
    ∀ (i : Nat) y, xs.length ≤ i → ys[i]? = some y → NewIn lo h' y

theorem kidsGrow_refl (lo : Nat) (h' : Heap) (xs : List Value) : KidsGrow lo h' xs xs :=
  ⟨Nat.le_refl _, fun i x y hx hy => by rw [hx] at hy; cases hy; exact RefEq.refl x,
    fun i y hi hy => by have := (List.getElem?_eq_some_iff.mp hy).1; omega⟩

theorem kids_SkelL {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') {c : Nat} (hc : c < h.next) :
    (okids (h.objs c) = none ∧ okids (h'.objs c) = none) ∨
      ∃ xs ys, okids (h.objs c) = some xs ∧ okids (h'.objs c) = some ys ∧ KidsGrow lo h' xs ys := by
  rcases hs.2.2 c hc with e | ⟨o, o', ho, ho', sk⟩
  · rw [e]
    cases hk : okids (h.objs c) with
    | none => exact .inl ⟨rfl, rfl⟩
    | some xs => exact .inr ⟨xs, xs, rfl, rfl, kidsGrow_refl lo h' xs⟩
  · rw [ho, ho']
    match o, o', sk with
    | .container _ fs, .container _ fs', sk =>
      exact .inr ⟨fs, fs', rfl, rfl, Nat.le_of_eq sk.2.1, sk.2.2, fun i y hi hy => by
        have h1 := (List.getElem?_eq_some_iff.mp hy).1; have h2 := sk.2.1; omega⟩
    | .list _ _ _ xs, .list _ _ _ xs', sk =>
      exact .inr ⟨xs, xs', rfl, rfl, sk.2.2.2.1, sk.2.2.2.2.1, sk.2.2.2.2.2⟩

/-- An old path to a reference still reads the same. -/
theorem follow_SkelL_fwd {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') :
    ∀ q v w, RefEq v w → Below h w → ∀ b, follow h w q = some (.ref b) → follow h' v q = some (.ref b) := by
  intro q
  induction q with
  | nil => intro v w hvw _ b e; simp only [follow, Option.some.injEq] at e ⊢; exact (hvw b).mpr e
  | cons j q ih =>
    intro v w hvw hbw b e
    by_cases hv : ∃ c, v = .ref c
    · obtain ⟨c, rfl⟩ := hv
      have hw : w = .ref c := (hvw c).mp rfl
      subst hw
      have hc : c < h.next := hbw [] c rfl
      rw [follow_ref_cons] at e ⊢
      rcases kids_SkelL hs hc with ⟨h1, -⟩ | ⟨xs, ys, hx, hy, hl, hr, -⟩
      · rw [h1] at e; cases e
      · rw [hx] at e; rw [hy]
        simp only [Option.bind_some] at e ⊢
        cases hxj : xs[j]? with
        | none => rw [hxj] at e; cases e
        | some x =>
          rw [hxj] at e
          simp only [Option.bind_some] at e
          have hj : j < ys.length := by have := (List.getElem?_eq_some_iff.mp hxj).1; omega
          rw [List.getElem?_eq_getElem hj]
          simp only [Option.bind_some]
          exact ih _ x (refEq_symm (hr j x _ hxj (List.getElem?_eq_getElem hj)))
            (below_child hx hxj hbw) b e
    · have hv' : ∀ c, v ≠ .ref c := fun c e => hv ⟨c, e⟩
      have hw' : ∀ c, w ≠ .ref c := fun c e => hv' c ((hvw c).mpr e)
      rw [follow_nonref hw'] at e; cases e

/-- A new path to a reference reads an old path, or reaches a new object. -/
theorem follow_SkelL_back {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') :
    ∀ q v w, RefEq v w → Below h w → ∀ b, follow h' v q = some (.ref b) →
      follow h w q = some (.ref b) ∨ (lo ≤ b ∧ b < h'.next) := by
  intro q
  induction q with
  | nil => intro v w hvw _ b e; simp only [follow, Option.some.injEq] at e ⊢; exact .inl ((hvw b).mp e)
  | cons j q ih =>
    intro v w hvw hbw b e
    by_cases hv : ∃ c, v = .ref c
    · obtain ⟨c, rfl⟩ := hv
      have hw : w = .ref c := (hvw c).mp rfl
      subst hw
      have hc : c < h.next := hbw [] c rfl
      rw [follow_ref_cons] at e ⊢
      rcases kids_SkelL hs hc with ⟨-, h2⟩ | ⟨xs, ys, hx, hy, hl, hr, hn⟩
      · rw [h2] at e; cases e
      · rw [hy] at e; rw [hx]
        simp only [Option.bind_some] at e ⊢
        cases hyj : ys[j]? with
        | none => rw [hyj] at e; cases e
        | some y =>
          rw [hyj] at e
          simp only [Option.bind_some] at e
          by_cases hj : j < xs.length
          · rw [List.getElem?_eq_getElem hj]
            simp only [Option.bind_some]
            exact ih y _ (refEq_symm (hr j _ y (List.getElem?_eq_getElem hj) hyj))
              (below_child hx (List.getElem?_eq_getElem hj) hbw) b e
          · exact .inr (hn j y (by omega) hyj q b e)
    · have hv' : ∀ c, v ≠ .ref c := fun c e => hv ⟨c, e⟩
      rw [follow_nonref hv'] at e; cases e

theorem newIn_SkelL {lo lo' : Nat} {h h' : Heap} (hs : SkelL lo' h h') (hle : lo ≤ lo') {y : Value}
    (hy : NewIn lo h y) : NewIn lo h' y := by
  intro q b e
  rcases follow_SkelL_back hs q y y (RefEq.refl y) (fun q' b' e' => (hy q' b' e').2) b e with e' | ⟨h1, h2⟩
  · exact ⟨(hy q b e').1, Nat.lt_of_lt_of_le (hy q b e').2 hs.1⟩
  · exact ⟨Nat.le_trans hle h1, h2⟩

theorem growSkel_SkelL {lo lo' : Nat} {h' h'' : Heap} (hs : SkelL lo' h' h'') (hle : lo ≤ lo')
    {o o' : HeapObj} (g : GrowSkel lo h' o o') : GrowSkel lo h'' o o' := by
  cases o <;> cases o' <;> simp only [GrowSkel] at g ⊢ <;> try exact g
  exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1,
    fun i y hi hy => newIn_SkelL hs hle (g.2.2.2.2.2 i y hi hy)⟩

theorem newIn_refEq {lo : Nat} {h : Heap} {v w : Value} (hvw : RefEq v w) (hv : NewIn lo h v) :
    NewIn lo h w := fun q b e => hv q b ((follow_refEq hvw q b).mpr e)

theorem growSkel_trans {lo lo' : Nat} {h2 h3 : Heap} (hs : SkelL lo' h2 h3) (hle : lo ≤ lo')
    {o o' o'' : HeapObj} (a : GrowSkel lo h2 o o') (b : GrowSkel lo' h3 o' o'') :
    GrowSkel lo h3 o o'' := by
  match o, o', o'', a, b with
  | .container _ fs, .container _ fs', .container _ fs'', a, b =>
    exact ⟨a.1.trans b.1, a.2.1.trans b.2.1, skelList_trans a.2.1 a.2.2 b.2.1 b.2.2⟩
  | .list _ _ _ xs, .list _ _ _ xs', .list _ _ _ xs'', a, b =>
    refine ⟨a.1.trans b.1, a.2.1.trans b.2.1, a.2.2.1.trans b.2.2.1,
      Nat.le_trans a.2.2.2.1 b.2.2.2.1, fun i x z hx hz => ?_, fun i y hi hy => ?_⟩
    · have hi : i < _ := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 a.2.2.2.1
      exact refEq_trans (a.2.2.2.2.1 i x _ hx (List.getElem?_eq_getElem hi))
        (b.2.2.2.2.1 i _ z (List.getElem?_eq_getElem hi) hz)
    · by_cases hi' : i < xs'.length
      · have hy' := List.getElem?_eq_getElem hi'
        exact newIn_refEq (b.2.2.2.2.1 i _ y hy' hy) (newIn_SkelL hs hle (a.2.2.2.2.2 i _ hi hy'))
      · exact newIn_mono hle (b.2.2.2.2.2 i y (by omega) hy)

theorem SkelL_refl (lo : Nat) (h : Heap) : SkelL lo h h := ⟨Nat.le_refl _, id, fun _ _ => .inl rfl⟩

theorem SkelL_of_Ext {h h' : Heap} (e : Ext h h') (lo : Nat) : SkelL lo h h' :=
  ⟨e.1, e.2.1, fun a ha => .inl (e.2.2 a ha)⟩

theorem SkelL_mono {lo lo' : Nat} {h h' : Heap} (hle : lo' ≤ lo) (hs : SkelL lo h h') : SkelL lo' h h' :=
  ⟨hs.1, hs.2.1, fun a ha => (hs.2.2 a ha).imp id fun ⟨o, o', ho, ho', g⟩ => ⟨o, o', ho, ho', growSkel_mono hle g⟩⟩

theorem SkelL_trans {lo lo' : Nat} {h1 h2 h3 : Heap} (a : SkelL lo h1 h2) (b : SkelL lo' h2 h3)
    (hle : lo ≤ lo') : SkelL lo h1 h3 := by
  refine ⟨Nat.le_trans a.1 b.1, fun w => b.2.1 (a.2.1 w), fun x hx => ?_⟩
  have hx2 : x < h2.next := Nat.lt_of_lt_of_le hx a.1
  rcases a.2.2 x hx with e1 | ⟨o, o', h1o, h2o, s1⟩ <;> rcases b.2.2 x hx2 with e2 | ⟨p, p', h2p, h3p, s2⟩
  · exact .inl (e2.trans e1)
  · rw [e1] at h2p; exact .inr ⟨p, p', h2p, h3p, growSkel_mono hle s2⟩
  · rw [← e2] at h2o; exact .inr ⟨o, o', h1o, h2o, growSkel_SkelL b hle s1⟩
  · rw [h2o] at h2p; cases h2p; exact .inr ⟨o, p', h1o, h3p, growSkel_trans b hle s1 s2⟩

theorem SkelL_set {lo : Nat} {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : GrowSkel lo (h.set a o') o o') : SkelL lo h (h.set a o') := by
  refine ⟨by simp [Heap.set], fun hwf b hb => ?_, fun b _ => ?_⟩
  · have hb' : h.next ≤ b := by simpa [Heap.set] using hb
    by_cases hba : b = a
    · subst hba; rw [hwf b hb'] at ho; cases ho
    · simp [hba, hwf b hb']
  · by_cases hb : b = a
    · subst hb; exact .inr ⟨o, o', ho, by simp, hs⟩
    · exact .inl (by simp [hb])

/-- A run that changes no old object keeps every path to a reference. -/
theorem follow_Ext {h h' : Heap} (e : Ext h h') (q : List Nat) {v : Value} (hb : Below h v) (b : Nat) :
    follow h' v q = some (.ref b) ↔ follow h v q = some (.ref b) := by
  constructor
  · intro e'
    rcases follow_SkelL_back (SkelL_of_Ext e h'.next) q v v (RefEq.refl v) hb b e' with r | ⟨h1, h2⟩
    · exact r
    · omega
  · exact follow_SkelL_fwd (SkelL_of_Ext e 0) q v v (RefEq.refl v) hb b

theorem at?_Ext {h h' : Heap} (e : Ext h h') {vs : List Value} (hb : BelowArgs h vs)
    (k : Nat) (q : List Nat) (b : Nat) : at? h' vs k q = some (.ref b) ↔ at? h vs k q = some (.ref b) := by
  unfold at?
  cases hv : vs[k]? with
  | none => simp
  | some v => simpa using follow_Ext e q (hb k v hv) b

theorem at?_SkelL_fwd {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') {vs : List Value} (hb : BelowArgs h vs)
    (k : Nat) (q : List Nat) (b : Nat) : at? h vs k q = some (.ref b) → at? h' vs k q = some (.ref b) := by
  unfold at?
  cases hv : vs[k]? with
  | none => simp
  | some v => simpa using follow_SkelL_fwd hs q v v (RefEq.refl v) (hb k v hv) b

theorem at?_SkelL_back {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') {vs : List Value} (hb : BelowArgs h vs)
    (k : Nat) (q : List Nat) (b : Nat) : at? h' vs k q = some (.ref b) →
      at? h vs k q = some (.ref b) ∨ (lo ≤ b ∧ b < h'.next) := by
  unfold at?
  cases hv : vs[k]? with
  | none => simp
  | some v => simpa using follow_SkelL_back hs q v v (RefEq.refl v) (hb k v hv) b

theorem rootTy_SkelL {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') {vs : List Value} (hb : BelowArgs h vs)
    (k : Nat) (ty : Name) : RootTy h' vs k ty ↔ RootTy h vs k ty := by
  constructor
  · rintro ⟨c, hc, hoc⟩
    have hlt : c < h.next := hb k _ hc [] c rfl
    refine ⟨c, hc, ?_⟩
    rcases hs.2.2 c hlt with e | ⟨o, o', ho, ho', sk⟩
    · rwa [e] at hoc
    · rw [ho'] at hoc; rw [ho]
      cases o <;> cases o' <;> simp only [GrowSkel] at sk <;>
        first
        | exact absurd sk id
        | (obtain ⟨rfl, rfl, -⟩ := sk; simpa using hoc)
        | (obtain ⟨rfl, -⟩ := sk; simpa using hoc)
  · rintro ⟨c, hc, hoc⟩
    have hlt : c < h.next := hb k _ hc [] c rfl
    refine ⟨c, hc, ?_⟩
    rcases hs.2.2 c hlt with e | ⟨o, o', ho, ho', sk⟩
    · rwa [e]
    · rw [ho] at hoc; rw [ho']
      cases o <;> cases o' <;> simp only [GrowSkel] at sk <;>
        first
        | exact absurd sk id
        | (obtain ⟨rfl, rfl, -⟩ := sk; simpa using hoc)
        | (obtain ⟨rfl, -⟩ := sk; simpa using hoc)

theorem Fresh_of_SkelL {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') : Fresh h h' := ⟨hs.1, hs.2.1⟩

theorem Reach_of_SkelL {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') (hlo : h.next ≤ lo) {vs : List Value}
    (hb : BelowArgs h vs) : Reach h h' vs :=
  fun k q b e => (at?_SkelL_back hs hb k q b e).imp id fun ⟨h1, _⟩ => Nat.le_trans hlo h1


/-- A path that reaches a new object: an old path to an old list, an index past its old end,
then a path from the new item. -/
theorem follow_new_split {lo : Nat} {h h' : Heap} (hs : SkelL lo h h') :
    ∀ q v, Below h v → ∀ b, follow h' v q = some (.ref b) → h.next ≤ b →
      ∃ q0 c j rest y xs ys, q = q0 ++ j :: rest ∧ follow h v q0 = some (.ref c) ∧ c < h.next ∧
        okids (h.objs c) = some xs ∧ okids (h'.objs c) = some ys ∧ xs.length ≤ j ∧
        ys[j]? = some y ∧ follow h' y rest = some (.ref b) := by
  intro q
  induction q with
  | nil =>
    intro v hb b e hn
    simp only [follow, Option.some.injEq] at e; subst e
    have := hb [] b rfl; omega
  | cons j q ih =>
    intro v hb b e hn
    by_cases hv : ∃ c, v = .ref c
    · obtain ⟨c, rfl⟩ := hv
      have hc : c < h.next := hb [] c rfl
      rw [follow_ref_cons] at e
      rcases kids_SkelL hs hc with ⟨-, h2⟩ | ⟨xs, ys, hx, hy, hl, hr, -⟩
      · rw [h2] at e; cases e
      · rw [hy] at e
        simp only [Option.bind_some] at e
        cases hyj : ys[j]? with
        | none => rw [hyj] at e; cases e
        | some y =>
          rw [hyj] at e
          simp only [Option.bind_some] at e
          by_cases hj : j < xs.length
          · have hxj := List.getElem?_eq_getElem hj
            have hrxy := hr j _ y hxj hyj
            have e' : follow h' xs[j] q = some (.ref b) := (follow_refEq (refEq_symm hrxy) q b).mp e
            obtain ⟨q0, c', j', rest, y', xs', ys', rfl, h1, h2, h3, h4, h5, h6, h7⟩ :=
              ih xs[j] (below_child hx hxj hb) b e' hn
            refine ⟨j :: q0, c', j', rest, y', xs', ys', rfl, ?_, h2, h3, h4, h5, h6, h7⟩
            rw [follow_ref_cons, hx]; simp [hxj, h1]
          · exact ⟨[], c, j, q, y, xs, ys, rfl, rfl, hc, hx, hy, by omega, hyj, e⟩
    · have hv' : ∀ c, v ≠ .ref c := fun c e => hv ⟨c, e⟩
      rw [follow_nonref hv'] at e; cases e

theorem Skel_refl (h : Heap) : Skel h h := SkelL_refl _ h

theorem Skel_of_Ext {h h' : Heap} (e : Ext h h') : Skel h h' := SkelL_of_Ext e _

theorem Skel_trans {h1 h2 h3 : Heap} (a : Skel h1 h2) (b : Skel h2 h3) : Skel h1 h3 :=
  SkelL_trans a b a.1

theorem Skel_set {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') : Skel h (h.set a o') :=
  SkelL_set ho (growSkel_of_same hs)

theorem rootTy_Skel {h h' : Heap} (hs : Skel h h') {vs : List Value} (hb : BelowArgs h vs) (k : Nat)
    (ty : Name) : RootTy h' vs k ty ↔ RootTy h vs k ty := rootTy_SkelL hs hb k ty

theorem Fresh_of_Skel {h h' : Heap} (hs : Skel h h') : Fresh h h' := Fresh_of_SkelL hs

theorem Reach_of_Skel {h h' : Heap} (hs : Skel h h') {vs : List Value} (hb : BelowArgs h vs) :
    Reach h h' vs := Reach_of_SkelL hs (Nat.le_refl _) hb

/-! ## Decoding after a run that keeps the shape -/

theorem dec_mono {h : Heap} : ∀ (n j : Nat) (v : Value) (d : DV), dec h n v = some d →
    dec h (n + j) v = some d
  | 0, j, v, d, hd => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr; simp [dec_zero_ref] at hd
    · rw [dec_nonref (fun b e => hr ⟨b, e⟩)] at hd ⊢; exact hd
  | m + 1, j, v, d, hd => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      rw [show m + 1 + j = (m + j) + 1 by omega, dec_ref_succ]
      rw [dec_ref_succ] at hd
      have lift : ∀ (xs : List Value) ds, xs.mapM (dec h m) = some ds →
          xs.mapM (dec h (m + j)) = some ds := by
        intro xs ds hm
        obtain ⟨hl, hp⟩ := (mapM_some_iff xs ds).mp hm
        refine (mapM_some_iff xs ds).mpr ⟨hl, fun i x hx => ?_⟩
        have := hp i x hx
        cases hdi : ds[i]? with
        | none =>
          exfalso
          have := (List.getElem?_eq_some_iff.mp hx).1
          rw [List.getElem?_eq_none_iff] at hdi; omega
        | some di => rw [hdi] at this; exact dec_mono m j x di this
      split at hd
      · next ty fs ho =>
        cases hm : fs.mapM (dec h m) with
        | none => simp [hm] at hd
        | some ds => simp [hm] at hd; subst hd; simp [lift fs ds hm]
      · next k e l xs ho =>
        cases hm : xs.mapM (dec h m) with
        | none => simp [hm] at hd
        | some ds => simp [hm] at hd; subst hd; simp [lift xs ds hm]
      · cases hd
    · rw [dec_nonref (fun b e => hr ⟨b, e⟩)] at hd ⊢; exact hd

theorem dec_mono' {h : Heap} {n n' : Nat} {v : Value} {d : DV} (hd : dec h n v = some d)
    (hle : n ≤ n') : dec h n' v = some d := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact dec_mono n j v d hd

/-- A value that decodes reaches only objects of the heap, so below `next` in a well-formed
heap. -/
theorem dec_below {h : Heap} (hwf : HeapWF h) :
    ∀ (n : Nat) (v : Value) (d : DV), dec h n v = some d → Below h v
  | 0, v, d, hd => by
    intro q a e
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr; simp [dec_zero_ref] at hd
    · exact absurd e (fun e' => follow_nonref_ref (fun b e => hr ⟨b, e⟩) e')
  | m + 1, v, d, hd => by
    intro q a e
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      rw [dec_ref_succ] at hd
      have hex : h.objs b ≠ none := by intro hn; rw [hn] at hd; simp at hd
      have hb : b < h.next := Nat.lt_of_not_le fun hle => hex (hwf b hle)
      cases q with
      | nil => simp [follow] at e; subst e; exact hb
      | cons j q =>
        rw [follow_ref_cons] at e
        have kid : ∀ xs, okids (h.objs b) = some xs → ∀ ds, xs.mapM (dec h m) = some ds → a < h.next := by
          intro xs hk ds hm
          rw [hk] at e
          simp only [Option.bind_some] at e
          cases hx : xs[j]? with
          | none => simp [hx] at e
          | some x =>
            simp only [hx, Option.bind_some] at e
            obtain ⟨c, -, hc⟩ := mapM_get' hm hx
            exact dec_below hwf m x c hc q a e
        cases hob : h.objs b with
        | none => exact absurd hob hex
        | some o =>
          rw [hob] at hd
          cases o with
          | container ty fs =>
            cases hm : fs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds => exact kid fs (by simp [okids, hob]) ds hm
          | list k el l xs =>
            cases hm : xs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds => exact kid xs (by simp [okids, hob]) ds hm
          | _ => simp at hd
    · exact absurd e (fun e' => follow_nonref_ref (fun b e => hr ⟨b, e⟩) e')

/-- Arguments that decode lie below `next`. -/
theorem decArgs_below {h : Heap} (hwf : HeapWF h) {vs : List Value} {roots : List DV}
    (hd : ∀ (k : Nat) (v : Value) (d : DV), vs[k]? = some v → roots[k]? = some d → ∃ n, dec h n v = some d)
    (hl : roots.length = vs.length) : BelowArgs h vs := by
  intro k v hv q a
  revert q a
  have hk : k < roots.length := by rw [hl]; exact (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨n, hn⟩ := hd k v roots[k] hv (List.getElem?_eq_getElem hk)
  exact dec_below hwf n v _ hn

/-- A value that reaches no changed object decodes the same. -/
theorem follow_unchanged {h h' : Heap} :
    ∀ (q : List Nat) (v : Value), (∀ q a, follow h v q = some (.ref a) → h'.objs a = h.objs a) →
      follow h' v q = follow h v q
  | [], v, _ => rfl
  | j :: q, v, hv => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      have hb : h'.objs b = h.objs b := hv [] b rfl
      rw [follow_ref_cons, follow_ref_cons, hb]
      cases hk : okids (h.objs b) with
      | none => rfl
      | some xs =>
        simp only [Option.bind_some]
        cases hx : xs[j]? with
        | none => rfl
        | some x =>
          simp only [Option.bind_some]
          exact follow_unchanged q x fun q' a e => hv (j :: q') a (by rw [follow_ref_cons, hk]; simp [hx, e])
    · have hr' : ∀ b, v ≠ .ref b := fun b e => hr ⟨b, e⟩
      rw [follow_nonref hr', follow_nonref hr']

theorem dec_unchanged {h h' : Heap} :
    ∀ (n : Nat) (v : Value), (∀ q a, follow h v q = some (.ref a) → h'.objs a = h.objs a) →
      dec h' n v = dec h n v
  | 0, v, _ => by cases v <;> rfl
  | m + 1, v, hv => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      rw [dec_ref_succ, dec_ref_succ, hv [] b rfl]
      have hc : ∀ xs, okids (h.objs b) = some xs → ∀ (i : Nat) x, xs[i]? = some x →
          dec h' m x = dec h m x := by
        intro xs hk i x hx
        refine dec_unchanged m x fun q a e => hv (i :: q) a ?_
        rw [follow_ref_cons, hk]; simp [hx, e]
      cases ho : h.objs b with
      | none => rfl
      | some o =>
        rw [ho] at hc
        cases o with
        | container ty fs => simp only [mapM_congr (hc fs rfl)]
        | list k e l xs => simp only [mapM_congr (hc xs rfl)]
        | _ => rfl
    · rw [dec_nonref (fun b e => hr ⟨b, e⟩), dec_nonref (fun b e => hr ⟨b, e⟩)]

theorem subAt_setAt_kids {ds : List DV} {j : Nat} {c x : DV} (hc : ds[j]? = some c) (p : List Nat) :
    (ds.set j (setAt p c x)).length = ds.length := by simp

/-- The caller's tree after a call: the callee's tree is put in at the place `p`. Every changed
object that `v` reaches is below `p`. -/
theorem dec_graft {h h' : Heap} (w : Value) (dw : DV) (mw : Nat) (hw : dec h' mw w = some dw) :
    ∀ (p : List Nat) (n : Nat) (v : Value) (d : DV), dec h n v = some d →
      follow h v p = some w →
      (∀ q a, follow h v q = some (.ref a) → h'.objs a ≠ h.objs a → ∃ r, q = p ++ r) →
      ∃ n', dec h' n' v = some (setAt p d dw)
  | [], n, v, d, _, hf, _ => by
    simp [follow] at hf; subst hf; exact ⟨mw, hw⟩
  | j :: p, n, v, d, hd, hf, hch => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      have hb : h'.objs b = h.objs b := by
        refine Classical.byContradiction fun hne => ?_
        obtain ⟨r, hr⟩ := hch [] b rfl hne
        simp at hr
      cases n with
      | zero => simp [dec_zero_ref] at hd
      | succ m =>
        rw [follow_ref_cons] at hf
        rw [dec_ref_succ] at hd
        have kid : ∀ xs, okids (h.objs b) = some xs →
            (∀ (j' : Nat) x, j' ≠ j → xs[j']? = some x → dec h' m x = dec h m x) ∧
            (∀ x, xs[j]? = some x → ∀ c, dec h m x = some c →
              follow h x p = some w → ∃ n', dec h' n' x = some (setAt p c dw)) := by
          intro xs hk
          refine ⟨fun j' x hne hx => dec_unchanged m x fun q a e => ?_, fun x hx c hc hfx => ?_⟩
          · refine Classical.byContradiction fun hne' => ?_
            obtain ⟨r, hr⟩ := hch (j' :: q) a (by rw [follow_ref_cons, hk]; simp [hx, e]) hne'
            simp at hr; exact hne hr.1
          · refine dec_graft w dw mw hw p m x c hc hfx fun q a e hne => ?_
            obtain ⟨r, hr⟩ := hch (j :: q) a (by rw [follow_ref_cons, hk]; simp [hx, e]) hne
            exact ⟨r, by simpa using hr⟩
        cases hob : h.objs b with
        | none => simp [hob] at hd
        | some ob =>
          rw [hob] at hd hf kid
          cases ob with
          | container ty fs =>
            obtain ⟨k1, k2⟩ := kid fs rfl
            cases hm : fs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds =>
              simp [hm] at hd; subst hd
              simp only [okids, Option.bind_some] at hf
              cases hx : fs[j]? with
              | none => simp [hx] at hf
              | some x =>
                simp only [hx, Option.bind_some] at hf
                obtain ⟨c, hc, hdc⟩ := mapM_get' hm hx
                obtain ⟨n1, h1⟩ := k2 x hx c hdc hf
                refine ⟨max m n1 + 1, ?_⟩
                rw [dec_ref_succ, hb, hob]
                simp only [setAt, hc]
                have := mapM_set_congr (g := dec h' (max m n1)) hm j x _
                  (dec_mono' h1 (Nat.le_max_right _ _))
                  (fun j' y hne hy => by
                    obtain ⟨dy, -, hdy⟩ := mapM_get' hm hy
                    rw [hdy]; exact dec_mono' ((k1 j' y hne hy).trans hdy) (Nat.le_max_left _ _))
                rw [set_self_of_get hx] at this
                simp [this]
          | list k e l xs =>
            obtain ⟨k1, k2⟩ := kid xs rfl
            cases hm : xs.mapM (dec h m) with
            | none => simp [hm] at hd
            | some ds =>
              simp [hm] at hd; subst hd
              simp only [okids, Option.bind_some] at hf
              cases hx : xs[j]? with
              | none => simp [hx] at hf
              | some x =>
                simp only [hx, Option.bind_some] at hf
                obtain ⟨c, hc, hdc⟩ := mapM_get' hm hx
                obtain ⟨n1, h1⟩ := k2 x hx c hdc hf
                refine ⟨max m n1 + 1, ?_⟩
                rw [dec_ref_succ, hb, hob]
                simp only [setAt, hc]
                have := mapM_set_congr (g := dec h' (max m n1)) hm j x _
                  (dec_mono' h1 (Nat.le_max_right _ _))
                  (fun j' y hne hy => by
                    obtain ⟨dy, -, hdy⟩ := mapM_get' hm hy
                    rw [hdy]; exact dec_mono' ((k1 j' y hne hy).trans hdy) (Nat.le_max_left _ _))
                rw [set_self_of_get hx] at this
                simp [this]
          | _ => simp at hd
    · rw [follow_nonref (fun b e => hr ⟨b, e⟩)] at hf; cases hf

/-! ## Footprint patterns -/

theorem genB_matches : ∀ (ps ps' : List PStep) (q : List Nat), genB ps ps' = true →
    Matches ps' q → Matches ps q
  | [], [], q, _, hm => hm
  | [], _ :: _, _, hg, _ => by simp [genB] at hg
  | .any :: _, [], _, hg, _ => by simp [genB] at hg
  | .exact _ :: _, [], _, hg, _ => by simp [genB] at hg
  | .exact _ :: _, .any :: _, _, hg, _ => by simp [genB] at hg
  | .any :: ps, st :: ps', q, hg, hm => by
    simp only [genB] at hg
    cases q with
    | nil => cases st <;> simp [Matches] at hm
    | cons k q =>
      simp only [Matches]
      cases st with
      | exact i => exact genB_matches ps ps' q hg hm.2
      | any => exact genB_matches ps ps' q hg hm
  | .exact i :: ps, .exact j :: ps', q, hg, hm => by
    simp only [genB, Bool.and_eq_true, beq_iff_eq] at hg
    cases q with
    | nil => simp [Matches] at hm
    | cons k q =>
      simp only [Matches] at hm ⊢
      exact ⟨hg.1.trans hm.1, genB_matches ps ps' q hg.2 hm.2⟩

theorem coversB_matches : ∀ (ps : List PStep) (p : List Nat) (ps' : List PStep) (q : List Nat),
    coversB ps p ps' = true → Matches ps' q → Matches ps (p ++ q)
  | ps, [], ps', q, hc, hm => by simpa [coversB] using genB_matches ps ps' q (by simpa [coversB] using hc) hm
  | .exact i :: ps, j :: p, ps', q, hc, hm => by
    simp only [coversB, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [List.cons_append, Matches]
    exact ⟨hc.1, coversB_matches ps p ps' q hc.2 hm⟩
  | .any :: ps, _ :: p, ps', q, hc, hm => by
    simp only [coversB] at hc
    simp only [List.cons_append, Matches]
    exact coversB_matches ps p ps' q hc hm
  | [], _ :: _, _, _, hc, _ => by simp [coversB] at hc

end SpecLean.Layer4
