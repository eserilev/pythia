import SpecLean.Encode
import SpecLean.Lemmas

/-!
# Heap path lemmas

A write changes one heap object. These lemmas say which paths still read the same after it.
-/

namespace SpecLean.Encode

open SpecLean

/-- Two values hold the same reference, or neither holds a reference. -/
def RefEq (x y : Value) : Prop := ∀ b, x = .ref b ↔ y = .ref b

theorem RefEq.refl (x : Value) : RefEq x x := fun _ => Iff.rfl

/-- Two heap objects of the same shape whose references sit at the same positions. -/
def SameSkel : HeapObj → HeapObj → Prop
  | .container ty fs, .container ty' fs' =>
    ty = ty' ∧ fs.length = fs'.length ∧ ∀ (i : Nat) x y, fs[i]? = some x → fs'[i]? = some y → RefEq x y
  | .list k e l xs, .list k' e' l' xs' =>
    k = k' ∧ e = e' ∧ l = l' ∧ xs.length = xs'.length ∧
      ∀ (i : Nat) x y, xs[i]? = some x → xs'[i]? = some y → RefEq x y
  | _, _ => False

theorem follow_nonref {h : Heap} {v : Value} (hv : ∀ b, v ≠ .ref b) (j : Nat) (q : List Nat) :
    follow h v (j :: q) = none := by
  cases v with
  | ref c => exact absurd rfl (hv c)
  | _ => rfl

/-- A write that keeps the shape of the object keeps every path that ends at a reference. -/
theorem follow_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') :
    ∀ q v w, RefEq v w → ∀ b,
      follow (h.set a o') v q = some (.ref b) ↔ follow h w q = some (.ref b) := by
  intro q
  induction q with
  | nil => intro v w hvw b; simp only [follow, Option.some.injEq]; exact hvw b
  | cons j q ih =>
    intro v w hvw b
    by_cases hv : ∃ c, v = .ref c
    · obtain ⟨c, rfl⟩ := hv
      have hw : w = .ref c := (hvw c).mp rfl
      subst hw
      simp only [follow, Heap.set_objs]
      by_cases hc : c = a
      · subst hc
        rw [if_pos rfl, ho]
        cases o with
        | container ty fs =>
          cases o' with
          | container ty' fs' =>
            obtain ⟨-, hl, hr⟩ := hs
            cases hx : fs'[j]? with
            | none =>
              have : fs[j]? = none := by
                rw [List.getElem?_eq_none_iff] at hx ⊢; omega
              simp only [hx, this, Option.bind_none, reduceCtorEq]
            | some y =>
              cases hx' : fs[j]? with
              | none =>
                exfalso
                rw [List.getElem?_eq_none_iff] at hx'
                have := (List.getElem?_eq_some_iff.mp hx).1; omega
              | some x =>
                simp only [hx, hx', Option.bind_some]
                exact ih y x (fun b' => (hr j x y hx' hx b').symm) b
          | list => exact absurd hs (by simp only [SameSkel]; exact id)
          | _ => exact absurd hs (by simp only [SameSkel]; exact id)
        | list k e l xs =>
          cases o' with
          | list k' e' l' xs' =>
            obtain ⟨-, -, -, hl, hr⟩ := hs
            cases hx : xs'[j]? with
            | none =>
              have : xs[j]? = none := by
                rw [List.getElem?_eq_none_iff] at hx ⊢; omega
              simp only [hx, this, Option.bind_none, reduceCtorEq]
            | some y =>
              cases hx' : xs[j]? with
              | none =>
                exfalso
                rw [List.getElem?_eq_none_iff] at hx'
                have := (List.getElem?_eq_some_iff.mp hx).1; omega
              | some x =>
                simp only [hx, hx', Option.bind_some]
                exact ih y x (fun b' => (hr j x y hx' hx b').symm) b
          | container => exact absurd hs (by simp only [SameSkel]; exact id)
          | _ => exact absurd hs (by simp only [SameSkel]; exact id)
        | _ => exact absurd hs (by simp only [SameSkel]; exact id)
      · rw [if_neg hc]
        cases h.objs c with
        | none => simp
        | some o2 =>
          cases o2 with
          | container ty fs =>
            cases hx : fs[j]? with
            | none => simp [hx]
            | some x => simp only [hx, Option.bind_some]; exact ih x x (RefEq.refl x) b
          | list k e l xs =>
            cases hx : xs[j]? with
            | none => simp [hx]
            | some x => simp only [hx, Option.bind_some]; exact ih x x (RefEq.refl x) b
          | _ => simp
    · have hv' : ∀ c, v ≠ .ref c := fun c e => hv ⟨c, e⟩
      have hw' : ∀ c, w ≠ .ref c := fun c e => hv' c ((hvw c).mpr e)
      rw [follow_nonref hv', follow_nonref hw']

/-- After a write that keeps the shape, the arguments reach the same references. -/
theorem at?_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') (vs : List Value) (k : Nat) (q : List Nat) (b : Nat) :
    at? (h.set a o') vs k q = some (.ref b) ↔ at? h vs k q = some (.ref b) := by
  unfold at?
  cases vs[k]? with
  | none => simp
  | some v => simpa using follow_skel ho hs q v v (RefEq.refl v) b

theorem rootTy_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') (vs : List Value) (k : Nat) (ty : Name) :
    RootTy (h.set a o') vs k ty ↔ RootTy h vs k ty := by
  unfold RootTy
  constructor
  · rintro ⟨c, fs, hc, hoc⟩
    by_cases hca : c = a
    · subst hca
      simp only [Heap.set_objs, ↓reduceIte, Option.some.injEq] at hoc; subst hoc
      cases o with
      | container ty' fs' => obtain ⟨rfl, -⟩ := hs; exact ⟨c, fs', hc, ho⟩
      | _ => exact absurd hs (by simp only [SameSkel]; exact id)
    · exact ⟨c, fs, hc, by simpa [hca] using hoc⟩
  · rintro ⟨c, fs, hc, hoc⟩
    by_cases hca : c = a
    · subst hca
      rw [ho] at hoc; cases hoc
      cases o' with
      | container ty' fs' => obtain ⟨rfl, -⟩ := hs; exact ⟨c, fs', hc, by simp⟩
      | _ => exact absurd hs (by simp only [SameSkel]; exact id)
    · exact ⟨c, fs, hc, by simp [hca, hoc]⟩

theorem WTree_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') {vs : List Value} {fp : Footprint} (hw : WTree h vs fp) :
    WTree (h.set a o') vs fp := by
  intro k pat hk hty q hq b hb k' q' hb'
  exact hw k pat hk ((rootTy_skel ho hs vs k pat.ty).mp hty) q hq b
    ((at?_skel ho hs vs k q b).mp hb) k' q' ((at?_skel ho hs vs k' q' b).mp hb')

/-- An argument list with one more value that holds no reference has the same paths to
references. -/
theorem WTree_append_nonref {h : Heap} {vs : List Value} {fp : Footprint} {v : Value}
    (hv : ∀ b, v ≠ .ref b) (hw : WTree h vs fp) : WTree h (vs ++ [v]) fp := by
  have key : ∀ k q b, at? h (vs ++ [v]) k q = some (.ref b) → at? h vs k q = some (.ref b) := by
    intro k q b hk
    unfold at? at hk ⊢
    by_cases hlt : k < vs.length
    · rwa [List.getElem?_append_left hlt] at hk
    · rw [List.getElem?_append_right (by omega)] at hk
      cases hkk : k - vs.length with
      | zero =>
        rw [hkk] at hk
        cases q with
        | nil => simp [follow] at hk; exact absurd (Eq.symm hk) (fun e => hv b e.symm)
        | cons j q => simp [follow_nonref hv] at hk
      | succ m => rw [hkk] at hk; simp at hk
  have keyTy : ∀ k ty, RootTy h (vs ++ [v]) k ty → RootTy h vs k ty := by
    rintro k ty ⟨c, fs, hc, hoc⟩
    refine ⟨c, fs, ?_, hoc⟩
    by_cases hlt : k < vs.length
    · rwa [List.getElem?_append_left hlt] at hc
    · rw [List.getElem?_append_right (by omega)] at hc
      cases hkk : k - vs.length with
      | zero => rw [hkk] at hc; simp at hc; exact absurd hc (hv c)
      | succ m => rw [hkk] at hc; simp at hc
  intro k pat hk hty q hq b hb k' q' hb'
  exact hw k pat hk (keyTy k _ hty) q hq b (key k q b hb) k' q' (key k' q' b hb')

theorem HeapWF_set {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hwf : HeapWF h) : HeapWF (h.set a o') := by
  intro b hb
  simp only [Heap.set_next] at hb
  simp only [Heap.set_objs]
  have : b ≠ a := fun e => by subst e; rw [hwf b hb] at ho; cases ho
  rw [if_neg this]; exact hwf b hb

/-- A write to an object at a footprint path is inside the frame. -/
theorem Frame_set {h : Heap} {vs : List Value} {fpf : Footprint} {a : Nat} {o' : HeapObj}
    (hat : AtFp h vs fpf a) : Frame h (h.set a o') vs fpf := by
  intro b _ hb
  have : b ≠ a := fun e => by subst e; exact hb hat
  simp [this]

theorem Frame_refl (h : Heap) (vs : List Value) (fpf : Footprint) : Frame h h vs fpf :=
  fun _ _ _ => rfl

theorem Frame_trans {h1 h2 h3 : Heap} {vs : List Value} {fpf : Footprint}
    (f12 : Frame h1 h2 vs fpf) (f23 : Frame h2 h3 vs fpf)
    (hmono : ∀ a, AtFp h2 vs fpf a → AtFp h1 vs fpf a) : Frame h1 h3 vs fpf := by
  intro a hn ha
  have e12 := f12 a hn ha
  rw [f23 a (by rw [e12]; exact hn) (fun h2a => ha (hmono a h2a)), e12]

theorem Fresh_set {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o) :
    Fresh h (h.set a o') := ⟨by simp, HeapWF_set ho⟩

theorem Fresh_refl (h : Heap) : Fresh h h := ⟨Nat.le_refl _, id⟩

theorem Fresh_trans {h1 h2 h3 : Heap} (a : Fresh h1 h2) (b : Fresh h2 h3) : Fresh h1 h3 :=
  ⟨Nat.le_trans a.1 b.1, fun w => b.2 (a.2 w)⟩

theorem Reach_refl (h : Heap) (vs : List Value) : Reach h h vs := fun _ _ _ e => .inl e

theorem Reach_skel {h : Heap} {a : Nat} {o o' : HeapObj} (ho : h.objs a = some o)
    (hs : SameSkel o o') (vs : List Value) : Reach h (h.set a o') vs :=
  fun k q b e => .inl ((at?_skel ho hs vs k q b).mp e)

/-- `follow` reads the same after a write to an object that no strict prefix of the path
reaches. -/
theorem follow_set_away {h : Heap} {a : Nat} {o' : HeapObj} :
    ∀ q v, (∀ p r, q = p ++ r → r ≠ [] → follow h v p ≠ some (.ref a)) →
      follow (h.set a o') v q = follow h v q := by
  intro q
  induction q with
  | nil => intro v _; rfl
  | cons j q ih =>
    intro v hp
    cases v with
    | ref c =>
      have hc : c ≠ a := fun e => hp [] (j :: q) rfl (by simp) (by subst e; rfl)
      simp only [follow, Heap.set_objs, if_neg hc]
      cases ho2 : h.objs c with
      | none => rfl
      | some o2 =>
        have step : ∀ xs : List Value, ∀ x, xs[j]? = some x →
            (∀ p r, q = p ++ r → r ≠ [] → follow h x p ≠ some (.ref a)) →
            (xs[j]?.bind fun x => follow (h.set a o') x q) = (xs[j]?.bind fun x => follow h x q) := by
          intro xs x hx hpx
          simp only [hx, Option.bind_some]
          exact ih x hpx
        cases o2 with
        | container ty fs =>
          cases hx : fs[j]? with
          | none => simp [hx]
          | some x =>
            refine step fs x hx fun p r hq hr => ?_
            have := hp (j :: p) r (by simp [hq]) hr
            simpa [follow, ho2, hx] using this
        | list k e l xs =>
          cases hx : xs[j]? with
          | none => simp [hx]
          | some x =>
            refine step xs x hx fun p r hq hr => ?_
            have := hp (j :: p) r (by simp [hq]) hr
            simpa [follow, ho2, hx] using this
        | _ => rfl
    | _ => rfl

end SpecLean.Encode
