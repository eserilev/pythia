import SpecLean.Layer4.Denote
import SpecLean.DecodeLemmas

/-!
# Layer 4 spike: facts about `dec`

How a decoded tree follows the heap paths, and how it changes after a write of a flat value to
an object with one path.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

theorem flat_nonref {v : Value} (hv : Flat v = true) : ∀ b, v ≠ .ref b := by
  intro b e; subst e; simp [Flat] at hv

/-- The children of a list or a container. -/
def okids : Option HeapObj → Option (List Value)
  | some (.container _ fs) => some fs
  | some (.list _ _ _ xs) => some xs
  | _ => none

theorem follow_ref_cons (h : Heap) (a i : Nat) (p : List Nat) :
    follow h (.ref a) (i :: p) = (okids (h.objs a)).bind fun xs => xs[i]?.bind (follow h · p) := by
  simp only [follow]
  cases h.objs a with
  | none => rfl
  | some o => cases o <;> rfl

theorem dec_flat {h : Heap} {v : Value} (hv : Flat v = true) (n : Nat) :
    dec h n v = some (.leaf v) := by
  cases n <;> cases v <;> simp_all [dec, Flat]

theorem dec_zero_ref {h : Heap} {a : Nat} : dec h 0 (.ref a) = none := by
  simp [dec, Flat]

theorem dec_nonref {h : Heap} {v : Value} (hv : ∀ b, v ≠ .ref b) (n : Nat) :
    dec h n v = if Flat v then some (.leaf v) else none := by
  cases n with
  | zero => simp [dec]
  | succ m => cases v <;> first | exact absurd rfl (hv _) | simp [dec]

theorem dec_ref_succ {h : Heap} {a m : Nat} :
    dec h (m + 1) (.ref a) =
      match h.objs a with
      | some (.container ty fs) => (DV.cont ty) <$> fs.mapM (dec h m)
      | some (.list k e l xs) => (DV.list k e l) <$> xs.mapM (dec h m)
      | _ => none := by
  rfl

theorem dec_leaf {h : Heap} {n : Nat} {v u : Value} (hd : dec h n v = some (.leaf u)) :
    v = u ∧ Flat u = true := by
  by_cases hr : ∃ b, v = .ref b
  · obtain ⟨b, rfl⟩ := hr
    cases n with
    | zero => simp [dec_zero_ref] at hd
    | succ m =>
      rw [dec_ref_succ] at hd
      split at hd <;> simp_all
  · rw [dec_nonref (fun b e => hr ⟨b, e⟩)] at hd
    split at hd <;> simp_all

/-- A node decodes from a reference to an object with the same children. -/
theorem dec_node {h : Heap} {n : Nat} {v : Value} {d : DV} (hd : dec h n v = some d)
    (hn : ∀ u, d ≠ .leaf u) :
    ∃ a m xs, v = .ref a ∧ n = m + 1 ∧ okids (h.objs a) = some xs ∧
      xs.mapM (dec h m) = some d.kids := by
  by_cases hr : ∃ b, v = .ref b
  · obtain ⟨a, rfl⟩ := hr
    cases n with
    | zero => simp [dec_zero_ref] at hd
    | succ m =>
      rw [dec_ref_succ] at hd
      refine ⟨a, m, ?_⟩
      split at hd
      · rename_i ty fs ho
        cases hm : fs.mapM (dec h m) with
        | none => simp [hm] at hd
        | some ds => simp [hm] at hd; subst hd; exact ⟨fs, rfl, rfl, by simp [okids, ho], by simp [DV.kids, hm]⟩
      · rename_i k e l xs ho
        cases hm : xs.mapM (dec h m) with
        | none => simp [hm] at hd
        | some ds => simp [hm] at hd; subst hd; exact ⟨xs, rfl, rfl, by simp [okids, ho], by simp [DV.kids, hm]⟩
      · simp at hd
  · rw [dec_nonref (fun b e => hr ⟨b, e⟩)] at hd
    split at hd
    · simp at hd; exact absurd hd.symm (hn v)
    · simp at hd

theorem dec_cont {h : Heap} {n : Nat} {v : Value} {ty : Name} {ds : List DV}
    (hd : dec h n v = some (.cont ty ds)) :
    ∃ a m fs, v = .ref a ∧ n = m + 1 ∧ h.objs a = some (.container ty fs) ∧
      fs.mapM (dec h m) = some ds := by
  obtain ⟨a, m, -, rfl, rfl, -, -⟩ := dec_node hd (fun _ e => by cases e)
  rw [dec_ref_succ] at hd
  refine ⟨a, m, ?_⟩
  split at hd
  · rename_i ty' fs ho
    cases hm : fs.mapM (dec h m) with
    | none => simp [hm] at hd
    | some ds' => simp [hm] at hd; obtain ⟨rfl, rfl⟩ := hd; exact ⟨fs, rfl, rfl, ho, hm⟩
  · rename_i k e l xs ho
    cases hm : xs.mapM (dec h m) with
    | none => simp [hm] at hd
    | some ds' => simp [hm] at hd
  · simp at hd

theorem dec_list {h : Heap} {n : Nat} {v : Value} {k : ListKind} {e : SszTy} {l : Option Nat}
    {ds : List DV} (hd : dec h n v = some (.list k e l ds)) :
    ∃ a m xs, v = .ref a ∧ n = m + 1 ∧ h.objs a = some (.list k e l xs) ∧
      xs.mapM (dec h m) = some ds := by
  obtain ⟨a, m, -, rfl, rfl, -, -⟩ := dec_node hd (fun _ e => by cases e)
  rw [dec_ref_succ] at hd
  refine ⟨a, m, ?_⟩
  split at hd
  · rename_i ty' fs ho
    cases hm : fs.mapM (dec h m) with
    | none => simp [hm] at hd
    | some ds' => simp [hm] at hd
  · rename_i k' e' l' xs ho
    cases hm : xs.mapM (dec h m) with
    | none => simp [hm] at hd
    | some ds' =>
      simp [hm] at hd; obtain ⟨rfl, rfl, rfl, rfl⟩ := hd; exact ⟨xs, rfl, rfl, ho, hm⟩
  · simp at hd

/-- Element `i` of two lists related by `mapM`. -/
theorem mapM_get {f : α → Option β} {xs : List α} {ys : List β} (hm : xs.mapM f = some ys)
    {i : Nat} {y : β} (hy : ys[i]? = some y) : ∃ x, xs[i]? = some x ∧ f x = some y := by
  obtain ⟨hl, hp⟩ := (mapM_some_iff xs ys).mp hm
  cases hx : xs[i]? with
  | none =>
    have := (List.getElem?_eq_some_iff.mp hy).1
    rw [List.getElem?_eq_none_iff] at hx; omega
  | some x => exact ⟨x, rfl, by rw [hp i x hx, hy]⟩

theorem mapM_get' {f : α → Option β} {xs : List α} {ys : List β} (hm : xs.mapM f = some ys)
    {i : Nat} {x : α} (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ f x = some y := by
  obtain ⟨hl, hp⟩ := (mapM_some_iff xs ys).mp hm
  have := hp i x hx
  cases hy : ys[i]? with
  | none => rw [hy] at this; exact absurd this (by
      intro e; have := (List.getElem?_eq_some_iff.mp hx).1
      rw [List.getElem?_eq_none_iff] at hy; omega)
  | some y => exact ⟨y, rfl, by rw [this, hy]⟩

/-- The subtree at a heap path. -/
theorem dec_sub {h : Heap} :
    ∀ (p : List Nat) (n : Nat) (v w : Value) (d : DV), dec h n v = some d →
      follow h v p = some w → ∃ m d', subAt p d = some d' ∧ dec h m w = some d'
  | [], n, v, w, d, hd, hf => by
    simp [follow] at hf; subst hf; exact ⟨n, d, rfl, hd⟩
  | i :: p, n, v, w, d, hd, hf => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨a, rfl⟩ := hr
      by_cases hl : ∃ u, d = .leaf u
      · obtain ⟨u, rfl⟩ := hl
        obtain ⟨e, hfl⟩ := dec_leaf hd; subst e; simp [Flat] at hfl
      · obtain ⟨a', m, xs, e, rfl, hk, hm⟩ := dec_node hd (fun u e => hl ⟨u, e⟩)
        cases e
        rw [follow_ref_cons, hk] at hf
        simp only [Option.bind_some] at hf
        cases hx : xs[i]? with
        | none => simp [hx] at hf
        | some x =>
          simp only [hx, Option.bind_some] at hf
          obtain ⟨c, hc, hdc⟩ := mapM_get' hm hx
          obtain ⟨m', d', h1, h2⟩ := dec_sub p m x w c hdc hf
          exact ⟨m', d', by simp [subAt, hc, h1], h2⟩
    · rw [follow_nonref (fun b e => hr ⟨b, e⟩)] at hf; cases hf

/-- A write to an object that `v` does not reach leaves the decoding of `v`. -/
theorem dec_away {h : Heap} {a : Nat} (o' : HeapObj) :
    ∀ (n : Nat) (v : Value), (∀ q, follow h v q ≠ some (.ref a)) →
      dec (h.set a o') n v = dec h n v
  | 0, v, _ => by cases v <;> rfl
  | m + 1, v, hv => by
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      have hb : b ≠ a := fun e => hv [] (by simp [follow, e])
      rw [dec_ref_succ, dec_ref_succ, Heap.set_objs, if_neg hb]
      have hc : ∀ xs, okids (h.objs b) = some xs → ∀ (i : Nat) x, xs[i]? = some x →
          dec (h.set a o') m x = dec h m x := by
        intro xs hk i x hx
        refine dec_away o' m x fun q e => hv (i :: q) ?_
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

def _root_.SpecLean.HeapObj.setChild : HeapObj → Nat → Value → HeapObj
  | .container ty fs, i, v => .container ty (fs.set i v)
  | .list k e l xs, i, v => .list k e l (xs.set i v)
  | o, _, _ => o

theorem set_self_of_get {xs : List α} {j : Nat} {x : α} (hx : xs[j]? = some x) :
    xs.set j x = xs := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_set]
  split
  · next hji =>
    subst hji
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hx
    simp [hlt, he]
  · rfl

/-- `mapM` over a list with one element replaced. -/
theorem mapM_set_congr {f g : α → Option β} {xs : List α} {ys : List β}
    (hm : xs.mapM f = some ys) (i : Nat) (x' : α) (y' : β) (hx' : g x' = some y')
    (hj : ∀ (j : Nat) x, j ≠ i → xs[j]? = some x → g x = f x) :
    (xs.set i x').mapM g = some (ys.set i y') := by
  obtain ⟨hl, hp⟩ := (mapM_some_iff xs ys).mp hm
  refine (mapM_some_iff _ _).mpr ⟨by simp [hl], fun j z hz => ?_⟩
  rw [List.getElem?_set] at hz ⊢
  by_cases hij : i = j
  · subst hij
    by_cases hlt : i < xs.length
    · simp [hlt] at hz; subst hz; simp [hl, hlt, hx']
    · simp [hlt] at hz
  · simp only [hij, if_false] at hz ⊢
    rw [hj j z (Ne.symm hij) hz]; exact hp j z hz

/-- A write of a flat value as child `i` of the object `a`, which `v` reaches at exactly the
path `p`, changes the decoding of `v` at that child. -/
theorem dec_at {h : Heap} {a : Nat} {o : HeapObj} (ho : h.objs a = some o) (i : Nat) {u : Value}
    (hu : Flat u = true) :
    ∀ (p : List Nat) (n : Nat) (v : Value) (d : DV), dec h n v = some d →
      (∀ q, follow h v q = some (.ref a) ↔ q = p) →
      dec (h.set a (o.setChild i u)) n v = some (updAt p d i (.leaf u))
  | [], n, v, d, hd, hp => by
    have hv : v = .ref a := by simpa [follow] using (hp []).mpr rfl
    subst hv
    have away : ∀ xs, okids (h.objs a) = some xs → ∀ (j : Nat) x, xs[j]? = some x →
        dec (h.set a (o.setChild i u)) (n - 1) x = dec h (n - 1) x := by
      intro xs hk j x hx
      refine dec_away _ _ x fun q e => ?_
      have := (hp (j :: q)).mp (by rw [follow_ref_cons, hk]; simp [hx, e])
      cases this
    cases n with
    | zero => simp [dec_zero_ref] at hd
    | succ m =>
      simp only [Nat.add_sub_cancel] at away
      rw [dec_ref_succ, ho] at hd
      rw [dec_ref_succ, Heap.set_objs, if_pos rfl]
      cases o with
      | container ty fs =>
        cases hm : fs.mapM (dec h m) with
        | none => simp [hm] at hd
        | some ds =>
          simp [hm] at hd; subst hd
          simp only [HeapObj.setChild, updAt] at away ⊢
          rw [mapM_set_congr hm i u (.leaf u) (dec_flat hu m)
            (fun j x _ hx => away fs (by simp [okids, ho]) j x hx)]
          rfl
      | list k e l xs =>
        cases hm : xs.mapM (dec h m) with
        | none => simp [hm] at hd
        | some ds =>
          simp [hm] at hd; subst hd
          simp only [HeapObj.setChild, updAt] at away ⊢
          rw [mapM_set_congr hm i u (.leaf u) (dec_flat hu m)
            (fun j x _ hx => away xs (by simp [okids, ho]) j x hx)]
          rfl
      | _ => simp at hd
  | j :: p, n, v, d, hd, hp => by
    have hf := (hp (j :: p)).mpr rfl
    by_cases hr : ∃ b, v = .ref b
    · obtain ⟨b, rfl⟩ := hr
      have hb : b ≠ a := fun e => by
        subst e; have := (hp []).mp (by simp [follow]); cases this
      cases n with
      | zero => simp [dec_zero_ref] at hd
      | succ m =>
        rw [follow_ref_cons] at hf
        have kid : ∀ xs, okids (h.objs b) = some xs →
            (∀ (j' : Nat) x, j' ≠ j → xs[j']? = some x →
              dec (h.set a (o.setChild i u)) m x = dec h m x) ∧
            (∀ x, xs[j]? = some x → ∀ c, dec h m x = some c →
              dec (h.set a (o.setChild i u)) m x = some (updAt p c i (.leaf u))) := by
          intro xs hk
          refine ⟨fun j' x hne hx => dec_away _ _ x fun q e => ?_, fun x hx c hc => ?_⟩
          · have := (hp (j' :: q)).mp (by rw [follow_ref_cons, hk]; simp [hx, e])
            simp at this; exact hne this.1
          · refine dec_at ho i hu p m x c hc fun q => ⟨fun e => ?_, fun e => ?_⟩
            · have := (hp (j :: q)).mp (by rw [follow_ref_cons, hk]; simp [hx, e])
              simpa using this
            · subst e; rw [hk] at hf; simpa [hx] using hf
        rw [dec_ref_succ] at hd
        rw [dec_ref_succ, Heap.set_objs, if_neg hb]
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
                obtain ⟨c, hc, hdc⟩ := mapM_get' hm hx
                simp only [updAt, hc]
                have := mapM_set_congr hm j x _ (k2 x hx c hdc) k1
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
                obtain ⟨c, hc, hdc⟩ := mapM_get' hm hx
                simp only [updAt, hc]
                have := mapM_set_congr hm j x _ (k2 x hx c hdc) k1
                rw [set_self_of_get hx] at this
                simp [this]
          | _ => simp at hd
    · rw [follow_nonref (fun b e => hr ⟨b, e⟩)] at hf; cases hf

end SpecLean.Layer4
