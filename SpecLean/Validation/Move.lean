import SpecLean.Validation.Where
import SpecLean.Validation.Grow

/-!
# A field that gets a new list of moved items keeps `NoNewPaths`

`state.f = state.f[n:]` builds a new list that holds old items at new positions, and stores it
in a field of the root. Item `j` of the new list is item `σ j` of the old one. A path through
the new list maps to the path through the old one, so no old object gains a path (SPEC 9.2,
`NoNewPaths`). The root must have one path, and the global footprint must address the items of
the field only by `*`.
-/

namespace SpecLean.Validation.Move

open SpecLean SpecLean.Encode SpecLean.Validation.Grow SpecLean.Validation.Where

/-- The heap after `root.fx = <a new list ys>`. -/
abbrev moved (h : Heap) (r0 fx : Nat) (ty : Name) (fs : List Value) (lk : ListKind) (le : SszTy)
    (ll : Option Nat) (ys : List Value) : Heap :=
  (h.alloc (.list lk le ll ys)).2.set r0 (.container ty (fs.set fx (.ref h.next)))

/-- The root object has one path: the empty path from its argument. -/
theorem root_unique {h : Heap} {vs : List Value} {k0 r0 : Nat} {ty : Name} {fs : List Value}
    (hw : WTree h vs [⟨ty, []⟩]) (hk0 : vs[k0]? = some (.ref r0))
    (hr0 : h.objs r0 = some (.container ty fs)) {k : Nat} {p : List Nat}
    (e : at? h vs k p = some (.ref r0)) : k = k0 ∧ p = [] := by
  have e0 : at? h vs k0 [] = some (.ref r0) := by simp [at?, hk0, follow]
  exact hw k0 ⟨ty, []⟩ (by simp) (rootTy_container hk0 hr0) [] trivial r0 e0 k p e

/-- Below an old object that is not the root, the moved heap reads as the old one. -/
theorem follow_moved {h : Heap} {vs : List Value} {k0 r0 fx : Nat} {ty : Name}
    {fs : List Value} {lk : ListKind} {le : SszTy} {ll : Option Nat} {ys : List Value}
    (hwf : HeapWF h) (haw : ArgsWF h vs) (hw : WTree h vs [⟨ty, []⟩])
    (hk0 : vs[k0]? = some (.ref r0)) (hr0 : h.objs r0 = some (.container ty fs)) :
    ∀ (q : List Nat) (k : Nat) (p : List Nat) (a : Nat), at? h vs k p = some (.ref a) →
      ¬ (k = k0 ∧ p = []) →
      follow (moved h r0 fx ty fs lk le ll ys) (.ref a) q = follow h (.ref a) q
  | [], _, _, _, _, _ => by simp [follow]
  | i :: q, k, p, a, e, hne => by
    have har : a ≠ r0 := fun ha => hne (by subst ha; exact root_unique hw hk0 hr0 e)
    have hlt : a < h.next := reached_old hwf haw e
    have hobj : (moved h r0 fx ty fs lk le ll ys).objs a = h.objs a := by
      simp only [moved, Heap.set_objs, if_neg har]
      exact objs_alloc_ne (by omega)
    rw [follow_cons, follow_cons, hobj]
    cases ho : h.objs a with
    | none => rfl
    | some o =>
      simp only
      cases hi : item o i with
      | none => rfl
      | some x =>
        simp only [Option.bind_some]
        by_cases hx : ∃ c, x = .ref c
        · obtain ⟨c, rfl⟩ := hx
          have e' : at? h vs k (p ++ [i]) = some (.ref c) := by
            refine at_follow e ?_
            rw [follow_cons, ho]; simp [hi, follow]
          exact follow_moved hwf haw hw hk0 hr0 q k (p ++ [i]) c e' (by simp)
        · cases q with
          | nil => simp [follow]
          | cons j q =>
            rw [follow_nonref (fun c hc => hx ⟨c, hc⟩), follow_nonref (fun c hc => hx ⟨c, hc⟩)]

/-- The map of paths: a path into the new list goes to the item `σ j` of the old list. -/
def moveMap (k0 fx : Nat) (σ : Nat → Nat) (k : Nat) : List Nat → List Nat
  | i :: j :: rest => if k = k0 ∧ i = fx then i :: σ j :: rest else i :: j :: rest
  | q => q

theorem moveMap_of_ne {k0 fx : Nat} {σ : Nat → Nat} {k : Nat} {q : List Nat}
    (h : ¬ (k = k0 ∧ q.head? = some fx)) : moveMap k0 fx σ k q = q := by
  match q with
  | [] => rfl
  | [_] => rfl
  | i :: j :: rest =>
    simp only [moveMap]
    rw [if_neg]; simpa using h

/-- Each path of the moved heap to an old object, mapped, is a path of the old heap to it. A
path into the new list goes through an item that is a reference. -/
theorem moved_path {h : Heap} {vs : List Value} {k0 r0 fx b : Nat}
    {ty : Name} {fs : List Value} {lk : ListKind} {le : SszTy} {ll : Option Nat}
    {xs ys : List Value} {σ : Nat → Nat}
    (hwf : HeapWF h) (haw : ArgsWF h vs) (hw : WTree h vs [⟨ty, []⟩])
    (hk0 : vs[k0]? = some (.ref r0)) (hr0 : h.objs r0 = some (.container ty fs))
    (hfx : fs[fx]? = some (.ref b)) (hb : ∃ lk0 le0 ll0, h.objs b = some (.list lk0 le0 ll0 xs))
    (hys : ∀ j c, ys[j]? = some (.ref c) → xs[σ j]? = some (.ref c))
    {k : Nat} {q : List Nat} {a : Nat}
    (e : at? (moved h r0 fx ty fs lk le ll ys) vs k q = some (.ref a)) (hlt : a < h.next) :
    at? h vs k (moveMap k0 fx σ k q) = some (.ref a) ∧
      ∀ j rest, k = k0 → q = fx :: j :: rest → ∃ c, ys[j]? = some (.ref c) := by
  have hr0n : r0 < h.next := reached_old hwf haw (k := k0) (q := []) (by simp [at?, hk0, follow])
  by_cases hk : k = k0
  · have hk' := hk.symm
    subst hk'
    cases q with
    | nil =>
      simp [at?, hk0, follow] at e
      subst e
      exact ⟨by simp [moveMap, at?, hk0, follow], fun _ _ _ h => by cases h⟩
    | cons i q =>
      have hroot : (moved h r0 fx ty fs lk le ll ys).objs r0 =
          some (.container ty (fs.set fx (.ref h.next))) := by simp [moved]
      simp only [at?, hk0, Option.bind_some] at e
      rw [follow_cons, hroot] at e
      simp only [item] at e
      by_cases hi : i = fx
      · subst hi
        rw [List.getElem?_set_self (by
          cases hl : fs[i]? with
          | none => simp [hfx] at hl
          | some _ => exact (List.getElem?_eq_some_iff.1 hl).1)] at e
        simp only [Option.bind_some] at e
        cases q with
        | nil => simp [follow] at e; omega
        | cons j rest =>
          have hnew : (moved h r0 i ty fs lk le ll ys).objs h.next = some (.list lk le ll ys) := by
            simp only [moved, Heap.set_objs, if_neg (show h.next ≠ r0 by omega)]
            exact objs_alloc_self
          rw [follow_cons, hnew] at e
          simp only [item] at e
          cases hy : ys[j]? with
          | none => rw [hy] at e; cases e
          | some y =>
            rw [hy] at e
            simp only [Option.bind_some] at e
            by_cases hyr : ∃ c, y = .ref c
            · obtain ⟨c, rfl⟩ := hyr
              obtain ⟨lk0, le0, ll0, hbo⟩ := hb
              have hc : at? h vs k0 [i, σ j] = some (.ref c) := by
                simp [at?, hk0, follow, hr0, hfx, hbo, hys j c hy]
              rw [follow_moved hwf haw hw hk0 hr0 rest k0 [i, σ j] c hc (by simp)] at e
              refine ⟨?_, fun j' rest' _ hq => ⟨c, by simp at hq; rw [← hq.1]; exact hy⟩⟩
              simp only [moveMap, and_self, if_true]
              have := at_follow hc e
              simpa using this
            · cases rest with
              | nil =>
                simp [follow] at e
                exact absurd ⟨a, e⟩ hyr
              | cons _ _ => rw [follow_nonref (fun c hc => hyr ⟨c, hc⟩)] at e; cases e
      · rw [List.getElem?_set_ne (Ne.symm hi)] at e
        cases hx : fs[i]? with
        | none => rw [hx] at e; cases e
        | some x =>
          rw [hx] at e
          simp only [Option.bind_some] at e
          have hmap : moveMap k0 fx σ k0 (i :: q) = i :: q := moveMap_of_ne (by simp [hi])
          refine ⟨?_, fun j rest _ hq => absurd (List.cons.inj hq).1 hi⟩
          rw [hmap]
          by_cases hxr : ∃ c, x = .ref c
          · obtain ⟨c, rfl⟩ := hxr
            have hc : at? h vs k0 [i] = some (.ref c) := by simp [at?, hk0, follow, hr0, hx]
            rw [follow_moved hwf haw hw hk0 hr0 q k0 [i] c hc (by simp)] at e
            simpa using at_follow hc e
          · cases q with
            | nil => simp [follow] at e; exact absurd ⟨a, e⟩ hxr
            | cons _ _ => rw [follow_nonref (fun c hc => hxr ⟨c, hc⟩)] at e; cases e
  · have hmap : moveMap k0 fx σ k q = q := moveMap_of_ne (by simp [hk])
    refine ⟨?_, fun _ _ h _ => absurd h hk⟩
    rw [hmap]
    simp only [at?] at e ⊢
    cases hv : vs[k]? with
    | none => rw [hv] at e; cases e
    | some v =>
      rw [hv] at e
      simp only [Option.bind_some] at e ⊢
      by_cases hvr : ∃ c, v = .ref c
      · obtain ⟨c, rfl⟩ := hvr
        have hc : at? h vs k [] = some (.ref c) := by simp [at?, hv, follow]
        rw [follow_moved hwf haw hw hk0 hr0 q k [] c hc (by simp [hk])] at e
        exact e
      · cases q with
        | nil => simp [follow] at e; exact absurd ⟨a, e⟩ hvr
        | cons _ _ => rw [follow_nonref (fun c hc => hvr ⟨c, hc⟩)] at e; cases e

/-- SPEC 9.2: `root.fx = ys` with `ys[j]` the old item `xs[σ j]` (or a value) keeps
`NoNewPaths` over a footprint that addresses the items of `fx` only by `*`. -/
theorem noNewPaths_moved {h : Heap} {vs : List Value} {gfp : Footprint} {k0 r0 fx b : Nat}
    {ty : Name} {fs : List Value} {lk : ListKind} {le : SszTy} {ll : Option Nat}
    {xs ys : List Value} {σ : Nat → Nat}
    (hwf : HeapWF h) (haw : ArgsWF h vs) (hw : WTree h vs [⟨ty, []⟩])
    (hk0 : vs[k0]? = some (.ref r0)) (hr0 : h.objs r0 = some (.container ty fs))
    (hfx : fs[fx]? = some (.ref b)) (hb : ∃ lk0 le0 ll0, h.objs b = some (.list lk0 le0 ll0 xs))
    (hys : ∀ j c, ys[j]? = some (.ref c) → xs[σ j]? = some (.ref c))
    (hinj : ∀ j j' c c', ys[j]? = some (.ref c) → ys[j']? = some (.ref c') → σ j = σ j' → j = j')
    (hgfp : ∀ pat ∈ gfp, ∀ j rest, Matches pat.steps (fx :: j :: rest) →
      Matches pat.steps (fx :: σ j :: rest)) :
    NoNewPaths h (moved h r0 fx ty fs lk le ll ys) vs gfp := by
  refine ⟨moveMap k0 fx σ, fun k q a e hlt _ => ?_⟩
  obtain ⟨e0, hitem⟩ := moved_path hwf haw hw hk0 hr0 hfx hb hys e hlt
  refine ⟨e0, fun pat hp hm => ?_, fun k' q' e' hk hq => ?_⟩
  · match q, hm with
    | i :: j :: rest, hm =>
      simp only [moveMap]
      split
      · rename_i hc; obtain ⟨-, rfl⟩ := hc; exact hgfp pat hp j rest hm
      · exact hm
    | [], hm => exact hm
    | [_], hm => exact hm
  · have hk' := hk.symm
    subst hk'
    obtain ⟨-, hitem'⟩ := moved_path hwf haw hw hk0 hr0 hfx hb hys e' hlt
    -- Both paths moved, or neither.
    match q, q', hq with
    | i :: j :: rest, i' :: j' :: rest', hq =>
      simp only [moveMap] at hq
      by_cases hc : k = k0 ∧ i = fx
      · rw [if_pos hc] at hq
        by_cases hc' : i' = fx
        · rw [if_pos ⟨hc.1, hc'⟩] at hq
          simp only [List.cons.injEq] at hq
          obtain ⟨-, hσ, rfl⟩ := hq
          obtain ⟨c, hcj⟩ := hitem j rest' hc.1 (by rw [hc.2])
          obtain ⟨c', hcj'⟩ := hitem' j' rest' hc.1 (by rw [hc'])
          rw [hc.2, hc', hinj j' j c' c hcj' hcj hσ]
        · rw [if_neg (fun h => hc' h.2)] at hq
          simp only [List.cons.injEq] at hq
          exact absurd (hq.1.trans hc.2) hc'
      · rw [if_neg hc] at hq
        by_cases hc' : k = k0 ∧ i' = fx
        · rw [if_pos hc'] at hq
          simp only [List.cons.injEq] at hq
          exact absurd ⟨hc'.1, hq.1 ▸ hc'.2⟩ hc
        · rw [if_neg hc'] at hq; exact hq
    | [], q', hq => cases q' with
      | nil => rfl
      | cons i' t => cases t with
        | nil => simp [moveMap] at hq
        | cons j' r' => simp only [moveMap] at hq; split at hq <;> simp at hq
    | [i], q', hq => cases q' with
      | nil => simp [moveMap] at hq
      | cons i' t => cases t with
        | nil => simpa [moveMap] using hq
        | cons j' r' => simp only [moveMap] at hq; split at hq <;> simp at hq
    | i :: j :: rest, [], hq => simp only [moveMap] at hq; split at hq <;> simp at hq
    | i :: j :: rest, [i'], hq => simp only [moveMap] at hq; split at hq <;> simp at hq

/-- `root.fx = root.fx[n:n+m]`: item `j` of the new list is item `j + n` of the old one. -/
theorem noNewPaths_sliced {h : Heap} {vs : List Value} {gfp : Footprint} {k0 r0 fx b : Nat}
    {ty : Name} {fs : List Value} {lk : ListKind} {le : SszTy} {ll : Option Nat}
    {xs : List Value} {n m : Nat}
    (hwf : HeapWF h) (haw : ArgsWF h vs) (hw : WTree h vs [⟨ty, []⟩])
    (hk0 : vs[k0]? = some (.ref r0)) (hr0 : h.objs r0 = some (.container ty fs))
    (hfx : fs[fx]? = some (.ref b)) (hb : ∃ lk0 le0 ll0, h.objs b = some (.list lk0 le0 ll0 xs))
    (hgfp : ∀ pat ∈ gfp, ∀ j j' rest, Matches pat.steps (fx :: j :: rest) →
      Matches pat.steps (fx :: j' :: rest)) :
    NoNewPaths h (moved h r0 fx ty fs lk le ll ((xs.drop n).take m)) vs gfp :=
  noNewPaths_moved (σ := (· + n)) hwf haw hw hk0 hr0 hfx hb
    (fun j c hy => by
      rw [List.getElem?_take] at hy
      split at hy
      · rw [List.getElem?_drop] at hy; rw [Nat.add_comm]; exact hy
      · cases hy)
    (fun j j' _ _ _ _ e => by simpa using e)
    (fun pat hp j rest hm => hgfp pat hp j (j + n) rest hm)

end SpecLean.Validation.Move
