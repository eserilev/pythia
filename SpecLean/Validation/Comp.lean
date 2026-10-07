import SpecLean.Validation.Loop

/-!
# Generic comprehensions (SPEC 9.3)

`[elt for t in it if c1 if c2 ...]` and the generator form `(elt for t in it if ...)`, with one
generator. The interpreter iterates live, like `for` (`compItems`): each item costs one unit of
fuel, binds the target, tests the conditions, and evaluates `elt` when they hold. The target names
stay bound into the next item. The readable Lean is `ys.filterMapM f` over the readable items
`ys`, or `ys.mapM g` when there is no condition.

One item is related to `f y` (`ItemRel`): both drop the item, both keep it with related values
(`E`), or both fail with the same class. Each item proves the contract from the heap at its start
(`CContract`: `Contract` and `FreshOnce`). The lemma chains the items.

`any` and `all` over a generator stop early (`compLoop` with `stop`). They are not covered here.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Encode

/-! ## The contract with `FreshOnce` -/

/-- `FreshOnce` composes along a run whose heap only grows: an object made by the first run has
one path after it, and the second run gives it no new path. -/
theorem FreshOnce_trans {h1 h2 h3 : Heap} {vs : List Value} {gfp : Footprint}
    (f12 : Fresh h1 h2) (a : FreshOnce h1 h2 vs gfp) (n23 : NoNewPaths h2 h3 vs gfp)
    (b : FreshOnce h2 h3 vs gfp) : FreshOnce h1 h3 vs gfp := by
  intro k q k' q' c hc hat e e'
  by_cases hold : c < h2.next
  · obtain ⟨φ, hφ⟩ := n23
    have hat2 : AtPat h2 vs gfp c := by
      obtain ⟨k0, pat, hpat, q0, hm, e0⟩ := hat
      obtain ⟨e0', p0, -⟩ := hφ k0 q0 c e0 hold ⟨k0, pat, hpat, q0, hm, e0⟩
      exact ⟨k0, pat, hpat, _, p0 pat hpat hm, e0'⟩
    obtain ⟨e1, -, hinj⟩ := hφ k q c e hold hat
    obtain ⟨e2, -, -⟩ := hφ k' q' c e' hold hat
    obtain ⟨hk, hq⟩ := a k (φ k q) k' (φ k' q') c hc hat2 e1 e2
    exact ⟨hk, hinj k' q' e' hk hq⟩
  · exact b k q k' q' c (Nat.le_of_not_lt hold) hat e e'

/-- The contract of SPEC 9.2 with `FreshOnce`, for runs that may make new objects. -/
structure CContract (gfp fpf : Footprint) (vs : List Value) (h h' : Heap) : Prop where
  base : Contract gfp fpf vs h h'
  once : FreshOnce h h' vs gfp

/-- At the start of a run the arguments reach no free address, so `FreshOnce` holds. -/
theorem CContract.refl (gfp fpf : Footprint) (vs : List Value) (h : Heap) (hwf : HeapWF h)
    (haw : ArgsWF h vs) : CContract gfp fpf vs h h :=
  ⟨Contract.refl gfp fpf vs h, fun k q _ _ c hc _ e _ => absurd (hwf c hc) (haw k q c e)⟩

theorem CContract.trans {gfp fpf : Footprint} {vs : List Value} {h1 h2 h3 : Heap}
    (hsub : ∀ p ∈ fpf, p ∈ gfp) (hwf : HeapWF h1) (a : CContract gfp fpf vs h1 h2)
    (b : CContract gfp fpf vs h2 h3) : CContract gfp fpf vs h1 h3 :=
  ⟨a.base.trans hsub hwf b.base, FreshOnce_trans a.base.fresh a.once b.base.paths b.once⟩

/-! ## One item and the whole comprehension -/

/-- One item: bind the target, test the conditions, and evaluate `elt` when they hold. The
locals after the target go to the next item. -/
def compItem (env : Env) (n : Nat) (L : Locals) (h : Heap) (t : Target) (ifs : List Expr)
    (elt : Expr) (x : Value) : Res (Option Value × Locals × Heap) := do
  let (L1, h1) ← assignTarget env n L h t x
  let (keep, h2) ← evalIfs env n L1 h1 ifs
  if keep then do
    let (v, h3) ← evalExpr env n L1 h2 elt
    pure (some v, L1, h3)
  else pure (none, L1, h2)

/-- Two lists related item by item. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

/-- One item of the interpreter against `f y`. `C h'` is the contract from the heap at the start
of the item. -/
def ItemRel {β : Type} (C : Heap → Prop) (Q : Locals → Heap → Prop)
    (E : Value → β → Heap → Prop) :
    Res (Option Value × Locals × Heap) → Except Fail (Option β) → Prop
  | .ok (some v, L', h'), .ok (some b) => C h' ∧ Q L' h' ∧ E v b h'
  | .ok (none, L', h'), .ok none => C h' ∧ Q L' h'
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

/-- The result of the items: the values relate one to one to the readable list. -/
def CompOut {β : Type} (Pend : Heap → Prop) (E : Value → β → Heap → Prop) :
    Res (List Value × Bool × Heap) → Except Fail (List β) → Prop
  | .ok (vs, false, h'), .ok bs => ListRel (fun v b => E v b h') vs bs ∧ Pend h'
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

theorem compItems_step (env : Env) (m : Nat) (L : Locals) (h : Heap) (t : Target)
    (ifs : List Expr) (elt : Expr) (src : IterSrc) (i : Nat) {x : Value}
    (hx : iterItem h src i = .ok (some x)) :
    compItems env (m + 1) L h t ifs [] elt none src i = (compItem env m L h t ifs elt x >>=
      fun r => match r with
        | (o, L1, h3) => do
          let (vs2, st2, h4) ← compItems env m L1 h3 t ifs [] elt none src (i + 1)
          pure (o.toList ++ vs2, st2, h4)) := by
  rw [compItems, hx]
  unfold compItem
  simp only [Except.bind_ok']
  rcases assignTarget env m L h t x with e | ⟨L1, h1⟩
  · rfl
  · simp only [Except.bind_ok']
    rcases evalIfs env m L1 h1 ifs with e | ⟨keep, h2⟩
    · rfl
    · simp only [Except.bind_ok']
      cases keep
      · simp only [Bool.false_eq_true, ↓reduceIte, Except.pure_ok', Except.bind_ok']
        rcases compItems env m L1 h2 t ifs [] elt none src (i + 1) with e | ⟨vs2, st2, h4⟩
        · rfl
        · rfl
      · simp only [↓reduceIte, compLoop]
        rcases evalExpr env m L1 h2 elt with e | ⟨v, h3⟩
        · rfl
        · simp only [Except.bind_ok', Except.pure_ok', Bool.false_eq_true, ↓reduceIte]
          rcases compItems env m L1 h3 t ifs [] elt none src (i + 1) with e | ⟨vs2, st2, h4⟩
          · rfl
          · rfl

/-- The generic comprehension. `hitem` and `hend` say where the items end, `hstep` relates one
item to `f`, and `hE` keeps a kept value related while later items run. Fuel `n + Kf + 1` with
`ys.length - i ≤ n` is enough. -/
theorem comp_sim {α β : Type} (env : Env) (t : Target) (ifs : List Expr) (elt : Expr)
    (src : IterSrc) (Kf : Nat) (ys : List α) (f : α → Except Fail (Option β))
    (E : Value → β → Heap → Prop)
    {gfp fpf : Footprint} {vs : List Value} (hsub : ∀ p ∈ fpf, p ∈ gfp) {h0 : Heap}
    (hwf : HeapWF h0) (Q : Nat → Locals → Heap → Prop)
    (hitem : ∀ i L h, Q i L h → i < ys.length → ∃ x, iterItem h src i = .ok (some x))
    (hend : ∀ i L h, Q i L h → ys.length ≤ i → iterItem h src i = .ok none)
    (hstep : ∀ n i L h x y, Q i L h → ys[i]? = some y → iterItem h src i = .ok (some x) →
      ItemRel (CContract gfp fpf vs h) (Q (i + 1)) E (compItem env (n + Kf) L h t ifs elt x)
        (f y))
    (hE : ∀ v b h h', E v b h → CContract gfp fpf vs h h' → E v b h') :
    ∀ n i L h, Q i L h → CContract gfp fpf vs h0 h → ys.length - i ≤ n →
      CompOut (fun h' => CContract gfp fpf vs h0 h' ∧ (∀ v b, E v b h → E v b h') ∧
          ∃ j L', Q j L' h' ∧ ys.length ≤ j) E
        (compItems env (n + Kf + 1) L h t ifs [] elt none src i) ((ys.drop i).filterMapM f) := by
  intro n
  induction n with
  | zero =>
    intro i L h hq hc hn
    rw [compItems, hend i L h hq (by omega), List.drop_eq_nil_of_le (by omega)]
    exact ⟨.nil, hc, fun _ _ e => e, i, L, hq, by omega⟩
  | succ n ih =>
    intro i L h hq hc hn
    by_cases hi : i < ys.length
    · obtain ⟨x, hx⟩ := hitem i L h hq hi
      have hy : ys[i]? = some ys[i] := List.getElem?_eq_getElem hi
      have hK := hstep (n + 1) i L h x ys[i] hq hy hx
      rw [compItems_step env (n + 1 + Kf) L h t ifs elt src i hx,
        List.drop_eq_getElem_cons hi, List.filterMapM_cons]
      revert hK
      generalize compItem env (n + 1 + Kf) L h t ifs elt x = R
      generalize f ys[i] = F
      intro hK
      rcases R with e | ⟨o, L1, h3⟩ <;> rcases F with e' | o'
      · obtain ⟨he, hf⟩ := hK
        exact ⟨he, hf⟩
      · exact hK.elim
      · cases o <;> exact hK.elim
      · have ih' := ih (i + 1) L1 h3
        rw [show n + 1 + Kf = n + Kf + 1 by omega]
        cases o with
        | none =>
          cases o' with
          | some _ => exact hK.elim
          | none =>
            obtain ⟨hc', hq'⟩ := hK
            have hr := ih' hq' (hc.trans hsub hwf hc') (by omega)
            simp only [Except.bind_ok', Option.toList, List.nil_append]
            revert hr
            generalize compItems env (n + Kf + 1) L1 h3 t ifs [] elt none src (i + 1) = R2
            generalize (ys.drop (i + 1)).filterMapM f = F2
            intro hr
            rcases R2 with e | ⟨vs2, st2, h4⟩ <;> rcases F2 with e' | bs
            · exact hr
            · exact hr.elim
            · cases st2 <;> exact hr.elim
            · cases st2
              · obtain ⟨hall, hc4, ht, rest⟩ := hr
                exact ⟨hall, hc4, fun v b e => ht v b (hE v b h h3 e hc'), rest⟩
              · exact hr.elim
        | some v =>
          cases o' with
          | none => exact hK.elim
          | some b =>
            obtain ⟨hc', hq', hEv⟩ := hK
            have hr := ih' hq' (hc.trans hsub hwf hc') (by omega)
            simp only [Except.bind_ok', Option.toList, List.singleton_append]
            revert hr
            generalize compItems env (n + Kf + 1) L1 h3 t ifs [] elt none src (i + 1) = R2
            generalize (ys.drop (i + 1)).filterMapM f = F2
            intro hr
            rcases R2 with e | ⟨vs2, st2, h4⟩ <;> rcases F2 with e' | bs
            · exact hr
            · exact hr.elim
            · cases st2 <;> exact hr.elim
            · cases st2
              · obtain ⟨hall, hc4, ht, rest⟩ := hr
                exact ⟨.cons (ht v b hEv) hall, hc4, fun v b e => ht v b (hE v b h h3 e hc'), rest⟩
              · exact hr.elim
    · rw [compItems, hend i L h hq (by omega), List.drop_eq_nil_of_le (by omega)]
      exact ⟨.nil, hc, fun _ _ e => e, i, L, hq, by omega⟩

/-- A comprehension with no condition: the readable `ys.mapM g` is a `filterMapM` that keeps
every item, so `comp_sim` applies with `f y := some <$> g y`. -/
theorem mapM_eq_filterMapM {α β : Type} (g : α → Except Fail β) :
    ∀ ys : List α, ys.mapM g = ys.filterMapM (fun y => some <$> g y)
  | [] => by simp
  | y :: ys => by
    rw [List.mapM_cons, List.filterMapM_cons, mapM_eq_filterMapM g ys]
    cases g y <;> rfl

end SpecLean.Validation
