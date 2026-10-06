import SpecLean.Lemmas
import SpecLean.Rd.Prelude

/-!
# The primitives on both sides (SPEC 4.4)

The interpreter and the readable Lean run each primitive of `Prim.lean` with their own item
operation. Two kinds of lemma connect them.

- Builtin lemmas: the interpreter builtin is the primitive on the interpreter's items, for
  example `applyBuiltin_sum`. Some builtins are written out because existing proofs unfold
  them. For those, an equation gives the primitive (`pickBest_eq_prim`, `fromLE_eq_prim`,
  `lslice_eq_prim`).
- Relation lemmas: if the items relate one to one (`ListR R`) and the item operations agree, the
  two runs of the primitive agree (`sum_rel`, `pick_rel`, `any_rel`, `all_rel`, `sortBy_rel`,
  `dedupBy_rel`). The tactic and layer 4 call these, so a proof about a builtin reduces to one
  fact about one item operation.
-/

namespace SpecLean.PrimRel

open SpecLean SpecLean.Rd

/-! ## Relations -/

/-- Two lists related item by item. -/
inductive ListR {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListR R [] []
  | cons {a b as bs} : R a b → ListR R as bs → ListR R (a :: as) (b :: bs)

/-- An interpreter result against a readable result: related values, or errors of one class
that are not `outOfFuel`. -/
def ResRel {α β : Type} (R : α → β → Prop) : Res α → SpecM β → Prop
  | .ok a, .ok b => R a b
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

theorem ResRel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Res α}
    {y : SpecM β} {f : α → Res γ} {g : β → SpecM δ} (hxy : ResRel R x y)
    (hfg : ∀ a b, R a b → ResRel S (f a) (g b)) : ResRel S (x >>= f) (y >>= g) := by
  rcases x with e | a <;> rcases y with e' | b
  · exact hxy
  · exact hxy.elim
  · exact hxy.elim
  · exact hfg a b hxy

/-! ## Relation lemmas -/

variable {α β : Type} {R : α → β → Prop}

/-- `sum`: an addition that agrees on related items gives related sums. -/
theorem sum_rel {add : α → α → Res α} {add' : β → β → SpecM β}
    (hadd : ∀ a b a' b', R a a' → R b b' → ResRel R (add a b) (add' a' b')) :
    ∀ {s : α} {s' : β} {xs : List α} {ys : List β}, R s s' → ListR R xs ys →
      ResRel R (Prim.sum add s xs) (Prim.sum add' s' ys)
  | _, _, _, _, hs, .nil => hs
  | _, _, _, _, hs, .cons hxy hrest => by
    simp only [Prim.sum, List.foldlM_cons]
    exact ResRel.bind (hadd _ _ _ _ hs hxy) fun _ _ h => sum_rel hadd h hrest

/-- `any` and `all`: a truth test that agrees on related items gives one answer. -/
theorem any_rel {p : α → Res Bool} {p' : β → SpecM Bool}
    (hp : ∀ a b, R a b → ResRel Eq (p a) (p' b)) :
    ∀ {xs : List α} {ys : List β}, ListR R xs ys → ResRel Eq (Prim.any p xs) (Prim.any p' ys)
  | _, _, .nil => rfl
  | _, _, .cons hxy hrest => by
    simp only [Prim.any, List.anyM_cons]
    refine ResRel.bind (hp _ _ hxy) fun a b hab => ?_
    subst hab
    cases a
    · exact any_rel hp hrest
    · rfl

theorem all_rel {p : α → Res Bool} {p' : β → SpecM Bool}
    (hp : ∀ a b, R a b → ResRel Eq (p a) (p' b)) :
    ∀ {xs : List α} {ys : List β}, ListR R xs ys → ResRel Eq (Prim.all p xs) (Prim.all p' ys)
  | _, _, .nil => rfl
  | _, _, .cons hxy hrest => by
    simp only [Prim.all, List.allM_cons]
    refine ResRel.bind (hp _ _ hxy) fun a b hab => ?_
    subst hab
    cases a
    · rfl
    · exact all_rel hp hrest

/-- `min` and `max`: a comparison that agrees on related items picks related items. -/
theorem pick_rel {better : α → α → Res Bool} {better' : β → β → SpecM Bool}
    (hb : ∀ a b a' b', R a a' → R b b' → ResRel Eq (better a b) (better' a' b')) :
    ∀ {best : α} {best' : β} {xs : List α} {ys : List β}, R best best' → ListR R xs ys →
      ResRel R (Prim.pick better best xs) (Prim.pick better' best' ys)
  | _, _, _, _, hbest, .nil => hbest
  | best, best', _, _, hbest, .cons (a := x) (b := y) hxy hrest => by
    simp only [Prim.pick]
    refine ResRel.bind (hb _ _ _ _ hxy hbest) fun c c' hc => ?_
    subst hc
    refine pick_rel hb ?_ hrest
    cases c
    · exact hbest
    · exact hxy

/-- One insertion of `sorted`, for keys and items that relate. -/
theorem insertLast_rel {κ κ' : Type} {K : κ → κ' → Prop} {lt : κ → κ → Res Bool}
    {lt' : κ' → κ' → SpecM Bool}
    (hlt : ∀ a b a' b', K a a' → K b b' → ResRel Eq (lt a b) (lt' a' b')) (rev : Bool)
    {k : κ} {k' : κ'} {x : α} {y : β} (hk : K k k') (hxy : R x y) :
    ∀ {ps : List (κ × α)} {qs : List (κ' × β)},
      ListR (fun p q => K p.1 q.1 ∧ R p.2 q.2) ps qs →
      ResRel (ListR (fun p q => K p.1 q.1 ∧ R p.2 q.2))
        (Prim.insertLast lt rev k x ps) (Prim.insertLast lt' rev k' y qs)
  | _, _, .nil => .cons ⟨hk, hxy⟩ .nil
  | (k1, x1) :: ps, (k1', y1) :: qs, .cons hp hrest => by
    have tail : ∀ c : Bool,
        ResRel (ListR (fun p q => K p.1 q.1 ∧ R p.2 q.2))
          (if c then pure ((k, x) :: (k1, x1) :: ps) else do
            pure ((k1, x1) :: (← Prim.insertLast lt rev k x ps)))
          (if c then pure ((k', y) :: (k1', y1) :: qs) else do
            pure ((k1', y1) :: (← Prim.insertLast lt' rev k' y qs))) := by
      intro c
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ResRel.bind (insertLast_rel hlt rev hk hxy hrest) fun _ _ h => .cons hp h
      · exact .cons ⟨hk, hxy⟩ (.cons hp hrest)
    cases rev
    · simp only [Prim.insertLast, Bool.false_eq_true, ↓reduceIte]
      exact ResRel.bind (hlt _ _ _ _ hk hp.1) fun c c' e => by subst e; exact tail c
    · simp only [Prim.insertLast, ↓reduceIte]
      exact ResRel.bind (hlt _ _ _ _ hp.1 hk) fun c c' e => by subst e; exact tail c

/-- `sorted`: a `<` that agrees on related keys sorts related items in one order. -/
theorem sortBy_rel {κ κ' : Type} {K : κ → κ' → Prop} {lt : κ → κ → Res Bool}
    {lt' : κ' → κ' → SpecM Bool}
    (hlt : ∀ a b a' b', K a a' → K b b' → ResRel Eq (lt a b) (lt' a' b')) (rev : Bool)
    {ps : List (κ × α)} {qs : List (κ' × β)}
    (hpq : ListR (fun p q => K p.1 q.1 ∧ R p.2 q.2) ps qs) :
    ResRel (ListR R) (Prim.sortBy lt rev ps) (Prim.sortBy lt' rev qs) := by
  simp only [Prim.sortBy]
  have hfold : ∀ {ps : List (κ × α)} {qs : List (κ' × β)}
      {acc : List (κ × α)} {acc' : List (κ' × β)},
      ListR (fun p q => K p.1 q.1 ∧ R p.2 q.2) ps qs →
      ListR (fun p q => K p.1 q.1 ∧ R p.2 q.2) acc acc' →
      ResRel (ListR (fun p q => K p.1 q.1 ∧ R p.2 q.2))
        (ps.foldlM (fun acc p => Prim.insertLast lt rev p.1 p.2 acc) acc)
        (qs.foldlM (fun acc p => Prim.insertLast lt' rev p.1 p.2 acc) acc') := by
    intro ps qs acc acc' hpq hacc
    induction hpq generalizing acc acc' with
    | nil => exact hacc
    | cons hp _ ih =>
      simp only [List.foldlM_cons]
      exact ResRel.bind (insertLast_rel hlt rev hp.1 hp.2 hacc) fun _ _ h => ih h
  refine ResRel.bind (hfold hpq .nil) fun acc acc' h => ?_
  show ListR R (acc.map (·.2)) (acc'.map (·.2))
  induction h with
  | nil => exact .nil
  | cons hp _ ih => exact .cons hp.2 ih

/-- `set`: a membership test that agrees on related lists keeps related items. -/
theorem dedupBy_rel {mem : α → List α → Res Bool} {mem' : β → List β → SpecM Bool}
    (hmem : ∀ a b acc acc', R a b → ListR R acc acc' → ResRel Eq (mem a acc) (mem' b acc')) :
    ∀ {acc : List α} {acc' : List β} {xs : List α} {ys : List β}, ListR R acc acc' →
      ListR R xs ys → ResRel (ListR R) (Prim.dedupBy mem acc xs) (Prim.dedupBy mem' acc' ys)
  | _, _, _, _, hacc, .nil => hacc
  | acc, acc', _, _, hacc, .cons (a := x) (b := y) hxy hrest => by
    simp only [Prim.dedupBy]
    refine ResRel.bind (hmem _ _ _ _ hxy hacc) fun c c' e => ?_
    subst e
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have happ : ListR R (acc ++ [x]) (acc' ++ [y]) := by
        clear hrest
        induction hacc with
        | nil => exact .cons hxy .nil
        | cons h _ ih => exact .cons h ih
      exact dedupBy_rel hmem happ hrest
    · exact dedupBy_rel hmem hacc hrest

/-! ## Builtin lemmas -/

/-- `sum(xs, start)` in the interpreter is the primitive on its values. -/
theorem applyBuiltin_sum (env : Env) (h : Heap) (v start : Value) (xs : List Value)
    (hb : LibModel.builtin env h .sum [v, start] [] = none) (hx : iterElems h v = .ok xs) :
    applyBuiltin env h .sum [v, start] [] =
      (do let r ← Prim.sum (binopVal .add) start xs; pure (r, h)) := by
  simp only [applyBuiltin, hb, hx, Except.bind_ok', List.headD_cons, Prim.sum]

/-- `any(xs)` in the interpreter is the primitive with Python's truth. -/
theorem applyBuiltin_any (env : Env) (h : Heap) (v : Value) (xs : List Value)
    (hb : LibModel.builtin env h .any [v] [] = none) (hx : iterElems h v = .ok xs) :
    applyBuiltin env h .any [v] [] = (do let r ← Prim.any (truthyH h) xs; pure (.bool r, h)) := by
  simp only [applyBuiltin, hb, hx, Except.bind_ok']

theorem applyBuiltin_all (env : Env) (h : Heap) (v : Value) (xs : List Value)
    (hb : LibModel.builtin env h .all [v] [] = none) (hx : iterElems h v = .ok xs) :
    applyBuiltin env h .all [v] [] = (do let r ← Prim.all (truthyH h) xs; pure (.bool r, h)) := by
  simp only [applyBuiltin, hb, hx, Except.bind_ok']

/-- `min(xs)` is the primitive with Python's `<`. -/
theorem applyBuiltin_min (env : Env) (h : Heap) (v x : Value) (xs : List Value)
    (hb : LibModel.builtin env h .min [v] [] = none) (hx : iterElems h v = .ok (x :: xs)) :
    applyBuiltin env h .min [v] [] =
      (do let r ← Prim.pick (fun a b => cmpVal .lt a b) x xs; pure (r, h)) := by
  have e := pickBest_eq_prim false x xs
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  simp only [applyBuiltin, hb, hx, Except.bind_ok', e]

theorem applyBuiltin_max (env : Env) (h : Heap) (v x : Value) (xs : List Value)
    (hb : LibModel.builtin env h .max [v] [] = none) (hx : iterElems h v = .ok (x :: xs)) :
    applyBuiltin env h .max [v] [] =
      (do let r ← Prim.pick (fun a b => cmpVal .gt a b) x xs; pure (r, h)) := by
  have e := pickBest_eq_prim true x xs
  simp only [↓reduceIte] at e
  simp only [applyBuiltin, hb, hx, Except.bind_ok', e]

/-- `sorted(xs)` is the primitive with Python's `<`, then a new Python list. -/
theorem applyBuiltin_sorted (env : Env) (h : Heap) (v : Value) (xs : List Value)
    (hb : LibModel.builtin env h .sorted [v] [] = none) (hx : iterElems h v = .ok xs) :
    applyBuiltin env h .sorted [v] [] =
      (do let ys ← Prim.sortBy (cmpVal .lt) false (xs.map fun x => (x, x)); pure (allocPyList h ys)) := by
  simp only [applyBuiltin, hb, hx, Except.bind_ok', kwArg, List.lookup, stableSort]

/-- The interpreter's `set` is the primitive with Python's `in` for sets. -/
theorem dedupe_eq_prim (h : Heap) : ∀ (acc xs : List Value),
    dedupe h acc xs = Prim.dedupBy (fun x acc => do pure (← findKey h x acc).isSome) acc xs
  | acc, [] => rfl
  | acc, x :: xs => by
    simp only [dedupe, Prim.dedupBy]
    cases findKey h x acc with
    | error => rfl
    | ok o =>
      simp only [Except.bind_ok', Except.pure_ok']
      cases o.isSome
      · exact dedupe_eq_prim h _ xs
      · exact dedupe_eq_prim h _ xs

/-- `set(xs)` is the primitive with Python's `in` for sets, then a new set. -/
theorem applyBuiltin_set (env : Env) (h : Heap) (v : Value) (xs : List Value)
    (hb : LibModel.builtin env h .set [v] [] = none) (hx : iterElems h v = .ok xs) :
    applyBuiltin env h .set [v] [] = (do
      let ys ← Prim.dedupBy (fun x acc => do pure (← findKey h x acc).isSome) [] xs
      let (a, h1) := h.alloc (.set ys)
      pure (.ref a, h1)) := by
  simp only [applyBuiltin, hb, hx, Except.bind_ok', dedupe_eq_prim]

/-- `ssz_serialize` of a uint or a `Boolean` is the primitive. -/
theorem sszSerialize_uint (env : Env) (h : Heap) (t : UintTy) (n : Nat) :
    LibModel.builtin env h .sszSerialize [.uint t n] [] =
      some (.ok (.bytes env.bytesName (Prim.serializeUint n (t.bits / 8)), h)) := rfl

theorem sszSerialize_boolean (env : Env) (h : Heap) (b : Bool) :
    LibModel.builtin env h .sszSerialize [.boolean b] [] =
      some (.ok (.bytes env.bytesName (Prim.serializeBool b), h)) := rfl

/-- `int.from_bytes` is the primitive. -/
theorem fromBytes_prim (env : Env) (bs : List UInt8) (c : Name) (e : String) :
    fromBytes env [.bytes c bs, .str e] =
      .ok (.int (if e = env.nm.little then Prim.fromBytesLE bs else Prim.fromBytesBE bs)) := by
  simp only [fromBytes]; split <;> rfl

/-! ## Builtins written out -/

/-- `int.from_bytes(b, "little")` of the readable Lean is the primitive. -/
theorem fromLE_eq_prim (b : Bytes) : fromLE b = (Prim.fromBytesLE b : Int) := by
  simp only [fromLE, Prim.fromBytesLE]
  congr 1
  induction b with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, ih]; omega

/-- `xs[lo:hi]` of the readable Lean is the primitive. -/
theorem lslice_eq_prim {γ : Type} (xs : List γ) (lo hi : Option Int) :
    lslice xs lo hi = Prim.slice xs lo hi := by
  have hb : (sliceBound' : Nat → Int → Nat) = sliceBound := by
    funext n i; simp only [sliceBound', sliceBound]
  simp only [lslice, Prim.slice, Prim.sliceAt, hb, List.extract]

/-- The readable `sum` of uints is the primitive with the checked addition. -/
theorem sumU_eq_prim {γ : Type} [UintC γ] (start : γ) (xs : List γ) :
    sumU start xs = Prim.sum (fun acc x => uOp .add (uv acc) (uv x)) start xs := rfl

/-- The readable `set` is the primitive on `Id`. -/
theorem dedup_eq_prim {γ : Type} [BEq γ] (xs : List γ) :
    dedup xs = Id.run (Prim.dedupBy (fun x acc => pure (acc.contains x)) [] xs) := by
  suffices ∀ acc : List γ, xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc =
      Id.run (Prim.dedupBy (fun x acc => pure (acc.contains x)) acc xs) from this []
  induction xs with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, Prim.dedupBy]
    cases acc.contains x <;> simp [ih]

/-- The readable `min` is the primitive on `Id`. -/
theorem pyMin_eq_prim {γ : Type} [PyOrd γ] (x : γ) (xs : List γ) :
    pyMin (x :: xs) = pure (Id.run (Prim.pick (fun y b => pure (PyOrd.lt y b)) x xs)) := rfl

theorem pyMax_eq_prim {γ : Type} [PyOrd γ] (x : γ) (xs : List γ) :
    pyMax (x :: xs) = pure (Id.run (Prim.pick (fun y b => pure (PyOrd.lt b y)) x xs)) := rfl

end SpecLean.PrimRel
