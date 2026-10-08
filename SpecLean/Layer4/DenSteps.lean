import SpecLean.Layer4.Den
import SpecLean.Layer4.Steps

/-!
# Layer 4: evaluation steps for the denotation with calls

Generic step lemmas, as in `Steps.lean`. A proof about a real function rewrites with them and
leaves `binopVal` and the constructors folded, so `simp` never unfolds a value rule.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

theorem dBinop_eval {op : BinOp} {x y v : Value} (h : binopVal op x y = .ok v)
    (hf : Flat v = true) : dBinop op (.val x) (.val y) = some (.ok (.val v)) := by
  simp [dBinop, h, DM.bind, lift_ok, hf, DM.ok]

theorem dBinop_err {op : BinOp} {x y : Value} {e : SpecError} (h : binopVal op x y = .error e)
    (he : e ≠ .outOfFuel) : dBinop op (.val x) (.val y) = some (.error e) := by
  simp [dBinop, h, DM.bind, lift_err e he]

theorem dCtor_eval {env : Env} {t : SszTy} {rs : List DRes} {vs : List Value} {v : Value}
    (hc : ctorFlat t = true) (hv : allVals rs = some vs)
    (h : LibModel.construct env Heap.empty t vs [] = .ok (v, Heap.empty)) (hf : Flat v = true) :
    dCtor env t rs = some (.ok (.val v)) := by
  simp [dCtor, hc, hv, h, DM.bind, lift_ok, hf, DM.ok]

theorem cmpF_eval {op : CmpOp} {x y : Value} {b : Bool} (h : cmpVal op x y = .ok b)
    (hop : op = .lt ∨ op = .ltE ∨ op = .gt ∨ op = .gtE) : cmpF op x y = some (.ok b) := by
  rcases hop with rfl | rfl | rfl | rfl <;> simp [cmpF, h, lift_ok]

theorem truthy_lift {v : Value} {b : Bool} (h : truthy v = .ok b) :
    lift (truthy v) = some (.ok b) := by rw [h]; rfl

/-! ## Statements, one at a time -/

theorem blockOf_ok {stmt : DSt → Stmt → DM (DOut × DSt)} {s s1 : DSt} {st : Stmt}
    {ss : List Stmt} (h : stmt s st = some (.ok (.normal, s1))) :
    blockOf stmt s (st :: ss) = blockOf stmt s1 ss := by
  simp [blockOf, h, DM.bind]

theorem blockOf_err {stmt : DSt → Stmt → DM (DOut × DSt)} {s : DSt} {st : Stmt}
    {ss : List Stmt} {e : SpecError} (h : stmt s st = some (.error e)) :
    blockOf stmt s (st :: ss) = some (.error e) := by
  simp [blockOf, h, DM.bind]

theorem blockOf_nil {stmt : DSt → Stmt → DM (DOut × DSt)} {s : DSt} :
    blockOf stmt s [] = some (.ok (.normal, s)) := rfl

/-- A last statement that ends normally or with an error is the block. -/
theorem blockOf_one {stmt : DSt → Stmt → DM (DOut × DSt)} {s : DSt} {st : Stmt}
    {r : Res (DOut × DSt)} (h : stmt s st = some r)
    (hr : ∀ o s', r = .ok (o, s') → o = .normal) : blockOf stmt s [st] = some r := by
  rcases r with e | ⟨o, s'⟩
  · simp [blockOf, h, DM.bind]
  · obtain rfl := hr o s' rfl
    simp [blockOf, h, DM.bind, DM.ok]

/-- A call in a statement that writes nothing is the expression. -/
theorem allKw_of_argsOf {ev : Expr → DM DRes} :
    ∀ (args : List Arg) (r : Res (List DRes)), argsOf ev args = some r → allKw args = false
  | [], _, _ => rfl
  | .pos _ :: _, _, _ => rfl
  | .starred _ :: _, _, h => by simp [argsOf] at h
  | .kw _ _ :: _, _, h => by simp [argsOf] at h

theorem call_ro {env : Env} {fps : Name → Footprint} {n : Nat} {P : Sem} {fp : Footprint}
    {s : DSt} {e : Expr}
    (h : ∀ g args, callHead env s e = some (g, args) →
      (fps g).isEmpty = true ∨ ∃ t, env.globals.lookup g = some (.type t))
    (hap : appendOf env e = none) :
    callStep env fps n P fp s e = (exprStep env fps n P fp s e).map (·.map (·, s.roots)) := by
  unfold callStep
  simp only [hap]
  split
  · next m g args hch =>
    obtain hro := h g args hch
    obtain ⟨l, l', rfl, -, -⟩ : ∃ l l', e = .call l (.name l' g) args ∧ True ∧ True := by
      unfold callHead at hch
      split at hch
      · next l l' g' args' => split at hch <;> simp at hch; obtain ⟨rfl, rfl⟩ := hch; exact ⟨l, l', rfl, trivial, trivial⟩
      · cases hch
    simp only [exprStep, hch]
    rw [show (fun rs => dCallW env fps P.fn fp s g rs) = fun rs =>
        (dCallRO env fps P.fn s g rs).map (·.map (·, s.roots)) from ?_]
    · by_cases hk : allKw args = true
      · simp only [hk, ↓reduceIte]
        cases DM.bind (kwsOf (P.expr fp s) args) (fun kvs => kwCtor env g kvs) with
        | none => rfl
        | some r => cases r <;> rfl
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
        cases argsOf (P.expr fp s) args with
        | none => rfl
        | some r => cases r <;> rfl
    · funext rs
      unfold dCallW
      rcases hro with he | ⟨t, ht⟩
      · split
        · next d hg =>
          simp only [he, ↓reduceIte]
          cases dCallRO env fps P.fn s g rs with
          | none => rfl
          | some q => cases q <;> rfl
        · rfl
      · simp [ht]
  · rfl

/-- `x = e` with an expression that writes nothing. -/
theorem assign_name {env : Env} {fps : Name → Footprint} {n : Nat} {fp : Footprint} {s : DSt}
    {l l' : Line} {x : Name} {e : Expr} {r : DRes}
    (hc : (den env fps (n + 1)).call fp s e = some (.ok (r, s.roots))) :
    (den env fps (n + 2)).stmt fp s (.assign l [.name l' x] e) =
      some (.ok (.normal, { s with loc := setLoc s.loc x r })) := by
  simp [stmtStep, hc, DM.bind, targetStep, DM.ok]

theorem assign_name_err {env : Env} {fps : Name → Footprint} {n : Nat} {fp : Footprint}
    {s : DSt} {l l' : Line} {x : Name} {e : Expr} {err : SpecError}
    (hc : (den env fps (n + 1)).call fp s e = some (.error err)) :
    (den env fps (n + 2)).stmt fp s (.assign l [.name l' x] e) = some (.error err) := by
  simp [stmtStep, hc, DM.bind]

theorem dm_bind_ok {α β : Type} (a : α) (f : α → DM β) : DM.bind (some (.ok a)) f = f a := rfl

theorem dm_ok {α : Type} (a : α) : (DM.ok a : DM α) = some (.ok a) := rfl

theorem blockOf_ret {stmt : DSt → Stmt → DM (DOut × DSt)} {s s' : DSt} {st : Stmt}
    {ss : List Stmt} {v : DRes} (h : stmt s st = some (.ok (.ret v, s'))) :
    blockOf stmt s (st :: ss) = some (.ok (.ret v, s')) := by
  simp only [blockOf, h, DM.bind]; rfl

theorem args1 {ev : Expr → DM DRes} {e : Expr} {r : DRes} (h : ev e = some (.ok r)) :
    argsOf ev [.pos e] = some (.ok [r]) := by
  simp only [argsOf, h, dm_bind_ok, DM.ok]

theorem args2 {ev : Expr → DM DRes} {e e' : Expr} {r r' : DRes} (h : ev e = some (.ok r))
    (h' : ev e' = some (.ok r')) : argsOf ev [.pos e, .pos e'] = some (.ok [r, r']) := by
  simp only [argsOf, h, h', dm_bind_ok, DM.ok]

end SpecLean.Layer4
