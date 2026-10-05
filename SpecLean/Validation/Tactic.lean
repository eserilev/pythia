import Lean
import SpecLean.Encode
import SpecLean.Validation.Attr

/-!
# Tactics for the generated validation theorems

`lookup_lit` evaluates a `List.lookup` of a literal key in a generated table. `rd_split`
splits on the next `if` condition or result that the evaluation waits on.
-/

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic Simp

/-- The entry of key `k` in a literal list of pairs, as written in the list. -/
partial def findEntry (k : Nat) (l : Lean.Expr) : MetaM (Option (Option Lean.Expr)) := do
  let l ← whnfD l
  match_expr l with
  | List.nil _ => return some none
  | List.cons _ hd tl =>
    let hd ← whnfD hd
    let_expr Prod.mk _ _ k' v := hd | return none
    let some k' := (← whnfD k').rawNatLit? | return none
    if k' == k then return some (some v) else findEntry k tl
  | _ => return none

/-- `List.lookup k xs` for a literal `k` and a literal table `xs`: the table entry. -/
simproc lookup_lit (List.lookup _ _) := fun e => do
  let_expr List.lookup _ β _ k xs := e | return .continue
  if k.hasFVar || k.hasMVar || xs.hasMVar then return .continue
  let some kn := (← whnfD k).rawNatLit? | return .continue
  let some r ← findEntry kn xs | return .continue
  let r ← match r with
    | some v => mkAppOptM ``Option.some #[β, v]
    | none => mkAppOptM ``Option.none #[β]
  -- The kernel checks the step in its own small theorem.
  let prf ← mkAuxTheorem (← mkEq e r) (← mkEqRefl e)
  return .done { expr := r, proof? := prf }

/-- A value of known shape: a constructor at the head, and the same for each argument of
type `Value` or `List Value`. -/
partial def known (e : Lean.Expr) : MetaM Bool := do
  let e ← whnfR e
  let ty ← whnfR (← inferType e)
  if ty.isConstOf ``SpecLean.Value || ty.isConstOf ``SpecLean.LibVal then
    let some c := e.getAppFn.constName? | return false
    let some (.ctorInfo ci) := (← getEnv).find? c | return false
    unless ci.induct == ``SpecLean.Value || ci.induct == ``SpecLean.LibVal do return false
    for a in e.getAppArgs do
      let at_ ← whnfR (← inferType a)
      if at_.isConstOf ``SpecLean.Value || at_.isConstOf ``SpecLean.LibVal ||
          at_.isAppOf ``List then
        unless ← known a do return false
    return true
  if ty.isAppOf ``List then
    match_expr e with
    | List.nil _ => return true
    | List.cons _ x xs => return (← known x) && (← known xs)
    | _ => return false
  return true

/-- The library functions that the proofs unfold once their value arguments are known. -/
def unfoldNames : NameSet := NameSet.ofList [``SpecLean.compareOp,
  ``SpecLean.cmpVal, ``SpecLean.LibValues.compare, ``SpecLean.Ssz.compare, ``SpecLean.pyCmp,
  ``SpecLean.truthyH, ``SpecLean.truthy, ``SpecLean.LibValues.truthy, ``SpecLean.Ssz.truthy,
  ``SpecLean.pyTruthy, ``SpecLean.binopVal, ``SpecLean.LibValues.binop, ``SpecLean.Ssz.binop,
  ``SpecLean.pyBinop, ``SpecLean.seqBinop, ``SpecLean.unopVal, ``SpecLean.LibValues.unop,
  ``SpecLean.Ssz.unop, ``SpecLean.pyUnop, ``SpecLean.LibModel.construct, ``SpecLean.Ssz.construct,
  ``SpecLean.coerceElem, ``SpecLean.toIndex, ``SpecLean.LibValues.index, ``SpecLean.Ssz.index,
  ``SpecLean.getSlice, ``SpecLean.sliceRange, ``SpecLean.getItem, ``SpecLean.getAttr,
  ``SpecLean.iterElems, ``SpecLean.memberOf, ``SpecLean.pyIndex, ``SpecLean.applyMethod,
  ``SpecLean.LibModel.method, ``SpecLean.Ssz.method, ``SpecLean.applyBuiltin,
  ``SpecLean.LibModel.builtin, ``SpecLean.Ssz.builtin, ``SpecLean.fromBytes]

/-- Unfold a function of `unfoldNames` once its value arguments have a known shape. -/
simproc ↓ unfold_known (_) := fun e => do
  -- A field of a library instance.
  if let .proj _ i st := e.getAppFn then
    -- The instance is a constant that only full transparency unfolds.
    let st ← withTransparency .all <| whnf st
    let some f ← projectCore? st i | return .continue
    return .visit { expr := (mkAppN f e.getAppArgs).headBeta }
  let some f := e.getAppFn.constName? | return .continue
  unless unfoldNames.contains f do return .continue
  for a in e.getAppArgs do
    let ty ← whnfR (← inferType a)
    if ty.isConstOf ``SpecLean.Value || ty.isAppOf ``List then
      if ty.isAppOf ``List then
        unless (← whnfR ty.appArg!).isConstOf ``SpecLean.Value do continue
      unless ← known a do return .continue
  let some e' ← delta? e | return .continue
  return .visit { expr := e' }

@[rd_simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
@[rd_simp] theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl
@[rd_simp] theorem except_mapError_ok {ε ε' α : Type} (g : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError g = Except.ok a := rfl
@[rd_simp] theorem except_mapError_error {ε ε' α : Type} (g : ε → ε') (e : ε) :
    (Except.error e : Except ε α).mapError g = Except.error (g e) := rfl
@[rd_simp] theorem except_map_ok {ε α β : Type} (g : α → β) (a : α) :
    (g <$> (Except.ok a : Except ε α)) = Except.ok (g a) := rfl
@[rd_simp] theorem except_map_error {ε α β : Type} (g : α → β) (e : ε) :
    (g <$> (Except.error e : Except ε α)) = Except.error e := rfl
@[rd_simp] theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = Except.ok a := rfl
@[rd_simp] theorem except_throw {ε α : Type} (e : ε) : (throw e : Except ε α) = Except.error e := rfl

/-- A head that `simp` already reduces. -/
def isValueHead (a : Lean.Expr) : Bool :=
  let f := a.getAppFn
  f.isConstOf ``Except.ok || f.isConstOf ``Except.error || f.isConstOf ``Option.some ||
    f.isConstOf ``Option.none || f.isConstOf ``Pure.pure || a.isFVar

/-- The terms that `x` evaluates first: the first argument of a `bind`, the scrutinees of a
`match`, the condition of an `if`. `none`: every explicit argument. -/
def firstParts (x : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  if x.isAppOfArity ``Bind.bind 6 then return some [x.getArg! 4]
  if x.isAppOfArity ``Except.bind 5 then return some [x.getArg! 3]
  if x.isAppOfArity ``Option.bind 4 then return some [x.getArg! 2]
  if x.isAppOfArity ``ite 5 || x.isAppOfArity ``dite 5 then return some [x.getArg! 1]
  if let .const n _ := x.getAppFn then
    if let some info ← getMatcherInfo? n then
      let args := x.getAppArgs
      return some ((List.range info.numDiscrs).filterMap fun i => args[info.numParams + 1 + i]?)
  return none

/-- What to split on next: an `if` condition (`true`) or a result (`false`). It is the first
closed term on the path of evaluation that is not a value. -/
partial def nextSplit (x : Lean.Expr) : MetaM (Option (Bool × Lean.Expr)) := do
  if x.hasLooseBVars then return none
  if x.isAppOfArity ``ite 5 || x.isAppOfArity ``dite 5 then
    let c := x.getArg! 1
    if let some r ← nextSplit c then return some r
    return some (true, c)
  match ← firstParts x with
  | some parts =>
    for p in parts do
      if let some r ← nextSplit p then return some r
      if !p.hasLooseBVars && !isValueHead p && (← firstParts p).isNone then
        let ty ← whnfR (← inferType p)
        if ty.isAppOf ``Except || ty.isAppOf ``Option then return some (false, p)
    return none
  | none =>
    if x.isApp then
      for a in x.getAppArgs do
        if let some r ← nextSplit a then return some r
    return none

/-- Split on the next `if` condition or result of the goal. -/
elab "rd_split" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (isCond, x) ← nextSplit t | throwError "rd_split: nothing to split"
  if isCond then
    let (gt, gf) ← g.byCases x `hc
    let mut gs := []
    let hc := mkIdent `hc
    for sg in [gt.mvarId, gf.mvarId] do
      gs := gs ++ (← evalTacticAt (← `(tactic| try simp only [$hc:ident, ite_true, ite_false, dite_true,
        dite_false, not_false_eq_true, not_true_eq_false, and_self, and_true, true_and, and_false,
        false_and, not_and, not_or] at ⊢)) sg)
    replaceMainGoal gs
  else
    let gs ← evalTacticAt
      (← `(tactic| (generalize hx : $(← Term.exprToSyntax x) = r; cases r))) g
    replaceMainGoal gs

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

/-- One evaluation step on both sides of the goal. -/
macro "rd_step" : tactic => `(tactic| simp [rd_simp, SpecLean.Validation.Tactic.unfold_known,
  SpecLean.Encode.ResultMatches] at ⊢)

end SpecLean.Validation.Tactic
