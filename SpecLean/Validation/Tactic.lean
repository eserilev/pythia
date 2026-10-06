import Lean
import SpecLean.Encode
import SpecLean.Validation.Attr
import SpecLean.Validation.Decode
import SpecLean.Validation.Where
import SpecLean.Validation.Local
import SpecLean.Validation.Steps
import SpecLean.Validation.Grow
import SpecLean.Validation.Sub
import SpecLean.Validation.Move

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

/-- The index and entry of key `k` in a literal list of pairs. -/
partial def findIndex (k : Nat) (l : Lean.Expr) (i : Nat := 0) :
    MetaM (Option (Nat × Lean.Expr)) := do
  let l ← whnfD l
  match_expr l with
  | List.cons _ hd tl =>
    let hd ← whnfD hd
    let_expr Prod.mk _ _ k' v := hd | return none
    let some k' := (← whnfD k').rawNatLit? | return none
    if k' == k then return some (i, v) else findIndex k tl (i + 1)
  | _ => return none

/-- `fieldIndex env ty f` for a literal class and field: the position and the type. -/
simproc fieldIndex_lit (SpecLean.fieldIndex _ _ _) := fun e => do
  let_expr SpecLean.fieldIndex env ty f := e | return .continue
  if ty.hasFVar || f.hasFVar then return .continue
  let some tyn := (← whnfD ty).rawNatLit? | return .continue
  let some fn := (← whnfD f).rawNatLit? | return .continue
  let cs ← whnfD (← mkAppM ``SpecLean.Env.containers #[env])
  let some (some fs) ← findEntry tyn cs | return .continue
  let some (i, t) ← findIndex fn fs | return .continue
  let r ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mkNatLit i, t]]
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
      let isVals ← if at_.isAppOf ``List then
          pure ((← whnfR at_.appArg!).isConstOf ``SpecLean.Value)
        else pure false
      if at_.isConstOf ``SpecLean.Value || at_.isConstOf ``SpecLean.LibVal || isVals then
        unless ← known a do return false
    return true
  if ty.isAppOf ``List then
    match_expr e with
    | List.nil _ => return true
    | List.cons _ x xs => return (← known x) && (← known xs)
    | _ => return false
  return true

/-- The library functions that the proofs unfold once their value arguments are known. -/
def unfoldNames : NameSet := NameSet.ofList [``SpecLean.compareOp, ``SpecLean.seqAugAdd,
  ``SpecLean.iterSource, ``SpecLean.toSeq,
  ``SpecLean.cmpVal, ``SpecLean.LibValues.compare, ``SpecLean.Ssz.compare, ``SpecLean.pyCmp,
  ``SpecLean.truthyH, ``SpecLean.truthy, ``SpecLean.LibValues.truthy, ``SpecLean.Ssz.truthy,
  ``SpecLean.pyTruthy, ``SpecLean.binopVal, ``SpecLean.LibValues.binop, ``SpecLean.Ssz.binop,
  ``SpecLean.pyBinop, ``SpecLean.seqBinop, ``SpecLean.unopVal, ``SpecLean.LibValues.unop,
  ``SpecLean.Ssz.unop, ``SpecLean.pyUnop, ``SpecLean.LibModel.construct, ``SpecLean.Ssz.construct,
  ``SpecLean.coerceElem, ``SpecLean.toIndex, ``SpecLean.LibValues.index, ``SpecLean.Ssz.index,
  ``SpecLean.getSlice, ``SpecLean.sliceRange, ``SpecLean.getItem, ``SpecLean.getAttr,
  ``SpecLean.iterElems, ``SpecLean.memberOf, ``SpecLean.pyIndex, ``SpecLean.applyMethod,
  ``SpecLean.LibModel.method, ``SpecLean.Ssz.method, ``SpecLean.applyBuiltin,
  ``SpecLean.LibModel.builtin, ``SpecLean.Ssz.builtin, ``SpecLean.fromBytes, ``SpecLean.setItem,
  ``SpecLean.setAttr, ``SpecLean.coerceWith, ``SpecLean.LibModel.coerce, ``SpecLean.Ssz.coerce, ``SpecLean.coerceField, ``SpecLean.appendItem,
  ``SpecLean.LibModel.append, ``SpecLean.Ssz.append]

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
  -- Only a full application: `simp` also visits the partial ones.
  if (← whnfR (← inferType e)).isForall then return .continue
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

/-- A decoder: the proofs compute it, they do not split on it. -/
def isDecoder (f : Lean.Expr) : Bool :=
  match f.constName? with
  | some (.str p s) => (p == `SpecLean.Rd.Gen && s.startsWith "dec_") ||
      (p == `SpecLean.Rd && s.startsWith "dec")
  | _ => false

/-- A head that `simp` already reduces. -/
def isValueHead (a : Lean.Expr) : Bool :=
  let f := a.getAppFn
  f.isConstOf ``Except.ok || f.isConstOf ``Except.error || f.isConstOf ``Option.some ||
    f.isConstOf ``Option.none || f.isConstOf ``Pure.pure || a.isFVar || isDecoder f ||
    -- A call waits for `rd_call`, which needs the readable call too; the next iteration of a
    -- loop waits for the induction hypothesis.
    f.isConstOf `SpecLean.Validation.Tactic.callStop || f.isConstOf ``SpecLean.execFor || f.isConstOf ``SpecLean.execWhile ||
    (match f.constName? with
     | some (.str _ s) => s.startsWith "loop"
     | _ => false)

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
  -- `generalize` leaves metadata on the goal.
  let x := x.consumeMData
  if x.hasLooseBVars then return none
  if x.isAppOfArity ``ite 5 || x.isAppOfArity ``dite 5 then
    let c := x.getArg! 1
    if let some r ← nextSplit c then return some r
    return some (true, c)
  match ← firstParts x with
  | some parts =>
    for p in parts do
      -- A `Bool` variable that a `match` waits on: split on its two values.
      if p.isFVar && (← whnfR (← inferType p)).isConstOf ``Bool then return some (false, p)
      if let some r ← nextSplit p then return some r
      if !p.hasLooseBVars && !isValueHead p && (← firstParts p).isNone then
        let ty ← whnfR (← inferType p)
        if ty.isAppOf ``Except || ty.isAppOf ``Option || ty.isConstOf ``Bool then
          unless p.isConstOf ``Bool.true || p.isConstOf ``Bool.false do
            return some (false, p)
    return none
  | none =>
    if x.isApp then
      for a in x.getAppArgs do
        if let some r ← nextSplit a then return some r
        -- A result inside an operation, such as `Option.map f xs[i]?`.
        if !a.hasLooseBVars && !isValueHead a && (← firstParts a).isNone then
          let ty ← whnfR (← inferType a)
          if ty.isAppOf ``Except || ty.isAppOf ``Option then
            return some (false, a)
    return none

/-- Split every hypothesis that is an `∃` or an `∧` into its parts. -/
partial def splitHyps (g : MVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then
      let gs ← g.cases d.fvarId
      if h : gs.size = 1 then
        return ← splitHyps gs[0].mvarId
  return g

/-- Add `xs.length = ys.length` for each hypothesis `xs.mapM f = some ys`. -/
def addLengths (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq _ lhs _ := ty | continue
    unless lhs.isAppOf ``List.mapM do continue
    let p ← mkAppM ``SpecLean.Validation.Decode.mapM_length #[d.toExpr]
    let (_, g') ← (← g.assert `hlen (← inferType p) p).intro1P
    g := g'
  return g

/-- Split the decode hypotheses into facts, and substitute the equations of variables. -/
elab "rd_split_hyps" : tactic => do
  let g ← splitHyps (← getMainGoal)
  replaceMainGoal [g]
  evalTactic (← `(tactic| try subst_vars))
  replaceMainGoal [← addLengths (← getMainGoal)]

/-- `xs[k]?` where a hypothesis decodes `xs` to `ys` (or `ys[k]?`): split both at once. In
the case where both hold an item, the item decodes; unfold that decode into facts. -/
def splitDecodedIndex (g : MVarId) (x : Lean.Expr) : TacticM (Option (List MVarId)) :=
  g.withContext do
  unless x.isAppOfArity ``GetElem?.getElem? 7 do return none
  let l := x.getArg! 5
  let k := x.getArg! 6
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq _ lhs rhs := ty | continue
    unless lhs.isAppOf ``List.mapM do continue
    let xs := lhs.appArg!
    let_expr Option.some _ ys := rhs | continue
    unless xs == l || ys == l do continue
    let pf ← Term.exprToSyntax (← mkAppM ``SpecLean.Validation.Decode.mapM_getElem? #[d.toExpr, k])
    let hn1 := mkIdent `hn1
    let hn2 := mkIdent `hn2
    let hs1 := mkIdent `hs1
    let hs2 := mkIdent `hs2
    let hd := mkIdent `hdec
    let gs ← evalTacticAt (← `(tactic|
      rcases $pf:term with ⟨$hn1:ident, $hn2:ident⟩ | ⟨_, _, $hs1:ident, $hs2:ident, $hd:ident⟩)) g
    let mut out := []
    for sg in gs do
      let tac ← `(tactic| (
        (try simp only [$hn1:ident, $hn2:ident] at ⊢)
        (try simp only [$hs1:ident, $hs2:ident] at ⊢)
        (try simp only [rd_dec, rd_simp, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq, Value.ref.injEq, exists_eq_left',
          exists_eq_right] at $hd:ident)
        (try rd_split_hyps)))
      out := out ++ (← evalTacticAt tac sg)
    return some out
  return none

/-- Split on the next `if` condition or result of the goal. -/
elab "rd_split" : tactic => withMainContext do
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
    if x.isFVar then
      let gs ← evalTacticAt
        (← `(tactic| (cases $(← Term.exprToSyntax x):term <;> try simp only at ⊢))) g
      replaceMainGoal gs
      return
    -- A known result: rewrite with its fact, do not split.
    let known ← g.withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let_expr Eq _ lhs _ := ty | continue
        if lhs == x then return some d.toExpr
      return none
    if let some hf := known then
      let gs ← evalTacticAt (← `(tactic| (rw [$(← Term.exprToSyntax hf):term]; try simp only at ⊢))) g
      replaceMainGoal gs
      return
    if let some gs ← splitDecodedIndex g x then
      replaceMainGoal gs
      return
    let gs ← evalTacticAt
      (← `(tactic| (generalize hx : $(← Term.exprToSyntax x) = r; cases r))) g
    replaceMainGoal gs

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

/-- A call of a spec function that the proofs do not unfold: the theorem of the callee gives
its result (SPEC 9.2, calls). -/
def callStop (env : Env) (n : Nat) (g : Name) (vs : List Value) (h : Heap) :
    Res (Value × Heap) :=
  interp env n g vs h

theorem callStop_eq (env : Env) (n : Nat) (g : Name) (vs : List Value) (h : Heap) :
    callValue env n (.glob g) vs [] h = callStop env n g vs h := rfl

theorem callStop_def (env : Env) (n : Nat) (g : Name) (vs : List Value) (h : Heap) :
    callStop env n g vs h = interp env n g vs h := rfl

attribute [irreducible] callStop

open Lean Meta in
/-- A call of a spec function as `callStop`, once its function value is known. -/
def stopCall? (e : Lean.Expr) : MetaM (Option Simp.Step) := do
  unless e.isAppOf ``SpecLean.callValue do return none
  -- The last six arguments; the first ones are section variables.
  let a := e.getAppArgs
  unless a.size ≥ 6 do return none
  let a := a.extract (a.size - 6) a.size
  let (env, n, vs, kws, h) := (a[0]!, a[1]!, a[3]!, a[4]!, a[5]!)
  let f ← whnfR a[2]!
  unless f.isAppOfArity ``SpecLean.Value.glob 1 do return none
  let g := f.appArg!
  unless (← whnfR kws).isAppOf ``List.nil do return none
  let some gn := (← whnfD g).rawNatLit? | return none
  let globals ← whnfD (← mkAppM ``SpecLean.Env.globals #[env])
  let some (some v) ← findEntry gn globals | return none
  unless (← whnfD v).isAppOf ``SpecLean.Global.fn do return none
  let e' ← mkAppM ``callStop #[env, n, g, vs, h]
  let pf ← mkAppM ``callStop_eq #[env, n, g, vs, h]
  return some (.done { expr := e', proof? := pf })

/-- Stop at a call of a spec function: it becomes `callStop`. Before and after its arguments
are simplified. -/
simproc ↓ stop_call (callValue _ _ _ _ _ _) := fun e => do
  return (← stopCall? e).getD .continue

simproc stop_call_post (callValue _ _ _ _ _ _) := fun e => do
  return (← stopCall? e).getD .continue

/-- One evaluation step on both sides of the goal, then the reads of written objects. Defined
after `rd_disch`. -/
syntax "rd_step" : tactic

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- The list literal `[a, b, ...]` as its items. -/
partial def listItems (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  match_expr e with
  | List.nil _ => return some []
  | List.cons _ x xs => return (← listItems xs).map (x :: ·)
  | _ => return none

/-- A path from argument `k` to the value `v`, with the proof of `at? h vs k q = some v`. It
follows the decode facts back to an argument: a field, an item, or a `follow` fact. -/
partial def pathOf (h vs : Lean.Expr) (items : List Lean.Expr) (v : Lean.Expr) (depth : Nat := 0) :
    MetaM (Option (Nat × Lean.Expr × Lean.Expr)) := do
  if depth > 16 then return none
  let valTy := mkConst ``SpecLean.Value
  -- An argument.
  for (x, k) in items.zipIdx do
    if x == v then
      let hv ← mkEqRefl (← mkAppOptM ``Option.some #[valTy, x])
      let hv ← mkExpectedTypeHint hv (← mkEq
        (← mkAppOptM ``GetElem?.getElem? #[none, none, none, none, none, vs, mkNatLit k])
        (← mkAppOptM ``Option.some #[valTy, x]))
      let pf ← mkAppOptM ``SpecLean.Validation.Where.at_root #[h, none, none, none, hv]
      return some (k, ← mkListLit (mkConst ``Nat) [], pf)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq _ lhs rhs := ty | continue
    let_expr Option.some _ v' := rhs | continue
    unless v' == v do continue
    -- A field or an item: `l[i]? = some v` and `h.objs p = some (... l)`.
    if lhs.isAppOfArity ``GetElem?.getElem? 7 then
      let l := lhs.getArg! 5
      let i := lhs.getArg! 6
      for d2 in ← getLCtx do
        if d2.isImplementationDetail then continue
        let ty2 ← instantiateMVars d2.type
        let_expr Eq _ lhs2 rhs2 := ty2 | continue
        let_expr Option.some _ o := rhs2 | continue
        let isField := o.isAppOfArity ``SpecLean.HeapObj.container 2 && o.appArg! == l
        let isItem := o.isAppOfArity ``SpecLean.HeapObj.list 4 && o.appArg! == l
        unless isField || isItem do continue
        unless lhs2.isApp && lhs2.appFn!.isAppOf ``SpecLean.Heap.objs do continue
        unless lhs2.appFn!.appArg! == h do continue
        let p ← mkAppM ``SpecLean.Value.ref #[lhs2.appArg!]
        let some (k, q, hp) ← pathOf h vs items p (depth + 1) | continue
        let q' ← mkAppM ``HAppend.hAppend #[q, ← mkListLit (mkConst ``Nat) [i]]
        let pf ← mkAppM (if isField then ``SpecLean.Validation.Where.at_field
          else ``SpecLean.Validation.Where.at_item) #[hp, d2.toExpr, d.toExpr]
        return some (k, q', pf)
    -- A `follow` fact: `follow h x r = some v`.
    if lhs.isAppOfArity ``SpecLean.Encode.follow 3 && lhs.getArg! 0 == h then
      let x := lhs.getArg! 1
      let r := lhs.getArg! 2
      let some (k, q, hp) ← pathOf h vs items x (depth + 1) | continue
      let q' ← mkAppM ``HAppend.hAppend #[q, r]
      let pf ← mkAppM ``SpecLean.Validation.Where.at_follow #[hp, d.toExpr]
      return some (k, q', pf)
  return none

/-- The path to the address `a`. -/
def pathTo (h vs : Lean.Expr) (items : List Lean.Expr) (a : Lean.Expr) :
    MetaM (Option (Nat × Lean.Expr × Lean.Expr)) := do
  pathOf h vs items (← mkAppM ``SpecLean.Value.ref #[a])

initialize registerTraceClass `rd.ne

/-- Prove `b ≠ a` for two addresses of the arguments, where one of them is at a footprint
path, from the `WTree` hypothesis. -/
def proveNe (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let (a, b) ← match_expr t with
    | Ne _ a b => pure (a, b)
    | Not p => match_expr p with
      | Eq _ a b => pure (a, b)
      | _ => return false
    | _ =>
      if t.isArrow then
        match_expr t.bindingDomain! with
        | Eq _ a b => if t.bindingBody!.isConstOf ``False then pure (a, b) else return false
        | _ => return false
      else return false
  -- The `WTree` hypothesis.
  let mut found := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``SpecLean.Encode.WTree 3 then found := some (d, ty)
  let some (hw, wty) := found | return false
  let h := wty.getArg! 0
  let vs := wty.getArg! 1
  let fp := wty.getArg! 2
  let some items ← listItems vs | return false
  let some pats ← listItems (← whnfR fp) | return false
  -- An argument object against a new address `h.next + c`.
  for (x, y, flip) in [(a, b, false), (b, a, true)] do
    let (base, c) ← match_expr y with
      | HAdd.hAdd _ _ _ _ n c => pure (n, c)
      | _ => pure (y, mkNatLit 0)
    unless base.isAppOfArity ``SpecLean.Heap.next 1 && base.appArg! == h do continue
    let mut hwfo := none
    let mut hawo := none
    for d in ← getLCtx do
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``SpecLean.Encode.HeapWF 1 && ty.appArg! == h then hwfo := some d.toExpr
      if ty.isAppOfArity ``SpecLean.Encode.ArgsWF 2 && ty.getArg! 0 == h then hawo := some d.toExpr
    let (some hwf, some haw) := (hwfo, hawo) | continue
    let some (_, _, px) ← pathTo h vs items x | continue
    let s ← saveState
    try
      let pf ← mkAppM ``SpecLean.Validation.Where.ne_next_of_at #[hwf, haw, px, c]
      -- `x ≠ h.next + c`, maybe with `+ 0` to drop.
      let pf ← if flip then mkAppM ``Ne.symm #[pf] else pure pf
      let ok ← withTransparency .default <| isDefEq (← inferType pf) (← g.getType)
      if ok then
        g.assign pf
        return true
      restoreState s
    catch _ => restoreState s
  let some (ka, qa, pa) ← pathTo h vs items a | return false
  let some (kb, qb, pb) ← pathTo h vs items b | return false
  -- Try each footprint pattern at each of the two paths.
  for (x, kx, qx, px, y, ky, qy, py, flip) in
      [(a, ka, qa, pa, b, kb, qb, pb, false), (b, kb, qb, pb, a, ka, qa, pa, true)] do
    for pat in pats do
      let s ← saveState
      try
        let g' ← mkFreshExprMVar (← mkAppM ``Ne #[y, x])
        let stx ← `(SpecLean.Validation.Where.wtree_ne $(← Term.exprToSyntax hw.toExpr)
          (k := $(Syntax.mkNumLit (toString kx))) (pat := $(← Term.exprToSyntax pat))
          (by simp) (by first | (apply SpecLean.Validation.Where.rootTy_of rfl; assumption) | simp_all)
          (by simp [SpecLean.Encode.Matches]) $(← Term.exprToSyntax px)
          $(← Term.exprToSyntax py)
          (by first | (simp; done) | (simp; omega) | (rintro ⟨-, hq⟩; simp at hq; omega) | (rintro ⟨-, hq⟩; simp at hq; exact absurd hq.1 ‹_›)))
        let pf ← Term.withoutErrToSorry do
          let pf ← Term.elabTermEnsuringType stx (← inferType g')
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars pf
        if pf.hasExprMVar || pf.hasSorry then throwError m!"no proof: {pf}"
        let pf ← if flip then pure pf else mkAppM ``Ne.symm #[pf]
        g.assign pf
        let _ := (x, y, ky, qy, qx)
        return true
      catch ex =>
        restoreState s
        trace[rd.ne] "{ex.toMessageData}"
  return false

/-- Discharge `b ≠ a` for two argument addresses under `WTree`. -/
elab "rd_ne" : tactic => do
  let g ← getMainGoal
  unless ← withTransparency .default (proveNe g) do throwError "rd_ne: no proof"

/-- `h'.objs c = h.objs c`: no write of `h'` is at `c`. -/
syntax "rd_same" : tactic

/-- `f (g y) = some y` for an item `y` of a decoded list of scalars: the decoder reads back the
encoding, and the item is in range. -/
syntax "rd_itemdec" : tactic

/-- A fact `∀ z ∈ ys, P z` of the context, at the item `y ∈ ys` of the goal. -/
elab "rd_mem" : tactic => withMainContext <| withTransparency .default do
  let g ← getMainGoal
  let lctx ← getLCtx
  let mems := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else
    match_expr d.type with
    | Membership.mem _ _ _ _ _ => acc.push d.toExpr
    | _ => acc
  for d in lctx do
    if d.isImplementationDetail then continue
    unless (← instantiateMVars d.type).isForall do continue
    for m in mems do
      let s ← saveState
      try
        let pf ← mkAppM' d.toExpr #[(← inferType m).appArg!, m]
        if ← isDefEq (← inferType pf) (← g.getType) then
          g.assign pf
          return
        restoreState s
      catch _ => restoreState s
  throwError "rd_mem: none"

/-- The side conditions of the heap steps: two addresses differ, or no object that the items
of a list reach is the written one. -/
macro "rd_disch" : tactic => `(tactic| first
  | (rd_ne; done)
  | (simp only [SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.alloc_next,
      SpecLean.Validation.Where.alloc_fst]; done)
  | (simp only [SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.alloc_next,
      SpecLean.Validation.Where.alloc_fst]; rd_ne; done)
  | (intro j x hj q c hf; rd_same; done)
  | (intro k x hk hkj q c hf; rd_ne; done)
  -- Reducible only: a full unification against each fact can unfold the decoders of a large
  -- heap past the recursion limit, and that error escapes `first`.
  | with_reducible assumption
  | omega
  | (intro y hy; rd_itemdec))

macro_rules
  | `(tactic| rd_step) => `(tactic| (
      (try simp (config := { maxSteps := 2000000 }) [rd_simp, SpecLean.Validation.Tactic.unfold_known,
        SpecLean.Validation.Tactic.stop_call, SpecLean.Validation.Tactic.stop_call_post,
        SpecLean.Validation.Tactic.fieldIndex_lit, SpecLean.Encode.ResultMatches,
        -SpecLean.Heap.set_objs, SpecLean.Validation.Where.alloc_fst,
        SpecLean.Validation.Where.alloc_next, SpecLean.Validation.Where.set_next, *] at ⊢)
      (try simp (disch := rd_disch) only [SpecLean.Validation.Where.objs_set_ne,
        SpecLean.Validation.Where.objs_set_self, SpecLean.Validation.Where.objs_alloc_ne,
        SpecLean.Validation.Where.objs_alloc_self, SpecLean.Validation.Where.objs_alloc_at] at ⊢)))

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- The decode facts of the context: objects, fields and items, decoded lists, ranges. -/
def heapFacts : MetaM (Array Lean.Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    -- Range facts of decoded uints: a write of the same value decodes again.
    if ty.isAppOfArity ``LT.lt 4 then out := out.push d.toExpr
    let_expr Eq _ lhs _ := ty | continue
    if (lhs.isApp && lhs.appFn!.isAppOf ``SpecLean.Heap.objs) ||
        lhs.isAppOfArity ``GetElem?.getElem? 7 || lhs.isAppOf ``List.mapM ||
        lhs.isAppOf ``List.length then
      out := out.push d.toExpr
    if lhs.isAppOf ``SpecLean.normIndex then
      out := out.push (← mkAppM ``SpecLean.Validation.Where.normIndex_lt #[d.toExpr])
  return out

/-- Decode the result heap: read each object through the writes. -/
elab "rd_heap" : tactic => withMainContext do
  let facts ← heapFacts
  let mut args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in facts do
    args := args.push (← `(Lean.Parser.Tactic.simpLemma| $(← Term.exprToSyntax f):term))
  evalTactic (← `(tactic| simp (config := { maxSteps := 4000000 }) (disch := rd_disch) only [Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_some, Option.some.injEq,
    if_true, if_false, ite_true, ite_false, and_self, true_and, and_true, decide_true,
    SpecLean.Rd.UintC.ofNat_val, SpecLean.Rd.BytesC.ofBytes_data, eq_self_iff_true,
    SpecLean.Rd.UintC.bits, SpecLean.Rd.BytesC.len, SpecLean.Validation.Decode.ite_lt_of,
    SpecLean.Validation.Decode.ite_eq_nat_of, List.length_cons, List.length_take, List.length_tail,
    List.length_drop, List.length_append, List.length_replicate,
    SpecLean.Validation.Where.objs_set_ne, SpecLean.Validation.Where.objs_set_self, rd_dec,
    SpecLean.Rd.containerFieldsT, SpecLean.Rd.decUintT, SpecLean.Rd.decBytesT,
    SpecLean.Rd.decBooleanV, SpecLean.Rd.decListT, SpecLean.Validation.Local.mapM_same_of,
    SpecLean.Validation.Local.mapM_set_item, SpecLean.Validation.Local.mapM_slice_same,
    SpecLean.Validation.Decode.mapM_map_of, SpecLean.Validation.Decode.mapM_set_map,
    List.mapM_append, List.mapM_cons, List.mapM_nil, rd_dec,
    List.getElem?_set_ne, List.getElem?_set_self', Option.map_eq_map, Option.map_some,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    Function.const_apply, SpecLean.Validation.Where.alloc_fst, SpecLean.Validation.Where.alloc_next,
    SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.objs_alloc_ne,
    SpecLean.Validation.Where.objs_alloc_self, SpecLean.Validation.Where.objs_alloc_at, $args,*]))

/-- Prove `AtFp h vs fp a`: the path of `a`, and a footprint pattern that matches it. -/
def proveAtFp (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SpecLean.Encode.AtFp 4 do return false
  let h := t.getArg! 0
  let vs := t.getArg! 1
  let fp := t.getArg! 2
  let a := t.getArg! 3
  let some items ← listItems vs | return false
  let some pats ← listItems (← whnfR fp) | return false
  let some (k, _, pa) ← pathTo h vs items a | return false
  for pat in pats do
    let s ← saveState
    try
      let stx ← `(SpecLean.Validation.Where.atFp_of (k := $(Syntax.mkNumLit (toString k)))
          (pat := $(← Term.exprToSyntax pat)) (by simp)
          (by first | (apply SpecLean.Validation.Where.rootTy_of rfl; assumption) | simp_all)
          (by simp [SpecLean.Encode.Matches]) $(← Term.exprToSyntax pa))
      let pf ← Term.withoutErrToSorry do
        let pf ← Term.elabTermEnsuringType stx t
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars pf
      if pf.hasExprMVar || pf.hasSorry then throwError "no proof"
      g.assign pf
      return true
    catch _ =>
      restoreState s
  return false

elab "rd_atfp" : tactic => do
  unless ← withTransparency .default (proveAtFp (← getMainGoal)) do
    throwError "rd_atfp: no proof"

/-- Read an object of a heap after writes: `h1.objs a = some ?o`. -/
elab "rd_objs" : tactic => withMainContext do
  let facts ← heapFacts
  let mut args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in facts do
    args := args.push (← `(Lean.Parser.Tactic.simpLemma| $(← Term.exprToSyntax f):term))
  evalTactic (← `(tactic| simp (disch := rd_disch) only
    [SpecLean.Validation.Where.objs_set_ne, SpecLean.Validation.Where.objs_set_self,
     List.getElem?_set_ne, List.getElem?_set_self', Option.map_eq_map, Option.map_some,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
     Function.const_apply, SpecLean.Validation.Where.alloc_fst, SpecLean.Validation.Where.alloc_next,
     SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.objs_alloc_ne,
     SpecLean.Validation.Where.objs_alloc_self, SpecLean.Validation.Where.objs_alloc_at, $args,*]))
  evalTactic (← `(tactic| try rfl))

/-- A write keeps the shape of the object: it writes a value with no reference. -/
macro "rd_skel" : tactic => `(tactic| first
  | (apply SpecLean.Validation.Where.sameSkel_list_set <;>
      first
      | exact SpecLean.Validation.Where.noRef_map_uint _ _ _
      | exact SpecLean.Validation.Where.noRef_map_bytes _ _ _
      | exact SpecLean.Validation.Where.noRef_map_boolean _ _
      | exact SpecLean.Validation.Where.noRef_uint _ _
      | exact SpecLean.Validation.Where.noRef_bytes _ _
      | exact SpecLean.Validation.Where.noRef_boolean _)
  | (apply SpecLean.Validation.Where.sameSkel_container_set <;>
      first
      | (intro x hx; simp_all; first
          | exact SpecLean.Validation.Where.noRef_uint _ _
          | exact SpecLean.Validation.Where.noRef_bytes _ _
          | exact SpecLean.Validation.Where.noRef_boolean _)
      | exact SpecLean.Validation.Where.noRef_uint _ _
      | exact SpecLean.Validation.Where.noRef_bytes _ _
      | exact SpecLean.Validation.Where.noRef_boolean _))

/-- Split a goal that is syntactically a conjunction. -/
elab "rd_and" : tactic => do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOfArity ``And 2 do throwError "rd_and: not a conjunction"
  evalTactic (← `(tactic| apply And.intro))

/-- The frame, the fresh addresses and the reach of a run of writes. Defined below. -/
syntax "rd_frame" : tactic

/-- `NoNewPaths` of a field that gets a slice of its own list. Defined below. -/
syntax "rd_nnp_move" : tactic

/-- The frame facts after a call, composed with the writes before it. Defined below. -/
syntax "rd_after_call" : tactic

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- Close a goal by two hypotheses `e = a` and `e = b` with different constructors. -/
elab "rd_contra" : tactic => withMainContext do
  let g ← getMainGoal
  let mut eqs : Array (Lean.Expr × Lean.Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq _ lhs _ := ty | continue
    eqs := eqs.push (lhs, d.toExpr)
  for i in [0:eqs.size] do
    for j in [i+1:eqs.size] do
      let (l1, p1) := eqs[i]!
      let (l2, p2) := eqs[j]!
      unless l1 == l2 do continue
      let s ← saveState
      try
        let e ← mkEqTrans (← mkEqSymm p1) p2
        let gs ← evalTacticAt (← `(tactic| (have hrd := $(← Term.exprToSyntax e); simp at hrd))) g
        if gs.isEmpty then
          replaceMainGoal []
          return
        restoreState s
      catch _ => restoreState s
  throwError "rd_contra: none"

end SpecLean.Validation.Tactic

macro_rules | `(tactic| rd_finish) => `(tactic| rd_contra)

macro_rules
  | `(tactic| rd_itemdec) => `(tactic| first
      | exact SpecLean.Validation.Decode.decBooleanV_eq.2 rfl
      | (refine SpecLean.Validation.Decode.decUintT_eq.2 ⟨rfl, ?_⟩; rd_mem)
      | (refine SpecLean.Validation.Decode.decBytesT_eq.2 ⟨rfl, ?_⟩; rd_mem))

macro_rules
  | `(tactic| rd_same) => `(tactic| simp (disch := rd_disch) only
      [SpecLean.Validation.Where.objs_set_ne, SpecLean.Validation.Where.objs_alloc_ne,
       SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.alloc_next])

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- `h.next ≤ a → P` for an argument object `a`: it is old. -/
elab "rd_old" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isArrow do throwError "rd_old: not an implication"
  let_expr LE.le _ _ nx a := t.bindingDomain! | throwError "rd_old: not ≤"
  unless nx.isAppOfArity ``SpecLean.Heap.next 1 do throwError "rd_old: not next"
  let h := nx.appArg!
  let mut hwfo := none
  let mut hawo := none
  let mut vso := none
  for d in ← getLCtx do
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``SpecLean.Encode.HeapWF 1 && ty.appArg! == h then hwfo := some d.toExpr
    if ty.isAppOfArity ``SpecLean.Encode.ArgsWF 2 && ty.getArg! 0 == h then
      hawo := some d.toExpr; vso := some (ty.getArg! 1)
  let (some hwf, some haw, some vs) := (hwfo, hawo, vso) | throwError "rd_old: no HeapWF"
  let some items ← listItems vs | throwError "rd_old: no items"
  let some (_, _, pa) ← pathTo h vs items a | throwError "rd_old: no path"
  g.assign (← mkAppOptM ``SpecLean.Validation.Grow.old_not_new
    #[none, none, hwf, haw, none, none, none, pa, t.bindingBody!])
  replaceMainGoal []

/-- A value or a list of values holds no old reference. -/
macro "rd_newval" : tactic => `(tactic| first
  | exact SpecLean.Validation.Grow.newVal_uint _ _ _
  | exact SpecLean.Validation.Grow.newVal_bytes _ _ _
  | exact SpecLean.Validation.Grow.newVal_boolean _ _
  | exact SpecLean.Validation.Grow.newVals_nil _
  | exact SpecLean.Validation.Grow.newVals_map_uint _ _ _ _
  | exact SpecLean.Validation.Grow.newVals_map_bytes _ _ _ _
  | exact SpecLean.Validation.Grow.newVals_map_boolean _ _ _
  -- `refine`, not `apply`: `apply` also matches a single `NewVal` goal through the bound `y`,
  -- and the loop never ends.
  | refine SpecLean.Validation.Grow.newVals_cons ?_ ?_
  | refine SpecLean.Validation.Grow.newVals_append ?_ ?_
  | (apply SpecLean.Validation.Grow.newVal_of_ge;
     (try simp only [SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.alloc_next,
       SpecLean.Validation.Where.alloc_fst]); omega))

/-- `Reach` of a run of writes: the heap grows. Defined below. -/
syntax "rd_reach" : tactic

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- `HeapWF h1` for a heap after writes: from `HeapWF h` and `Fresh h h1`. -/
elab "rd_heapwf" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SpecLean.Encode.HeapWF 1 do throwError "rd_heapwf: not HeapWF"
  for d in ← getLCtx do
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``SpecLean.Encode.HeapWF 1 then
      let hs ← Term.exprToSyntax d.toExpr
      let s ← saveState
      let gs ← evalTacticAt (← `(tactic| refine SpecLean.Validation.Where.heapWF_of_fresh $hs ?_)) g
      let fr ← `(tactic| rd_frame)
      let gs ← gs.flatMapM fun sg => evalTacticAt fr sg
      unless gs.isEmpty do restoreState s
      if gs.isEmpty then
        replaceMainGoal []
        return
  throwError "rd_heapwf: none"

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- `Grows h h' n`: one step back along the writes of `h'`, by its last write. -/
elab "rd_grows" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``SpecLean.Validation.Grow.Grows 3 do throwError "rd_grows: not Grows"
  let h := t.getArg! 0
  let h' := t.getArg! 1
  if h' == h then
    let gs ← evalTacticAt (← `(tactic|
      exact SpecLean.Validation.Grow.grows_refl _ _ (by assumption) (Nat.le_refl _))) g
    replaceMainGoal gs
    return
  if h'.isAppOfArity ``SpecLean.Heap.set 3 then
    let h1 ← Term.exprToSyntax (h'.getArg! 0)
    let a ← Term.exprToSyntax (h'.getArg! 1)
    let o ← Term.exprToSyntax (h'.getArg! 2)
    let gs ← evalTacticAt (← `(tactic|
      refine SpecLean.Validation.Grow.grows_set (h1 := $h1) (a := $a) (o' := $o) (o := ?_) ?_ ?_ ?_ ?_)) g
    -- Read the old object first: the goal `ObjGrows n ?o o'` needs it.
    let mut out := []
    for sg in gs do
      let ty := (← instantiateMVars (← sg.getType)).consumeMData
      if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isApp &&
          (ty.getArg! 1).appFn!.isAppOf ``SpecLean.Heap.objs then
        let s ← saveState
        try
          let r ← evalTacticAt (← `(tactic| (rd_objs; done))) sg
          out := out ++ r
          continue
        catch _ => s.restore
      out := out ++ [sg]
    let open_ ← out.filterM fun sg => return !(← sg.isAssigned)
    replaceMainGoal open_
    return
  if h'.isAppOfArity ``Prod.snd 3 && (h'.getArg! 2).isAppOfArity ``SpecLean.Heap.alloc 2 then
    let al := h'.getArg! 2
    let h1 ← Term.exprToSyntax (al.getArg! 0)
    let o ← Term.exprToSyntax (al.getArg! 1)
    let gs ← evalTacticAt (← `(tactic|
      refine SpecLean.Validation.Grow.grows_alloc (h1 := $h1) (o := $o) ?_ ?_ ?_ ?_)) g
    replaceMainGoal gs
    return
  throwError "rd_grows: no write"

end SpecLean.Validation.Tactic

macro_rules
  | `(tactic| rd_reach) => `(tactic| (
  apply SpecLean.Validation.Grow.reach_of_grows (by assumption) (by assumption)
  repeat' (first
    | rd_grows
    | rd_old
    | rd_newval
    | (rd_objs; done)
    | rd_heapwf
    | ((try simp only [SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.alloc_next,
        SpecLean.Validation.Where.alloc_fst]); omega)
    | with_reducible apply SpecLean.Validation.Grow.objGrows_list_set
    | with_reducible apply SpecLean.Validation.Grow.objGrows_container_set
    | with_reducible apply SpecLean.Validation.Grow.objGrows_list_append
    | with_reducible apply SpecLean.Validation.Grow.newObj_container
    | with_reducible apply SpecLean.Validation.Grow.newObj_list
    | (intro _; first
        | with_reducible apply SpecLean.Validation.Grow.newObj_container
        | with_reducible apply SpecLean.Validation.Grow.newObj_list)
)))

macro_rules
  | `(tactic| rd_frame) => `(tactic| repeat' (first
  | rd_after_call
  | exact SpecLean.Encode.Frame_refl _ _ _
  | exact SpecLean.Encode.Fresh_refl _
  | exact SpecLean.Encode.Reach_refl _ _
  | exact SpecLean.Encode.NoNewPaths_refl _ _ _
  | rd_nnp_move
  | apply SpecLean.Encode.noNewPaths_of_reach
  | rd_atfp
  | (rd_objs; done)
  | rd_skel
  | (rd_reach; done)
  | ((try simp only [SpecLean.Validation.Where.set_next, SpecLean.Validation.Where.alloc_next,
      SpecLean.Validation.Where.alloc_fst]); omega)
  | assumption
  -- Reducible only: at default transparency `h.set a o` unifies with `(h.alloc o).2`, and the
  -- loop never ends.
  | with_reducible apply SpecLean.Validation.Where.frame_alloc
  | with_reducible apply SpecLean.Validation.Where.fresh_alloc
  | with_reducible refine SpecLean.Validation.Where.frame_set ?_ ?_
  | with_reducible refine SpecLean.Validation.Where.frame_set_fresh ?_ (by assumption) ?_
  | with_reducible apply SpecLean.Validation.Where.fresh_set
  | with_reducible apply SpecLean.Validation.Where.reach_set
  | rfl
  | rd_and))

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- Fill a hypothesis of a callee theorem from the context: a fact with the same statement. -/
def fillFromContext (m : Lean.Expr) : MetaM Bool := do
  let ty ← instantiateMVars (← inferType m)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dty ← instantiateMVars d.type
    -- Only a fact of the same shape: a full unification would unfold the decoders.
    unless dty.getAppFn == ty.getAppFn && dty.getAppNumArgs == ty.getAppNumArgs do continue
    if ty.isAppOfArity ``Eq 3 && !(dty.getArg! 1).getAppFn.isFVar &&
        (dty.getArg! 1).getAppFn != (ty.getArg! 1).getAppFn then continue
    let s ← saveState
    if ← withReducible (isDefEq dty ty) then
      if ← isDefEq m d.toExpr then return true
    restoreState s
  return false

/-- The first subterm of `e` that `p` holds on and that has no loose bound variables. -/
def findClosed (e : Lean.Expr) (p : Lean.Expr → Bool) : Option Lean.Expr :=
  e.find? fun x => p x && !x.hasLooseBVars

/-- Each `ref` argument of the callee is the caller's at the same position. -/
macro "rd_subargs" : tactic => `(tactic| (
  intro k a hk
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, id,
      Option.some.injEq, SpecLean.Value.ref.injEq, reduceCtorEq] at hk ⊢ <;>
    first | (subst hk; rfl) | exact hk | rfl))

/-- A hypothesis of a callee theorem at a call: a fact about literals, or the write condition
of the callee from the caller's, when the callee takes the caller's arguments in place. -/
macro "rd_callhyp" : tactic => `(tactic| first
  | rfl
  | decide
  -- The decode of an argument after writes: the readable argument of the call.
  | (rd_heap; done)
  | (rd_heap; rfl)
  | (refine SpecLean.Encode.WTree_sub (σ := id) ‹_› ?_ (by decide)
      (fun _ _ _ _ _ _ e => e)
     rd_subargs)
  | (refine SpecLean.Encode.ArgsWF_sub (σ := id) ‹_› ?_
     rd_subargs)
  -- After a write that keeps the shape of an object: the caller's condition still holds.
  | (refine SpecLean.Encode.WTree_sub (σ := id) (SpecLean.Encode.WTree_skel ‹_› ?_ ‹_›) ?_
      (by decide) (fun _ _ _ _ _ _ e => e)
     rd_skel
     rd_subargs)
  | (refine SpecLean.Encode.ArgsWF_sub (σ := id) (SpecLean.Encode.ArgsWF_skel ‹_› ?_ ‹_›) ?_
     rd_skel
     rd_subargs)
  | rd_heapwf)

/-- A call of a callee with a theorem: the theorem `L` of the callee relates the call to the
readable call. Both results are split, and a pair of results that `L` rules out closes. -/
elab "rd_call" "[" ls:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some cs := findClosed t (·.isAppOfArity ``callStop 5) | throwError "rd_call: no call"
  let callee := cs.getArg! 2
  for l in ls.getElems do
    let s ← saveState
    try
      let c ← elabTerm l none
      let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType c)
      -- `ResultMatches gfp fp h vs E (interp env N g vs h) R`
      unless concl.isAppOfArity ``SpecLean.Encode.ResultMatches 8 do
        throwError "rd_call: not a validation theorem"
      let run := concl.getArg! 6
      let rd := concl.getArg! 7
      unless run.isAppOf ``SpecLean.interp && run.getAppNumArgs ≥ 5 do
        throwError "rd_call: no interp"
      unless ← isDefEq (run.getArg! (run.getAppNumArgs - 3)) callee do
        throwError "rd_call: other callee"
      let target ← mkAppM ``SpecLean.interp cs.getAppArgs
      unless ← withTransparency .default (isDefEq run target) do
        throwError "rd_call: the call does not match"
      -- The readable call of the goal: the same head constant.
      let rdh ← instantiateMVars rd
      let some fc := rdh.getAppFn.constName? | throwError "rd_call: no readable head"
      let some rg := findClosed t (fun x => x.isAppOf fc && x.getAppNumArgs == rdh.getAppNumArgs)
        | throwError "rd_call: no readable call"
      unless ← withTransparency .default (isDefEq rdh rg) do
        throwError "rd_call: the readable call does not match"
      -- The hypotheses: from the context, or the caller's footprint.
      for m in ms do
        if (← m.mvarId!.isAssigned) then continue
        let ty ← instantiateMVars (← inferType m)
        if ty.isConstOf ``SpecLean.Encode.Footprint then
          for d in ← getLCtx do
            if d.userName == `gfp then
              m.mvarId!.assign d.toExpr
          continue
        if (← isClass? ty).isSome then
          m.mvarId!.assign (← synthInstance ty)
          continue
        if (← inferType ty).isProp then
          if ← fillFromContext m then continue
          -- A fact about literals, such as the width of a uint class, or the write condition of
          -- the callee from the caller's.
          let gs ← try evalTacticAt (← `(tactic| rd_callhyp)) m.mvarId!
            catch _ =>
              let s2 ← saveState
              let msg ← try
                  let r ← evalTacticAt (← `(tactic| rd_heap)) m.mvarId!
                  let ts ← r.mapM fun g => do return m!"{← g.getType}"
                  pure m!"after rd_heap: {ts}"
                catch e => pure m!"rd_heap failed: {e.toMessageData}"
              restoreState s2
              throwError m!"rd_call: no fact for {ty}; {msg}"
          unless gs.isEmpty do throwError m!"rd_call: no fact for {ty}"
      let pf ← instantiateMVars (mkAppN c ms)
      if pf.hasMVar then throwError "rd_call: open arguments"
      -- The fact about the call as the goal writes it: `callStop`, not `interp`.
      let concl ← instantiateMVars concl
      let cargs := concl.getAppArgs
      let rmOf (x : Lean.Expr) := mkAppN concl.getAppFn ((cargs.set! 6 x).set! 7 rg)
      let eqT ← mkCongrArg (← withLocalDeclD `x (← inferType cs) fun x => do
        mkLambdaFVars #[x] (rmOf x)) (← mkAppM ``callStop_def cs.getAppArgs)
      let hcallPf ← mkEqMPR eqT pf
      let (_, g1) ← (← g.assert `hcall (rmOf cs) hcallPf).intro1P
      let css ← Term.exprToSyntax cs
      let rgs ← Term.exprToSyntax rg
      let hc := mkIdent `hcall
      let rc := mkIdent `rcall
      let rdc := mkIdent `rdcall
      let mut gs := [g1]
      let steps : List (TSyntax `tactic) := [
        ← `(tactic| generalize $css:term = $rc:ident at $hc:ident ⊢),
        ← `(tactic| generalize $rgs:term = $rdc:ident at $hc:ident ⊢),
        ← `(tactic| rcases $rc:ident with _ | ⟨_, _⟩),
        ← `(tactic| all_goals rcases $rdc:ident with _ | _),
        ← `(tactic| all_goals simp only [SpecLean.Encode.ResultMatches] at $hc:ident)]
      for st in steps do
        gs ← gs.flatMapM fun sg => evalTacticAt st sg
      let mut out := []
      for sg in gs do
        out := out ++ (← evalTacticAt (← `(tactic| (
          (try simp only [rd_dec, Option.bind_eq_bind, Option.bind_eq_some_iff, rd_simp,
            Option.pure_def, Option.some.injEq, Value.ref.injEq, exists_eq_left',
            exists_eq_right] at $hc:ident)
          (try rd_split_hyps)
          (try rd_step)))) sg)
      -- `generalize` leaves metadata on the goal.
      let out' ← out.mapM fun sg => do
        sg.replaceTargetDefEq (← instantiateMVars (← sg.getType)).consumeMData
      replaceMainGoal out'
      return
    catch e =>
      restoreState s
      trace[debug] "rd_call {l}: {e.toMessageData}"
  throwError "rd_call: no theorem fits the call"

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- The facts of the items that a proof read from decoded lists: for `l[i]? = some v` and
`∀ y ∈ l, P y`, add `P v`. -/
elab "rd_range" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut added := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq _ lhs rhs := ty | continue
    unless lhs.isAppOfArity ``GetElem?.getElem? 7 do continue
    let_expr Option.some _ v := rhs | continue
    let l := lhs.getArg! 5
    for e in ← getLCtx do
      if e.isImplementationDetail then continue
      let ety ← instantiateMVars e.type
      unless ety.isForall do continue
      let s ← saveState
      try
        let mem ← mkAppM ``List.mem_of_getElem? #[d.toExpr]
        let pf ← mkAppM' e.toExpr #[v, mem]
        let (_, g') ← (← g.assert `hrange (← inferType pf) pf).intro1P
        g := g'
        added := true
        let _ := l
      catch _ => s.restore
  unless added do throwError "rd_range: none"
  replaceMainGoal [g]

end SpecLean.Validation.Tactic

macro_rules | `(tactic| rd_finish) => `(tactic| (rd_range; omega))

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- An item `xs[i]` of a list that a fact decodes: add the decode of the item, split into facts. -/
elab "rd_items" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some x := findClosed t (fun e => e.isAppOfArity ``GetElem.getElem 8 &&
      (e.getArg! 0).isAppOf ``List) | throwError "rd_items: none"
  do
    let xs := x.getArg! 5
    let i := x.getArg! 6
    let p := x.getArg! 7
    -- Only once: a fact that mentions the item means it is decoded already.
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if (ty.find? fun e => e.isAppOfArity ``GetElem.getElem 8 && e.getArg! 5 == xs &&
          e.getArg! 6 == i).isSome then
        throwError "rd_items: decoded already"
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let_expr Eq _ lhs _ := ty | continue
      unless lhs.isAppOf ``List.mapM && lhs.appArg! == xs do continue
      let pf ← mkAppM ``SpecLean.Validation.Decode.mapM_getElem_some #[d.toExpr, i, p]
      let pfs ← Term.exprToSyntax pf
      let xis ← Term.exprToSyntax x
      -- The item becomes a variable: a term `xs[i]` with its bound proof in the facts makes
      -- `simp` build proofs that never end.
      let gs ← evalTacticAt (← `(tactic| (
        obtain ⟨_, _, hitem⟩ := $pfs:term
        generalize hxi : $xis = xitem at hitem ⊢
        clear hxi
        simp only [rd_dec, Option.bind_eq_bind, Option.bind_eq_some_iff, rd_simp,
          Option.pure_def, Option.some.injEq, Value.ref.injEq, exists_eq_left',
          exists_eq_right] at hitem
        rd_split_hyps))) g
      replaceMainGoal gs
      return
  throwError "rd_items: none"

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- Replace a fact `x = S.mk a₁ … aₙ` about the variable `x` by the facts `x.fᵢ = aᵢ`, so that
`x` stays a variable: the proofs of loops keep the readable state small. -/
def projFacts (g : MVarId) (x : FVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq T lhs0 rhs0 := ty | continue
    let (lhs, rhs, hx) ← if lhs0 == mkFVar x then pure (lhs0, rhs0, d.toExpr)
      else if rhs0 == mkFVar x then pure (rhs0, lhs0, ← mkEqSymm d.toExpr)
      else continue
    let some sn := T.getAppFn.constName? | continue
    unless isStructure (← getEnv) sn do continue
    let fields := getStructureFields (← getEnv) sn
    let some ctor := (getStructureCtor (← getEnv) sn).name |> some | continue
    unless rhs.isAppOf ctor do continue
    let args := rhs.getAppArgs
    let nparams := args.size - fields.size
    let mut g := g
    for j in [0:fields.size] do
      let some proj := getProjFnForField? (← getEnv) sn fields[j]! | continue
      let lhsj ← mkAppM proj #[lhs]
      let fn ← withLocalDeclD `s T fun s => do mkLambdaFVars #[s] (← mkAppM proj #[s])
      let pf ← mkCongrArg fn hx
      let tyj ← mkEq lhsj args[nparams + j]!
      let (_, g') ← (← g.assert `hproj tyj pf).intro1P
      g := g'
    return ← g.clear d.fvarId
  return g

/-- `rd_split_hyps`, but the variable `x` keeps its name: its facts are per field. -/
elab "rd_split_keep" x:ident : tactic => withMainContext do
  let xn := (← getLocalDeclFromUserName x.getId).userName
  let g ← splitHyps (← getMainGoal)
  let xv ← g.withContext do return (← getLocalDeclFromUserName xn).fvarId
  let g ← projFacts g xv
  replaceMainGoal [g]
  evalTactic (← `(tactic| try subst_vars))
  replaceMainGoal [← addLengths (← getMainGoal)]

end SpecLean.Validation.Tactic

macro_rules
  | `(tactic| rd_nnp_move) => `(tactic| (
      refine SpecLean.Validation.Move.noNewPaths_sliced (k0 := 0) ‹_› ‹_› ?_ rfl ‹_› ‹_›
        ⟨_, _, _, ‹_›⟩ ‹_›
      rd_callhyp))

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- The frame, the fresh addresses and `NoNewPaths` after a call: the facts of the callee from
the heap at the call, composed with the writes before the call. -/
elab_rules : tactic | `(tactic| rd_after_call) => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some kind := (if t.isAppOfArity ``SpecLean.Encode.Frame 4 then some 0
    else if t.isAppOfArity ``SpecLean.Encode.Fresh 2 then some 1
    else if t.isAppOfArity ``SpecLean.Encode.NoNewPaths 4 then some 2 else none)
    | throwError "rd_after_call: not a frame goal"
  let h2 := t.getArg! 1
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    unless ty.getAppFn == t.getAppFn && ty.getAppNumArgs == t.getAppNumArgs do continue
    unless ty.getArg! 1 == h2 do continue
    let h1 := ty.getArg! 0
    if h1 == t.getArg! 0 then continue
    let hB ← Term.exprToSyntax d.toExpr
    let h1s ← Term.exprToSyntax h1
    let tac ← match kind with
      | 0 => `(tactic| (
          refine SpecLean.Encode.Frame_trans (h2 := $h1s) ?_
            (SpecLean.Encode.Frame_mono_fp $hB (by decide)) ?_
          · rd_frame
          · intro a ha
            first
            | exact ha
            | exact SpecLean.Encode.AtFp_skel ‹_› (by rd_skel) ha))
      | 1 => `(tactic| exact SpecLean.Encode.Fresh_trans (h2 := $h1s) (by rd_frame) $hB)
      | _ => `(tactic| exact SpecLean.Encode.NoNewPaths_trans (h2 := $h1s) (by rd_frame)
          (by rd_frame) $hB)
    let s ← saveState
    try
      let gs ← evalTacticAt tac g
      if gs.isEmpty then
        replaceMainGoal []
        return
      restoreState s
    catch _ => restoreState s
  throwError "rd_after_call: none"

end SpecLean.Validation.Tactic

-- A list index from a `Nat` that a fact says is out of range, against a bound.
macro_rules | `(tactic| rd_finish) => `(tactic| (
  simp only [normIndex_nat] at *
  simp only [ite_eq_right_iff, ite_eq_left_iff, Option.some.injEq, reduceCtorEq, imp_false,
    Nat.not_lt] at *
  omega))

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- A fact that `simp` does not use: the induction hypothesis of a loop proof. -/
@[irreducible] def Hide (p : Prop) : Prop := p
theorem Hide.mk {p : Prop} (h : p) : Hide p := by unfold Hide; exact h
theorem Hide.get {p : Prop} (h : Hide p) : p := by unfold Hide at h; exact h

/-- The goal relates the next iteration of a loop on both sides. -/
elab "rd_loop_tail" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := t.getAppArgs
  unless args.size ≥ 2 && ((args[args.size - 2]!).isAppOf ``SpecLean.execFor || (args[args.size - 2]!).isAppOf ``SpecLean.execWhile) do
    throwError "rd_loop_tail: no"

/-- A hypothesis of a loop theorem: an iteration source, a local, a range or a bound. -/
macro "rd_loophyp" : tactic => `(tactic| first
  | (intro i; simp [SpecLean.iterItem, SpecLean.seqItem, SpecLean.Encode.follow, *])
  | omega
  | (dsimp only; omega)
  | (simp only [SpecLean.Locals.set_apply]
     simp (config := { decide := true }) only [ite_true, ite_false, *]; done)
  | (simp [*]; omega)
  | (simp [rd_simp, *]; omega)
  | rfl)

/-- The next iteration of a loop: the induction hypothesis `Hide _` of the context. -/
macro "rd_ih" : tactic => `(tactic| (
  rd_loop_tail
  have ihh := SpecLean.Validation.Tactic.Hide.get ‹SpecLean.Validation.Tactic.Hide _›
  apply ihh
  all_goals rd_loophyp))

/-- A loop: the loop theorem `L` relates the interpreter's `for` to the readable loop. Both
results are split, with the facts of the relation. -/
elab "rd_loop" "[" ls:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some ex := findClosed t (fun e => e.isAppOf ``SpecLean.execFor || e.isAppOf ``SpecLean.execWhile) | throwError "rd_loop: no loop"
  let some rd := findClosed t (fun e => match e.getAppFn.constName? with
      | some (.str _ s) => s.startsWith "loop"
      | _ => false) | throwError "rd_loop: no readable loop"
  for l in ls.getElems do
    let s ← saveState
    try
      let c ← elabTerm l none
      let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType c)
      let cargs := concl.getAppArgs
      unless cargs.size ≥ 2 do throwError "rd_loop: no relation"
      unless ← isDefEq cargs[cargs.size - 2]! ex do throwError "rd_loop: the loop does not match"
      unless ← isDefEq cargs[cargs.size - 1]! rd do throwError "rd_loop: the readable loop does not match"
      for m in ms do
        if (← m.mvarId!.isAssigned) then continue
        let ty ← instantiateMVars (← inferType m)
        if (← isClass? ty).isSome then
          m.mvarId!.assign (← synthInstance ty)
          continue
        if (← inferType ty).isProp then
          if ← fillFromContext m then continue
          let gs ← try evalTacticAt (← `(tactic| rd_loophyp)) m.mvarId!
            catch _ => throwError m!"rd_loop: no fact for {ty}"
          unless gs.isEmpty do throwError m!"rd_loop: no fact for {ty}"
      let pf ← instantiateMVars (mkAppN c ms)
      if pf.hasMVar then throwError "rd_loop: open arguments"
      let rel := concl.getAppFn
      let some relName := rel.constName? | throwError "rd_loop: no relation name"
      -- The fact names the loop terms of the goal, so `generalize` finds them.
      let cargs' ← cargs.mapM instantiateMVars
      let hty := mkAppN rel (cargs'.extract 0 (cargs'.size - 2) ++ #[ex, rd])
      let (_, g1) ← (← g.assert `hloop hty pf).intro1P
      let exs ← Term.exprToSyntax ex
      let rds ← Term.exprToSyntax rd
      let hc := mkIdent `hloop
      let rc := mkIdent `rloop
      let rdc := mkIdent `rdloop
      let relId := mkIdent relName
      let mut gs := [g1]
      let steps : List (TSyntax `tactic) := [
        ← `(tactic| generalize $exs:term = $rc:ident at $hc:ident ⊢),
        ← `(tactic| generalize $rds:term = $rdc:ident at $hc:ident ⊢),
        ← `(tactic| rcases $rc:ident with _ | ⟨⟨⟩ | ⟨⟩ | ⟨⟩ | _, _, _⟩),
        ← `(tactic| all_goals rcases $rdc:ident with _ | _),
        ← `(tactic| all_goals simp only [$relId:ident] at $hc:ident)]
      for st in steps do
        gs ← gs.flatMapM fun sg => evalTacticAt st sg
      let mut out := []
      for sg in gs do
        out := out ++ (← evalTacticAt (← `(tactic| (
          (try rd_split_hyps)
          (try rd_step)))) sg)
      let out' ← out.mapM fun sg => do
        sg.replaceTargetDefEq (← instantiateMVars (← sg.getType)).consumeMData
      replaceMainGoal out'
      return
    catch e =>
      restoreState s
      trace[debug] "rd_loop {l}: {e.toMessageData}"
  throwError "rd_loop: no theorem fits the loop"

end SpecLean.Validation.Tactic
