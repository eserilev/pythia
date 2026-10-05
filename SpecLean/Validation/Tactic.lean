import Lean
import SpecLean.Encode
import SpecLean.Validation.Attr
import SpecLean.Validation.Decode
import SpecLean.Validation.Where
import SpecLean.Validation.Local

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
  ``SpecLean.LibModel.builtin, ``SpecLean.Ssz.builtin, ``SpecLean.fromBytes, ``SpecLean.setItem,
  ``SpecLean.setAttr, ``SpecLean.coerceWith, ``SpecLean.LibModel.coerce, ``SpecLean.Ssz.coerce, ``SpecLean.coerceField]

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
    f.isConstOf ``Option.none || f.isConstOf ``Pure.pure || a.isFVar || isDecoder f

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
    if let some gs ← splitDecodedIndex g x then
      replaceMainGoal gs
      return
    let gs ← evalTacticAt
      (← `(tactic| (generalize hx : $(← Term.exprToSyntax x) = r; cases r))) g
    replaceMainGoal gs

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

/-- One evaluation step on both sides of the goal. -/
macro "rd_step" : tactic => `(tactic| simp [rd_simp, SpecLean.Validation.Tactic.unfold_known,
  SpecLean.Validation.Tactic.fieldIndex_lit, SpecLean.Encode.ResultMatches, *] at ⊢)

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
          $(← Term.exprToSyntax py) (by simp))
        let pf ← Term.withoutErrToSorry do
          let pf ← Term.elabTermEnsuringType stx (← inferType g')
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars pf
        if pf.hasExprMVar || pf.hasSorry then throwError "no proof"
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
  unless ← proveNe g do throwError "rd_ne: no proof"

/-- The side conditions of the heap steps: two addresses differ, or no object that the items
of a list reach is the written one. -/
macro "rd_disch" : tactic => `(tactic| first
  | (rd_ne; done)
  | (intro j x hj; unfold SpecLean.Validation.Local.Away; intro q c hf; rd_ne; done)
  | (unfold SpecLean.Validation.Local.Away; intro q c hf; rd_ne; done)
  | assumption
  | decide
  | (intro y; with_unfolding_all rfl))

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- The decode facts of the context: objects, fields and items, decoded lists. -/
def heapFacts : MetaM (Array Lean.Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq _ lhs _ := ty | continue
    if (lhs.isApp && lhs.appFn!.isAppOf ``SpecLean.Heap.objs) ||
        lhs.isAppOfArity ``GetElem?.getElem? 7 || lhs.isAppOf ``List.mapM then
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
    SpecLean.Validation.Where.objs_set_ne, SpecLean.Validation.Where.objs_set_self, rd_dec,
    SpecLean.Rd.containerFieldsT, SpecLean.Rd.decUintT, SpecLean.Rd.decBytesT,
    SpecLean.Rd.decBooleanV, SpecLean.Rd.decListT, SpecLean.Validation.Local.mapM_set_away,
    SpecLean.Validation.Decode.mapM_map_of, SpecLean.Validation.Decode.mapM_set_map,
    List.getElem?_set_ne, List.getElem?_set_self', Option.map_eq_map, Option.map_some,
    Function.const_apply, $args,*]))

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
  unless ← proveAtFp (← getMainGoal) do throwError "rd_atfp: no proof"

/-- Read an object of a heap after writes: `h1.objs a = some ?o`. -/
elab "rd_objs" : tactic => withMainContext do
  let facts ← heapFacts
  let mut args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for f in facts do
    args := args.push (← `(Lean.Parser.Tactic.simpLemma| $(← Term.exprToSyntax f):term))
  evalTactic (← `(tactic| simp (disch := rd_disch) only
    [SpecLean.Validation.Where.objs_set_ne, SpecLean.Validation.Where.objs_set_self,
     List.getElem?_set_ne, List.getElem?_set_self', Option.map_eq_map, Option.map_some,
     Function.const_apply, $args,*]))
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
  let t ← instantiateMVars (← getMainTarget)
  unless t.isAppOfArity ``And 2 do throwError "rd_and: not a conjunction"
  evalTactic (← `(tactic| apply And.intro))

/-- The frame, the fresh addresses and the reach of a run of writes. -/
macro "rd_frame" : tactic => `(tactic| repeat' (first
  | exact SpecLean.Encode.Frame_refl _ _ _
  | exact SpecLean.Encode.Fresh_refl _
  | exact SpecLean.Encode.Reach_refl _ _
  | rd_atfp
  | (rd_objs; done)
  | rd_skel
  | refine SpecLean.Validation.Where.frame_set ?_ ?_
  | apply SpecLean.Validation.Where.fresh_set
  | apply SpecLean.Validation.Where.reach_set
  | rfl
  | rd_and))

end SpecLean.Validation.Tactic
