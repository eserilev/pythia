import SpecLean.Validation.Keep
import SpecLean.Validation.FieldKeep
import SpecLean.Validation.BlsBridge
import SpecLean.Validation.SigningRoots

/-!
# Tactic rules of the conditional tier

The conditional theorems (`Gen/Cond.lean`) state more of the result than the tiers do: the
range of each uint argument, and the lengths of new lists. These rules close the goals that
come from that.
-/

/-- A contract goal can hold the range of a list item that the proof read: the item's fact
from the list's facts (`rd_range`). -/
macro_rules
  | `(tactic| rd_frame) =>
    `(tactic| ((repeat' (first | rd_chain | rd_struct_eq | (rd_range; omega) | with_reducible apply And.intro)); done))

namespace SpecLean.Validation.BlsBridge

open SpecLean SpecLean.Rd

theorem mapM_bytes {α : Type} {c : Name} (f : α → Bytes) (xs : List α) :
    (xs.map fun y => Value.bytes c (f y)).mapM
      (fun | .bytes _ b => some b | _ => none) = some (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- The byte strings of a heap list of byte values of one class. -/
theorem byteItems_of_objs {α : Type} {h : Heap} {a : Nat} {k : ListKind} {e : SszTy}
    {l : Option Nat} {c : Name} (f : α → Bytes) (xs : List α)
    (ho : h.objs a = some (.list k e l (xs.map fun y => .bytes c (f y)))) :
    byteItems h (.ref a) = some (xs.map f) := by
  simp only [byteItems, ho]
  exact mapM_bytes f xs

end SpecLean.Validation.BlsBridge

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- A fact `sha.bls m h [.ref a, .bytes .., .bytes ..] = r` of `FastAggregateVerify`, with the
list of keys in the heap: `r` is the readable result (`OracleBls.fastAggregateVerify`). -/
elab "rd_bls" : tactic => withMainContext do
  let some hb := (← getLCtx).findFromUserName? `hb | throwError "rd_bls: no OracleBls"
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Eq _ lhs _ := ty | continue
    unless lhs.getAppNumArgs ≥ 3 do continue
    let args := lhs.getAppArgs
    let some (_, l) := (args[args.size - 1]!).listLit? | continue
    let some pv := l.head? | continue
    let_expr SpecLean.Value.ref a := pv | continue
    for e in ← getLCtx do
      if e.isImplementationDetail then continue
      let ety ← instantiateMVars e.type
      let_expr Eq _ ol _ := ety | continue
      unless ol.isAppOfArity ``SpecLean.Heap.objs 2 do continue
      unless ← isDefEq (ol.getArg! 1) a do continue
      let s ← saveState
      try
        let hbS ← Term.exprToSyntax hb.toExpr
        let eS ← Term.exprToSyntax e.toExpr
        let dS := mkIdent d.userName
        evalTactic (← `(tactic| simp only [($hbS).fastAggregateVerify _ _ _ _ _ _ _
          (SpecLean.Validation.BlsBridge.byteItems_of_objs _ _ $eS)] at $dS:ident))
        return
      catch _ => s.restore
  throwError "rd_bls: none"

end SpecLean.Validation.Tactic

macro_rules
  | `(tactic| rd_finish) =>
    `(tactic| (rd_bls; simp only [Except.ok.injEq, reduceCtorEq] at *; first | done | (subst_vars; rfl)))

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- A direct `hash_tree_root(x)` of a decoded object of class `X`: the readable `htr enc_X x`
becomes the oracle call that the interpreter makes (`htr_codec`), so both sides split on one
result. The decode comes from the facts and `Shaped` from `rd_shaped`. -/
elab "rd_htr" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some rd := findClosed t (·.isAppOf ``SpecLean.Rd.htr) | throwError "rd_htr: no htr"
  let n := rd.getAppNumArgs
  let enc := rd.getArg! (n - 2)
  let x := rd.getArg! (n - 1)
  let some encName := enc.constName? | throwError "rd_htr: no encoder"
  let .str _ s := encName | throwError "rd_htr: no encoder"
  unless s.startsWith "enc_" do throwError "rd_htr: no encoder"
  let codec := mkIdent (Name.mkStr `SpecLean.Validation.HtrBridge ("codec_" ++ (s.drop 4).toString))
  let some ir := findClosed t (·.isAppOfArity ``SpecLean.Oracle.hashTreeRoot 3)
    | throwError "rd_htr: no oracle call"
  let hS ← Term.exprToSyntax (ir.getArg! 1)
  let vS ← Term.exprToSyntax (ir.getArg! 2)
  let xS ← Term.exprToSyntax x
  evalTactic (← `(tactic| (
    have hhtr := SpecLean.Validation.HtrBridge.htr_codec ‹_› $codec (h := $hS) (v := $vS)
      (x := $xS) (by first | assumption | (rd_heap; done) | (rd_heap; rfl)) (by rd_shaped)
    rw [← hhtr])))

end SpecLean.Validation.Tactic

/-- After `rd_htr`, an error of the oracle: never out of fuel, and its class on both sides. -/
macro_rules
  | `(tactic| rd_finish) =>
    `(tactic| (exact fun e => SpecLean.Validation.HtrBridge.OracleHtr.noOof ‹_› _ _ (e ▸ ‹_›)))

/-- The end of a write of one item into a list argument: the new items and their range. -/
macro "rd_item_write_end" : tactic => `(tactic| (
  refine ⟨_, rfl, rfl, ?_⟩
  intro y hy
  first
  | (rcases List.mem_or_eq_of_mem_set hy with hy | hy)
  | (rcases hy with hy | hy)
  all_goals first
    | (have hyr := ‹∀ (y : _), y ∈ _ → _› y hy; simp only [Nat.reducePow] at hyr ⊢; exact hyr)
    | (have hyr := ‹_ < 2 ^ _›; rw [hy]; simp only [Nat.reducePow] at hyr ⊢; exact hyr)))

/-- A list argument is at a pattern rooted at its list type. -/
macro "rd_atfp_list" : tactic => `(tactic| first
  | exact ⟨0, _, [], List.mem_singleton_self _, SpecLean.Encode.rootTy_list rfl ‹_›, trivial, rfl⟩
  | exact ⟨1, _, [], List.mem_singleton_self _, SpecLean.Encode.rootTy_list rfl ‹_›, trivial, rfl⟩
  | exact ⟨2, _, [], List.mem_singleton_self _, SpecLean.Encode.rootTy_list rfl ‹_›, trivial, rfl⟩)

macro_rules | `(tactic| rd_finish) => `(tactic| rd_item_write_end)
macro_rules | `(tactic| rd_finish) => `(tactic| rd_atfp_list)

namespace SpecLean.Validation

/-- A product in a fuel bound, opaque: `omega` reads it as one number, so the bounds stay
linear. Fuel only has to be large enough (`mul_le_bigProd`). -/
@[irreducible] def bigProd (a b : Nat) : Nat := a * b

theorem mul_le_bigProd (a b : Nat) : a * b ≤ bigProd a b := by
  unfold bigProd; exact Nat.le_refl _

theorem bigProd_mono {a b c d : Nat} (hac : a ≤ c) (hbd : b ≤ d) : bigProd a b ≤ bigProd c d := by
  unfold bigProd; exact Nat.mul_le_mul hac hbd

end SpecLean.Validation

open Lean Meta Elab Tactic in
/-- Two facts give one object two different contents. -/
elab "rd_clash" : tactic => withMainContext do
  let g ← getMainGoal
  let mut facts := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, _) := ty.eq? | continue
    if l.isAppOfArity ``SpecLean.Heap.objs 2 then facts := facts.push (d, l)
  for (d1, l1) in facts do
    for (d2, l2) in facts do
      if d1.fvarId == d2.fvarId then continue
      unless l1 == l2 do continue
      let s ← saveState
      try
        let e ← mkEqTrans (← mkEqSymm d1.toExpr) d2.toExpr
        let (_, g1) ← (← g.assert `hcl (← inferType e) e).intro1P
        let gs ← evalTacticAt (← `(tactic| simp (config := { decide := true }) only
          [Option.some.injEq, SpecLean.HeapObj.container.injEq, reduceCtorEq, false_and, and_false] at $(mkIdent `hcl):ident)) g1
        if gs.isEmpty then replaceMainGoal []; return
        restoreState s
      catch _ => restoreState s
  throwError "rd_clash: none"

/-- Object `a` is at no path of the footprint: each pattern with exact steps reaches one object
per argument, and the facts show it is another object. -/
macro "rd_not_atfp" : tactic => `(tactic| (
  rintro ⟨k, pat, q, hmem, ⟨c, hc, -⟩, hm, hat⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  (repeat' (rcases hmem with hmem | hmem)) <;> (try subst hmem) <;>
    rcases q with _ | ⟨q0, _ | ⟨q1, _ | ⟨q2, q⟩⟩⟩ <;>
    (try simp only [SpecLean.Encode.Matches, and_true, true_and, and_false, false_and] at hm) <;>
    (try subst hm) <;>
    (try (obtain ⟨hm1, hm2⟩ := hm; subst hm1; subst hm2)) <;>
    rcases k with _ | _ | _ | _ | _ | k <;>
    (try simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      reduceCtorEq, Option.some.injEq, SpecLean.Value.ref.injEq] at hc) <;>
    (try subst hc) <;>
    (try simp only [SpecLean.Encode.at?, SpecLean.Encode.follow, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.bind_some, Option.bind] at hat) <;>
    (try simp only [*, Option.some.injEq, SpecLean.Value.ref.injEq, reduceCtorEq] at hat) <;>
    (try subst hat) <;>
    rd_clash))

namespace SpecLean.Validation.Tactic
open Lean Meta Elab Tactic

/-- Each fact `x = y` of two local names: one name goes. -/
elab "rd_subst_vv" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut done := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isFVar && r.isFVar && l != r do continue
    try
      let (_, g') ← substCore g d.fvarId (symm := false) (tryToSkip := true)
      g := g'
      done := true
      break
    catch _ => pure ()
  unless done do throwError "rd_subst_vv: none"
  replaceMainGoal [g]

/-- A read `h'.objs a` after a callee that writes (`Frame h h' vs fp`, with `fp` not empty):
an object of `h` at no path of `fp` keeps its contents. -/
elab "rd_frame_fp" : tactic => do
  let g ← getMainGoal
  let found : Option Lean.Expr ← g.withContext do
    let lctx ← getLCtx
    let mut frames : Array LocalDecl := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).isAppOfArity ``SpecLean.Encode.Frame 4 then
        frames := frames.push d
    let mut texts : Array Lean.Expr := #[← instantiateMVars (← g.getType)]
    for d in lctx do
      if d.isImplementationDetail then continue
      texts := texts.push (← instantiateMVars d.type)
    for f in frames do
      let fty ← instantiateMVars f.type
      let h0 := fty.getArg! 0
      let h1 := fty.getArg! 1
      for t in texts do
        for rd in findAllApps (fun e => e.isAppOfArity ``SpecLean.Heap.objs 2 && !e.hasLooseBVars) t do
          unless ← withReducible (isDefEq (rd.getArg! 0) h1) do continue
          let a := rd.getArg! 1
          -- Done before: a kept fact `hfk : h1.objs a = ...`.
          let done ← lctx.anyM fun d => do
            if d.userName.eraseMacroScopes != `hfo then return false
            let some (_, l, _) := (← instantiateMVars d.type).eq? | return false
            return l.isAppOfArity ``SpecLean.Heap.objs 2 && (← withReducible (isDefEq (l.getArg! 1) a))
          if done then continue
          for d in lctx do
            if d.isImplementationDetail then continue
            let ty ← instantiateMVars d.type
            let some (_, l, _) := ty.eq? | continue
            unless l.isAppOfArity ``SpecLean.Heap.objs 2 do continue
            unless ← withReducible (isDefEq (l.getArg! 0) h0) do continue
            unless ← withReducible (isDefEq (l.getArg! 1) a) do continue
            unless (ty.getArg! 2).isAppOfArity ``Option.some 2 do continue
            let s ← saveState
            try
              let notAt ← mkFreshExprMVar (← mkArrow
                (← mkAppM ``SpecLean.Encode.AtFp #[h0, fty.getArg! 2, fty.getArg! 3, a])
                (mkConst ``False))
              let stx ← `(tactic| rd_not_atfp)
              let gs ← Tactic.run notAt.mvarId! (Term.withoutErrToSorry <| withoutRecover <| evalTactic stx)
              unless gs.isEmpty do throwError "not at"
              let pfN ← instantiateMVars notAt
              if pfN.hasSorry || pfN.hasExprMVar then throwError "not at: open proof"
              let neN ← mkFreshExprMVar (← mkAppM ``Ne #[l, ← mkAppOptM ``Option.none #[some (mkConst ``SpecLean.HeapObj)]])
              let stx2 ← `(tactic| (rw [$(← Term.exprToSyntax d.toExpr):term]; exact Option.some_ne_none _))
              let gs2 ← Tactic.run neN.mvarId! (evalTactic stx2)
              unless gs2.isEmpty do throwError "ne none"
              let eq ← mkAppM' f.toExpr #[a, neN, notAt]
              return some (← mkEqTrans eq d.toExpr)
            catch _ => restoreState s
    return none
  let some pf := found | throwError "rd_frame_fp: none"
  let (fo, g1) ← (← g.assert `hfo (← inferType pf) pf).intro1P
  replaceMainGoal [g1]
  -- A fact of the new heap about the same object (a decode after the call): its parts are the
  -- old parts. Else the reads of the goal.
  let unified ← g1.withContext do
    let some (_, l, _) := (← instantiateMVars (← inferType pf)).eq? | return false
    for d in ← getLCtx do
      if d.isImplementationDetail || d.fvarId == fo then continue
      let ty ← instantiateMVars d.type
      let some (_, l2, r2) := ty.eq? | continue
      unless l2 == l && r2.isAppOfArity ``Option.some 2 do continue
      let s ← saveState
      try
        let e ← mkEqTrans (← mkEqSymm d.toExpr) (mkFVar fo)
        let (_, g2) ← (← g1.assert `hinj (← inferType e) e).intro1P
        let gs ← evalTacticAt (← `(tactic| (
          simp only [Option.some.injEq, SpecLean.HeapObj.list.injEq,
            SpecLean.HeapObj.container.injEq, true_and] at $(mkIdent `hinj):ident
          try subst $(mkIdent `hinj):ident))) g2
        replaceMainGoal gs
        return true
      catch _ => restoreState s
    return false
  unless unified do
    evalTactic (← `(tactic| try simp only [$(mkIdent `hfo):ident]))

end SpecLean.Validation.Tactic

/-- The `FieldKeep` part of a writer's contract (`f_pk`, SPEC 9.2). -/
macro_rules | `(tactic| rd_frame) => `(tactic| ((repeat' (first | rd_fieldkeep | rd_chain | rd_struct_eq | with_reducible apply And.intro)); done))

namespace SpecLean.Validation.Tactic
open Lean Meta Elab Tactic

/-- Two reads of one index, `normIndex A i = none` and `normIndex B i = some _`, where the
facts give `A = B`: a value read through a structure fact (`{ .. } = r`) and lengths that
`omega` relates. -/
elab "rd_norm_clash" : tactic => withMainContext do
  let g ← getMainGoal
  let mut nones := #[]
  let mut somes := #[]
  let mut structs : Array Lean.Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    if l.isAppOfArity ``SpecLean.normIndex 2 then
      if r.isAppOfArity ``Option.none 1 then nones := nones.push (d, l)
      else if r.isAppOfArity ``Option.some 2 then somes := somes.push (d, l)
    if l.getAppFn.isConst then
      if let some (.ctorInfo ci) := (← getEnv).find? l.getAppFn.constName! then
        if ci.numFields > 4 then structs := structs.push d.toExpr
  for (dn, ln) in nones do
    for (ds, ls) in somes do
      unless ← withReducible (isDefEq (ln.getArg! 1) (ls.getArg! 1)) do continue
      let s ← saveState
      try
        let eqT ← mkAppM ``Eq #[ln.getArg! 0, ls.getArg! 0]
        let rws ← structs.mapM fun e => do
          `(Lean.Parser.Tactic.simpLemma| ← $(← Term.exprToSyntax e):term)
        let some heq ← proveBy eqT (← `(tactic| (
            (try simp only [$rws,*])
            omega)))
          | throwError "no equality"
        let gs ← evalTacticAt (← `(tactic| exact absurd $(← Term.exprToSyntax dn.toExpr)
          (by rw [$(← Term.exprToSyntax heq):term, $(← Term.exprToSyntax ds.toExpr):term]; simp))) g
        unless gs.isEmpty do throwError "open"
        replaceMainGoal []
        return
      catch _ => restoreState s
  throwError "rd_norm_clash: none"

end SpecLean.Validation.Tactic

macro_rules | `(tactic| rd_finish) => `(tactic| rd_norm_clash)

namespace SpecLean.Validation.Tactic
open Lean Meta Elab Tactic

/-- `normIndex xs.length i = some k` and `xs[k]? = none`: the index is in range, so the read
gives an item. -/
elab "rd_index_none" : tactic => withMainContext do
  let g ← getMainGoal
  let mut somes := #[]
  let mut nones := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    if l.isAppOfArity ``SpecLean.normIndex 2 && r.isAppOfArity ``Option.some 2 then
      somes := somes.push d.toExpr
    if l.isAppOfArity ``GetElem?.getElem? 7 && r.isAppOfArity ``Option.none 1 then
      nones := nones.push d.toExpr
  for hs in somes do
    for hn in nones do
      let s ← saveState
      try
        let gs ← evalTacticAt (← `(tactic| (
          have h1 := SpecLean.Validation.Where.normIndex_lt $(← Term.exprToSyntax hs)
          have h2 := List.getElem?_eq_none_iff.mp $(← Term.exprToSyntax hn)
          omega))) g
        if gs.isEmpty then replaceMainGoal []; return
        restoreState s
      catch _ => restoreState s
  throwError "rd_index_none: none"

end SpecLean.Validation.Tactic

macro_rules | `(tactic| rd_finish) => `(tactic| rd_index_none)
