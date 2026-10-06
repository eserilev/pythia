import SpecLean.Validation.Tactic
import SpecLean.Validation.LoopRule

/-!
# The tactic steps of the loop rule (SPEC 9.3)

A loop step of `for_rule` ends in `IterK`: a normal end gives the contract from the heap at the
start of the step and the invariant, an error gives an error of the same class. The steps here
close these goals. They read the goal syntactically: a unification of two heaps at default
transparency computes the store of the heap, and that does not end.
-/

/-- `rd_skel` without `simp_all`: a loop step has a large context, and `simp_all` on it does not
end. -/
macro "rd_skel_safe" : tactic => `(tactic| first
  | (with_reducible apply SpecLean.Validation.Where.sameSkel_list_set <;>
      first
      | exact SpecLean.Validation.Where.noRef_map_uint _ _ _
      | exact SpecLean.Validation.Where.noRef_map_bytes _ _ _
      | exact SpecLean.Validation.Where.noRef_map_boolean _ _
      | exact SpecLean.Validation.Where.noRef_uint _ _
      | exact SpecLean.Validation.Where.noRef_bytes _ _
      | exact SpecLean.Validation.Where.noRef_boolean _)
  | (with_reducible apply SpecLean.Validation.Where.sameSkel_container_set <;>
      first
      | (rd_item_of; first
          | exact SpecLean.Validation.Where.noRef_uint _ _
          | exact SpecLean.Validation.Where.noRef_bytes _ _
          | exact SpecLean.Validation.Where.noRef_boolean _)
      | exact SpecLean.Validation.Where.noRef_uint _ _
      | exact SpecLean.Validation.Where.noRef_bytes _ _
      | exact SpecLean.Validation.Where.noRef_boolean _))

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic SpecLean SpecLean.Encode SpecLean.Validation

/-- Two facts `e = some a` and `e = some b` on the same `e`: `a = b`, split and substituted. It
fails when it substitutes nothing. -/
elab "rd_unify" : tactic => withMainContext do
  let g ← getMainGoal
  let mut seen : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless r.isAppOfArity ``Option.some 2 do continue
    for (l', r', d') in seen do
      unless l' == l do continue
      if r' == r then continue
      let s ← saveState
      try
        let pf ← mkAppM ``Option.some.inj #[← mkEqTrans (← mkEqSymm d') d.toExpr]
        let (_, g1) ← (← g.assert `hsame (← inferType pf) pf).intro1P
        let hs := mkIdent `hsame
        let gs ← evalTacticAt (← `(tactic| (
          simp only [SpecLean.HeapObj.container.injEq, SpecLean.HeapObj.list.injEq,
            SpecLean.Value.ref.injEq, true_and, and_true] at $hs:ident
          repeat (obtain ⟨hs1, $hs:ident⟩ := $hs:ident; subst hs1)
          subst $hs:ident))) g1
        replaceMainGoal gs
        return
      catch _ => restoreState s
    seen := seen.push (l, r, d.toExpr)
  throwError "rd_unify: none"

/-- The fact `h.objs a = some o` of the context, found by syntax. -/
def findObj (h a : Lean.Expr) : MetaM (Option Lean.Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless r.isAppOfArity ``Option.some 2 do continue
    unless l.isAppOfArity ``SpecLean.Heap.objs 2 do continue
    if l.getArg! 0 == h && l.getArg! 1 == a then return some d.toExpr
  return none

/-- `RootsKept h h' vs`, where `h'` is `h` after writes that keep the shape of each object. -/
partial def rootsKept (g : MVarId) : TacticM Unit := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``SpecLean.Encode.RootsKept 3 do throwError "rd_roots: not RootsKept"
  let h := t.getArg! 0
  let h' := t.getArg! 1
  let vs := t.getArg! 2
  if h == h' then
    g.assign (← mkAppM ``RootsKept_refl #[h, vs])
    return
  unless h'.isAppOfArity ``SpecLean.Heap.set 3 do throwError "rd_roots: not a write"
  let h1 := h'.getArg! 0
  let a := h'.getArg! 1
  let some ho ← findObj h1 a | throwError "rd_roots: no object"
  let hs ← Term.exprToSyntax ho
  let tac ← if h1 == h then `(tactic| exact RootsKept_skel $hs (by rd_skel_safe) _)
    else do
      let h1s ← Term.exprToSyntax h1
      `(tactic| refine RootsKept_trans (h2 := $h1s) ?_ (RootsKept_skel $hs (by rd_skel_safe) _))
  let gs ← evalTacticAt tac g
  for g' in gs do rootsKept g'

elab "rd_roots" : tactic => do rootsKept (← getMainGoal)

/-- The frame, the fresh addresses and the reach from `h` to `h'`, where `h'` is `h` after
writes that keep the shape of each object. It reads the chain of writes by syntax. -/
partial def writes (g : MVarId) : TacticM Unit := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some kind := (if t.isAppOfArity ``SpecLean.Encode.Frame 4 then some 0
      else if t.isAppOfArity ``SpecLean.Encode.Fresh 2 then some 1
      else if t.isAppOfArity ``SpecLean.Encode.Reach 3 then some 2
      else if t.isAppOfArity ``SpecLean.Encode.NoNewPaths 4 then some 3 else none)
    | throwError "rd_writes: not a frame goal"
  if kind == 3 then
    let gs ← evalTacticAt (← `(tactic| apply SpecLean.Encode.noNewPaths_of_reach)) g
    for g' in gs do writes g'
    return
  let h := t.getArg! 0
  let h' := t.getArg! 1
  if h == h' then
    let tac ← match kind with
      | 0 => `(tactic| exact SpecLean.Encode.Frame_refl _ _ _)
      | 1 => `(tactic| exact SpecLean.Encode.Fresh_refl _)
      | _ => `(tactic| exact SpecLean.Encode.Reach_refl _ _)
    let gs ← evalTacticAt tac g
    unless gs.isEmpty do throwError "rd_writes: refl"
    return
  unless h'.isAppOfArity ``SpecLean.Heap.set 3 do throwError "rd_writes: not a write"
  let h1 := h'.getArg! 0
  let a := h'.getArg! 1
  let h1s ← Term.exprToSyntax h1
  let hos ← match ← findObj h1 a with
    | some ho => Term.exprToSyntax ho
    | none => `((by rd_objs))
  let tac ← match kind with
    | 0 => `(tactic| refine SpecLean.Validation.Where.frame_set (h1 := $h1s) ?_ (by rd_atfp))
    | 1 => `(tactic| refine SpecLean.Validation.Where.fresh_set (h1 := $h1s) ?_ $hos)
    | _ => `(tactic| refine SpecLean.Validation.Where.reach_set (h1 := $h1s) ?_ ?_ $hos (by rd_skel_safe))
  let gs ← evalTacticAt tac g
  for g' in gs do writes g'

elab "rd_writes" : tactic => do writes (← getMainGoal)

/-- A fact `P h` of the context, for a heap `h`, with `P` a constant of arity `n`. -/
def findHeapFact (c : Lean.Name) (n : Nat) (pos : Nat) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity c n then out := out.push (ty.getArg! pos, d.toExpr)
  return out

/-- `WTree`, `ArgsWF` and `HeapWF` of a heap after writes that keep the shape of each object,
from the same fact before the writes. -/
partial def wfAfter (g : MVarId) : TacticM Unit := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some (c, n, pos) := (if t.isAppOfArity ``SpecLean.Encode.WTree 3 then
        some (``SpecLean.Encode.WTree, 3, 0)
      else if t.isAppOfArity ``SpecLean.Encode.ArgsWF 2 then some (``SpecLean.Encode.ArgsWF, 2, 0)
      else if t.isAppOfArity ``SpecLean.Encode.HeapWF 1 then some (``SpecLean.Encode.HeapWF, 1, 0)
      else none) | throwError "rd_wf: not a well-formedness goal"
  let h' := t.getArg! pos
  for (h, d) in ← findHeapFact c n pos do
    if h == h' then
      let ds ← Term.exprToSyntax d
      let gs ← evalTacticAt (← `(tactic| exact $ds)) g
      unless gs.isEmpty do throwError "rd_wf: exact"
      return
  if c == ``SpecLean.Encode.HeapWF then
    -- From any older heap: the writes only add fresh objects.
    for (h, d) in ← findHeapFact c n pos do
      let s ← saveState
      try
        let ds ← Term.exprToSyntax d
        let gs ← evalTacticAt
          (← `(tactic| refine SpecLean.Validation.Where.heapWF_of_fresh $ds ?_)) g
        for g' in gs do writes g'
        let _ := h
        return
      catch _ => restoreState s
    throwError "rd_wf: no older HeapWF"
  unless h'.isAppOfArity ``SpecLean.Heap.set 3 do throwError "rd_wf: not a write"
  let h1 := h'.getArg! 0
  let a := h'.getArg! 1
  let some ho ← findObj h1 a | throwError "rd_wf: no object"
  let hs ← Term.exprToSyntax ho
  let tac ← if c == ``SpecLean.Encode.WTree then
      `(tactic| refine SpecLean.Encode.WTree_skel $hs (by rd_skel_safe) ?_)
    else `(tactic| refine SpecLean.Encode.ArgsWF_skel $hs (by rd_skel_safe) ?_)
  let gs ← evalTacticAt tac g
  for g' in gs do wfAfter g'

elab "rd_wf" : tactic => do wfAfter (← getMainGoal)

/-- The goal is `IterK … (.ok (.normal, L, h)) (K s)`: the step ends normally on both sides. -/
elab "rd_iter_shape" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isAppOf ``SpecLean.Validation.IterK do throwError "rd_iter_shape: not IterK"
  let args := t.getAppArgs
  let run := args[args.size - 2]!
  let rd := args[args.size - 1]!
  unless run.isAppOfArity ``Except.ok 3 do throwError "rd_iter_shape: no normal end"
  let p := run.getArg! 2
  unless p.isAppOfArity ``Prod.mk 4 && (p.getArg! 2).isConstOf ``SpecLean.Outcome.normal do
    throwError "rd_iter_shape: no normal end"
  unless rd.getAppFn.isFVar do throwError "rd_iter_shape: no continuation"

end SpecLean.Validation.Tactic

/-- The contract of a loop step: the frame, the fresh addresses, no new paths, the roots. -/
-- `focus`, not `·`: a `·` in a macro recovers from an error, so a failed step goes unseen.
macro "rd_contract" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_⟩
  focus rd_writes
  focus rd_writes
  focus rd_writes
  focus rd_roots))

/-- An error of the same class ends the step. -/
macro "rd_iter_err" : tactic => `(tactic| (
  with_reducible apply SpecLean.Validation.iterK_error
  first
  | assumption
  | (constructor <;> first | assumption | rd_oof | rfl | (simp [SpecError.fail]; done))))

/-- A conjunct of the loop invariant after a normal end of a step. -/
macro "rd_inv_part" : tactic => `(tactic| first
  | with_reducible assumption
  | (simp (config := { decide := true }) only [SpecLean.Locals.set_apply, ite_true, ite_false]
     first | with_reducible assumption | rfl)
  | (rd_objs; done)
  | rd_wf
  | ((set_option maxHeartbeats 400000 in rd_heap)
     (try simp only [SpecLean.Rd.UintC.ofNat, SpecLean.Rd.BytesC.ofBytes])
     (try simp only [SpecLean.Validation.Steps.toNat_natCast_emod_lit,
       SpecLean.Validation.Steps.toNat_natCast_sub_emod_lit])
     first | done | with_reducible rfl))

open Lean Elab Tactic in
/-- A normal end of a loop step: the contract and each conjunct of the invariant. The invariant
is a definition: `rd_iter_ok` unfolds it. -/
elab "rd_iter_ok" : tactic => withMainContext do
  evalTactic (← `(tactic| (rd_iter_shape; apply SpecLean.Validation.iterK_normal)))
  evalTactic (← `(tactic| rd_contract))
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some inv := t.getAppFn.constName? | throwError "rd_iter_ok: no invariant"
  let invId := mkIdent inv
  evalTactic (← `(tactic| (
    unfold $invId:ident
    repeat' rd_and
    all_goals rd_inv_part)))

/-- The end of a loop step: an error, a contradiction, or a normal end. -/
macro "rd_iter_end" : tactic => `(tactic| first
  | rd_iter_err
  | (exfalso; omega)
  | with_reducible contradiction
  | (simp only [SpecLean.normIndex_nat] at *
     simp only [ite_eq_right_iff, ite_eq_left_iff, Option.some.injEq, reduceCtorEq, imp_false,
       Nat.not_lt, List.getElem?_eq_none_iff] at *
     omega)
  | rd_iter_ok)
