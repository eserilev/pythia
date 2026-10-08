import SpecLean.Validation.Keep
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
