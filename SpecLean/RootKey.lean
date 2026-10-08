import Lean
import SpecLean.Encode

/-!
# Comparisons with the list root key

`coversAll` (layer 4) tests `Nat.blt pg.ty listRootBase` for each callee pattern. A class name is
a constant that unfolds to a literal, so `simp` does not compare it on its own.
-/

namespace SpecLean.Encode


open Lean Meta Simp in
/-- `Nat.blt ty b` of two names that unfold to literals (`Scope.Id.BeaconState`,
`listRootBase`): its value, by the kernel's fast comparison. -/
simproc ↓ reduceBltName (Nat.blt _ _) := fun e => do
  let_expr Nat.blt a b := e | return .continue
  let some an := (← whnfD a).rawNatLit? <|> (← instantiateMVars (← whnfD a)).nat?
    | return .continue
  let some bn := (← whnfD b).rawNatLit? <|> (← instantiateMVars (← whnfD b)).nat?
    | return .continue
  return .done { expr := toExpr (Nat.blt an bn) }

end SpecLean.Encode
