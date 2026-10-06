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

end SpecLean.Layer4
