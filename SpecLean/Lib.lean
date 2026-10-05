import SpecLean.Env

/-!
# The library model

The core interprets Python. A library adds classes with their own rules: for the spec, the SSZ
types of eth-ssz-specs (`SpecLean/Ssz`). The core asks the library first, at each point below.
A hook that gives `none` leaves the operation to plain Python rules.
-/

namespace SpecLean

class LibModel extends LibValues where
  /-- Coerce `v` for an element (`field = false`) or a field (`field = true`) of type `t`. -/
  coerce : Env → Bool → Heap → SszTy → Value → Option (Res (Value × Heap))
  /-- `x op y` where an operand is a heap object. -/
  binopH : Env → Heap → BinOp → Value → Value → Option (Res (Value × Heap))
  /-- `T(args)` for a library class `T`. -/
  construct : Env → Heap → SszTy → List Value → List (Name × Value) → Res (Value × Heap)
  /-- `self.m(args)`. -/
  method : Env → Heap → Value → Name → List Value → Option (Res (Value × Heap))
  /-- `obj.append(v)` on the list at `a`. -/
  append : Env → Heap → Nat → Value → Option (Res Heap)
  /-- `obj[lo:hi] = vals` on the list at `a`, with the bounds resolved. -/
  setSlice : Env → Heap → Nat → Nat → Nat → List Value → Option (Res Heap)
  /-- A builtin call. -/
  builtin : Env → Heap → Builtin → List Value → List (Name × Value) →
    Option (Res (Value × Heap))

variable [LibModel]

/-- Coerce `v` for an element or a field of type `t`: the library rule, else no change. -/
def coerceWith (env : Env) (field : Bool) (h : Heap) (t : SszTy) (v : Value) :
    Res (Value × Heap) :=
  match LibModel.coerce env field h t v with
  | some r => r
  | none => .ok (v, h)

end SpecLean
