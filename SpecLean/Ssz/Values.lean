import SpecLean.Heap

/-!
# eth-ssz-specs: value rules

The library model for SSZ values: uints of a class (`Uint64`, `Gwei`) and `Boolean`. The rules
come from probes (`tools/probes/value_rules.py`). Each hook gives `none` for a pair of plain
Python values, and the core applies Python rules.
-/

namespace SpecLean

/-- The result class of an operation on two uints: the more derived class wins.
Unrelated classes raise `TypeError`. -/
def resolveUint : UintTy → UintTy → Res UintTy
  | .width b, .width b' => if b = b' then .ok (.width b) else .error .typeError
  | .width b, .nominal n b' => if b = b' then .ok (.nominal n b') else .error .typeError
  | .nominal n b, .width b' => if b = b' then .ok (.nominal n b) else .error .typeError
  | .nominal n b, .nominal n' b' =>
    if n = n' ∧ b = b' then .ok (.nominal n b) else .error .typeError

/-- `cls._wrap`: the range check of a uint result. -/
def wrapUint (t : UintTy) (r : Int) : Res Value :=
  if 0 ≤ r ∧ r < 2 ^ t.bits then .ok (.uint t r.toNat) else .error .sszValue

/-- Element write of a value that is not a heap object, into a list
(`_SSZList._validate_element`). The exact class passes. An ancestor class (a plain `int` or
the width class) is wrapped with a range check. Anything else raises `SSZTypeError`. -/
def coerceElem : SszTy → Value → Res Value
  | .uint t, .uint t' n =>
    if t' = t then .ok (.uint t n)
    else if t' = .width t.bits then wrapUint t n
    else .error .typeError
  | .uint t, .int n => wrapUint t n
  | .container _, .ref a => .ok (.ref a)
  | .boolean, .boolean b => .ok (.boolean b)
  | .boolean, .bool b => .ok (.boolean b)
  | .boolean, .int n =>
    if n = 0 then .ok (.boolean false) else if n = 1 then .ok (.boolean true)
    else .error .sszValue
  | .bytes ty len, .bytes _ b => if b.length = len then .ok (.bytes ty b) else .error .sszValue
  | .any, v => .ok v
  | _, _ => .error .typeError

/-- Field write of a value that is not a heap object, into a container (pydantic
`validate_assignment`). The field schema is a strict `int` in range, so every uint class
passes, siblings included. A subclass of the field type keeps its class (probed: `Slot` into a
`Uint64` field stays `Slot`). A range failure raises a pydantic `ValidationError`. -/
def coerceField : SszTy → Value → Res Value
  | .uint t, .uint t' n =>
    if n < 2 ^ t.bits then
      .ok (.uint (if t'.subOf t then t' else t) n)
    else .error .validation
  | .uint t, .int n =>
    if 0 ≤ n ∧ n < 2 ^ t.bits then .ok (.uint t n.toNat) else .error .validation
  -- A Python `bool` passes. An `int`, even 0 or 1, does not (probed).
  | .boolean, .boolean b => .ok (.boolean b)
  | .boolean, .bool b => .ok (.boolean b)
  | .boolean, _ => .error .validation
  | .bytes ty len, .bytes _ b => if b.length = len then .ok (.bytes ty b) else .error .validation
  | .any, v => .ok v
  | _, _ => .error .validation

end SpecLean

namespace SpecLean.Ssz

/-- A binary operator with a uint or a `Boolean` operand. A plain `int` operand takes the class
of the uint operand. The class check comes before the arithmetic, as in `BaseUint.__add__`. A
`bool` on the left uses `int` rules (probed): `True + Uint64(1)` is the `int` 2. A `bool` on
the right raises `TypeError`. -/
def binop (op : BinOp) : Value → Value → Option (Res Value)
  | .uint t a, .uint t' b => some do
    let r ← resolveUint t t'
    wrapUint r (← intArith op a b)
  | .uint t a, .int b => some do wrapUint t (← intArith op a b)
  | .int a, .uint t b => some do wrapUint t (← intArith op a b)
  | .boolean _, _ | _, .boolean _ => some (.error .typeError)
  | .bool a, .uint _ b => some (.int <$> intArith op (if a then 1 else 0) b)
  | .uint _ _, .bool _ => some (.error .typeError)
  | _, _ => none

/-- A unary operator on a uint or a `Boolean`. `-x` and `~x` of a uint give a plain `int`. -/
def unop : UnOp → Value → Option (Res Value)
  | .neg, .uint _ n => some (.ok (.int (-(n : Int))))
  | .invert, .uint _ n => some (.ok (.int (Int.not n)))
  | _, .boolean _ => some (.error .typeError)
  | _, _ => none

/-- A comparison with a uint or a `Boolean` operand. Two uints need related classes, as in
`BaseUint._require_relation`. A uint against a value that is not an `int` or a uint raises
`TypeError`. `Boolean` is nominal: it does not compare with `bool`, `int` or a uint. A `bool`
on the left compares as an `int` (probed): `True == Gwei(0)` is `False`. -/
def compare (op : CmpOp) : Value → Value → Option (Res Bool)
  | .uint t a, .uint t' b => some do
    let _ ← resolveUint t t'
    pure (cmpInt op a b)
  | .uint _ a, .int b => some (.ok (cmpInt op a b))
  | .int a, .uint _ b => some (.ok (cmpInt op a b))
  | .boolean a, .boolean b =>
    some (match op with
      | .eq => .ok (a == b)
      | .notEq => .ok (a != b)
      | _ => .error .unsupported)
  | .boolean _, _ | _, .boolean _ => some (.error .typeError)
  | .bool a, .uint _ b => some (.ok (cmpInt op (if a then 1 else 0) b))
  | .uint _ _, _ | _, .uint _ _ => some (.error .typeError)
  | _, _ => none

def truthy : Value → Option (Res Bool)
  | .boolean b => some (.ok b)
  | .uint _ n => some (.ok (n != 0))
  | _ => none

def index : Value → Option (Res Int)
  | .uint _ n => some (.ok n)
  | _ => none

instance values : LibValues where
  binop := binop
  unop := unop
  compare := compare
  truthy := truthy
  index := index

/-! ## The core functions on SSZ values -/

@[simp] theorem toIndex_uint (t : UintTy) (n : Nat) : toIndex (.uint t n) = .ok (n : Int) := by
  simp only [toIndex, LibValues.index, index]

@[simp] theorem toIndex_int (n : Int) : toIndex (.int n) = .ok n := by
  simp only [toIndex, LibValues.index, index, pyIndex]

@[simp] theorem truthy_bool (b : Bool) : SpecLean.truthy (.bool b) = .ok b := by
  simp only [SpecLean.truthy, LibValues.truthy, Ssz.truthy, pyTruthy]

@[simp] theorem truthy_boolean (b : Bool) : SpecLean.truthy (.boolean b) = .ok b := by
  simp only [SpecLean.truthy, LibValues.truthy, Ssz.truthy]

@[simp] theorem truthy_uint (t : UintTy) (n : Nat) :
    SpecLean.truthy (.uint t n) = .ok (n != 0) := by
  simp only [SpecLean.truthy, LibValues.truthy, Ssz.truthy]

@[simp] theorem truthy_int (n : Int) : SpecLean.truthy (.int n) = .ok (n != 0) := by
  simp only [SpecLean.truthy, LibValues.truthy, Ssz.truthy, pyTruthy]

theorem binopVal_uint (op : BinOp) (t t' : UintTy) (a b : Nat) :
    binopVal op (.uint t a) (.uint t' b) = (do
      let r ← resolveUint t t'
      wrapUint r (← intArith op a b)) := by
  simp only [binopVal, LibValues.binop, binop]

theorem binopVal_uint_int (op : BinOp) (t : UintTy) (a : Nat) (b : Int) :
    binopVal op (.uint t a) (.int b) = (do wrapUint t (← intArith op a b)) := by
  simp only [binopVal, LibValues.binop, binop]

theorem cmpVal_uint (op : CmpOp) (t t' : UintTy) (a b : Nat) :
    cmpVal op (.uint t a) (.uint t' b) = (do
      let _ ← resolveUint t t'
      pure (cmpInt op a b)) := by
  simp only [cmpVal, LibValues.compare, compare]

end SpecLean.Ssz
