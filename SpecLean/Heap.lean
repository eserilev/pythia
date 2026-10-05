import SpecLean.Value

/-!
# Heap

Lists, containers, dicts, sets and closures live in the heap, as in Python. A `Value.ref`
points at them.
-/

namespace SpecLean

inductive ListKind where
  | list | vector | progressiveList | bitlist | bitvector | progressiveBitlist
  /-- A plain Python `list`: no element type and no limit. -/
  | pyList
  deriving DecidableEq, Repr

/-- The SSZ type of a list element or a container field. `any` is a field of a Python
dataclass, or an element of a Python list: no coercion. -/
inductive SszTy where
  | uint (t : UintTy)
  | boolean
  /-- A fixed-size byte vector class, for example `Bytes32`. -/
  | bytes (ty : Name) (len : Nat)
  | container (ty : Name)
  | list (kind : ListKind) (elem : SszTy) (limit : Option Nat)
  | any
  deriving Repr, DecidableEq

/-- Local variables of one call frame. -/
abbrev Locals := Name → Option Value

/-- The body of a closure: a `lambda` expression or the statements of a nested `def`. -/
inductive ClosureBody where
  | expr (e : Expr)
  | stmts (ss : List Stmt)

inductive HeapObj where
  | list (kind : ListKind) (elem : SszTy) (limit : Option Nat) (xs : List Value)
  | container (ty : Name) (fields : List Value)
  /-- Insertion order, as Python keeps it. -/
  | dict (entries : List (Value × Value))
  /-- Insertion order. Spec code iterates a set only through `sorted` (SPEC 6.3). -/
  | set (elems : List Value)
  /-- A `lambda` or a nested `def`. `captured` is the frame where it was made. Spec code calls
  a closure before that frame changes the names it reads, so a snapshot is enough. -/
  | closure (params : Params) (body : ClosureBody) (captured : Locals)

structure Heap where
  objs : Nat → Option HeapObj
  next : Nat

namespace Heap

def empty : Heap := ⟨fun _ => none, 0⟩

def set (h : Heap) (a : Nat) (o : HeapObj) : Heap :=
  { h with objs := fun b => if b = a then some o else h.objs b }

def alloc (h : Heap) (o : HeapObj) : Nat × Heap :=
  (h.next, { objs := fun b => if b = h.next then some o else h.objs b, next := h.next + 1 })

@[simp] theorem set_objs (h : Heap) (a : Nat) (o : HeapObj) (b : Nat) :
    (h.set a o).objs b = if b = a then some o else h.objs b := by
  simp only [Heap.set]

@[simp] theorem set_next (h : Heap) (a : Nat) (o : HeapObj) : (h.set a o).next = h.next := by
  simp only [Heap.set]

end Heap

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
  | _, _ => .error .unsupported

/-- Field write of a value that is not a heap object, into a container (pydantic
`validate_assignment`). The field schema is a strict `int` in range, so every uint class
passes, siblings included. A range failure raises a pydantic `ValidationError`. -/
def coerceField : SszTy → Value → Res Value
  | .uint t, .uint _ n => if n < 2 ^ t.bits then .ok (.uint t n) else .error .validation
  | .uint t, .int n =>
    if 0 ≤ n ∧ n < 2 ^ t.bits then .ok (.uint t n.toNat) else .error .validation
  -- A Python `bool` passes. An `int`, even 0 or 1, does not (probed).
  | .boolean, .boolean b => .ok (.boolean b)
  | .boolean, .bool b => .ok (.boolean b)
  | .boolean, _ => .error .validation
  | .bytes ty len, .bytes _ b => if b.length = len then .ok (.bytes ty b) else .error .validation
  | .any, v => .ok v
  | _, _ => .error .unsupported

end SpecLean
