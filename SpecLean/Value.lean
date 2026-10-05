import SpecLean.Ast

/-!
# Values and value rules

The rules come from probes against `eth-ssz-specs` (`tools/probes/value_rules.py`).
-/

namespace SpecLean

/-- A uint class. `width b` is `Uint8`, `Uint64` and so on. `nominal n b` is a subclass of
`width b` with the interned class name `n`, for example `Gwei`. The probes show that no class
derives from a nominal class. -/
inductive UintTy where
  | width (bits : Nat)
  | nominal (name : Name) (bits : Nat)
  deriving DecidableEq, Repr

def UintTy.bits : UintTy → Nat
  | .width b => b
  | .nominal _ b => b

/-- The diagnostic of an error (SPEC 6.4). Proofs compare only the class (`Fail`), never the
diagnostic. `outOfFuel` is not a Python error and never matches. -/
inductive SpecError where
  | assertionFailed
  /-- `SSZValueError`: a uint out of range, or a list over its limit. -/
  | sszValue
  /-- pydantic `ValidationError`, from a container field write. -/
  | validation
  | indexError
  | valueError
  | divisionByZero
  | typeError
  | keyError
  | nameError
  /-- A `raise` statement. -/
  | raised
  /-- A construct or a value pair that the interpreter does not model yet. -/
  | unsupported
  | outOfFuel
  deriving DecidableEq, Repr

abbrev Res := Except SpecError

/-- The error class that proofs compare (SPEC 9.2). `invalid` is an `AssertionError` or an
`IndexError`: the input is not valid. Every other exception is `bug`. -/
inductive Fail where
  | invalid | bug
  deriving DecidableEq, Repr

def SpecError.fail : SpecError → Fail
  | .assertionFailed | .indexError => .invalid
  | _ => .bug

inductive Value where
  | int (n : Int)
  | uint (t : UintTy) (n : Nat)
  /-- Python `bool`. -/
  | bool (b : Bool)
  /-- SSZ `Boolean`. It is nominal: `Boolean == True` raises `TypeError`. -/
  | boolean (b : Bool)
  | str (s : String)
  | none
  /-- A byte string. `ty` is the interned class name: `Bytes32`, `Root`, `bytes` and so on. -/
  | bytes (ty : Name) (b : List UInt8)
  /-- A list, container, dict, set or closure in the heap. -/
  | ref (addr : Nat)
  | tuple (xs : List Value)
  /-- A `frozendict` constant, for example an entry of `BLOB_SCHEDULE`. -/
  | frozenDict (kvs : List (Value × Value))
  /-- `enumerate(v)`: a lazy view. A `for` loop over it reads `v` live. -/
  | enumView (inner : Value)
  /-- `zip(a, b, ...)`: a lazy view. `strict` raises `ValueError` on different lengths. -/
  | zipView (inners : List Value) (strict : Bool)
  /-- A global name used as a value: a spec function, a type, a builtin or a module. -/
  | glob (n : Name)
  /-- `base.m` used as a value: a method of an object, or a member of a module or type. -/
  | member (base : Value) (m : Name)
  deriving Repr, Inhabited

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

/-! ## Python integer bit operations, in two's complement -/

def pyAnd : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc m => .ofNat (a ^^^ (a &&& m))
  | .negSucc m, .ofNat b => .ofNat (b ^^^ (b &&& m))
  | .negSucc m, .negSucc k => .negSucc (m ||| k)

def pyOr : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ||| b)
  | .ofNat a, .negSucc m => .negSucc (m ^^^ (m &&& a))
  | .negSucc m, .ofNat b => .negSucc (m ^^^ (m &&& b))
  | .negSucc m, .negSucc k => .negSucc (m &&& k)

def pyXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc m => .negSucc (a ^^^ m)
  | .negSucc m, .ofNat b => .negSucc (m ^^^ b)
  | .negSucc m, .negSucc k => .ofNat (m ^^^ k)

/-- Python integer arithmetic. `//` and `%` round to negative infinity. -/
def intArith : BinOp → Int → Int → Res Int
  | .add, a, b => .ok (a + b)
  | .sub, a, b => .ok (a - b)
  | .mul, a, b => .ok (a * b)
  | .floorDiv, a, b => if b = 0 then .error .divisionByZero else .ok (a.fdiv b)
  | .mod, a, b => if b = 0 then .error .divisionByZero else .ok (a.fmod b)
  -- A negative exponent gives a float. No spec code does that.
  | .pow, a, b => if 0 ≤ b then .ok (a ^ b.toNat) else .error .unsupported
  | .bitAnd, a, b => .ok (pyAnd a b)
  | .bitOr, a, b => .ok (pyOr a b)
  | .bitXor, a, b => .ok (pyXor a b)
  | .lShift, a, b => if 0 ≤ b then .ok (a * 2 ^ b.toNat) else .error .valueError
  | .rShift, a, b => if 0 ≤ b then .ok (a.fdiv (2 ^ b.toNat)) else .error .valueError

/-- A binary operator. A plain `int` operand takes the class of the uint operand. The class
check comes before the arithmetic, as in `BaseUint.__add__`. A Python `bool` acts as an `int`
with another `int` or `bool`, and raises `TypeError` with a uint. -/
def binopVal (op : BinOp) : Value → Value → Res Value
  | .int a, .int b => .int <$> intArith op a b
  | .uint t a, .uint t' b => do
    let r ← resolveUint t t'
    wrapUint r (← intArith op a b)
  | .uint t a, .int b => do wrapUint t (← intArith op a b)
  | .int a, .uint t b => do wrapUint t (← intArith op a b)
  | .boolean _, _ | _, .boolean _ => .error .typeError
  | .bool a, .int b => .int <$> intArith op (if a then 1 else 0) b
  | .int a, .bool b => .int <$> intArith op a (if b then 1 else 0)
  | .bool a, .bool b => .int <$> intArith op (if a then 1 else 0) (if b then 1 else 0)
  | .bool _, .uint _ _ | .uint _ _, .bool _ => .error .typeError
  | .bytes _ a, .bytes _ b =>
    -- `Bytes32 + bytes` gives Python `bytes`. The interpreter names that class `bytes` = 0.
    match op with
    | .add => .ok (.bytes 0 (a ++ b))
    | _ => .error .typeError
  | .tuple a, .tuple b =>
    match op with
    | .add => .ok (.tuple (a ++ b))
    | _ => .error .typeError
  -- `b"\x01" * 32`: repetition gives Python `bytes`.
  | .bytes _ a, .int k | .int k, .bytes _ a =>
    match op with
    | .mul => .ok (.bytes 0 ((List.replicate k.toNat a).flatten))
    | _ => .error .typeError
  | .tuple a, .int k | .int k, .tuple a =>
    match op with
    | .mul => .ok (.tuple ((List.replicate k.toNat a).flatten))
    | _ => .error .typeError
  | _, _ => .error .unsupported

/-- A unary operator. `-x` and `~x` of a uint give a plain `int`. -/
def unopVal : UnOp → Value → Res Value
  | .neg, .int n => .ok (.int (-n))
  | .neg, .uint _ n => .ok (.int (-(n : Int)))
  | .invert, .int n => .ok (.int (Int.not n))
  | .invert, .uint _ n => .ok (.int (Int.not n))
  | .neg, .bool b => .ok (.int (if b then -1 else 0))
  | _, .boolean _ => .error .typeError
  | _, _ => .error .unsupported

def cmpInt : CmpOp → Int → Int → Bool
  | .eq, a, b => a == b
  | .notEq, a, b => a != b
  | .lt, a, b => decide (a < b)
  | .ltE, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .gtE, a, b => decide (a ≥ b)
  -- The interpreter handles `is` and `in` before it calls `cmpVal`.
  | _, _, _ => false

/-- The equality of two lists: `false` at the first pair that is not equal. -/
def eqLex : List Bool → Bool
  | [] => true
  | b :: bs => b && eqLex bs

/-- An ordinary comparison of two values that need no heap. Two uints need related classes,
as in `BaseUint._require_relation`. A uint against `None` or a `bool` raises `TypeError`. Two
byte strings compare their contents, whatever their classes. -/
def cmpVal (op : CmpOp) : Value → Value → Res Bool
  | .int a, .int b => .ok (cmpInt op a b)
  | .uint t a, .uint t' b => do
    let _ ← resolveUint t t'
    pure (cmpInt op a b)
  | .uint _ a, .int b => .ok (cmpInt op a b)
  | .int a, .uint _ b => .ok (cmpInt op a b)
  | .bytes _ a, .bytes _ b =>
    match op with
    | .eq => .ok (a == b)
    | .notEq => .ok (a != b)
    | _ => .error .unsupported
  | .boolean a, .boolean b =>
    match op with
    | .eq => .ok (a == b)
    | .notEq => .ok (a != b)
    | _ => .error .unsupported
  -- `Boolean` is nominal: it does not compare with `bool`, `int` or a uint.
  | .boolean _, _ | _, .boolean _ => .error .typeError
  -- A uint against any value that is not an `int` or a uint raises (`_require_relation`).
  | .uint _ _, _ | _, .uint _ _ => .error .typeError
  | .bool a, .bool b => .ok (cmpInt op (if a then 1 else 0) (if b then 1 else 0))
  | .bool a, .int b => .ok (cmpInt op (if a then 1 else 0) b)
  | .int a, .bool b => .ok (cmpInt op a (if b then 1 else 0))
  | .str a, .str b =>
    match op with
    | .eq => .ok (a == b)
    | .notEq => .ok (a != b)
    | .lt => .ok (decide (a < b))
    | .gt => .ok (decide (b < a))
    | _ => .error .unsupported
  | .none, .none =>
    match op with
    | .eq => .ok true
    | .notEq => .ok false
    | _ => .error .typeError
  -- Values of different kinds are not equal. Python `==` does not raise here.
  | .none, _ | _, .none | .str _, _ | _, .str _ | .int _, .bytes _ _ | .bytes _ _, .int _ =>
    match op with
    | .eq => .ok false
    | .notEq => .ok true
    | _ => .error .typeError
  | _, _ => .error .unsupported

/-- `a is b`. Only `None` and heap objects have an identity that spec code tests. -/
def isVal : Value → Value → Bool
  | .none, .none => true
  | .ref a, .ref b => a == b
  | _, _ => false

/-- Python truth value of a value that needs no heap. -/
def truthy : Value → Res Bool
  | .bool b => .ok b
  | .boolean b => .ok b
  | .int n => .ok (n != 0)
  | .uint _ n => .ok (n != 0)
  | .none => .ok false
  | .str s => .ok (!s.isEmpty)
  | .bytes _ b => .ok (!b.isEmpty)
  | .tuple xs => .ok (!xs.isEmpty)
  | _ => .error .unsupported

/-- A Python index: an `int`, a `bool` or a uint. -/
def toIndex : Value → Res Int
  | .int n => .ok n
  | .uint _ n => .ok n
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error .typeError

/-- Resolve a Python index against a length. A negative index counts from the end. -/
def normIndex (len : Nat) (i : Int) : Option Nat :=
  if i < 0 then
    if 0 ≤ i + len then some (i + len).toNat else none
  else if i < len then some i.toNat else none

/-- Clamp a slice bound, as `slice.indices` does for step 1. -/
def sliceBound (len : Nat) (i : Int) : Nat :=
  if i < 0 then (i + len).toNat else min i.toNat len

/-! ## Checked uint arithmetic

The interpreter and the readable Lean share these. The bridge lemmas state that an interpreter
operator on two 64-bit uints equals one of them. -/

def chkRange (n : Nat) : Res Nat := if n < 2 ^ 64 then .ok n else .error .sszValue

def chkAdd (a b : Nat) : Res Nat := chkRange (a + b)

def chkSub (a b : Nat) : Res Nat := if b ≤ a then chkRange (a - b) else .error .sszValue

def chkMul (a b : Nat) : Res Nat := chkRange (a * b)

def chkDiv (a b : Nat) : Res Nat := if b = 0 then .error .divisionByZero else chkRange (a / b)

def chkMod (a b : Nat) : Res Nat := if b = 0 then .error .divisionByZero else chkRange (a % b)

end SpecLean
