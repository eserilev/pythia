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

/-- `t` is a subclass of `u`: a nominal class of the width class `u`. -/
def UintTy.subOf : UintTy → UintTy → Bool
  | .nominal _ b, .width b' => b == b'
  | _, _ => false

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
  /-- Another Python exception, by class name: `AttributeError`, `MemoryError`. -/
  | other (cls : String)
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

/-- The data of a value of a library class: an SSZ uint of a class, or an SSZ `Boolean`. The
core only carries it. The library (`SpecLean/Ssz`) owns every rule on it. -/
inductive LibVal where
  | uint (t : UintTy) (n : Nat)
  | boolean (b : Bool)
  deriving Repr, Inhabited, DecidableEq

inductive Value where
  | int (n : Int)
  /-- Python `bool`. -/
  | bool (b : Bool)
  /-- A value of a library class. -/
  | lib (v : LibVal)
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

/-- The value rules of a Python library: SSZ for the spec (`SpecLean/Ssz`). The core asks the
library first. A hook gives `none` when plain Python rules apply. -/
class LibValues where
  binop : BinOp → Value → Value → Option (Res Value)
  unop : UnOp → Value → Option (Res Value)
  compare : CmpOp → Value → Value → Option (Res Bool)
  truthy : Value → Option (Res Bool)
  index : Value → Option (Res Int)

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
  -- A result too large to build raises `MemoryError` in CPython. The bound keeps Lean from
  -- building it.
  | .pow, a, b =>
    if b < 0 then .error .unsupported
    else if a.natAbs ≤ 1 ∨ b < 2 ^ 32 then .ok (a ^ b.toNat) else .error (.other "MemoryError")
  | .bitAnd, a, b => .ok (pyAnd a b)
  | .bitOr, a, b => .ok (pyOr a b)
  | .bitXor, a, b => .ok (pyXor a b)
  | .lShift, a, b =>
    if b < 0 then .error .valueError
    else if a = 0 then .ok 0
    else if b < 2 ^ 32 then .ok (a * 2 ^ b.toNat) else .error (.other "MemoryError")
  | .rShift, a, b => if 0 ≤ b then .ok (a.fdiv (2 ^ b.toNat)) else .error .valueError

/-- A binary operator on Python values: `int`, `bool`, `bytes` and `tuple`. A `bool` acts as
an `int`. `bytes` of any class concatenate and repeat into plain `bytes`. -/
def pyBinop (op : BinOp) : Value → Value → Res Value
  | .int a, .int b => .int <$> intArith op a b
  | .bool a, .int b => .int <$> intArith op (if a then 1 else 0) b
  | .int a, .bool b => .int <$> intArith op a (if b then 1 else 0)
  | .bool a, .bool b => .int <$> intArith op (if a then 1 else 0) (if b then 1 else 0)
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

/-- A binary operator: the library first, then Python. -/
def binopVal [LibValues] (op : BinOp) (x y : Value) : Res Value :=
  match LibValues.binop op x y with
  | some r => r
  | none => pyBinop op x y

/-- A unary operator on Python values. -/
def pyUnop : UnOp → Value → Res Value
  | .neg, .int n => .ok (.int (-n))
  | .invert, .int n => .ok (.int (Int.not n))
  | .neg, .bool b => .ok (.int (if b then -1 else 0))
  | _, _ => .error .unsupported

/-- A unary operator: the library first, then Python. -/
def unopVal [LibValues] (op : UnOp) (x : Value) : Res Value :=
  match LibValues.unop op x with
  | some r => r
  | none => pyUnop op x

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

/-- `a < b` for byte strings: the first byte that differs decides, and a prefix is less. -/
def bytesLt : List UInt8 → List UInt8 → Bool
  | [], _ :: _ => true
  | x :: xs, y :: ys => x < y || (x == y && bytesLt xs ys)
  | _, _ => false

/-- An ordinary comparison of two Python values that need no heap. Two byte strings compare
their contents, whatever their classes. -/
def pyCmp (op : CmpOp) : Value → Value → Res Bool
  | .int a, .int b => .ok (cmpInt op a b)
  | .bytes _ a, .bytes _ b =>
    match op with
    | .eq => .ok (a == b)
    | .notEq => .ok (a != b)
    | .lt => .ok (bytesLt a b)
    | .ltE => .ok !(bytesLt b a)
    | .gt => .ok (bytesLt b a)
    | .gtE => .ok !(bytesLt a b)
    | _ => .error .unsupported
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

/-- An ordinary comparison: the library first, then Python. -/
def cmpVal [LibValues] (op : CmpOp) (x y : Value) : Res Bool :=
  match LibValues.compare op x y with
  | some r => r
  | none => pyCmp op x y

/-- `a is b`. Only `None` and heap objects have an identity that spec code tests. -/
def isVal : Value → Value → Bool
  | .none, .none => true
  | .ref a, .ref b => a == b
  | _, _ => false

/-- Python truth value of a Python value that needs no heap. -/
def pyTruthy : Value → Res Bool
  | .bool b => .ok b
  | .int n => .ok (n != 0)
  | .none => .ok false
  | .str s => .ok (!s.isEmpty)
  | .bytes _ b => .ok (!b.isEmpty)
  | .tuple xs => .ok (!xs.isEmpty)
  | _ => .error .unsupported

/-- Truth value: the library first, then Python. -/
def truthy [LibValues] (v : Value) : Res Bool :=
  match LibValues.truthy v with
  | some r => r
  | none => pyTruthy v

/-- A Python index: an `int` or a `bool`. -/
def pyIndex : Value → Res Int
  | .int n => .ok n
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error .typeError

/-- An index: the library first, then Python. -/
def toIndex [LibValues] (v : Value) : Res Int :=
  match LibValues.index v with
  | some r => r
  | none => pyIndex v

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
