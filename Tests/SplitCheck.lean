import SpecLean.Ssz

/-!
# The core/library split changes no value rule

The rules before the split, copied, and a check that the core with the SSZ model gives the
same result for every pair of value kinds.
-/

namespace SpecLean.Tests.Split

open SpecLean

def binopValOld (op : BinOp) : Value → Value → Res Value
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
  -- A `bool` on the left uses `int` rules (probed): `True + Uint64(1)` is the `int` 2.
  | .bool a, .uint _ b => .int <$> intArith op (if a then 1 else 0) b
  | .uint _ _, .bool _ => .error .typeError
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


def unopValOld : UnOp → Value → Res Value
  | .neg, .int n => .ok (.int (-n))
  | .neg, .uint _ n => .ok (.int (-(n : Int)))
  | .invert, .int n => .ok (.int (Int.not n))
  | .invert, .uint _ n => .ok (.int (Int.not n))
  | .neg, .bool b => .ok (.int (if b then -1 else 0))
  | _, .boolean _ => .error .typeError
  | _, _ => .error .unsupported


def cmpValOld (op : CmpOp) : Value → Value → Res Bool
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
  -- A `bool` on the left compares as an `int` (probed): `True == Gwei(0)` is `False`.
  | .bool a, .uint _ b => .ok (cmpInt op (if a then 1 else 0) b)
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


def truthyOld : Value → Res Bool
  | .bool b => .ok b
  | .boolean b => .ok b
  | .int n => .ok (n != 0)
  | .uint _ n => .ok (n != 0)
  | .none => .ok false
  | .str s => .ok (!s.isEmpty)
  | .bytes _ b => .ok (!b.isEmpty)
  | .tuple xs => .ok (!xs.isEmpty)
  | _ => .error .unsupported


def toIndexOld : Value → Res Int
  | .int n => .ok n
  | .uint _ n => .ok n
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error .typeError


theorem binop_same (op : BinOp) (x y : Value) : binopVal op x y = binopValOld op x y := by
  rcases x with (_ | _ | (_ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    rcases y with (_ | _ | (_ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> rfl

theorem unop_same (op : UnOp) (x : Value) : unopVal op x = unopValOld op x := by
  cases op <;> rcases x with (_ | _ | (_ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> rfl

theorem cmp_same (op : CmpOp) (x y : Value) : cmpVal op x y = cmpValOld op x y := by
  rcases x with (_ | _ | (_ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    rcases y with (_ | _ | (_ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> rfl

theorem truthy_same (x : Value) : truthy x = truthyOld x := by
  rcases x with (_ | _ | (_ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> rfl

theorem index_same (x : Value) : toIndex x = toIndexOld x := by
  rcases x with (_ | _ | (_ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> rfl

end SpecLean.Tests.Split
