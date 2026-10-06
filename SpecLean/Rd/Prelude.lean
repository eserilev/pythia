import SpecLean.Ssz

/-!
# The prelude of the generated readable Lean (SPEC 9.1)

The operations that `tools/translate.py` emits: checked uint arithmetic per class, Python `int`
arithmetic, list and byte-string access with Python's errors, sorting, and the oracle (sha256,
BLS) with `hash_tree_root` through the SSZ model. Errors keep their class only (`Fail`).
-/

namespace SpecLean.Rd

open SpecLean

abbrev SpecM := Except Fail

/-- Keep the class of an error and drop its diagnostic. -/
def erase (r : Res α) : SpecM α := r.mapError SpecError.fail

abbrev Bytes := List UInt8

/-! ## SSZ scalar classes -/

/-- A uint class: its width and its value. -/
class UintC (α : Type) where
  bits : Nat
  val : α → Nat
  ofNat : Nat → α
  val_ofNat : ∀ n, val (ofNat n) = n
  ofNat_val : ∀ x, ofNat (val x) = x

/-- A byte vector class: its length and its bytes. -/
class BytesC (α : Type) where
  len : Nat
  data : α → Bytes
  ofBytes : Bytes → α
  data_ofBytes : ∀ b, data (ofBytes b) = b
  ofBytes_data : ∀ x, ofBytes (data x) = x

structure Boolean where
  val : Bool
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- The value of a uint as a Python `int`. -/
def uv [UintC α] (x : α) : Int := (UintC.val x : Int)

/-- `cls(n)`: the range check. Out of range is `SSZValueError`, a bug. -/
def uOf (α : Type) [UintC α] (n : Int) : SpecM α :=
  if 0 ≤ n ∧ n < 2 ^ UintC.bits α then pure (UintC.ofNat n.toNat) else throw .bug

/-- A uint operator in class `α`. The translator casts both operands to `α` first. -/
def uOp [UintC α] (op : BinOp) (a b : Int) : SpecM α := do
  uOf α (← erase (intArith op a b))

/-- A Python `int` operator. -/
def iOp (op : BinOp) (a b : Int) : SpecM Int := erase (intArith op a b)

/-- The same number in another uint class, with the range check. -/
def uCast (β : Type) [UintC α] [UintC β] (x : α) : SpecM β := uOf β (uv x)

def bytesOf (β : Type) [BytesC β] (b : Bytes) : SpecM β :=
  if b.length = BytesC.len β then pure (BytesC.ofBytes b) else throw .bug

def bd [BytesC α] (x : α) : Bytes := BytesC.data x

/-! ## Errors -/

def assert (c : Bool) : SpecM Unit := if c then pure () else throw .invalid

/-! ## Sequences -/

def pyIndex (len : Nat) (i : Int) : Option Nat :=
  if i < 0 then (if 0 ≤ i + len then some (i + len).toNat else none)
  else if i < len then some i.toNat else none

/-- `xs[i]`. A bad index is `IndexError`, so the input is invalid. -/
def lget (xs : List α) (i : Int) : SpecM α :=
  match pyIndex xs.length i >>= (xs[·]?) with
  | some x => pure x
  | none => throw .invalid

/-- `xs[i] = x`. -/
def lset (xs : List α) (i : Int) (x : α) : SpecM (List α) :=
  match pyIndex xs.length i with
  | some k => pure (xs.set k x)
  | none => throw .invalid

/-- `xs.append(x)`, with the limit of an SSZ list. Over the limit is a bug. -/
def lappend (xs : List α) (x : α) (limit : Option Nat) : SpecM (List α) :=
  match limit with
  | some l => if xs.length + 1 ≤ l then pure (xs ++ [x]) else throw .bug
  | none => pure (xs ++ [x])

def sliceBound' (len : Nat) (i : Int) : Nat :=
  if i < 0 then (i + len).toNat else min i.toNat len

/-- `xs[lo:hi]`, step 1. -/
def lslice (xs : List α) (lo hi : Option Int) : List α :=
  let a := (lo.map (sliceBound' xs.length)).getD 0
  let b := (hi.map (sliceBound' xs.length)).getD xs.length
  (xs.drop a).take (b - a)

/-- `xs[lo:hi] = ys`, step 1. -/
def lsetSlice (xs : List α) (lo hi : Option Int) (ys : List α) : List α :=
  let a := (lo.map (sliceBound' xs.length)).getD 0
  let b := (hi.map (sliceBound' xs.length)).getD xs.length
  xs.take a ++ ys ++ xs.drop (max a b)

/-- `xs.index(x)`. Not found is `ValueError`, a bug. -/
def lindex [BEq α] (xs : List α) (x : α) : SpecM Int :=
  match xs.findIdx? (· == x) with
  | some i => pure i
  | none => throw .bug

def lcount [BEq α] (xs : List α) (x : α) : Int := (xs.filter (· == x)).length

/-- A set: the first copy of each element, in order. -/
def dedup [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def bget (b : Bytes) (i : Int) : SpecM Int := do pure (← lget b i).toNat

/-- `int.from_bytes(b, "little")`. -/
def fromLE (b : Bytes) : Int := (b.foldr (fun x acc => acc * 256 + x.toNat) 0 : Nat)

/-- `n.to_bytes(w, "little")`. -/
def toLE (n : Nat) (w : Nat) : Bytes := leBytes n w

/-- `range(lo, hi, step)`. -/
def pyRange (lo hi step : Int) : SpecM (List Int) :=
  if step = 0 then throw .bug
  else
    let count := if step > 0 then ((hi - lo + step - 1) / step).toNat
      else ((lo - hi - step - 1) / (-step)).toNat
    pure ((List.range count).map fun (i : Nat) => lo + step * (i : Int))

/-! ## Order -/

/-- Python `<` for the key types of `sorted`, `min` and `max`. -/
class PyOrd (α : Type) where
  lt : α → α → Bool

instance : PyOrd Int := ⟨fun a b => decide (a < b)⟩
instance : PyOrd Bool := ⟨fun a b => !a && b⟩
instance : PyOrd Bytes := ⟨fun a b => decide (a.map (·.toNat) < b.map (·.toNat))⟩
instance [PyOrd α] [PyOrd β] [BEq α] : PyOrd (α × β) :=
  ⟨fun a b => PyOrd.lt a.1 b.1 || (a.1 == b.1 && PyOrd.lt a.2 b.2)⟩

/-- Stable sort by key, as `sorted(xs, key=k, reverse=r)`. -/
def pySort [PyOrd κ] (key : α → κ) (rev : Bool) (xs : List α) : List α :=
  let ins := fun (x : α) (acc : List α) =>
    let k := key x
    let (lo, hi) := acc.span fun y =>
      if rev then !(PyOrd.lt (key y) k) else !(PyOrd.lt k (key y))
    lo ++ [x] ++ hi
  xs.foldl (fun acc x => ins x acc) []

/-- `min(xs)`: the first of the least. Empty is `ValueError`, a bug. -/
def pyMin [PyOrd α] : List α → SpecM α
  | [] => throw .bug
  | x :: xs => pure (xs.foldl (fun b y => if PyOrd.lt y b then y else b) x)

def pyMax [PyOrd α] : List α → SpecM α
  | [] => throw .bug
  | x :: xs => pure (xs.foldl (fun b y => if PyOrd.lt b y then y else b) x)

/-! ## SSZ encoding, the oracle and `hash_tree_root` -/

/-- Encode a value into the interpreter heap. `hash_tree_root` and the runner use it. -/
abbrev Enc (α : Type) := α → Heap → Value × Heap

/-- An SSZ object of any class, with its encoder: the type of an `SSZObject` parameter. -/
structure SszObj where
  enc : Heap → Value × Heap

/-- The oracle: sha256, BLS, and the tables of the SSZ model for `hash_tree_root`. -/
class Spec where
  sha256 : Bytes → Bytes
  containers : List (Name × List (Name × SszTy))
  active : List (Name × List Nat)
  zero : Nat → Bytes
  blsVerify : Bytes → Bytes → Bytes → Bool
  blsFastAggregateVerify : List Bytes → Bytes → Bytes → Bool
  blsAggregateVerify : List Bytes → List Bytes → Bytes → Bool
  blsKeyValidate : Bytes → Bool
  blsAggregatePKs : List Bytes → Bytes
  /-- G1 point addition and negation, on points as their 48 bytes. -/
  blsG1Add : Bytes → Bytes → Bytes
  blsG1Neg : Bytes → Bytes
  /-- `hash_tree_root` of an encoded value: an oracle, the same one the interpreter calls. The
  runner sets it to `Htr.root`. -/
  hashTreeRoot : Heap → Value → Res Bytes

variable [Spec]

def hasher : Htr.Hasher where
  sha := Spec.sha256
  zero := Spec.zero
  containers := Spec.containers
  active := Spec.active

/-- `hash_tree_root` of an encoded value, through the oracle. -/
def htrObj (o : SszObj) : SpecM Bytes :=
  let (v, h) := o.enc Heap.empty
  erase (Spec.hashTreeRoot h v)

def htr (enc : Enc α) (x : α) : SpecM Bytes := htrObj ⟨enc x⟩

/-! ## Encoders of generic shapes -/

def encUint (t : UintTy) [UintC α] : Enc α := fun x h => (.uint t (UintC.val x), h)

def encBoolean : Enc Boolean := fun x h => (.boolean x.val, h)

def encBytesN (cls : Name) [BytesC α] : Enc α := fun x h => (.bytes cls (BytesC.data x), h)

def encList (k : ListKind) (e : SszTy) (l : Option Nat) (f : Enc α) : Enc (List α) :=
  fun xs h =>
    let (vs, h') := xs.foldl (fun (acc : List Value × Heap) x =>
      let (v, h1) := f x acc.2
      (acc.1 ++ [v], h1)) ([], h)
    let (a, h'') := h'.alloc (.list k e l vs)
    (.ref a, h'')

def encContainer (ty : Name) (fs : List (Heap → Value × Heap)) : Heap → Value × Heap :=
  fun h =>
    let (vs, h') := fs.foldl (fun (acc : List Value × Heap) f =>
      let (v, h1) := f acc.2
      (acc.1 ++ [v], h1)) ([], h)
    let (a, h'') := h'.alloc (.container ty vs)
    (.ref a, h'')

/-! ## Decoders of generic shapes -/

abbrev Dec (α : Type) := Heap → Value → Option α

def decUintC [UintC α] : Dec α
  | _, .uint _ n => some (UintC.ofNat n)
  | _, _ => none

/-- A uint of class `t`, in range. A heap field holds its exact class: a write coerces to it.
The range check makes a decoded value a valid SSZ value, as Python's type guarantees. -/
def decUintT [UintC α] (t : UintTy) : Dec α
  | _, .uint t' n => if t' = t ∧ n < 2 ^ UintC.bits α then some (UintC.ofNat n) else none
  | _, _ => none

def decBooleanV : Dec Boolean
  | _, .boolean b => some ⟨b⟩
  | _, _ => none

def decBytesC [BytesC α] : Dec α
  | _, .bytes _ b => some (BytesC.ofBytes b)
  | _, _ => none

/-- A byte vector of class `cls`, of the length of the class. -/
def decBytesT [BytesC α] (cls : Name) : Dec α
  | _, .bytes c b => if c = cls ∧ b.length = BytesC.len α then some (BytesC.ofBytes b) else none
  | _, _ => none

def decListV (f : Dec α) : Dec (List α)
  | h, .ref a =>
    match h.objs a with
    | some (.list _ _ _ xs) => xs.mapM (f h)
    | _ => none
  | _, _ => none

/-- A list of SSZ type `.list k e l`. A field holds its exact type: a write coerces to it. -/
def decListT (k : ListKind) (e : SszTy) (l : Option Nat) (f : Dec α) : Dec (List α)
  | h, .ref a =>
    match h.objs a with
    | some (.list k' e' l' xs) => if k' = k ∧ e' = e ∧ l' = l then xs.mapM (f h) else none
    | _ => none
  | _, _ => none

def containerFields : Heap → Value → Option (List Value)
  | h, .ref a =>
    match h.objs a with
    | some (.container _ fs) => some fs
    | _ => none
  | _, _ => none

/-- The fields of a container of class `ty`. -/
def containerFieldsT (ty : Name) : Heap → Value → Option (List Value)
  | h, .ref a =>
    match h.objs a with
    | some (.container ty' fs) => if ty' = ty then some fs else none
    | _ => none
  | _, _ => none

end SpecLean.Rd

namespace SpecLean.Rd

/-! ## More operations that the translator emits -/

/-- `assert` of a condition whose failure is a bug, not an invalid input. -/
def assertBug (c : Bool) : SpecM Unit := if c then pure () else throw .bug

/-- An SSZ `Boolean` element from an `int`: only 0 and 1 pass. -/
def booleanOfInt (n : Int) : SpecM Boolean :=
  if n = 0 then pure ⟨false⟩ else if n = 1 then pure ⟨true⟩ else throw .bug

/-- `C(data=xs)` for an SSZ list class: a vector needs its length, a list stays within its
limit. pydantic raises `ValidationError`, a bug. -/
def lfrom (k : ListKind) (limit : Option Nat) (xs : List α) : SpecM (List α) :=
  match k, limit with
  | .vector, some n | .bitvector, some n => if xs.length = n then pure xs else throw .bug
  | .list, some n | .bitlist, some n => if xs.length ≤ n then pure xs else throw .bug
  | _, _ => pure xs

/-- The limit check of `a + b` for an SSZ list. -/
def lcheck (xs : List α) (limit : Nat) : SpecM (List α) :=
  if xs.length ≤ limit then pure xs else throw .bug

def lextend (xs ys : List α) (limit : Option Nat) : SpecM (List α) :=
  match limit with
  | some l => if xs.length + ys.length ≤ l then pure (xs ++ ys) else throw .bug
  | none => pure (xs ++ ys)

/-- `sum(xs, start)` of uints. -/
def sumU [UintC α] (start : α) (xs : List α) : SpecM α :=
  xs.foldlM (fun acc x => uOp .add (uv acc) (uv x)) start

/-- `d[k]`. Not found is `KeyError`, a bug. -/
def dget [BEq κ] (d : List (κ × ν)) (k : κ) : SpecM ν :=
  match d.find? (·.1 == k) with
  | some (_, v) => pure v
  | none => throw .bug

def dgetD [BEq κ] [Inhabited ν] (d : List (κ × ν)) (k : κ) : ν :=
  match d.find? (·.1 == k) with
  | some (_, v) => v
  | none => default

/-- `d[k] = v`: replace in place, or add at the end, as Python keeps insertion order. -/
def dset [BEq κ] (d : List (κ × ν)) (k : κ) (v : ν) : List (κ × ν) :=
  if d.any (·.1 == k) then d.map fun p => if p.1 == k then (k, v) else p else d ++ [(k, v)]

def lsetSlice' (xs : List α) (lo hi : Option Int) (ys : List α) : SpecM (List α) :=
  pure (lsetSlice xs lo hi ys)

end SpecLean.Rd

namespace SpecLean.Rd

def decBoolV : Dec Bool
  | _, .bool b => some b
  | _, _ => none

def decIntV : Dec Int
  | _, .int n => some n
  | _, _ => none

end SpecLean.Rd
