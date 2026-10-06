import SpecLean.Value

/-!
# Trusted primitives (SPEC 4.4)

Library and builtin operations of Python and `eth-ssz-specs`, each defined once. The interpreter's
builtins and the readable Lean both compute through these functions. An operation that compares,
adds or tests items takes that item operation as an argument: the interpreter passes its value
rule (`cmpVal`, `binopVal`, `truthyH`), and the readable Lean passes the operation of its type.
So the two sides share the algorithm by definition. `PrimRel.lean` relates the item operations.

The uint arithmetic and coercion table is `intArith`, `wrapUint` and `resolveUint` in
`Value.lean` and `Ssz/Values.lean`. The readable `uOf` and `uOp` use `intArith` too.
-/

namespace SpecLean.Prim

variable {m : Type → Type} [Monad m]

/-! ## Order: `sorted`, `min`, `max`

The functions that are not recursive are reducible and `simp` lemmas: a proof that unfolds a
builtin sees the same terms as before the primitives were shared. -/

/-- Insert after every item that is not after it, so equal items keep their order. -/
@[simp] def insertLast {κ α : Type} (lt : κ → κ → m Bool) (rev : Bool) (k : κ) (x : α) :
    List (κ × α) → m (List (κ × α))
  | [] => pure [(k, x)]
  | (k', x') :: rest => do
    let after ← if rev then lt k' k else lt k k'
    if after then pure ((k, x) :: (k', x') :: rest)
    else do pure ((k', x') :: (← insertLast lt rev k x rest))

/-- `sorted(xs, key=..., reverse=rev)` of `(key, item)` pairs: a stable insertion sort. -/
@[reducible, simp] def sortBy {κ α : Type} (lt : κ → κ → m Bool) (rev : Bool) (ps : List (κ × α)) :
    m (List α) := do
  let acc ← ps.foldlM (fun acc p => insertLast lt rev p.1 p.2 acc) []
  pure (acc.map (·.2))

/-- `min` and `max` of `best :: xs`: an item replaces the best only when `better` holds, so the
first of equal items wins. -/
@[simp] def pick {α : Type} (better : α → α → m Bool) : α → List α → m α
  | best, [] => pure best
  | best, x :: xs => do
    let b ← better x best
    pick better (if b then x else best) xs

/-! ## Folds: `sum`, `any`, `all`, `len` -/

/-- `sum(xs, start)`. -/
@[reducible, simp] def sum {α : Type} (add : α → α → m α) (start : α) (xs : List α) : m α := xs.foldlM add start

/-- `any(xs)` of items with the truth test `p`. -/
@[reducible, simp] def any {α : Type} (p : α → m Bool) (xs : List α) : m Bool := xs.anyM p

/-- `all(xs)`. -/
@[reducible, simp] def all {α : Type} (p : α → m Bool) (xs : List α) : m Bool := xs.allM p

/-- `len(xs)`. -/
@[reducible, simp] def len {α : Type} (xs : List α) : Nat := xs.length

/-! ## Sets -/

/-- `set(xs)`: the first copy of each item, in order. `mem x acc` is Python's `x in acc`. -/
@[simp] def dedupBy {α : Type} (mem : α → List α → m Bool) : List α → List α → m (List α)
  | acc, [] => pure acc
  | acc, x :: xs => do
    if (← mem x acc) then dedupBy mem acc xs else dedupBy mem (acc ++ [x]) xs

/-! ## Bytes and integers -/

/-- `int.from_bytes(bs, "little")`. -/
@[reducible, simp] def fromBytesLE (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- `int.from_bytes(bs, "big")`. -/
@[reducible, simp] def fromBytesBE (bs : List UInt8) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- `n.bit_length()`. -/
@[reducible, simp] def bitLength (n : Int) : Nat := Nat.log2 n.natAbs + if n = 0 then 0 else 1

/-- `ssz_serialize` of a uint of `width` bytes: little endian. -/
@[reducible, simp] def serializeUint (n width : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

/-- `ssz_serialize` of a `Boolean`. -/
@[reducible, simp] def serializeBool (b : Bool) : List UInt8 := [if b then 1 else 0]

/-- The items `a` to `b` of a list, for bounds that `sliceBounds` resolved. -/
@[reducible, simp] def sliceAt {α : Type} (xs : List α) (a b : Nat) : List α := xs.extract a b

/-- The bounds of `xs[lo:hi]`, step 1, for a length. -/
@[reducible, simp] def sliceBounds (len : Nat) (lo hi : Option Int) : Nat × Nat :=
  ((lo.map (sliceBound len)).getD 0, (hi.map (sliceBound len)).getD len)

/-- `xs[lo:hi]`, step 1, for bytes and lists. -/
@[reducible, simp] def slice {α : Type} (xs : List α) (lo hi : Option Int) : List α :=
  sliceAt xs (sliceBounds xs.length lo hi).1 (sliceBounds xs.length lo hi).2

/-- `a + b` for bytes. -/
@[reducible, simp] def concat {α : Type} (a b : List α) : List α := a ++ b

end SpecLean.Prim
