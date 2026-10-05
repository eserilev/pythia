import SpecLean.Builtins

/-!
# SSZ `hash_tree_root`

`hash_tree_root` on top of the `sha256` oracle (SPEC 8). It covers bounded and progressive
lists, bitfields, containers and progressive containers (EIP-7916, EIP-7495). It has no cache.
-/

namespace SpecLean.Htr

/-- What `hash_tree_root` needs besides the heap. `zero d` is the root of the all-zero tree of
depth `d`. The caller computes it once. -/
structure Hasher where
  sha : List UInt8 → List UInt8
  zero : Nat → List UInt8
  containers : List (Name × List (Name × SszTy))
  /-- The layout of each progressive container, one bit per position. -/
  active : List (Name × List Nat)

def zeroChunk : List UInt8 := List.replicate 32 0

/-- The all-zero roots of depth `0` to `n - 1`. -/
def zeroRoots (sha : List UInt8 → List UInt8) (n : Nat) : Array (List UInt8) :=
  (List.range n).foldl (fun acc _ => acc.push (sha (acc.back! ++ acc.back!))) #[zeroChunk]

/-- Split bytes into 32-byte chunks. The last chunk gets zero padding. -/
def pack (bs : List UInt8) : List (List UInt8) :=
  if bs.isEmpty then [] else
  (List.range ((bs.length + 31) / 32)).map fun i =>
    let c := (bs.drop (32 * i)).take 32
    c ++ List.replicate (32 - c.length) 0

/-- Bits in little-endian bit order, then into bytes. -/
def packBitBytes (bits : List Bool) : List UInt8 :=
  (List.range ((bits.length + 7) / 8)).map fun i =>
    ((bits.drop (8 * i)).take 8).foldr (fun b acc => acc * 2 + (if b then 1 else 0)) (0 : UInt8)

def log2Ceil (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

def mixIn (H : Hasher) (root : List UInt8) (n : Nat) : List UInt8 :=
  H.sha (root ++ leBytes n 32)

/-- One tree level: hash pairs, and pair a last odd node with the zero root of depth `d`. -/
def layer (H : Hasher) (d : Nat) : List (List UInt8) → List (List UInt8)
  | a :: b :: rest => H.sha (a ++ b) :: layer H d rest
  | [a] => [H.sha (a ++ H.zero d)]
  | [] => []

/-- The root of a tree of depth `depth - d` over `cs`, whose nodes are at depth `d`. -/
def climb (H : Hasher) (cs : List (List UInt8)) (d : Nat) : Nat → List UInt8
  | 0 => match cs with
    | [c] => c
    | _ => H.zero d
  | k + 1 => if cs.isEmpty then H.zero (d + k + 1) else climb H (layer H d cs) (d + 1) k

/-- `merkleize(chunks, limit)`. A count over the limit raises `SSZValueError`. -/
def merkleize (H : Hasher) (cs : List (List UInt8)) (limit : Option Nat) : Res (List UInt8) :=
  match limit with
  | some l => if l < cs.length then .error .sszValue else .ok (climb H cs 0 (log2Ceil l))
  | none => .ok (climb H cs 0 (log2Ceil cs.length))

/-- `merkleize_progressive(chunks, num_leaves)`. `fuel` bounds the number of levels. -/
def progressive (H : Hasher) : Nat → List (List UInt8) → Nat → List UInt8
  | 0, _, _ => zeroChunk
  | fuel + 1, cs, n =>
    if cs.isEmpty then zeroChunk
    else H.sha (climb H (cs.take n) 0 (log2Ceil n) ++ progressive H fuel (cs.drop n) (n * 4))

def merkleizeProgressive (H : Hasher) (cs : List (List UInt8)) : List UInt8 :=
  progressive H (cs.length + 1) cs 1

/-- The serialized bytes of a basic value. -/
def basicBytes : Value → Option (List UInt8)
  | .uint t n => some (leBytes n (t.bits / 8))
  | .boolean b => some [if b then 1 else 0]
  | _ => none

def elemSize : SszTy → Option Nat
  | .uint t => some (t.bits / 8)
  | .boolean => some 1
  | _ => none

def bitOf : Value → Res Bool
  | .boolean b => .ok b
  | .bool b => .ok b
  | _ => .error .unsupported

/-- The chunks of a list of basic values, and the chunk limit for `n` elements. -/
def packBasic (xs : List Value) : Res (List (List UInt8)) := do
  let bs ← xs.mapM fun x => match basicBytes x with
    | some b => .ok b
    | none => .error .unsupported
  pure (pack bs.flatten)

/-- `hash_tree_root` of a value. `d` bounds the nesting depth. -/
def root (H : Hasher) (h : Heap) : Nat → Value → Res (List UInt8)
  | 0, _ => .error .unsupported
  | d + 1, v =>
    match v with
    | .uint t n => .ok (leBytes n (t.bits / 8) ++ List.replicate (32 - t.bits / 8) 0)
    | .boolean b => .ok ((if b then 1 else 0) :: List.replicate 31 0)
    | .bytes _ bs => let cs := pack bs; merkleize H cs (some cs.length)
    | .ref a =>
      match h.objs a with
      | some (.container ty fs) => do
        let rs ← fs.mapM (root H h d)
        match H.active.lookup ty with
        | some bits =>
          let (leaves, _) := bits.foldl (init := (([] : List (List UInt8)), rs))
            fun (acc, rest) b =>
              if b = 1 then
                match rest with
                | r :: rest' => (acc ++ [r], rest')
                | [] => (acc ++ [zeroChunk], [])
              else (acc ++ [zeroChunk], rest)
          let word := packBitBytes (bits.map (· = 1))
          let word := word ++ List.replicate (32 - word.length) 0
          pure (H.sha (merkleizeProgressive H leaves ++ word))
        | none => merkleize H rs (some rs.length)
      | some (.list kind elem limit xs) =>
        match kind with
        | .bitvector | .bitlist | .progressiveBitlist => do
          let bits ← xs.mapM bitOf
          let cs := pack (packBitBytes bits)
          match kind, limit with
          | .bitvector, some n => merkleize H cs (some ((n + 255) / 256))
          | .bitlist, some n => do
            pure (mixIn H (← merkleize H cs (some ((n + 255) / 256))) xs.length)
          | .progressiveBitlist, _ => pure (mixIn H (merkleizeProgressive H cs) xs.length)
          | _, _ => .error .unsupported
        | .vector | .list | .progressiveList => do
          let cs ← match elemSize elem with
            | some _ => packBasic xs
            | none => xs.mapM (root H h d)
          let lim := match elemSize elem, limit with
            | some s, some n => some ((n * s + 31) / 32)
            | none, some n => some n
            | _, none => none
          match kind with
          | .vector => merkleize H cs lim
          | .list => do pure (mixIn H (← merkleize H cs lim) xs.length)
          | _ => pure (mixIn H (merkleizeProgressive H cs) xs.length)
        | .pyList => .error .unsupported
      | _ => .error .unsupported
    | _ => .error .unsupported

end SpecLean.Htr
