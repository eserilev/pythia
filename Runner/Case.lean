import SpecLean.Interp
import SpecLean.Ssz
import Std.Data.HashMap

/-!
# Case files

Reads the case files of `tools/ef_cases.py` into heap values. The file docstring of that script
gives the encoding.
-/

namespace SpecLean.Runner

/-- A reader over the bytes of one case file. -/
abbrev Rd := StateT Nat (Except String)

/-- What the reader needs: the bytes and the interned names of the build. -/
structure Ctx where
  data : ByteArray
  ids : Std.HashMap String Name

def u8 (c : Ctx) : Rd Nat := do
  let p ← get
  if h : p < c.data.size then
    set (p + 1); pure c.data[p].toNat
  else throw s!"end of data at {p}"

def uN (c : Ctx) (k : Nat) : Rd Nat := do
  let mut n := 0
  for i in [0:k] do
    n := n + (← u8 c) * 256 ^ i
  pure n

def bytesN (c : Ctx) (k : Nat) : Rd (List UInt8) := do
  let p ← get
  if p + k ≤ c.data.size then
    set (p + k); pure (c.data.extract p (p + k)).toList
  else throw s!"end of data at {p}"

def str (c : Ctx) : Rd String := do
  let n ← uN c 2
  match String.fromUTF8? ⟨(← bytesN c n).toArray⟩ with
  | some s => pure s
  | none => throw "bad string"

def name (c : Ctx) (s : String) : Rd Name :=
  match c.ids[s]? with
  | some n => pure n
  | none => throw s!"name not in the build: {s}"

def uintTy (c : Ctx) (cls : String) (bits : Nat) : Rd UintTy :=
  if cls.isEmpty then pure (.width bits) else do pure (.nominal (← name c cls) bits)

def kind : Nat → Rd ListKind
  | 0 => pure .list | 1 => pure .vector | 2 => pure .progressiveList | 3 => pure .bitlist
  | 4 => pure .bitvector | 5 => pure .progressiveBitlist | k => throw s!"list kind {k}"

def limit (c : Ctx) : Rd (Option Nat) := do
  let has ← u8 c
  let l ← uN c 8
  pure (if has = 1 then some l else none)

partial def ty (c : Ctx) : Rd SszTy := do
  match Char.ofNat (← u8 c) with
  | 'U' => let cls ← str c; let bits ← uN c 2; pure (.uint (← uintTy c cls bits))
  | 'O' => pure .boolean
  | 'Y' => let cls ← str c; let len ← uN c 4; pure (.bytes (← name c cls) len)
  | 'C' => pure (.container (← name c (← str c)))
  | 'L' => let k ← kind (← u8 c); let e ← ty c; let l ← limit c; pure (.list k e l)
  | t => throw s!"type tag {t}"

/-- A value. `state` is the value that the tag `S` stands for. Containers and lists go into
the heap. -/
partial def value (c : Ctx) (state : Value) (h : Heap) : Rd (Value × Heap) := do
  match Char.ofNat (← u8 c) with
  | 'S' => pure (state, h)
  | 'u' =>
    let cls ← str c; let bits ← uN c 2
    let t ← uintTy c cls bits
    pure (.uint t (← uN c (bits / 8)), h)
  | 'o' => pure (.boolean ((← u8 c) = 1), h)
  | 'b' => pure (.bool ((← u8 c) = 1), h)
  | 'y' =>
    let cls ← str c; let len ← uN c 4
    pure (.bytes (← name c cls) (← bytesN c len), h)
  | 'c' =>
    let ty ← name c (← str c)
    let n ← uN c 2
    let mut fs := #[]
    let mut h := h
    for _ in [0:n] do
      let (v, h') ← value c state h
      fs := fs.push v; h := h'
    let (a, h2) := h.alloc (.container ty fs.toList)
    pure (.ref a, h2)
  | 'l' =>
    let k ← kind (← u8 c)
    let e ← ty c
    let l ← limit c
    let n ← uN c 4
    let mut xs := #[]
    let mut h := h
    for _ in [0:n] do
      let (v, h') ← value c state h
      xs := xs.push v; h := h'
    let (a, h2) := h.alloc (.list k e l xs.toList)
    pure (.ref a, h2)
  | t => throw s!"value tag {t}"

structure Call where
  fn : Name
  args : List Value

structure Case where
  id : String
  blsSetting : Nat
  heap : Heap
  state : Value
  calls : List Call
  /-- Compare the root of the last result, not of the state. -/
  resultRoot : Bool
  post : Option (List UInt8)
  config : List (Name × Value)
  /-- Inputs and results of `bls.AggregatePKs`. -/
  aggregates : List (List (List UInt8) × List UInt8)

def readCase (c : Ctx) : Rd Case := do
  let magic ← bytesN c 4
  if magic ≠ "SLC1".toUTF8.toList then throw "bad magic"
  let id ← str c
  let bls ← u8 c
  let (state, h) ← value c .none Heap.empty
  let n ← uN c 2
  let mut calls := #[]
  let mut h := h
  for _ in [0:n] do
    let fn ← name c (← str c)
    let k ← u8 c
    let mut args := #[]
    for _ in [0:k] do
      let (v, h') ← value c state h
      args := args.push v; h := h'
    calls := calls.push { fn, args := args.toList }
  let result ← u8 c
  let hasPost ← u8 c
  let root ← bytesN c 32
  let nc ← uN c 2
  let mut config := #[]
  for _ in [0:nc] do
    -- A config value that no code in the build reads is not in the name table.
    let nm := c.ids[← str c]?
    let (v, h') ← value c state h
    if let some nm := nm then config := config.push (nm, v)
    h := h'
  let na ← uN c 2
  let mut aggs := #[]
  for _ in [0:na] do
    let k ← uN c 2
    let mut pks := #[]
    for _ in [0:k] do pks := pks.push (← bytesN c 48)
    aggs := aggs.push (pks.toList, ← bytesN c 48)
  pure { id, blsSetting := bls, heap := h, state, calls := calls.toList,
         resultRoot := result = 1, post := if hasPost = 1 then some root else none,
         config := config.toList, aggregates := aggs.toList }

def parse (ids : Std.HashMap String Name) (data : ByteArray) : Except String Case :=
  (readCase ⟨data, ids⟩).run' 0

end SpecLean.Runner
