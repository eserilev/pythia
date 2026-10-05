import Fuzz.Decode
import Fuzz.Render
import Runner.Main

/-!
# Fuzz runner

Reads programs that `tools/fuzz/harness.py` writes, runs the interpreter, and prints one result
line per program (`Fuzz.Render.renderResult`).

- `pythiafuzz [--watch] FILE`: run one program file.
- `pythiafuzz [--watch]`: a stream on stdin. Each program is a line with its length in bytes,
  then the program. Each result is one line on stdout.

A program is one `key term` line per section: `names`, `containers`, `globals`, `heap`,
`entry`, `args` and `fuel`, and optionally `active`, `fp` and `fnfp` (the tables of the write
condition check, as `tools/serialize.py` makes them).

`--watch` turns on the dynamic write condition check of the EF runner (`Runner.Watch`). Its
hits follow the result on the same line, each after ` || HIT `.
-/

namespace SpecLean.Fuzz

def section_ (secs : List (String × String)) (k : String) : D Term := do
  match secs.lookup k with
  | some s => parseTerm s
  | none => .error s!"missing section {k}"

def sectionOr (secs : List (String × String)) (k : String) : D Term :=
  if (secs.lookup k).isSome then section_ secs k else .ok (.list [])

def knownNames (names : Array String) : KnownNames :=
  let id (s : String) : Name := (names.findIdx? (· == s)).getD names.size
  { append := id "append", extend := id "extend", index := id "index", count := id "count",
    copy := id "copy", union := id "union", intersection := id "intersection", add := id "add",
    fromBytes := id "from_bytes", empty := id "empty", hashTreeRoot := id "hash_tree_root",
    data := id "data", key := id "key", reverse := id "reverse", strict := id "strict",
    get := id "get", bytes32 := id "Bytes32", root := id "Root" }

structure Program where
  build : Runner.Build
  env : Env
  heap : Heap
  entry : Name
  args : List Value
  fuel : Nat

def decodeProgram (text : String) : D Program := do
  let secs := (text.splitOn "\n").filterMap fun line =>
    match line.splitOn " " with
    | k :: rest => if k.isEmpty then none else some (k, " ".intercalate rest)
    | [] => none
  let names := (← dList dStr (← section_ secs "names")).toArray
  let containers ← dList (dPair dNat (dList (dPair dNat dSszTy))) (← section_ secs "containers")
  let globals ← dList (dPair dNat dGlobal) (← section_ secs "globals")
  let objs ← dList dHeapObj (← section_ secs "heap")
  let entry ← dNat (← section_ secs "entry")
  let args ← dList dValue (← section_ secs "args")
  let fuel ← dNat (← section_ secs "fuel")
  let activeFields ← dList (dPair dNat (dList dNat)) (← sectionOr secs "active")
  let footprint ← dList (dPair dNat (dList dNat)) (← sectionOr secs "fp")
  let fnFootprint ← dList (dPair dNat (dList (dPair dNat (dList dNat)))) (← sectionOr secs "fnfp")
  let base : Oracle → Env := fun o =>
    { globals, containers, bytesName := 0, nm := knownNames names, config := [],
      sha256 := o.sha256, hashTreeRoot := o.hashTreeRoot, bls := o.bls }
  let build : Runner.Build :=
    Runner.Build.withIds { names, containers, activeFields, footprint, fnFootprint, env := base }
  let env := base
    { sha256 := Tests.Sha256.hash
      hashTreeRoot := fun h v => Htr.root (Runner.hasher build) h 64 v
      bls := fun _ _ _ => .error .unsupported }
  let heap := objs.foldl (fun h o => (h.alloc o).2) Heap.empty
  pure { build, env, heap, entry, args, fuel }

def runProgram (watch : Bool) (text : String) : IO String := do
  match decodeProgram text with
  | .error e => pure s!"decode-error {e}"
  | .ok p =>
    if watch then
      Runner.Watch.ctxRef.set (Runner.Watch.Ctx.ofBuild p.build)
      Runner.Watch.install p.build
    let r ← IO.lazyPure fun _ => interp p.env p.fuel p.entry p.args p.heap
    let line := renderResult p.build.names p.env p.args r
    if !watch then return line
    let hits ← Runner.Watch.hits
    return line ++ String.join (hits.map fun (msg, n) => s!" || HIT {msg} (x{n})")

partial def readExact (s : IO.FS.Stream) (n : Nat) (acc : ByteArray) : IO ByteArray := do
  if acc.size ≥ n then return acc
  let chunk ← s.read (n - acc.size).toUSize
  if chunk.isEmpty then return acc
  readExact s n (acc ++ chunk)

partial def serve (watch : Bool) (inp out : IO.FS.Stream) : IO Unit := do
  let line ← inp.getLine
  if line.isEmpty then return
  match line.trimAscii.toString.toNat? with
  | none => out.putStrLn s!"decode-error bad length line"; out.flush
  | some n =>
    let bytes ← readExact inp n .empty
    let text := (String.fromUTF8? bytes).getD ""
    out.putStrLn (← runProgram watch text)
    out.flush
  serve watch inp out

end SpecLean.Fuzz

open SpecLean.Fuzz in
def main (args : List String) : IO Unit := do
  let watch := args.contains "--watch"
  match args.filter (· != "--watch") with
  | [file] => IO.println (← runProgram watch (← IO.FS.readFile file))
  | _ => serve watch (← IO.getStdin) (← IO.getStdout)
