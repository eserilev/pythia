import Fuzz.Decode
import Fuzz.Render

/-!
# Fuzz runner

Reads programs that `tools/fuzz/encode.py` writes, runs the interpreter, and prints one result
line per program (`Fuzz.Render.renderResult`).

- `pythiafuzz FILE`: run one program file.
- `pythiafuzz`: a stream on stdin. Each program is a line with its length in bytes, then the
  program. Each result is one line on stdout.

A program is one `key term` line per section: `names`, `containers`, `globals`, `heap`,
`entry`, `args` and `fuel`.
-/

namespace SpecLean.Fuzz

def section_ (secs : List (String × String)) (k : String) : D Term := do
  match secs.lookup k with
  | some s => parseTerm s
  | none => .error s!"missing section {k}"

def knownNames (names : Array String) : KnownNames :=
  let id (s : String) : Name := (names.findIdx? (· == s)).getD names.size
  { append := id "append", extend := id "extend", index := id "index", count := id "count",
    copy := id "copy", union := id "union", intersection := id "intersection", add := id "add",
    fromBytes := id "from_bytes", empty := id "empty", hashTreeRoot := id "hash_tree_root",
    data := id "data", key := id "key", reverse := id "reverse", strict := id "strict",
    get := id "get", bytes32 := id "Bytes32", root := id "Root" }

def runProgram (text : String) : String :=
  let res : D String := do
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
    let env : Env :=
      { globals, containers, bytesName := 0, nm := knownNames names, config := [],
        sha256 := fun _ => [], hashTreeRoot := fun _ _ => .error .unsupported,
        bls := fun _ _ _ => .error .unsupported }
    let h := objs.foldl (fun h o => (h.alloc o).2) Heap.empty
    pure (renderResult names env args (interp env fuel entry args h))
  match res with
  | .ok s => s
  | .error e => s!"decode-error {e}"

partial def readExact (s : IO.FS.Stream) (n : Nat) (acc : ByteArray) : IO ByteArray := do
  if acc.size ≥ n then return acc
  let chunk ← s.read (n - acc.size).toUSize
  if chunk.isEmpty then return acc
  readExact s n (acc ++ chunk)

partial def serve (inp out : IO.FS.Stream) : IO Unit := do
  let line ← inp.getLine
  if line.isEmpty then return
  match line.trimAscii.toString.toNat? with
  | none => out.putStrLn s!"decode-error bad length line"; out.flush
  | some n =>
    let bytes ← readExact inp n .empty
    let text := (String.fromUTF8? bytes).getD ""
    out.putStrLn (runProgram text)
    out.flush
  serve inp out

end SpecLean.Fuzz

open SpecLean.Fuzz in
def main (args : List String) : IO Unit := do
  match args with
  | [file] => IO.println (runProgram (← IO.FS.readFile file))
  | _ => serve (← IO.getStdin) (← IO.getStdout)
