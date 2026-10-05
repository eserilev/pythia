import Runner.Case
import Runner.Watch
import SpecLean.Ssz
import Tests.Sha256

/-!
# EF vector runner

Runs case files from `tools/ef_cases.py` on the interpreter (SPEC 11, item 1).

    lake exe efrunner [--quiet] [--watch] FILE_OR_DIR...           (minimal preset)
    lake exe efrunner-mainnet [--quiet] [--watch] FILE_OR_DIR...   (mainnet preset)

`--readable` (minimal only) also runs each case through the generated readable Lean, and prints
`RD-PASS` or `RD-FAIL` for it.

One line per case, then counts per runner and handler. `--watch` turns on the dynamic write
condition check and prints its hits after each case.
-/

namespace SpecLean.Runner

def zeros : Array (List UInt8) := Htr.zeroRoots Tests.Sha256.hash 64

def hasher (B : Build) : Htr.Hasher where
  sha := Tests.Sha256.hash
  zero := fun d => zeros[d]?.getD Htr.zeroChunk
  containers := B.containers
  active := B.activeFields

/-- The bytes of each element of a list of byte strings. -/
def byteList (h : Heap) : Value → Option (List (List UInt8))
  | .ref a => match h.objs a with
    | some (.list _ _ _ xs) => xs.mapM fun | .bytes _ b => some b | _ => none
    | _ => none
  | _ => none

def stubPubkey : List UInt8 := List.replicate 48 0x22

/-- The BLS oracle for `bls_setting` 0 and 2: every check passes, as in pyspec with
`bls_active = False`. `AggregatePKs` reads the table of the case. The G1 operations pass a
point through as its bytes. -/
def blsStub (B : Build) (table : List (List (List UInt8) × List UInt8)) (m : Name) (h : Heap)
    (args : List Value) : Res Value :=
  let pubkey := fun b => Value.bytes (B.ids["BLSPubkey"]?.getD 0) b
  match B.nameOf m, args with
  | "Verify", _ | "FastAggregateVerify", _ | "AggregateVerify", _ | "KeyValidate", _ =>
    .ok (.bool true)
  | "AggregatePKs", [v] =>
    match byteList h v with
    | some pks => .ok (pubkey ((table.lookup pks).getD stubPubkey))
    | none => .error .unsupported
  | "bytes48_to_G1", [v] | "neg", [v] | "G1_to_bytes48", [v] => .ok v
  | "add", [a, _] => .ok a
  | _, _ => .error .unsupported

def env (B : Build) (c : Case) : Env :=
  let e := B.env
    { sha256 := Tests.Sha256.hash
      hashTreeRoot := fun h v => Htr.root (hasher B) h 64 v
      bls := blsStub B c.aggregates }
  { e with config := c.config ++ e.config }

def errTag : SpecError → String
  | .assertionFailed => "assertionFailed" | .sszValue => "sszValue"
  | .validation => "validation" | .indexError => "indexError"
  | .valueError => "valueError" | .divisionByZero => "divisionByZero"
  | .typeError => "typeError" | .keyError => "keyError" | .nameError => "nameError"
  | .raised => "raised" | .unsupported => "unsupported" | .outOfFuel => "outOfFuel"
  | .other c => "other." ++ c

def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s)

inductive Verdict where
  | pass (note : String)
  | fail (why : String)

def fuel : Nat := 1000000000000

def runCalls (env : Env) : List Call → Heap → Value → Except (Nat × SpecError) (Heap × Value)
  | [], h, v => .ok (h, v)
  | c :: cs, h, _ =>
    match interp env fuel c.fn c.args h with
    | .ok (v, h') => match runCalls env cs h' v with
      | .ok r => .ok r
      | .error (i, e) => .error (i + 1, e)
    | .error e => .error (0, e)

def run (B : Build) (c : Case) : Verdict :=
  let env := env B c
  match runCalls env c.calls c.heap .none, c.post with
  | .error (i, e), none =>
    if e = .outOfFuel || e = .unsupported then .fail s!"call {i}: {errTag e}"
    else .pass s!"invalid ({errTag e} in call {i})"
  | .error (i, e), some _ =>
    .fail s!"call {i} ({B.nameOf (c.calls[i]?.map (·.fn) |>.getD 0)}): {errTag e}"
  | .ok _, none => .fail "expected an error, got a result"
  | .ok (h, v), some root =>
    let target := if c.resultRoot then v else c.state
    match Htr.root (hasher B) h 64 target with
    | .ok r => if r = root then .pass "" else .fail s!"root {hex r} ≠ post {hex root}"
    | .error e => .fail s!"hash_tree_root: {errTag e}"

partial def caseFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let mut out := #[]
    for e in (← p.readDir).qsort (·.fileName < ·.fileName) do
      out := out ++ (← caseFiles e.path)
    pure out
  else if p.extension == some "case" then pure #[p]
  else pure #[]

/-- `runner/handler` of a case id. -/
def group (id : String) : String :=
  "/".intercalate ((id.splitOn "/").take 2)

/-- The runner on the build `B`. -/
def main (B : Build) (args : List String) (rd : Option (Build → Case → Verdict) := none) :
    IO UInt32 := do
  let B := B.withIds
  let quiet := args.contains "--quiet"
  let watch := args.contains "--watch"
  let readable := args.contains "--readable"
  let mut files := #[]
  for a in args.filter (fun a => a != "--quiet" && a != "--watch" && a != "--readable") do
    files := files ++ (← caseFiles a)
  let mut counts : Std.HashMap String (Nat × Nat) := {}
  let mut order : Array String := #[]
  let t0 ← IO.monoMsNow
  for f in files do
    let data ← IO.FS.readBinFile f
    let t ← IO.monoMsNow
    if watch then Watch.install B
    let (id, verdict) ← match parse B.ids data with
      | .ok c => do
        let v ← IO.lazyPure fun _ => run B c
        if readable then
          if let some f := rd then
            let r ← IO.lazyPure fun _ => f B c
            match r with
            | .pass note => IO.println s!"RD-PASS {c.id} {note}"
            | .fail why => IO.println s!"RD-FAIL {c.id} {why}"
        pure (c.id, v)
      | .error e => pure (f.toString, .fail s!"parse: {e}")
    let ms := (← IO.monoMsNow) - t
    let g := group id
    if !counts.contains g then order := order.push g
    let (p, n) := counts.getD g (0, 0)
    match verdict with
    | .pass note =>
      counts := counts.insert g (p + 1, n)
      if !quiet then IO.println s!"PASS {id} {ms}ms {note}"
    | .fail why =>
      counts := counts.insert g (p, n + 1)
      IO.println s!"FAIL {id} {ms}ms {why}"
    if watch then
      for (msg, n) in ← Watch.hits do IO.println s!"  HIT {id}: {msg} (x{n})"
    (← IO.getStdout).flush
  let total := (← IO.monoMsNow) - t0
  let mut fails := 0
  for g in order do
    let (p, n) := counts.getD g (0, 0)
    fails := fails + n
    IO.println s!"{g}: {p} pass, {n} fail"
  IO.println s!"total {files.size} cases, {fails} fail, {total}ms"
  pure (if fails = 0 then 0 else 1)

end SpecLean.Runner
