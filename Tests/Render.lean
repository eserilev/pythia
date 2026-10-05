import SpecLean.Interp
import Tests.Sha256

/-!
# Canonical rendering of interpreter values

`tools/constructs.py` renders CPython values in the same form, then compares the strings.
-/

namespace SpecLean.Tests

def hex (b : List UInt8) : String :=
  String.join (b.map fun x =>
    let s := Nat.toDigits 16 x.toNat
    if s.length = 1 then "0" ++ String.mk s else String.mk s)

def pyBool (b : Bool) : String := if b then "True" else "False"

def uintName (names : Array String) : UintTy → String
  | .width b => s!"Uint{b}"
  | .nominal k _ => names.getD k "?"

def insertStr (s : String) : List String → List String
  | [] => [s]
  | x :: xs => if s < x then s :: x :: xs else x :: insertStr s xs

def sortStrs (xs : List String) : List String := xs.foldr insertStr []

partial def render (names : Array String) (env : Env) (h : Heap) : Value → String
  | .int n => s!"int:{n}"
  | .uint t n => s!"{uintName names t}:{n}"
  | .bool b => s!"bool:{pyBool b}"
  | .boolean b => s!"Boolean:{pyBool b}"
  | .str s => s!"str:{s}"
  | .none => "None"
  | .bytes ty b => s!"{names.getD ty "?"}:{hex b}"
  | .tuple xs => "(" ++ ",".intercalate (xs.map (render names env h)) ++ ")"
  | .frozenDict kvs =>
    "{" ++ ",".intercalate (kvs.map fun (k, v) =>
      render names env h k ++ ":" ++ render names env h v) ++ "}"
  | .ref a =>
    match h.objs a with
    | some (.list _ _ _ xs) => "[" ++ ",".intercalate (xs.map (render names env h)) ++ "]"
    | some (.container ty fs) =>
      let fnames := ((env.containers.lookup ty).getD []).map (·.1)
      names.getD ty "?" ++ "{" ++ ",".intercalate ((fnames.zip fs).map fun (f, v) =>
        names.getD f "?" ++ "=" ++ render names env h v) ++ "}"
    | some (.set xs) => "set{" ++ ",".intercalate (sortStrs (xs.map (render names env h))) ++ "}"
    | some (.dict es) =>
      "{" ++ ",".intercalate (es.map fun (k, v) =>
        render names env h k ++ ":" ++ render names env h v) ++ "}"
    | some (.closure _ _ _) => "<fn>"
    | none => "<dangling>"
  | _ => "<view>"

def errTag : SpecError → String
  | .assertionFailed => "assertionFailed" | .sszValue => "sszValue"
  | .validation => "validation" | .indexError => "indexError"
  | .valueError => "valueError" | .divisionByZero => "divisionByZero"
  | .typeError => "typeError" | .keyError => "keyError" | .nameError => "nameError"
  | .raised => "raised" | .unsupported => "unsupported" | .outOfFuel => "outOfFuel"
  | .other c => "other." ++ c

/-- The test oracle: real SHA-256. `hash_tree_root` and BLS are not in the construct tests. -/
def testOracle : Oracle where
  sha256 := Sha256.hash
  hashTreeRoot := fun _ _ => .error .unsupported
  bls := fun _ _ _ => .error .unsupported

def runCase (names : Array String) (env : Env) (fuel : Nat) (label : String) (f : Name) :
    IO Unit := do
  let line := match interp env fuel f [] Heap.empty with
    | .ok (v, h) => "ok " ++ render names env h v
    | .error e => "err " ++ errTag e
  IO.println s!"{label}: {line}"

end SpecLean.Tests
