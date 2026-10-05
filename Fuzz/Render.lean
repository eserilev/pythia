import SpecLean.Interp
import SpecLean.Ssz

/-!
# Canonical rendering with object identity

`tools/fuzz/render.py` renders CPython values in the same form. A heap object gets the label
`#k=` at its first visit, in depth-first order, and `#k` at each later visit. So two outputs
match only if the values and the sharing between objects match.
-/

namespace SpecLean.Fuzz

def hex (b : List UInt8) : String :=
  String.join (b.map fun x =>
    let s := Nat.toDigits 16 x.toNat
    if s.length = 1 then "0" ++ String.ofList s else String.ofList s)

def pyBool (b : Bool) : String := if b then "True" else "False"

def uintName (names : Array String) : UintTy → String
  | .width b => s!"Uint{b}"
  | .nominal k _ => names.getD k "?"

def sortStrs (xs : List String) : List String :=
  (xs.toArray.qsort (· < ·)).toList

partial def tyStr (names : Array String) : SszTy → String
  | .uint u => uintName names u
  | .boolean => "Boolean"
  | .bytes n _ => names.getD n "?"
  | .container n => names.getD n "?"
  | .any => "any"
  | .list k e l =>
    let lim := match l with | some n => s!",{n}" | none => ""
    match k with
    | .list => s!"List[{tyStr names e}{lim}]"
    | .vector => s!"Vector[{tyStr names e}{lim}]"
    | .progressiveList => s!"ProgressiveList[{tyStr names e}]"
    | .bitlist => s!"Bitlist[{lim.drop 1}]"
    | .bitvector => s!"Bitvector[{lim.drop 1}]"
    | .progressiveBitlist => "ProgressiveBitlist"
    | .pyList => "list"

structure RS where
  seen : List (Nat × Nat) := []
  next : Nat := 0

partial def render (names : Array String) (env : Env) (h : Heap) : Value → StateM RS String
  | .int n => pure s!"int:{n}"
  | .uint t n => pure s!"{uintName names t}:{n}"
  | .bool b => pure s!"bool:{pyBool b}"
  | .boolean b => pure s!"Boolean:{pyBool b}"
  | .str s => pure s!"str:{s}"
  | .none => pure "None"
  | .bytes ty b => pure s!"{names.getD ty "?"}:{hex b}"
  | .tuple xs => do
    let parts ← xs.mapM (render names env h)
    pure ("(" ++ ",".intercalate parts ++ ")")
  | .frozenDict kvs => do
    let parts ← kvs.mapM fun (k, v) => do
      pure ((← render names env h k) ++ ":" ++ (← render names env h v))
    pure ("frozendict{" ++ ",".intercalate parts ++ "}")
  | .ref a => do
    let st ← get
    match st.seen.lookup a with
    | some k => pure s!"#{k}"
    | none =>
      let k := st.next
      set { st with seen := (a, k) :: st.seen, next := k + 1 }
      let body ← match h.objs a with
        | some (.list kind e l xs) => do
          let parts ← xs.mapM (render names env h)
          pure (tyStr names (.list kind e l) ++ "[" ++ ",".intercalate parts ++ "]")
        | some (.container ty fs) => do
          let fnames := ((env.containers.lookup ty).getD []).map (·.1)
          let parts ← (fnames.zip fs).mapM fun (f, v) => do
            pure (names.getD f "?" ++ "=" ++ (← render names env h v))
          pure (names.getD ty "?" ++ "{" ++ ",".intercalate parts ++ "}")
        | some (.set xs) => do
          let parts ← xs.mapM (render names env h)
          pure ("set{" ++ ",".intercalate (sortStrs parts) ++ "}")
        | some (.dict es) => do
          let parts ← es.mapM fun (k, v) => do
            pure ((← render names env h k) ++ ":" ++ (← render names env h v))
          pure ("dict{" ++ ",".intercalate parts ++ "}")
        | some (.closure _ _ _) => pure "<fn>"
        | none => pure "<dangling>"
      pure s!"#{k}={body}"
  | .enumView _ => pure "<enumerate>"
  | .zipView _ _ => pure "<zip>"
  | .glob g => pure s!"<global {names.getD g "?"}>"
  | .member _ m => pure s!"<member {names.getD m "?"}>"

def errTag : SpecError → String
  | .assertionFailed => "assertionFailed" | .sszValue => "sszValue"
  | .validation => "validation" | .indexError => "indexError"
  | .valueError => "valueError" | .divisionByZero => "divisionByZero"
  | .typeError => "typeError" | .keyError => "keyError" | .nameError => "nameError"
  | .raised => "raised" | .unsupported => "unsupported" | .outOfFuel => "outOfFuel"
  | .other c => "other." ++ c

def failTag : SpecError → String
  | .outOfFuel => "outOfFuel"
  | e => match e.fail with
    | .invalid => "invalid"
    | .bug => "bug"

/-- `ok ret=<v> | a0=<v> | ...` with one label space, or `err <class>:<diagnostic>`. -/
def renderResult (names : Array String) (env : Env) (args : List Value) :
    Res (Value × Heap) → String
  | .ok (v, h) =>
    let go : StateM RS (List String) := do
      let r ← render names env h v
      let as ← args.mapM (render names env h)
      pure (("ret=" ++ r) :: (as.zipIdx.map fun (s, i) => s!"a{i}={s}"))
    "ok " ++ " | ".intercalate (go.run' {})
  | .error e => s!"err {failTag e}:{errTag e}"

end SpecLean.Fuzz
