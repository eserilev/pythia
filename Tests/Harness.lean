import SpecLean.Gen.Ast
import SpecLean.Readable

/-!
# Test harness for `tools/difftest.py`

Builds heaps and readable values for the cases and prints one line per case for each model.
-/

namespace SpecLean.Tests

open SpecLean SpecLean.Gen

def env0 : Env :=
  Gen.env ⟨fun _ => [], fun _ _ => .error .unsupported, fun _ _ _ => .error .unsupported⟩
def fuel : Nat := 10000

def gwei : UintTy := .nominal Id.Gwei 64
def vidx : UintTy := .nominal Id.ValidatorIndex 64
def epoch : UintTy := .nominal Id.Epoch 64
def u64 : UintTy := .width 64

def tyName : UintTy → String
  | .width b => s!"Uint{b}"
  | .nominal k _ => Gen.names.getD k "?"

def showVal : Value → String
  | .uint t n => s!"{tyName t} {n}"
  | .int n => s!"int {n}"
  | v => reprStr v

def errTag : SpecError → String
  | .assertionFailed => "assertionFailed" | .sszValue => "sszValue"
  | .validation => "validation" | .indexError => "indexError"
  | .valueError => "valueError" | .divisionByZero => "divisionByZero"
  | .typeError => "typeError" | .keyError => "keyError" | .nameError => "nameError"
  | .raised => "raised" | .unsupported => "unsupported" | .outOfFuel => "outOfFuel"

def wc (prefix_ : Nat) : List UInt8 := UInt8.ofNat prefix_ :: List.replicate 31 0

/-- A heap with one `BeaconState`. Fields that no target reads hold `None`. -/
def mkState (vals : List (Nat × Nat)) (bals : List Nat) : Nat × Heap :=
  let (refs, h) := vals.foldl (init := (([] : List Nat), Heap.empty)) fun (rs, h) (e, p) =>
    let (r, h) := h.alloc (.container Id.Validator
      [.bytes Id.BLSPubkey (List.replicate 48 0), .bytes Id.Bytes32 (wc p), .uint gwei e,
       .boolean false, .uint epoch 0, .uint epoch 0, .uint epoch 0, .uint epoch 0])
    (rs ++ [r], h)
  let (va, h) := h.alloc (.list .progressiveList (.container Id.Validator) none (refs.map .ref))
  let (ba, h) := h.alloc (.list .progressiveList (.uint gwei) none (bals.map (.uint gwei ·)))
  let fields := ((List.replicate 46 Value.none).set 11 (.ref va)).set 12 (.ref ba)
  h.alloc (.container Id.BeaconState fields)

def listAt (h : Heap) (root : Nat) (field : Nat) : List Value :=
  match h.objs root with
  | some (.container _ fs) =>
    match fs[field]? with
    | some (.ref a) => match h.objs a with
      | some (.list _ _ _ xs) => xs
      | _ => []
    | _ => []
  | _ => []

def natOf : Value → Nat
  | .uint _ n => n
  | _ => 0

def showNats (xs : List Nat) : String := "[" ++ ",".intercalate (xs.map toString) ++ "]"

def readBalances (h : Heap) (root : Nat) : List Nat := (listAt h root 12).map natOf

def readEffs (h : Heap) (root : Nat) : List Nat :=
  (listAt h root 11).map fun
    | .ref r => match h.objs r with
      | some (.container _ fs) => natOf (fs.getD 2 .none)
      | _ => 0
    | _ => 0

def readableState (vals : List (Nat × Nat)) (bals : List Nat) : Readable.BeaconState :=
  { validators := vals.map fun (e, p) =>
      { pubkey := ⟨List.replicate 48 0⟩, withdrawal_credentials := ⟨wc p⟩,
        effective_balance := ⟨e⟩, slashed := ⟨false⟩, activation_eligibility_epoch := ⟨0⟩,
        activation_epoch := ⟨0⟩, exit_epoch := ⟨0⟩, withdrawable_epoch := ⟨0⟩ },
    balances := bals.map (⟨·⟩) }

def line (model name : String) (r : Except SpecError String) : IO Unit :=
  IO.println <| s!"{model} {name}: " ++ match r with
    | .ok s => s!"ok {s}"
    | .error e => s!"err {errTag e}"

/-- The readable Lean keeps only the error class. -/
def rline (name : String) (r : Except Fail String) : IO Unit :=
  IO.println <| s!"readable {name}: " ++ match r with
    | .ok s => s!"ok {s}"
    | .error .invalid => "err invalid"
    | .error .bug => "err bug"

/-- `deltaVidx` passes `delta` as a `ValidatorIndex`. The readable Lean cannot express that. -/
def runDB (name : String) (bals : List Nat) (index delta : Nat) (deltaVidx : Bool) :
    IO Unit := do
  let (root, h) := mkState [] bals
  line "interp" name <| (interp env0 fuel Id.decrease_balance
    [.ref root, .uint vidx index, .uint (if deltaVidx then vidx else gwei) delta] h).map
      fun (_, h') => s!"balances={showNats (readBalances h' root)}"
  if deltaVidx then IO.println s!"readable {name}: skip" else
  rline name <| (Readable.decrease_balance (readableState [] bals) ⟨index⟩ ⟨delta⟩).map
    fun s => s!"balances={showNats (s.balances.map (·.val))}"

def runPEB (name : String) (vals : List (Nat × Nat)) (bals : List Nat) : IO Unit := do
  let (root, h) := mkState vals bals
  line "interp" name <| (interp env0 fuel Id.process_effective_balance_updates [.ref root] h).map
    fun (_, h') => s!"eff={showNats (readEffs h' root)}"
  rline name <| (Readable.process_effective_balance_updates (readableState vals bals)).map
    fun s => s!"eff={showNats (s.validators.map (·.effective_balance.val))}"

def runIsqrt (name : String) (n : Nat) (plainInt : Bool) : IO Unit := do
  let arg : Value := if plainInt then .int n else .uint u64 n
  line "interp" name <| (interp env0 fuel Id.integer_squareroot [arg] Heap.empty).map
    fun (v, _) => showVal v
  if plainInt then IO.println s!"readable {name}: skip"
  else rline name <| (Readable.integer_squareroot ⟨n⟩).map fun r => s!"Uint64 {r.val}"

end SpecLean.Tests
