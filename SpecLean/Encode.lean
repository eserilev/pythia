import SpecLean.Gen.Ast
import SpecLean.Readable

/-!
# Decode, heap paths, the write condition and `ResultMatches` (SPEC 9.2)

`decode` reads the readable Lean value of an interpreter value out of the heap. The translator
generates the decoders from the SSZ container definitions. For the spike they are written by
hand. `BeaconState` decodes only the fields that the targets use. `StateRest` says that every
other field of the state is unchanged.
-/

namespace SpecLean.Encode

open SpecLean SpecLean.Gen SpecLean.Readable

def gweiTy : UintTy := .nominal Id.Gwei 64
def vidxTy : UintTy := .nominal Id.ValidatorIndex 64
def epochTy : UintTy := .nominal Id.Epoch 64
def u64Ty : UintTy := .width 64

/-- Field positions, from `Gen.containers`. -/
abbrev fWithdrawalCredentials : Nat := 1
abbrev fEffectiveBalance : Nat := 2
abbrev fValidators : Nat := 11
abbrev fBalances : Nat := 12

/-! ## Decode -/

/-- A uint of class `t`, in range. -/
def decUint (t : UintTy) : Value → Option Nat
  | .uint t' n => if t' = t ∧ n < 2 ^ t.bits then some n else none
  | _ => none

def decGwei (v : Value) : Option Gwei := (decUint gweiTy v).map Gwei.mk
def decEpoch (v : Value) : Option Epoch := (decUint epochTy v).map Epoch.mk
def decVidx (v : Value) : Option ValidatorIndex := (decUint vidxTy v).map ValidatorIndex.mk
def decU64 (v : Value) : Option Uint64 := (decUint u64Ty v).map Uint64.mk

def decBytes (cls len : Nat) : Value → Option (List UInt8)
  | .bytes c b => if c = cls ∧ b.length = len then some b else none
  | _ => none

def decBoolean : Value → Option Boolean
  | .boolean b => some ⟨b⟩
  | _ => none

def decValidatorFields (fs : List Value) : Option Validator := do
  let pubkey ← fs[0]? >>= decBytes Id.BLSPubkey 48
  let withdrawal_credentials ← fs[1]? >>= decBytes Id.Bytes32 32
  let effective_balance ← fs[2]? >>= decGwei
  let slashed ← fs[3]? >>= decBoolean
  let activation_eligibility_epoch ← fs[4]? >>= decEpoch
  let activation_epoch ← fs[5]? >>= decEpoch
  let exit_epoch ← fs[6]? >>= decEpoch
  let withdrawable_epoch ← fs[7]? >>= decEpoch
  if fs.length = 8 then
    pure { pubkey := ⟨pubkey⟩, withdrawal_credentials := ⟨withdrawal_credentials⟩,
           effective_balance, slashed, activation_eligibility_epoch, activation_epoch,
           exit_epoch, withdrawable_epoch }
  else none

def decValidator (h : Heap) : Value → Option Validator
  | .ref a =>
    match h.objs a with
    | some (.container ty fs) => if ty = Id.Validator then decValidatorFields fs else none
    | _ => none
  | _ => none

def decList (h : Heap) (elem : SszTy) (dec : Value → Option α) : Value → Option (List α)
  | .ref a =>
    match h.objs a with
    | some (.list .progressiveList e none xs) => if e = elem then xs.mapM dec else none
    | _ => none
  | _ => none

def decState (h : Heap) : Value → Option BeaconState
  | .ref a =>
    match h.objs a with
    | some (.container ty fs) =>
      if ty = Id.BeaconState then do
        let validators ← fs[fValidators]? >>=
          decList h (.container Id.Validator) (decValidator h)
        let balances ← fs[fBalances]? >>= decList h (.uint gweiTy) decGwei
        pure { validators, balances }
      else none
    | _ => none
  | _ => none

/-! ## Heap paths and the write condition -/

/-- The value at a path of field and element positions. -/
def follow (h : Heap) : Value → List Nat → Option Value
  | v, [] => some v
  | .ref a, i :: p =>
    match h.objs a with
    | some (.container _ fs) => fs[i]?.bind (follow h · p)
    | some (.list _ _ _ xs) => xs[i]?.bind (follow h · p)
    | _ => none
  | _, _ :: _ => none

/-- The value at path `q` from argument `k`. -/
def at? (h : Heap) (vs : List Value) (k : Nat) (q : List Nat) : Option Value :=
  vs[k]?.bind (follow h · q)

/-- One step of a footprint pattern. -/
inductive PStep where
  | exact (i : Nat)
  | any

def Matches : List PStep → List Nat → Prop
  | [], [] => True
  | .exact i :: ps, j :: qs => i = j ∧ Matches ps qs
  | .any :: ps, _ :: qs => Matches ps qs
  | _, _ => False

/-- A path pattern rooted at an SSZ container type, for example `BeaconState.validators[*]`. -/
structure FPat where
  ty : Name
  steps : List PStep

/-- A footprint: a set of path patterns. -/
abbrev Footprint := List FPat

/-- Argument `k` is a container of class `ty`. A pattern applies to every root of its type. -/
def RootTy (h : Heap) (vs : List Value) (k : Nat) (ty : Name) : Prop :=
  ∃ a fs, vs[k]? = some (.ref a) ∧ h.objs a = some (.container ty fs)

/-- Object `a` is at a footprint path from the arguments. -/
def AtFp (h : Heap) (vs : List Value) (fp : Footprint) (a : Nat) : Prop :=
  ∃ k pat q, pat ∈ fp ∧ RootTy h vs k pat.ty ∧ Matches pat.steps q ∧
    at? h vs k q = some (.ref a)

/-- The global footprint of the spike: the state container (its fields are rebound), the
balances list and each validator. -/
def FP : Footprint :=
  [⟨Id.BeaconState, []⟩, ⟨Id.BeaconState, [.exact fBalances]⟩,
   ⟨Id.BeaconState, [.exact fValidators, .any]⟩]

/-- `WTree`: every object at an `fp` path is reachable from the arguments by exactly that one
heap path. -/
def WTree (h : Heap) (vs : List Value) (fp : Footprint) : Prop :=
  ∀ k pat, pat ∈ fp → RootTy h vs k pat.ty → ∀ q, Matches pat.steps q → ∀ a,
    at? h vs k q = some (.ref a) → ∀ k' q', at? h vs k' q' = some (.ref a) → k' = k ∧ q' = q

/-- Every address at or past `next` is free. -/
def HeapWF (h : Heap) : Prop := ∀ a, h.next ≤ a → h.objs a = none

/-- Every reference that the arguments reach points to an object of the heap. -/
def ArgsWF (h : Heap) (vs : List Value) : Prop :=
  ∀ k q a, at? h vs k q = some (.ref a) → h.objs a ≠ none

/-- The frame of a function with footprint `fpf`: every object of `h` that is not at an `fpf`
path from the arguments keeps its contents. A new object is outside the frame. -/
def Frame (h h' : Heap) (vs : List Value) (fpf : Footprint) : Prop :=
  ∀ a, h.objs a ≠ none → ¬ AtFp h vs fpf a → h'.objs a = h.objs a

/-- New objects come from free addresses. -/
def Fresh (h h' : Heap) : Prop := h.next ≤ h'.next ∧ (HeapWF h → HeapWF h')

/-- The arguments reach no old object that they did not reach before. -/
def Reach (h h' : Heap) (vs : List Value) : Prop :=
  ∀ k q b, at? h' vs k q = some (.ref b) → at? h vs k q = some (.ref b) ∨ h.next ≤ b

/-- Object `a` is at a path from the arguments that matches the steps of a pattern of `fp`. The
root class of the pattern does not matter here. -/
def AtPat (h : Heap) (vs : List Value) (fp : Footprint) (a : Nat) : Prop :=
  ∃ k, ∃ pat ∈ fp, ∃ q, Matches pat.steps q ∧ at? h vs k q = some (.ref a)

/-- No old object at a footprint path gains a path. For an old object (below `h.next`) that
`h'` has at a path matching a pattern of `fp`, each path of `h'` to it comes from a path of `h`
to it from the same argument: `φ` maps the `h'`-paths to the object one to one onto `h`-paths to
it, and keeps footprint patterns. So such an object has at most as many paths after as before. A
moved list item keeps its one path, a dropped object has none, and two fields that come to hold
one such object break it. Sharing of objects at no pattern path is free (SPEC 9.2): `WTree`
speaks only of objects at a pattern path. -/
def NoNewPaths (h h' : Heap) (vs : List Value) (fp : Footprint) : Prop :=
  ∃ φ : Nat → List Nat → List Nat, ∀ k q a, at? h' vs k q = some (.ref a) → a < h.next →
    AtPat h' vs fp a →
    at? h vs k (φ k q) = some (.ref a) ∧
    (∀ pat ∈ fp, Matches pat.steps q → Matches pat.steps (φ k q)) ∧
    ∀ k' q', at? h' vs k' q' = some (.ref a) → k' = k → φ k' q' = φ k q → q' = q

/-- Every path from the state that does not start with a decoded field reads the same. -/
def StateRest (h h' : Heap) (root : Value) : Prop :=
  ∀ i q, i ≠ fValidators → i ≠ fBalances → follow h' root (i :: q) = follow h root (i :: q)

/-- SPEC 9.2. `fpf` is the footprint of the function. `Expect x h' v`: the return value and
every argument decode to the readable result `x` in the result heap. The function takes
`WTree` over `fpf` only. It promises no `WTree` on its result: `NoNewPaths` over the global
footprint `fp` and the composition lemma (`SpecLean/Compose.lean`) give it where a caller needs
it. `gfp` is the global footprint `FP`: each footprint is a part of it, and its patterns
address list items only by `*`, so a function that moves list items keeps them. -/
def ResultMatches (gfp fpf : Footprint) (h : Heap) (vs : List Value)
    (Expect : α → Heap → Value → Prop) : Res (Value × Heap) → SpecM α → Prop
  | .ok (v, h'), .ok x => Expect x h' v ∧ Frame h h' vs fpf ∧ Fresh h h' ∧
      NoNewPaths h h' vs gfp
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

end SpecLean.Encode
