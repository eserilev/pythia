import SpecLean.Value

/-!
# Readable Lean for the spike targets

Written by hand in the state-passing style of the translator (SPEC 9.1). The source is the spec as
written, from consensus-specs `889a389f9`. Each nominal uint class and `Boolean` is its own type.
`BeaconState` carries only the fields that the targets use. `Validator` carries all fields.
-/

namespace SpecLean.Readable

/-- The readable Lean keeps only the error class (SPEC 9.2). -/
abbrev SpecM := Except Fail

/-- Keep the class of an error and drop its diagnostic. -/
def erase (r : Res α) : SpecM α := r.mapError SpecError.fail

/-! ## Types -/

/-- A 64-bit uint class. -/
class Uint64Class (α : Type) where
  val : α → Nat
  ofVal : Nat → α

export Uint64Class (val ofVal)

structure Uint64 where val : Nat deriving DecidableEq, Repr
structure Gwei where val : Nat deriving DecidableEq, Repr
structure ValidatorIndex where val : Nat deriving DecidableEq, Repr
structure Epoch where val : Nat deriving DecidableEq, Repr
structure Boolean where val : Bool deriving DecidableEq, Repr
structure Bytes32 where data : List UInt8 deriving DecidableEq, Repr
structure BLSPubkey where data : List UInt8 deriving DecidableEq, Repr

instance : Uint64Class Uint64 := ⟨Uint64.val, Uint64.mk⟩
instance : Uint64Class Gwei := ⟨Gwei.val, Gwei.mk⟩
instance : Uint64Class ValidatorIndex := ⟨ValidatorIndex.val, ValidatorIndex.mk⟩
instance : Uint64Class Epoch := ⟨Epoch.val, Epoch.mk⟩

structure Validator where
  pubkey : BLSPubkey
  withdrawal_credentials : Bytes32
  effective_balance : Gwei
  slashed : Boolean
  activation_eligibility_epoch : Epoch
  activation_epoch : Epoch
  exit_epoch : Epoch
  withdrawable_epoch : Epoch
  deriving DecidableEq, Repr

structure BeaconState where
  validators : List Validator
  balances : List Gwei
  deriving DecidableEq, Repr

/-! ## Checked operations

Python picks the more derived class of the two operands. The translator writes a `cast` where
the readable types differ, for example `Gwei + Uint64`. -/

section ops

variable {α β : Type} [Uint64Class α] [Uint64Class β]

/-- The same number in another uint class. -/
def cast (x : α) : β := ofVal (val x)

/-- `Uint64(x)` and the other class constructors: the range check. -/
@[irreducible] def toUint (x : α) : SpecM β := erase (ofVal <$> chkRange (val x))

@[irreducible] def uAdd (a b : α) : SpecM α := erase (ofVal <$> chkAdd (val a) (val b))
@[irreducible] def uSub (a b : α) : SpecM α := erase (ofVal <$> chkSub (val a) (val b))
@[irreducible] def uMul (a b : α) : SpecM α := erase (ofVal <$> chkMul (val a) (val b))
@[irreducible] def uDiv (a b : α) : SpecM α := erase (ofVal <$> chkDiv (val a) (val b))
@[irreducible] def uMod (a b : α) : SpecM α := erase (ofVal <$> chkMod (val a) (val b))

/-- `min(a, b)` keeps `a` unless `b < a`. -/
def umin (a b : α) : α := if val b < val a then b else a

end ops

def listGet (xs : List α) (i : Nat) : SpecM α :=
  match xs[i]? with
  | some x => pure x
  | none => throw .invalid

def listSet (xs : List α) (i : Nat) (x : α) : SpecM (List α) :=
  if i < xs.length then pure (xs.set i x) else throw .invalid

/-! ## Constants (minimal preset) -/

def UINT64_MAX : Uint64 := ⟨2 ^ 64 - 1⟩
def UINT64_MAX_SQRT : Uint64 := ⟨4294967295⟩
def COMPOUNDING_WITHDRAWAL_PREFIX : List UInt8 := [2]
def EFFECTIVE_BALANCE_INCREMENT : Gwei := ⟨1000000000⟩
def HYSTERESIS_QUOTIENT : Uint64 := ⟨4⟩
def HYSTERESIS_DOWNWARD_MULTIPLIER : Uint64 := ⟨1⟩
def HYSTERESIS_UPWARD_MULTIPLIER : Uint64 := ⟨5⟩
def MIN_ACTIVATION_BALANCE : Gwei := ⟨32000000000⟩
def MAX_EFFECTIVE_BALANCE_ELECTRA : Gwei := ⟨2048000000000⟩

/-! ## Targets -/

/-- ```python
def saturating_sub(a: Uint64, b: int) -> Any:
    return a - b if a > b else a - a
``` -/
def saturating_sub {α : Type} [Uint64Class α] (a b : α) : SpecM α :=
  if val b < val a then uSub a b else uSub a a

/-- ```python
def decrease_balance(state: BeaconState, index: ValidatorIndex, delta: Gwei) -> None:
    state.balances[index] = saturating_sub(state.balances[index], delta)
``` -/
def decrease_balance (state : BeaconState) (index : ValidatorIndex) (delta : Gwei) :
    SpecM BeaconState := do
  let balance ← listGet state.balances index.val
  let new_balance ← saturating_sub balance delta
  let balances ← listSet state.balances index.val new_balance
  pure { state with balances }

/-- ```python
def is_compounding_withdrawal_credential(withdrawal_credentials: Bytes32) -> bool:
    return withdrawal_credentials[:1] == COMPOUNDING_WITHDRAWAL_PREFIX
``` -/
def is_compounding_withdrawal_credential (withdrawal_credentials : Bytes32) : Bool :=
  withdrawal_credentials.data.take 1 == COMPOUNDING_WITHDRAWAL_PREFIX

/-- ```python
def has_compounding_withdrawal_credential(validator: Validator) -> bool:
    return is_compounding_withdrawal_credential(validator.withdrawal_credentials)
``` -/
def has_compounding_withdrawal_credential (validator : Validator) : Bool :=
  is_compounding_withdrawal_credential validator.withdrawal_credentials

/-- ```python
def get_max_effective_balance(validator: Validator) -> Gwei:
    if has_compounding_withdrawal_credential(validator):
        return MAX_EFFECTIVE_BALANCE_ELECTRA
    else:
        return MIN_ACTIVATION_BALANCE
``` -/
def get_max_effective_balance (validator : Validator) : Gwei :=
  if has_compounding_withdrawal_credential validator then MAX_EFFECTIVE_BALANCE_ELECTRA
  else MIN_ACTIVATION_BALANCE

/-- One iteration of the loop in `process_effective_balance_updates`.

The loop variable `validator` refers to the object at `state.validators[index]`. So a read
through it reads that path, and the write `validator.effective_balance = …` writes that path. -/
def process_effective_balance_updates.body (state : BeaconState) (index : Nat) :
    SpecM BeaconState := do
  let validator ← listGet state.validators index
  let balance ← listGet state.balances index
  let HYSTERESIS_INCREMENT : Uint64 ←
    toUint (← uDiv EFFECTIVE_BALANCE_INCREMENT (cast HYSTERESIS_QUOTIENT))
  let DOWNWARD_THRESHOLD ← uMul HYSTERESIS_INCREMENT HYSTERESIS_DOWNWARD_MULTIPLIER
  let UPWARD_THRESHOLD ← uMul HYSTERESIS_INCREMENT HYSTERESIS_UPWARD_MULTIPLIER
  let max_effective_balance := get_max_effective_balance validator
  let below ← uAdd balance (cast DOWNWARD_THRESHOLD)
  let update ←
    if below.val < validator.effective_balance.val then pure true
    else do
      let above ← uAdd validator.effective_balance (cast UPWARD_THRESHOLD)
      pure (decide (above.val < balance.val))
  if update then
    let rounded ← uSub balance (← uMod balance EFFECTIVE_BALANCE_INCREMENT)
    let validator' := { validator with effective_balance := umin rounded max_effective_balance }
    pure { state with validators := state.validators.set index validator' }
  else pure state

theorem bind_ok {x : SpecM α} {f : α → SpecM β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The body keeps the number of validators. The loop below needs this to end. -/
theorem process_effective_balance_updates.body_length {state state' : BeaconState}
    {index : Nat} (h : process_effective_balance_updates.body state index = .ok state') :
    state'.validators.length = state.validators.length := by
  unfold process_effective_balance_updates.body at h
  obtain ⟨v, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  dsimp only at h
  repeat' (first
    | (obtain ⟨_, -, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals first | (subst h; simp) | (have h' := Except.ok.inj h; subst h'; simp)

/-- The `for` loop, by index. Python reads the length of `state.validators` again at each
step. -/
def process_effective_balance_updates.loop (state : BeaconState) (index : Nat) :
    SpecM BeaconState :=
  if _hi : index < state.validators.length then
    match hb : process_effective_balance_updates.body state index with
    | .error e => .error e
    | .ok state' => process_effective_balance_updates.loop state' (index + 1)
  else pure state
termination_by state.validators.length - index
decreasing_by have := process_effective_balance_updates.body_length hb; omega

/-- ```python
def process_effective_balance_updates(state: BeaconState) -> None:
    # Update effective balances with hysteresis
    for index, validator in enumerate(state.validators):
        balance = state.balances[index]
        HYSTERESIS_INCREMENT = Uint64(EFFECTIVE_BALANCE_INCREMENT // HYSTERESIS_QUOTIENT)
        DOWNWARD_THRESHOLD = HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER
        UPWARD_THRESHOLD = HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER
        # [Modified in Electra:EIP7251]
        max_effective_balance = get_max_effective_balance(validator)

        if (
            balance + DOWNWARD_THRESHOLD < validator.effective_balance
            or validator.effective_balance + UPWARD_THRESHOLD < balance
        ):
            validator.effective_balance = min(
                balance - balance % EFFECTIVE_BALANCE_INCREMENT, max_effective_balance
            )
``` -/
def process_effective_balance_updates (state : BeaconState) : SpecM BeaconState :=
  process_effective_balance_updates.loop state 0

/-- The `while` loop of `integer_squareroot`. It ends because `x` gets smaller. -/
def integer_squareroot.loop (n x y : Uint64) : SpecM Uint64 :=
  if _h : y.val < x.val then do
    let y' ← uDiv (← uAdd y (← uDiv n y)) ⟨2⟩
    integer_squareroot.loop n y y'
  else pure x
termination_by x.val

/-- ```python
def integer_squareroot(n: Uint64) -> Uint64:
    if n == UINT64_MAX:
        return UINT64_MAX_SQRT
    x = n
    y = (x + 1) // 2
    while y < x:
        x = y
        y = (x + n // x) // 2
    return x
``` -/
def integer_squareroot (n : Uint64) : SpecM Uint64 :=
  if n.val = UINT64_MAX.val then pure UINT64_MAX_SQRT
  else do
    let x := n
    let y ← uDiv (← uAdd x ⟨1⟩) ⟨2⟩
    integer_squareroot.loop n x y

end SpecLean.Readable
