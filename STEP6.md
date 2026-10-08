# Step 6: move the Lighthouse epoch proofs onto the generated Lean

The Lighthouse epoch proofs (`lighthouse-epoch-proofs`, `consensus/state_processing/proofs`)
prove that Lighthouse equals a hand-written Lean spec (`EpochProofs/Spec/*`). Step 6 replaces
that hand-written spec with the readable Lean that Pythia generates
(`SpecLean/Gen/Readable.lean`). This file maps the two models, lists their differences, gives a
plan for the bridge, and reports a prototype.

Names: "hand" is `EpochProofs.Spec` (commit 71dc4d7855 of `lighthouse-epoch-proofs`). "Readable"
is `SpecLean.Rd.Gen` on branch `fixes` (2efd5b2).

## 1. Function map

The Lighthouse proofs (`Equiv/*` and `Sanity/*`) use 122 hand functions. 113 of them match a
readable function: 106 readable functions, because the 7 hand `_loop` helpers match the loop
inside their readable function. The other 9 hand names are helpers with no spec function. Each
one matches a readable prelude operation: `uint64Add`, `uint64Sub`, `uint64Mul`, `uint64Div` and `uint64Mod`
match `uOp`. `listGet` and `listSet` match `lget` and `lset`. `uint64Sum` matches the sum in the
readable function. `listIndexOf` matches `.index()`.

Columns:

- Tactic: the function has a `_run` theorem in `SpecLean/Validation` (the tactic proof that the
  interpreter equals the readable Lean). A `_p…` variant counts.
- Layer 4: the function has an `_l4` theorem in `SpecLean/Layer4/Gen/Funcs.lean` on
  `origin/layer4-spike`.
- Parameters: "same" when the hand parameters (without the preset `p` and the oracle `o`) have
  the readable names. Otherwise the two lists. A hand `_loop` function is the loop inside the
  readable function. Its parameters are the loop state, so they always differ.

Totals: 45 of 113 have a tactic proof, 33 have a layer 4 proof, 46 have one or the other. 84
have the same parameters.

| Hand function (`Spec/` file) | Readable (`Gen/Readable.lean`) | Tactic | Layer 4 | Parameters |
|---|---|---|---|---|
| `process_attestation_loop` (Block/Attestations.lean) | `process_attestation` (loop) | no | no | hand: (state, data, participation_flag_indices, attesting_indices, epoch_participation, payment); readable: (state, attestation, parent_slot) |
| `process_attestation` (Block/Attestations.lean) | `process_attestation` | no | no | same |
| `process_payload_attestation` (Block/Attestations.lean) | `process_payload_attestation` | no | no | hand: (GLOAS_FORK_EPOCH, state, payload_attestation); readable: (state, payload_attestation) |
| `process_operations` (Block/Block.lean) | `process_operations` | no | no | hand: (GLOAS_FORK_EPOCH, state, body, parent_slot); readable: (state, body, parent_slot) |
| `process_block` (Block/Block.lean) | `process_block` | no | no | hand: (max_blobs_per_block, GLOAS_FORK_EPOCH, state, block); readable: (state, block) |
| `verify_block_signature` (Block/Block.lean) | `verify_block_signature` | no | no | same |
| `state_transition` (Block/Block.lean) | `state_transition` | no | no | hand: (max_blobs_per_block, GLOAS_FORK_EPOCH, state, signed_block, validate_result); readable: (state, signed_block, validate_result) |
| `process_eth1_data` (Block/Eth1Data.lean) | `process_eth1_data` | no | no | same |
| `set_or_append_list` (Block/ExecutionRequests.lean) | `set_or_append_list` | no | no | same |
| `compute_consolidation_epoch_and_update_churn` (Block/ExecutionRequests.lean) | `compute_consolidation_epoch_and_update_churn` | no | no | hand: (total_active_balance, state, consolidation_balance); readable: (state, consolidation_balance) |
| `queue_excess_active_balance` (Block/ExecutionRequests.lean) | `queue_excess_active_balance` | yes | yes | same |
| `switch_to_compounding_validator` (Block/ExecutionRequests.lean) | `switch_to_compounding_validator` | yes | no | same |
| `process_deposit_request` (Block/ExecutionRequests.lean) | `process_deposit_request` | yes | yes | same |
| `process_withdrawal_request` (Block/ExecutionRequests.lean) | `process_withdrawal_request` | no | no | same |
| `process_consolidation_request` (Block/ExecutionRequests.lean) | `process_consolidation_request` | no | no | same |
| `initiate_builder_exit` (Block/ExecutionRequests.lean) | `initiate_builder_exit` | yes | yes | same |
| `add_builder_to_registry` (Block/ExecutionRequests.lean) | `add_builder_to_registry` | no | no | same |
| `process_builder_deposit_request` (Block/ExecutionRequests.lean) | `process_builder_deposit_request` | no | no | same |
| `process_builder_exit_request` (Block/ExecutionRequests.lean) | `process_builder_exit_request` | no | no | same |
| `process_voluntary_exit` (Block/Exits.lean) | `process_voluntary_exit` | no | no | same |
| `process_bls_to_execution_change` (Block/Exits.lean) | `process_bls_to_execution_change` | no | no | same |
| `process_block_header` (Block/Header.lean) | `process_block_header` | no | no | same |
| `settle_builder_payment` (Block/ParentPayload.lean) | `settle_builder_payment` | no | no | same |
| `apply_parent_execution_payload` (Block/ParentPayload.lean) | `apply_parent_execution_payload` | no | no | same |
| `process_parent_execution_payload` (Block/ParentPayload.lean) | `process_parent_execution_payload` | no | no | same |
| `process_execution_payload_bid` (Block/ParentPayload.lean) | `process_execution_payload_bid` | no | no | hand: (max_blobs_per_block, state, signed_bid); readable: (state, signed_bid) |
| `process_randao` (Block/Randao.lean) | `process_randao` | no | no | same |
| `slash_validator` (Block/Slashings.lean) | `slash_validator` | no | no | same |
| `is_slashable_validator` (Block/Slashings.lean) | `is_slashable_validator` | yes | yes | same |
| `process_proposer_slashing` (Block/Slashings.lean) | `process_proposer_slashing` | no | no | same |
| `process_attester_slashing` (Block/Slashings.lean) | `process_attester_slashing` | no | no | same |
| `process_sync_aggregate_loop` (Block/SyncAggregate.lean) | `process_sync_aggregate` (loop) | no | no | hand: (state, participant_reward, proposer_reward); readable: (state, sync_aggregate) |
| `process_sync_aggregate` (Block/SyncAggregate.lean) | `process_sync_aggregate` | no | no | same |
| `is_fully_withdrawable_validator` (Block/Withdrawals.lean) | `is_fully_withdrawable_validator` | yes | yes | same |
| `is_partially_withdrawable_validator` (Block/Withdrawals.lean) | `is_partially_withdrawable_validator` | yes | yes | same |
| `is_eligible_for_partial_withdrawals` (Block/Withdrawals.lean) | `is_eligible_for_partial_withdrawals` | yes | yes | same |
| `is_builder_index` (Block/Withdrawals.lean) | `is_builder_index` | yes | yes | same |
| `convert_builder_index_to_validator_index` (Block/Withdrawals.lean) | `convert_builder_index_to_validator_index` | yes | yes | same |
| `get_balance_after_withdrawals` (Block/Withdrawals.lean) | `get_balance_after_withdrawals` | yes | no | same |
| `get_builder_withdrawals_loop` (Block/Withdrawals.lean) | `get_builder_withdrawals` (loop) | no | no | hand: (prior_withdrawals, withdrawals_limit); readable: (state, withdrawal_index, prior_withdrawals) |
| `get_builder_withdrawals` (Block/Withdrawals.lean) | `get_builder_withdrawals` | no | no | same |
| `get_pending_partial_withdrawals_loop` (Block/Withdrawals.lean) | `get_pending_partial_withdrawals` (loop) | no | no | hand: (state, epoch, prior_withdrawals, withdrawals_limit); readable: (state, withdrawal_index, prior_withdrawals) |
| `get_pending_partial_withdrawals` (Block/Withdrawals.lean) | `get_pending_partial_withdrawals` | no | no | same |
| `get_builders_sweep_withdrawals_loop` (Block/Withdrawals.lean) | `get_builders_sweep_withdrawals` (loop) | no | no | hand: (state, epoch, prior_withdrawals, withdrawals_limit); readable: (state, withdrawal_index, prior_withdrawals) |
| `get_builders_sweep_withdrawals` (Block/Withdrawals.lean) | `get_builders_sweep_withdrawals` | no | no | same |
| `get_validators_sweep_withdrawals_loop` (Block/Withdrawals.lean) | `get_validators_sweep_withdrawals` (loop) | no | no | hand: (state, epoch, prior_withdrawals, withdrawals_limit); readable: (state, withdrawal_index, prior_withdrawals) |
| `get_validators_sweep_withdrawals` (Block/Withdrawals.lean) | `get_validators_sweep_withdrawals` | no | no | same |
| `get_expected_withdrawals` (Block/Withdrawals.lean) | `get_expected_withdrawals` | no | no | same |
| `apply_withdrawals` (Block/Withdrawals.lean) | `apply_withdrawals` | no | no | same (the hand version recurses on `withdrawals`) |
| `update_next_withdrawal_index` (Block/Withdrawals.lean) | `update_next_withdrawal_index` | yes | yes | same |
| `update_payload_expected_withdrawals` (Block/Withdrawals.lean) | `update_payload_expected_withdrawals` | no | no | same |
| `update_builder_pending_withdrawals` (Block/Withdrawals.lean) | `update_builder_pending_withdrawals` | yes | no | same |
| `update_pending_partial_withdrawals` (Block/Withdrawals.lean) | `update_pending_partial_withdrawals` | yes | no | same |
| `update_next_withdrawal_builder_index` (Block/Withdrawals.lean) | `update_next_withdrawal_builder_index` | yes | yes | same |
| `update_next_withdrawal_validator_index` (Block/Withdrawals.lean) | `update_next_withdrawal_validator_index` | yes | no | same |
| `process_withdrawals` (Block/Withdrawals.lean) | `process_withdrawals` | no | no | same |
| `get_builder_payment_quorum_threshold` (BuilderPendingPayments.lean) | `get_builder_payment_quorum_threshold` | yes | no | hand: (total_active_balance); readable: (state) |
| `process_builder_pending_payments` (BuilderPendingPayments.lean) | `process_builder_pending_payments` | no | no | hand: (total_active_balance, state); readable: (state) |
| `get_max_effective_balance` (EffectiveBalanceUpdates.lean) | `get_max_effective_balance` | yes | yes | same |
| `process_effective_balance_updates` (EffectiveBalanceUpdates.lean) | `process_effective_balance_updates` | yes | no | same |
| `get_index_for_new_validator` (Epoch.lean) | `get_index_for_new_validator` | yes | yes | same |
| `get_validator_from_deposit` (Epoch.lean) | `get_validator_from_deposit` | yes | no | same |
| `add_validator_to_registry` (Epoch.lean) | `add_validator_to_registry` | no | no | same |
| `is_valid_deposit_signature` (Epoch.lean) | `is_valid_deposit_signature` | no | yes | same |
| `apply_pending_deposit` (Epoch.lean) | `apply_pending_deposit` | no | no | same |
| `process_epoch` (Epoch.lean) | `process_epoch` | no | no | same |
| `process_sync_committee_updates` (EpochCommittees.lean) | `process_sync_committee_updates` | no | no | same |
| `process_proposer_lookahead` (EpochCommittees.lean) | `process_proposer_lookahead` | no | no | same |
| `process_ptc_window` (EpochCommittees.lean) | `process_ptc_window` | no | no | same |
| `process_eth1_data_reset` (EpochRest.lean) | `process_eth1_data_reset` | yes | no | same |
| `process_slashings_reset` (EpochRest.lean) | `process_slashings_reset` | yes | yes | same |
| `process_randao_mixes_reset` (EpochRest.lean) | `process_randao_mixes_reset` | yes | yes | same |
| `process_historical_summaries_update` (EpochRest.lean) | `process_historical_summaries_update` | no | no | same |
| `process_participation_flag_updates` (EpochRest.lean) | `process_participation_flag_updates` | no | no | same |
| `compute_epoch_at_slot` (InactivityUpdates.lean) | `compute_epoch_at_slot` | yes | yes | same |
| `get_current_epoch` (InactivityUpdates.lean) | `get_current_epoch` | yes | yes | same |
| `saturating_sub` (InactivityUpdates.lean) | `saturating_sub` | yes | yes | same |
| `get_previous_epoch` (InactivityUpdates.lean) | `get_previous_epoch` | yes | yes | same |
| `is_active_validator` (InactivityUpdates.lean) | `is_active_validator` | yes | yes | same |
| `get_active_validator_indices` (InactivityUpdates.lean) | `get_active_validator_indices` | yes | yes | same |
| `get_finality_delay` (InactivityUpdates.lean) | `get_finality_delay` | yes | yes | same |
| `is_in_inactivity_leak` (InactivityUpdates.lean) | `is_in_inactivity_leak` | yes | yes | same |
| `get_eligible_validator_indices` (InactivityUpdates.lean) | `get_eligible_validator_indices` | yes | yes | same |
| `has_flag` (InactivityUpdates.lean) | `has_flag` | yes | yes | same |
| `get_unslashed_participating_indices` (InactivityUpdates.lean) | `get_unslashed_participating_indices` | no | no | same |
| `process_inactivity_updates` (InactivityUpdates.lean) | `process_inactivity_updates` | no | no | same |
| `weigh_justification_and_finalization` (JustificationFinalization.lean) | `weigh_justification_and_finalization` | no | no | same |
| `process_justification_and_finalization` (JustificationFinalization.lean) | `process_justification_and_finalization` | no | no | same |
| `process_pending_consolidations` (PendingConsolidations.lean) | `process_pending_consolidations` | no | no | same |
| `compute_start_slot_at_epoch` (PendingDeposits.lean) | `compute_start_slot_at_epoch` | yes | yes | same |
| `get_activation_churn_limit` (PendingDeposits.lean) | `get_activation_churn_limit` | yes | no | hand: (total_active_balance); readable: (state) |
| `process_pending_deposits` (PendingDeposits.lean) | `process_pending_deposits` | no | no | hand: (total_active_balance, apply_pending_deposit, state); readable: (state) |
| `compute_activation_exit_epoch` (RegistryUpdates.lean) | `compute_activation_exit_epoch` | yes | yes | same |
| `get_exit_churn_limit` (RegistryUpdates.lean) | `get_exit_churn_limit` | yes | no | hand: (total_active_balance); readable: (state) |
| `compute_exit_epoch_and_update_churn` (RegistryUpdates.lean) | `compute_exit_epoch_and_update_churn` | no | no | hand: (total_active_balance, state, exit_balance); readable: (state, exit_balance) |
| `initiate_validator_exit` (RegistryUpdates.lean) | `initiate_validator_exit` | no | no | hand: (total_active_balance, state, index); readable: (state, index) |
| `is_eligible_for_activation_queue` (RegistryUpdates.lean) | `is_eligible_for_activation_queue` | yes | yes | same |
| `is_eligible_for_activation` (RegistryUpdates.lean) | `is_eligible_for_activation` | yes | yes | same |
| `process_registry_updates` (RegistryUpdates.lean) | `process_registry_updates` | no | no | hand: (total_active_balance, state); readable: (state) |
| `integer_squareroot` (RewardsAndPenalties.lean) | `integer_squareroot` | yes | no | same |
| `get_base_reward_per_increment` (RewardsAndPenalties.lean) | `get_base_reward_per_increment` | no | no | hand: (total_active_balance); readable: (state) |
| `get_base_reward` (RewardsAndPenalties.lean) | `get_base_reward` | no | no | hand: (total_active_balance, state, index); readable: (state, index) |
| `get_total_balance` (RewardsAndPenalties.lean) | `get_total_balance` | yes | yes | same |
| `increase_balance` (RewardsAndPenalties.lean) | `increase_balance` | yes | yes | hand: (balances, index, delta); readable: (state, index, delta) |
| `get_flag_index_deltas` (RewardsAndPenalties.lean) | `get_flag_index_deltas` | no | no | hand: (total_active_balance, state, flag_index); readable: (state, flag_index) |
| `get_inactivity_penalty_deltas` (RewardsAndPenalties.lean) | `get_inactivity_penalty_deltas` | no | no | same |
| `process_rewards_and_penalties` (RewardsAndPenalties.lean) | `process_rewards_and_penalties` | no | no | hand: (total_active_balance, state); readable: (state) |
| `decrease_balance` (Slashings.lean) | `decrease_balance` | yes | yes | hand: (balances, index, delta); readable: (state, index, delta) |
| `process_slashings` (Slashings.lean) | `process_slashings` | no | no | hand: (total_active_balance, state); readable: (state) |
| `process_slot` (Slots.lean) | `process_slot` | no | no | same |
| `process_slots_loop` (Slots.lean) | `process_slots` (loop) | no | no | hand: (processEpoch, slot); readable: (state, slot) |
| `process_slots` (Slots.lean) | `process_slots` | no | no | hand: (processEpoch, state, slot); readable: (state, slot) |
| `get_total_active_balance` (TotalActiveBalance.lean) | `get_total_active_balance` | yes | no | same |

## 2. Differences between the two models

### Spec version

The hand spec says v1.7.0-beta.2 (`5afdff6288`). Pythia pins `889a389f9`. That commit is 31
commits after v1.7.0-beta.2 and it does not contain v1.7.0-beta.3. In `specs/*/beacon-chain.md`,
the changes in that range that touch the functions in the table are these:

- `get_finality_delay` returns `Epoch` and drops the `Uint64(...)` cast. The value is the same.
  The subtraction raises in both versions when it goes below zero.
- `get_builder_payment_quorum_threshold` returns `Gwei` and drops the `Uint64(...)` cast. The
  value is the same.
- The other changes are type spellings (`Tuple` to `tuple`, `Optional[X]` to `X | None`), quote
  styles, prose, and `compute_time_at_slot(genesis_time, slot)`. No function in the table calls
  `compute_time_at_slot`.

So the two pins agree on every function in the table, up to the class of two return values.

### Types

| | Hand | Readable |
|---|---|---|
| uint classes (`Gwei`, `Epoch`, `Slot`, ...) | `abbrev Gwei := Nat`. All classes are the same type. | One structure per class: `structure Gwei where val : Nat`, with `UintC` (width and value). |
| range | No bound in the type. `uint64Add` and the others check `< 2 ^ 64`. | No bound in the type. `uOf` checks the range at each operation and each cast. |
| `ParticipationFlags` | `UInt8` | structure over `Nat`, width 8 |
| byte vectors | `Vector UInt8 n` (length in the type) | structure over `List UInt8`, with `BytesC.len` |
| SSZ booleans | `Bool` | `Boolean` (structure over `Bool`) |
| SSZ lists and vectors | `List`. `VectorLengths p` gives the vector lengths. | `List`. The SSZ decoder gives the lengths. |
| containers | Lean structures, spec field names and spec order. | The same. |

Field names are the same in both models: both use the spec names. `Validator` has all 8 fields
in both. `BeaconState` has all 46 Gloas fields in both. The hand fields have defaults (empty
lists for vectors). The readable `Inhabited` default uses the SSZ default (full-length vectors).

### Errors

Hand: `SpecM := Except SpecError`, with `overflow`, `divisionByZero`, `indexOutOfRange` and
`assertionFailed`. Readable: `SpecM := Except Fail`, with `invalid` (the input is invalid:
`assert` or `IndexError`) and `bug` (any other exception). The map is `errClass` in the
prototype: `indexOutOfRange` and `assertionFailed` go to `invalid`, `overflow` and
`divisionByZero` go to `bug`. The hand class is finer, so each bridge theorem is
`readable = (hand).mapError errClass`.

The readable Lean raises at the same Python line as pyspec (SPEC 4.2, and the alias order fix on
`fixes`). The hand spec is a line-by-line transcription, so it mostly raises at the same line.
Where it does not, the error class can differ. Example: the hand `decrease_balance` takes the
balances list, so it cannot fail on a bad `state` field. Each bridge theorem finds such cases.

### Preset and configuration

Hand: one `Preset` structure as a parameter `p`. It holds preset values and configuration
values (for example `CHURN_LIMIT_QUOTIENT_GLOAS` and `GENESIS_FORK_VERSION`), with mainnet
defaults and `Preset.minimal`. Readable: preset values are constants in the generated file
(`SLOTS_PER_EPOCH : Slot := ⟨8⟩`, minimal only). Configuration values are fields of the class
`Cfg`. A readable mainnet file does not exist yet (`ScopeMainnet.lean` does, so
`translate.py` needs a `--preset mainnet` run). The bridge needs a `Cfg` instance that matches
`p`, and one bridge per preset.

### Oracle

Hand: `Oracle` structure, passed as `o`. It has `hash : List UInt8 → Bytes32`, one
`hash_tree_root_T : T → Root` per type, and `bls_*` functions on the hand types. Readable: the
class `Spec`, with `sha256 : Bytes → Bytes`, one `hashTreeRoot` on encoded values (`Heap →
Value → Res Bytes`), the SSZ tables, and BLS on byte lists (`blsG1Add` and `blsG1Neg` in place
of `bls_SubtractPK`). The bridge builds a hand oracle from `Spec`:
`hash_tree_root_T x := htr (enc_T (toRd x))`, and `hash := sha256` with the length fact from
`OracleHtr.sha256`. Then a hand theorem for every oracle holds for this one.

### Parameter shapes

29 hand functions take other parameters than the spec. These are the patterns:

- `total_active_balance` is a parameter in 14 functions (the reference hoists it). The readable
  function calls `get_total_active_balance state`. The bridge theorem takes
  `total_active_balance = get_total_active_balance state` as a hypothesis.
- `decrease_balance` and `increase_balance` take `balances`, not `state`. The bridge maps
  `state.balances` and proves that the other fields do not change.
- `GLOAS_FORK_EPOCH` and `max_blobs_per_block` are parameters (configuration in the readable
  Lean).
- `process_pending_deposits` takes `apply_pending_deposit` as a function parameter, and
  `process_slots` takes `processEpoch`. The bridge passes the hand functions in.
- The 7 `_loop` helpers are explicit recursions. The readable loops are `f.loopN` functions over
  an index. Each pair needs a loop lemma.

## 3. Plan for the bridge

Goal: for each function in the table, a theorem

```lean
theorem f_eq (args : readable types) (hr : InRange args) :
    Gen.f args = ((Hand.f p (abs args)).mapError errClass).map abs
```

where `abs` maps a readable value to a hand value. Then each Lighthouse theorem `lighthouse = Hand.f`
becomes `lighthouse = Gen.f` by rewriting with `f_eq`. The readable functions are equal to the
interpreter (tactic and layer 4 proofs), and the interpreter is tested against pyspec. So the
chain is Lighthouse = hand = readable = interpreter = pyspec.

Steps:

1. Translation of types (generated). A new `tools/gen_bridge.py` reads the same type table as
   `rd_types.py` and writes `abs_T : Gen.T → Hand.T` for each container (uint: `.val`; bytes:
   `Vector.ofFn` with the length from `BytesC.len`; `Boolean`: `.val`; lists: `List.map`). It also
   writes `toRd_T` the other way and `InRange_T` (each uint below `2 ^ bits`, each byte vector of
   the right length). The two maps are inverse on values in range. Direction: `abs` from
   readable to hand is total on values in range, so the theorems use it.
2. Shared lemmas (hand-written, once). `uOf_ok`, `lget_ok`/`lget_err`, `lset_ok`, `fdiv_nat`, and
   one lemma per `uint64X` that says `uOp .x` equals it under `errClass`. The prototype has the
   first four.
3. Statements (generated). One `f_eq` statement per row of the table, with the parameter
   adapters of section 2 for the 29 functions with other shapes.
4. Proofs. Functions with no loop of their own (83 of the 106): generated, with a tactic that
   rewrites callees with their `f_eq` and the prelude lemmas, in call order. This is the same
   approach as `rd_call` in `Validation/Tactic.lean`. Functions with a loop (23): a loop lemma
   that pairs `Gen.f.loopN` with the hand `_loop` or `foldlM`, written once and then
   instantiated, as the generic loop lemmas in `Validation/Loop*.lean` do for the interpreter.
   The big functions (`process_epoch`, `process_block`, `process_withdrawals`, the operations)
   only compose the callee theorems.
5. Order. Leaves first (`compute_epoch_at_slot`, `saturating_sub`, `is_active_validator`, the
   credential checks), then the epoch sub-functions that have `Equiv/*` theorems
   (`process_effective_balance_updates`, `process_slashings`, `process_inactivity_updates`,
   `process_rewards_and_penalties`, `process_registry_updates`, `process_pending_deposits`,
   `process_pending_consolidations`, `process_builder_pending_payments`), then `process_epoch`.
6. After the bridge: restate the `Equiv/*` theorems on `Gen.f`, then remove `EpochProofs/Spec`
   from the Lighthouse proofs.

What can be generated: `abs`, `toRd`, `InRange`, all statements, and the proofs of the
functions with no loop. What is hand-written: the shared lemmas, the loop lemmas, the 29
parameter adapters, and the oracle construction.

Preset: the plan above is for minimal. The Lighthouse theorems take any `p`. For mainnet, the
bridge needs a mainnet readable file and the same theorems again. The generator can write both.

## 4. Prototype

`Bridge/Bridge/Prototype.lean` proves two equalities, with no `sorry` (axioms: `propext`,
`Quot.sound`, and `Classical.choice` for the second):

```lean
theorem decrease_balance_eq (r : Gen.BeaconState) (i d : Nat)
    (hb : ∀ b ∈ r.balances, b.val < 2 ^ 64) :
    Gen.decrease_balance r ⟨i⟩ ⟨d⟩ =
      ((EpochProofs.Spec.decrease_balance (r.balances.map (·.val)) i d).mapError errClass).map
        fun bs => { r with balances := bs.map Gen.Gwei.mk }

theorem get_current_epoch_eq (s : EpochProofs.Spec.BeaconState) (r : Gen.BeaconState)
    (hslot : r.slot.val = s.slot) (hs : s.slot < 2 ^ 64) :
    (Gen.get_current_epoch r).map (·.val) =
      (EpochProofs.Spec.get_current_epoch Hand s).mapError errClass
```

`decrease_balance_eq` covers both cases: index in range (the same new state) and index out of
range (`invalid` on both sides). The hypothesis `hb` is the `InRange` condition: a balance at or
above `2 ^ 64` makes the readable subtraction a `bug`, but the hand subtraction succeeds.

### How the import works

`Bridge/` is a separate Lake project in the Pythia repo:

- `require ConsensusSpecsLean` with `path = ".."`. Lake builds Pythia in place, in `../.lake`, and
  reuses the oleans that are there.
- A `lean_lib` named `EpochSpec` with `srcDir` set to the Lighthouse proofs directory and
  `globs = ["EpochProofs.Spec.+"]`. Lake compiles the hand spec from its source into
  `Bridge/.lake`. The Lighthouse lakefile requires Aeneas and Mathlib, but `EpochProofs/Spec/*`
  imports only core Lean, so the bridge does not need those packages. Nothing in the Lighthouse
  repo changes.
- The path assumes that `pythia` and `lighthouse-epoch-proofs` are sibling directories. Both
  use Lean v4.31.0.

Build: `cd Bridge && lake build` (under the usual 8 GB cap). The other direction (the Lighthouse
project requires Pythia by path) also works, because Pythia has no dependencies. The Lighthouse
proofs will need that direction in step 6.6.

### Notes from the prototype

- `simp` with `bind` and `Except.bind` closed the goal, but the kernel then failed with "deep
  recursion". Rewriting one bind at a time with `rfl` lemmas (`ok_bind`, `err_bind`,
  `mapError_ok`) avoids it. The generated proofs must use this style.
- `uOf_ok` takes `UintC.bits α = 64` as a separate hypothesis. A bound stated as
  `n < 2 ^ UintC.bits α` made the same kernel failure.
- `simp` rewrites `↑(n / 8)` to `↑n / 8` and `Int.fdiv` to `/`. Lemmas stated on the
  cast form (`fdiv_nat`) must be applied with `rw` before `simp` runs.

## 5. The bridge generator

`tools/gen_bridge.py` writes three files in `Bridge/Bridge/Gen/`:

- `Types.lean`: `abs_T` (readable to hand) and `IR_T` (each uint below `2 ^ bits`, each byte
  vector of its length, each list shorter than `2 ^ 64`) for the 46 containers in both models.
  It also writes one `decide` check per constant and configuration value that both models define.
- `Specs.lean`: one statement `spec_f` per function with the same parameters in both models
  (85: 60 mapped functions and 25 of their callees). The statement is
  `SimI P abs (Gen.f x) (Hand.f p (abs x))` under `IR` hypotheses: the same result up to `abs`
  or errors of the same class, and the readable result in range (`P`).
- `Eqs.lean`: `cond_f`, the proof of `spec_f` with the callee statements as hypotheses, and
  `full_f`, the same proof with the callee hypotheses discharged.

`tools/bridge_trials.py` runs one trial per function and lists the proofs that pass. Only those go
into `Eqs.lean`. The proofs use `bridge_main` (`Bridge/Bridge/Tactic.lean`). It steps through both
`do` blocks one bind at a time with the lemmas of `Sim.lean` and `Lists.lean`, and never unfolds
`bind` with `simp`.

Status on mainnet, the target preset (`GenMainnet/Eqs.lean` lists the names):

| | Count |
|---|---|
| Mapped functions without a loop | 83 |
| with a statement | 74 |
| proved, conditional | 47 (and 31 callees) |
| proved, full | 46 (and 27 callees) |
| loops proved by hand (`Mainnet/Proofs.lean`) | 3 of the 23 mapped loops, and 3 callee loops |
| loops proved by `bridge_loop` (generated) | 1 (`process_inactivity_updates`, conditional) |

`bridge_main` has these steps in addition to the steps for binds, `if` and leaves:

- Oracle: `sha256` and `hash_tree_root` then `bytesOf` against the hand oracle, the BLS calls
  rewritten with `OracleAgrees`, and an `obtain` of the root for each SSZ object argument.
- Callees: the callee theorem `h_f` only for a call to `f`. Other callee theorems make the
  unifier unfold large definitions. When the hand arguments are equal only after a rewrite, the
  step uses `sim_hand_eq` and closes the equation with `bridge_eqv` (the value facts of the
  context, then the constants).
- Parameter adapter: the hand functions that take `total_active_balance` get a statement with
  the hand value and the hypothesis `get_total_active_balance … = .ok total_active_balance`
  (`sim_of_ok`).
- Lists: `filterMapM` over `enumerate` (`sim_filterMapM_zipIdx`, `post_filterMapM_ir`), `dedup`
  of a list with no duplicates, `contains` and `lindex` on lists of byte values, `xs[-1]`.
- Range facts: `lset` keeps the item facts of a list, `sumU`, `max` and `min` results, and
  `IR_T` of a structure value with one goal per field.
- Each `bridge_close` alternative has its own heartbeat budget (`bridge.closeHeartbeats`).

Functions with a loop get hand-written proofs in `Bridge/Bridge/Mainnet/Proofs.lean`, one
theorem `hand_f : spec_f` each. The generator reads the names and adds `full_f := hand_f` to
`Eqs.lean`. A hand proof can take callee statements as hypotheses (`(h_g : spec_g)`), as the
generated proofs do.

### Shapes of the hand proofs

`Bridge/Bridge/Loops.lean` has one generic lemma per shape. A hand proof gives only the parts
that are not the same for all functions of its shape.

| Shape | Generic lemma | Hand proofs |
|---|---|---|
| (a) index loop against `forIn`, with an invariant | `sim_loop`, `sim_loop0` | `process_slashings` (`slash_step`), `process_effective_balance_updates` (`ebu_step`) |
| (b) index loop that adds amounts | `sum_loop` | `get_pending_balance_to_withdraw`, `get_pending_balance_to_withdraw_for_builder` |
| (c) `range` comprehension | `pyRange_nat`, `pyRange_zero`, `sim_mapM_range`, `mapM_const_ok` | `process_participation_flag_updates` |
| (d) filter comprehension against a hand `filter` or `for` loop | `forIn_append`, `sim_filterMapM_gen` | `get_eligible_validator_indices`, `get_set_bit_count`, `get_balance_after_withdrawals` |
| (e) search loop with an early `return` | `sim_loop` (`.done` step) | `get_index_for_new_builder` (`nb_loop`, not converted yet) |

`sim_loop` relates the readable loop `L i c` to the hand loop `forIn (items.drop i) r B`, then
`K`. The caller gives an invariant `Inv i c r` on the readable loop variables `c` and the hand
accumulator `r`, one loop step, and the end of the loop. The lemma does the recursion on `i`,
the list split at `i`, and the termination proof. The epoch loops use two invariants:

- One list field `F` of the state changes in place on both sides: the readable state is
  `{ st0 with F := X }` and `r = X.map conv` (`process_slashings`, and next
  `process_inactivity_updates`).
- The hand loop builds a new list and the readable loop sets item `i`: the readable state is
  `{ st0 with F := P ++ st0.F.drop i }` with `P.length = i`, and `r = P.map conv`
  (`process_effective_balance_updates`). `lget_split` and `lset_split` read and write item `i`.

The generator writes the proofs of the loops of the first shape (`loop_shape` and `loop_proof` in
`tools/gen_bridge.py`). It reads the shape from the hand source: one `for` loop,
`let mut F := state.F`, then `pure { state with F }`. The proof is the same for each function:

1. `bridge_walk` walks the code before the loop and keeps the loop goal.
2. `bridge_loop (Inv)` reads the readable loop call (the parameter `i_`, the bound before it, the
   loop variables after it) and applies `sim_loopvₖ` for `k` loop variables. The goals left are
   `hn`, `init`, `fin` and `step`.
3. In `step`, `bridge_item` replaces the hand item by item `i` of the readable list. Then
   `bridge_run` walks one loop body. At the recursive call it applies the claim `ih` for step
   `i + 1` and closes the invariant with `bridge_inv`.

`bridge_run` has three steps for loop bodies:

- A callee on a state `{ s with F := X }` gets the state `s` if the callee does not read `F`
  (`sim_bind_eq_l`). The check is `rfl`: it fails for a callee that reads `F`. So no lemma per
  callee is necessary. The hand loop calls its callees on the old state, so this step makes both
  sides call them on the same state.
- A bind whose first step is a bind or an `if` is put in order first (`sim_assoc_r`,
  `sim_ite_bind_r`, and the same on the readable side). The hand loop body has this form,
  because it is followed by the rest of the loop.
- A readable `contains` on a list of uints against the hand `∈` (`contains_iff_mem_val`), and a
  fact `a = c` of the context for a goal `a = b` (`bridge_rw_fact`).

`process_inactivity_updates` has a generated proof. `process_slashings` has the same shape, but
its body calls `decrease_balance`, whose hand version takes the balances and not the state. Its
proof is still `slash_step`. `process_effective_balance_updates` (a new list, not a field
changed in place) is still `ebu_step`.

Hand proofs with an odd shape, kept as they are:

- `integer_squareroot`: a Newton recursion on `x`, not an index loop. The proof keeps
  `x ≤ n` and `1 ≤ y`, so the division and the addition in the loop cannot fail.
- `get_block_root_at_slot`: one readable `assert` of a chained comparison
  (`slot < state.slot <= slot + SLOTS_PER_HISTORICAL_ROOT`) against two hand checks.
- `xor`: a byte-wise `zip` of two `Bytes32` values against `Vector.zipWith`.

Not proved yet, by cause (examples):

- Functions that return a tuple: the post condition is `True`, so the caller has no range facts
  for the state in the tuple (`initiate_validator_exit`).
- Block functions with more steps: `process_withdrawal_request`, `process_consolidation_request`,
  `process_builder_exit_request`, `process_voluntary_exit`, `process_randao`, `process_slot`.

The hand spec has the mainnet value of four minimal-preset values:
`PENDING_CONSOLIDATIONS_LIMIT`, `PENDING_PARTIAL_WITHDRAWALS_LIMIT`,
`CONSOLIDATION_CHURN_LIMIT_QUOTIENT` and `MIN_BUILDER_WITHDRAWABILITY_DELAY` (the `decide`
checks fail for them). So on the minimal preset, the hand `process_withdrawal_request`,
`process_consolidation_request`, `get_consolidation_churn_limit` and `initiate_builder_exit` differ
from the spec. They are correct on mainnet.

Left for later:

- 20 of the 23 functions with a loop: `apply_parent_execution_payload`, `apply_withdrawals`,
  `get_builders_sweep_withdrawals`, `get_builder_withdrawals`, `get_flag_index_deltas`,
  `get_inactivity_penalty_deltas`, `get_pending_partial_withdrawals`,
  `get_validators_sweep_withdrawals`, `process_attestation`,
  `process_attester_slashing`, `process_builder_pending_payments`,
  `process_inactivity_updates`, `process_operations`,
  `process_pending_consolidations`, `process_pending_deposits`, `process_proposer_slashing`,
  `process_registry_updates`, `process_rewards_and_penalties`,
  `process_slots`, `process_sync_aggregate`. Those with a statement are hypotheses of their callers.
- The 29 parameter adapters (hand functions): `process_attestation_loop`,
  `process_payload_attestation`, `process_operations`, `process_block`, `state_transition`,
  `compute_consolidation_epoch_and_update_churn`, `process_execution_payload_bid`,
  `process_sync_aggregate_loop`, `get_builder_withdrawals_loop`,
  `get_pending_partial_withdrawals_loop`, `get_builders_sweep_withdrawals_loop`,
  `get_validators_sweep_withdrawals_loop`, `get_builder_payment_quorum_threshold`,
  `process_builder_pending_payments`, `get_activation_churn_limit`, `process_pending_deposits`,
  `get_exit_churn_limit`, `compute_exit_epoch_and_update_churn`, `initiate_validator_exit`,
  `process_registry_updates`, `get_base_reward_per_increment`, `get_base_reward`,
  `increase_balance`, `get_flag_index_deltas`, `process_rewards_and_penalties`,
  `decrease_balance`, `process_slashings`, `process_slots_loop`, `process_slots`.

To regenerate: `python3 tools/gen_bridge.py --trials DIR`, then
`python3 tools/bridge_trials.py DIR` (3 runners, 6 GB each), then
`python3 tools/gen_bridge.py --proved DIR/proved.txt`, then `cd Bridge && lake build`.
