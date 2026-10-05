FP BeaconBlock.body.attestations
FP BeaconBlock.body.attester_slashings
FP BeaconBlock.body.bls_to_execution_changes
FP BeaconBlock.body.deposits
FP BeaconBlock.body.parent_execution_requests.builder_deposits
FP BeaconBlock.body.parent_execution_requests.builder_exits
FP BeaconBlock.body.parent_execution_requests.consolidations
FP BeaconBlock.body.parent_execution_requests.deposits
FP BeaconBlock.body.parent_execution_requests.withdrawals
FP BeaconBlock.body.payload_attestations
FP BeaconBlock.body.proposer_slashings
FP BeaconBlock.body.voluntary_exits
FP BeaconBlockBody.attestations
FP BeaconBlockBody.attester_slashings
FP BeaconBlockBody.bls_to_execution_changes
FP BeaconBlockBody.deposits
FP BeaconBlockBody.payload_attestations
FP BeaconBlockBody.proposer_slashings
FP BeaconBlockBody.voluntary_exits
FP BeaconState
FP BeaconState.balances
FP BeaconState.block_roots
FP BeaconState.builder_pending_payments
FP BeaconState.builder_pending_payments.*
FP BeaconState.builder_pending_withdrawals
FP BeaconState.builders
FP BeaconState.builders.*
FP BeaconState.current_epoch_participation
FP BeaconState.eth1_data_votes
FP BeaconState.execution_payload_availability
FP BeaconState.historical_summaries
FP BeaconState.inactivity_scores
FP BeaconState.justification_bits
FP BeaconState.latest_block_header
FP BeaconState.pending_consolidations
FP BeaconState.pending_deposits
FP BeaconState.pending_partial_withdrawals
FP BeaconState.previous_epoch_participation
FP BeaconState.proposer_lookahead
FP BeaconState.ptc_window
FP BeaconState.randao_mixes
FP BeaconState.slashings
FP BeaconState.state_roots
FP BeaconState.validators
FP BeaconState.validators.*
FP ExecutionRequests.builder_deposits
FP ExecutionRequests.builder_exits
FP ExecutionRequests.consolidations
FP ExecutionRequests.deposits
FP ExecutionRequests.withdrawals
FP PendingDeposits
FP SignedBeaconBlock.message.body.attestations
FP SignedBeaconBlock.message.body.attester_slashings
FP SignedBeaconBlock.message.body.bls_to_execution_changes
FP SignedBeaconBlock.message.body.deposits
FP SignedBeaconBlock.message.body.parent_execution_requests.builder_deposits
FP SignedBeaconBlock.message.body.parent_execution_requests.builder_exits
FP SignedBeaconBlock.message.body.parent_execution_requests.consolidations
FP SignedBeaconBlock.message.body.parent_execution_requests.deposits
FP SignedBeaconBlock.message.body.parent_execution_requests.withdrawals
FP SignedBeaconBlock.message.body.payload_attestations
FP SignedBeaconBlock.message.body.proposer_slashings
FP SignedBeaconBlock.message.body.voluntary_exits
FP Validator
WRITE apply_parent_execution_payload:specs/gloas/beacon-chain.md:1779 BeaconState.builder_pending_withdrawals
WRITE apply_parent_execution_payload:specs/gloas/beacon-chain.md:1788 BeaconState.execution_payload_availability
WRITE apply_parent_execution_payload:specs/gloas/beacon-chain.md:1789 BeaconState
WRITE apply_withdrawals:specs/gloas/beacon-chain.md:1943 BeaconState.builders.*
WRITE compute_consolidation_epoch_and_update_churn:specs/electra/beacon-chain.md:969 BeaconState
WRITE compute_consolidation_epoch_and_update_churn:specs/electra/beacon-chain.md:972 BeaconState
WRITE compute_exit_epoch_and_update_churn:specs/gloas/beacon-chain.md:1513 BeaconState
WRITE compute_exit_epoch_and_update_churn:specs/gloas/beacon-chain.md:1514 BeaconState
WRITE decrease_balance:specs/phase0/beacon-chain.md:1657 BeaconState.balances
WRITE get_validator_from_deposit:specs/electra/beacon-chain.md:1723 Validator
WRITE increase_balance:specs/phase0/beacon-chain.md:1647 BeaconState.balances
WRITE initiate_builder_exit:specs/gloas/beacon-chain.md:1530 BeaconState.builders.*
WRITE initiate_validator_exit:specs/electra/beacon-chain.md:880 BeaconState.validators.*
WRITE initiate_validator_exit:specs/electra/beacon-chain.md:881 BeaconState.validators.*
WRITE onboard_builders_from_pending_deposits:specs/gloas/fork.md:81 PendingDeposits
WRITE onboard_builders_from_pending_deposits:specs/gloas/fork.md:94 PendingDeposits
WRITE onboard_builders_from_pending_deposits:specs/gloas/fork.md:97 PendingDeposits
WRITE onboard_builders_from_pending_deposits:specs/gloas/fork.md:117 BeaconState.builders.*
WRITE onboard_builders_from_pending_deposits:specs/gloas/fork.md:119 BeaconState
WRITE process_attestation:specs/gloas/beacon-chain.md:2395 BeaconState.current_epoch_participation
WRITE process_attestation:specs/gloas/beacon-chain.md:2395 BeaconState.previous_epoch_participation
WRITE process_attestation:specs/gloas/beacon-chain.md:2407 BeaconState.builder_pending_payments.*
WRITE process_attestation:specs/gloas/beacon-chain.md:2419 BeaconState.builder_pending_payments
WRITE process_attestation:specs/gloas/beacon-chain.md:2421 BeaconState.builder_pending_payments
WRITE process_block_header:specs/phase0/beacon-chain.md:2337 BeaconState
WRITE process_bls_to_execution_change:specs/capella/beacon-chain.md:638 BeaconState.validators.*
WRITE process_builder_deposit_request:specs/gloas/beacon-chain.md:2298 BeaconState.builders.*
WRITE process_builder_deposit_request:specs/gloas/beacon-chain.md:2301 BeaconState.builders.*
WRITE process_builder_pending_payments:specs/gloas/beacon-chain.md:1686 BeaconState.builder_pending_withdrawals
WRITE process_builder_pending_payments:specs/gloas/beacon-chain.md:1689 BeaconState.builder_pending_payments
WRITE process_builder_pending_payments:specs/gloas/beacon-chain.md:1691 BeaconState.builder_pending_payments
WRITE process_consolidation_request:specs/electra/beacon-chain.md:2064 BeaconState.validators.*
WRITE process_consolidation_request:specs/electra/beacon-chain.md:2067 BeaconState.validators.*
WRITE process_consolidation_request:specs/electra/beacon-chain.md:2070 BeaconState.pending_consolidations
WRITE process_deposit_request:specs/fulu/beacon-chain.md:207 BeaconState.pending_deposits
WRITE process_effective_balance_updates:specs/electra/beacon-chain.md:1252 BeaconState.validators.*
WRITE process_eth1_data:specs/phase0/beacon-chain.md:2368 BeaconState.eth1_data_votes
WRITE process_eth1_data:specs/phase0/beacon-chain.md:2373 BeaconState
WRITE process_eth1_data_reset:specs/phase0/beacon-chain.md:2249 BeaconState
WRITE process_execution_payload_bid:specs/gloas/beacon-chain.md:2151 BeaconState.builder_pending_payments
WRITE process_execution_payload_bid:specs/gloas/beacon-chain.md:2156 BeaconState
WRITE process_historical_summaries_update:specs/capella/beacon-chain.md:387 BeaconState.historical_summaries
WRITE process_inactivity_updates:specs/altair/beacon-chain.md:762 BeaconState.inactivity_scores
WRITE process_inactivity_updates:specs/altair/beacon-chain.md:764 BeaconState.inactivity_scores
WRITE process_inactivity_updates:specs/altair/beacon-chain.md:767 BeaconState.inactivity_scores
WRITE process_participation_flag_updates:specs/altair/beacon-chain.md:825 BeaconState
WRITE process_participation_flag_updates:specs/altair/beacon-chain.md:826 BeaconState
WRITE process_pending_consolidations:specs/electra/beacon-chain.md:1229 BeaconState
WRITE process_pending_deposits:specs/gloas/beacon-chain.md:1667 BeaconState
WRITE process_pending_deposits:specs/gloas/beacon-chain.md:1671 BeaconState
WRITE process_pending_deposits:specs/gloas/beacon-chain.md:1673 BeaconState
WRITE process_proposer_lookahead:specs/fulu/beacon-chain.md:484 BeaconState.proposer_lookahead
WRITE process_proposer_lookahead:specs/fulu/beacon-chain.md:489 BeaconState.proposer_lookahead
WRITE process_proposer_slashing:specs/gloas/beacon-chain.md:2480 BeaconState.builder_pending_payments
WRITE process_proposer_slashing:specs/gloas/beacon-chain.md:2485 BeaconState.builder_pending_payments
WRITE process_ptc_window:specs/gloas/beacon-chain.md:1702 BeaconState.ptc_window
WRITE process_ptc_window:specs/gloas/beacon-chain.md:1706 BeaconState.ptc_window
WRITE process_randao:specs/phase0/beacon-chain.md:2361 BeaconState.randao_mixes
WRITE process_randao_mixes_reset:specs/phase0/beacon-chain.md:2287 BeaconState.randao_mixes
WRITE process_registry_updates:specs/electra/beacon-chain.md:1065 BeaconState.validators.*
WRITE process_registry_updates:specs/electra/beacon-chain.md:1073 BeaconState.validators.*
WRITE process_slashings_reset:specs/phase0/beacon-chain.md:2277 BeaconState.slashings
WRITE process_slot:specs/gloas/beacon-chain.md:1572 BeaconState.state_roots
WRITE process_slot:specs/gloas/beacon-chain.md:1575 BeaconState.latest_block_header
WRITE process_slot:specs/gloas/beacon-chain.md:1578 BeaconState.block_roots
WRITE process_slot:specs/gloas/beacon-chain.md:1582 BeaconState.execution_payload_availability
WRITE process_slots:specs/phase0/beacon-chain.md:1839 BeaconState
WRITE process_sync_committee_updates:specs/altair/beacon-chain.md:839 BeaconState
WRITE process_sync_committee_updates:specs/altair/beacon-chain.md:840 BeaconState
WRITE process_withdrawal_request:specs/electra/beacon-chain.md:1927 BeaconState.pending_partial_withdrawals
WRITE queue_excess_active_balance:specs/electra/beacon-chain.md:902 BeaconState.balances
WRITE queue_excess_active_balance:specs/electra/beacon-chain.md:906 BeaconState.pending_deposits
WRITE settle_builder_payment:specs/gloas/beacon-chain.md:1540 BeaconState.builder_pending_withdrawals
WRITE settle_builder_payment:specs/gloas/beacon-chain.md:1541 BeaconState.builder_pending_payments
WRITE slash_validator:specs/electra/beacon-chain.md:995 BeaconState.validators.*
WRITE slash_validator:specs/electra/beacon-chain.md:996 BeaconState.validators.*
WRITE slash_validator:specs/electra/beacon-chain.md:999 BeaconState.slashings
WRITE switch_to_compounding_validator:specs/electra/beacon-chain.md:889 BeaconState.validators.*
WRITE update_builder_pending_withdrawals:specs/gloas/beacon-chain.md:1965 BeaconState
WRITE update_next_withdrawal_builder_index:specs/gloas/beacon-chain.md:1980 BeaconState
WRITE update_next_withdrawal_index:specs/capella/beacon-chain.md:510 BeaconState
WRITE update_next_withdrawal_validator_index:specs/capella/beacon-chain.md:523 BeaconState
WRITE update_next_withdrawal_validator_index:specs/capella/beacon-chain.md:528 BeaconState
WRITE update_payload_expected_withdrawals:specs/gloas/beacon-chain.md:1956 BeaconState
WRITE update_pending_partial_withdrawals:specs/electra/beacon-chain.md:1489 BeaconState
WRITE upgrade_to_gloas:specs/gloas/fork.md:227 BeaconState
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1958 BeaconState
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1959 BeaconState.justification_bits
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1960 BeaconState.justification_bits
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1962 BeaconState
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1965 BeaconState.justification_bits
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1967 BeaconState
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1970 BeaconState.justification_bits
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1976 BeaconState
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1979 BeaconState
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1982 BeaconState
WRITE weigh_justification_and_finalization:specs/phase0/beacon-chain.md:1985 BeaconState
