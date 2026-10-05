#!/bin/sh
# Generate SpecLean/Gen/Scope.lean (minimal preset) or SpecLean/Gen/ScopeMainnet.lean (mainnet
# preset): the version 1 scope, with every EF vector entry point.
# Run from the consensus-specs checkout: gen_scope.sh [minimal|mainnet]
set -e
ROOTS=state_transition,process_slots,process_block,process_epoch,upgrade_to_gloas
ROOTS=$ROOTS,process_attestation,process_attester_slashing,process_block_header
ROOTS=$ROOTS,process_bls_to_execution_change,process_builder_deposit_request
ROOTS=$ROOTS,process_builder_exit_request,process_consolidation_request,process_deposit_request
ROOTS=$ROOTS,process_execution_payload_bid,process_parent_execution_payload
ROOTS=$ROOTS,process_payload_attestation,process_proposer_slashing,process_sync_aggregate
ROOTS=$ROOTS,process_voluntary_exit,process_withdrawal_request,process_withdrawals
TYPES=BeaconState,SignedBeaconBlock,BeaconBlock,Attestation,AttesterSlashing,ProposerSlashing
TYPES=$TYPES,SignedVoluntaryExit,SyncAggregate,SignedBLSToExecutionChange,DepositRequest
TYPES=$TYPES,WithdrawalRequest,ConsolidationRequest,SignedExecutionPayloadBid
TYPES=$TYPES,PayloadAttestation,BuilderDepositRequest,BuilderExitRequest
PRESET=${1:-minimal}
NS=Scope
[ "$PRESET" = mainnet ] && NS=ScopeMainnet
HERE=$(dirname "$0")
uv run python "$HERE/serialize.py" --preset "$PRESET" --roots "$ROOTS" --containers "$TYPES" \
  --namespace "$NS" --prev-fork fulu --fp-out "$HERE/../SpecLean/Gen/$NS.fp" \
  --out "$HERE/../SpecLean/Gen/$NS.lean"
