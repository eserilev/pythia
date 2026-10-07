import SpecLean.Validation.HtrForkData
import SpecLean.Validation.Codecs

/-!
# `compute_signing_root` of real signed classes, end to end

The readable Lean calls `compute_signing_root ⟨enc_X x⟩ domain` for an object of class `X`. The
interpreter gets the heap value that `dec_X` decodes to `x`. `codec_X` gives the content
condition of `compute_signing_root_run`, so one lemma covers every class (`signing_root_codec`).
-/

namespace SpecLean.Validation.HtrBridge

open SpecLean SpecLean.Rd SpecLean.Rd.Gen SpecLean.Encode

variable (sha : Oracle) [Spec]

attribute [local instance] Cfg.default

/-- `compute_signing_root` of any decoded object with a codec. -/
theorem signing_root_codec (ho : OracleHtr sha) {α : Type} {dec : Dec α} {enc : Enc α}
    (hc : Codec dec enc) (gfp : Footprint) (h : Heap) (hwf : HeapWF h) (v0 : Value) (x : α)
    (hd : dec h v0 = some x) (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc x⟩ (⟨x1⟩ : Domain)) :=
  compute_signing_root_run sha ho gfp h hwf v0 ⟨enc x⟩ ((hc.good h v0 x hd hs Heap.empty).1 64)
    x1 h1 haw k

/-- A block: `compute_signing_root(block, domain)` in `verify_block_signature`. -/
theorem signing_root_BeaconBlock (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : BeaconBlock) (hd : dec_BeaconBlock h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_BeaconBlock x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_BeaconBlock gfp h hwf v0 x hd hs x1 h1 haw k

/-- A voluntary exit: `process_voluntary_exit`. -/
theorem signing_root_VoluntaryExit (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : VoluntaryExit) (hd : dec_VoluntaryExit h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_VoluntaryExit x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_VoluntaryExit gfp h hwf v0 x hd hs x1 h1 haw k

/-- Attestation data: `is_valid_indexed_attestation`. -/
theorem signing_root_AttestationData (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : AttestationData) (hd : dec_AttestationData h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_AttestationData x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_AttestationData gfp h hwf v0 x hd hs x1 h1 haw k

/-- A payload bid: `verify_execution_payload_bid_signature`. -/
theorem signing_root_ExecutionPayloadBid (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : ExecutionPayloadBid)
    (hd : dec_ExecutionPayloadBid h v0 = some x) (hs : Shaped h v0) (x1 : List UInt8)
    (h1 : x1.length = 32) (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_ExecutionPayloadBid x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_ExecutionPayloadBid gfp h hwf v0 x hd hs x1 h1 haw k

end SpecLean.Validation.HtrBridge
