import SpecLean.Validation.HtrForkData
import SpecLean.Validation.Codecs

/-!
# `compute_signing_root` of real signed classes, end to end

The readable Lean calls `compute_signing_root ⟨enc_X x⟩ domain` for an object of class `X`. The
interpreter gets the heap value that `dec_X` decodes to `x`. `codec_X` gives the content
condition of `compute_signing_root_run`, so one lemma covers every class (`signing_root_codec`).
-/

namespace SpecLean.Validation.HtrBridge

open SpecLean SpecLean.Rd SpecLean.Rd.Gen SpecLean.Encode SpecLean.Validation.Tactic

variable (sha : Oracle) [Spec]

attribute [local instance] Cfg.default

/-! ## `Shaped` of the parts of a shaped value -/

/-- A value that is not a reference reaches no container. -/
theorem shaped_nonref {h : Heap} {v : Value} (hv : ∀ c, v ≠ .ref c) : Shaped h v := by
  intro q c ty fs tys e
  cases q with
  | nil => simp [Encode.follow] at e; exact (hv c e).elim
  | cons i p => cases v with
    | ref b => exact absurd rfl (hv b)
    | _ => simp [Encode.follow] at e

/-- A field of a shaped container. -/
theorem shaped_field {h : Heap} {a b : Nat} {ty : Name} {fs : List Value} {i : Nat}
    (hs : Shaped h (.ref b)) (ho : h.objs b = some (.container ty fs))
    (hx : fs[i]? = some (.ref a)) : Shaped h (.ref a) :=
  shaped_item hs ho (by simpa using hx)

/-- An item of a list that a shaped value reaches. -/
theorem shaped_listitem {h : Heap} {a b : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} {i : Nat} (hs : Shaped h (.ref b)) (ho : h.objs b = some (.list k e l xs))
    (hx : xs[i]? = some (.ref a)) : Shaped h (.ref a) :=
  shaped_item hs ho (by simpa using hx)

macro_rules | `(tactic| rd_shaped) => `(tactic| first
  | assumption
  | exact shaped_nonref (fun _ e => by cases e)
  | (refine shaped_field ?_ ?ho ?hx
     case hx => assumption
     case ho => assumption
     rd_shaped)
  | (refine shaped_listitem ?_ ?ho ?hx
     case hx => assumption
     case ho => assumption
     rd_shaped))

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

/-- AttestationData: `is_valid_indexed_attestation`. -/
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

/-- BeaconBlock: `verify_block_signature`. -/
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

/-- BeaconBlockHeader: `process_proposer_slashing`. -/
theorem signing_root_BeaconBlockHeader (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : BeaconBlockHeader) (hd : dec_BeaconBlockHeader h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_BeaconBlockHeader x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_BeaconBlockHeader gfp h hwf v0 x hd hs x1 h1 haw k

/-- BLSToExecutionChange: `process_bls_to_execution_change`. -/
theorem signing_root_BLSToExecutionChange (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : BLSToExecutionChange) (hd : dec_BLSToExecutionChange h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_BLSToExecutionChange x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_BLSToExecutionChange gfp h hwf v0 x hd hs x1 h1 haw k

/-- DepositMessage: the deposit signatures. -/
theorem signing_root_DepositMessage (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : DepositMessage) (hd : dec_DepositMessage h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_DepositMessage x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_DepositMessage gfp h hwf v0 x hd hs x1 h1 haw k

/-- Epoch: `process_randao`. -/
theorem signing_root_Epoch (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : Epoch) (hd : dec_Epoch h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_Epoch x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_Epoch gfp h hwf v0 x hd hs x1 h1 haw k

/-- ExecutionPayloadBid: `verify_execution_payload_bid_signature`. -/
theorem signing_root_ExecutionPayloadBid (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : ExecutionPayloadBid) (hd : dec_ExecutionPayloadBid h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_ExecutionPayloadBid x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_ExecutionPayloadBid gfp h hwf v0 x hd hs x1 h1 haw k

/-- PayloadAttestationData: `is_valid_indexed_payload_attestation`. -/
theorem signing_root_PayloadAttestationData (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : PayloadAttestationData) (hd : dec_PayloadAttestationData h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_PayloadAttestationData x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_PayloadAttestationData gfp h hwf v0 x hd hs x1 h1 haw k

/-- Root: `process_sync_aggregate`. -/
theorem signing_root_Root (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (v0 : Value) (x : Root) (hd : dec_Root h v0 = some x)
    (hs : Shaped h v0) (x1 : List UInt8) (h1 : x1.length = 32)
    (haw : ArgsWF h [v0, (.bytes Scope.Id.«Domain» x1)]) (k : Nat) :
    ResultMatches gfp [] h [v0, (.bytes Scope.Id.«Domain» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_signing_root»
        [v0, (.bytes Scope.Id.«Domain» x1)] h)
      (compute_signing_root ⟨enc_Root x⟩ (⟨x1⟩ : Domain)) :=
  signing_root_codec sha ho codec_Root gfp h hwf v0 x hd hs x1 h1 haw k

/-- VoluntaryExit: `process_voluntary_exit`. -/
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

end SpecLean.Validation.HtrBridge
