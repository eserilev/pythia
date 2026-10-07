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
open SpecLean.Validation.Decode (decUintT_eq)

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

/-! ## `==` on decoded containers

Python's `==` on two containers compares their fields in order. With `Shaped` the objects hold
exactly the fields of their class, so `==` is equality of the decoded values.
-/

theorem resolveUint_self' (t : UintTy) : resolveUint t t = .ok t := by
  cases t <;> simp [resolveUint]

/-- The fields of a shaped container: the object holds exactly `n` of them. -/
theorem shaped_fields {h : Heap} {a : Nat} {ty : Name} {fs : List Value} {tys : List (Name × SszTy)}
    (hs : Shaped h (.ref a)) (ho : h.objs a = some (.container ty fs))
    (ht : Scope.containers.lookup ty = some tys) : fs.length = tys.length :=
  hs [] a ty fs tys rfl ho ht

theorem cmp_uint_eq (t : UintTy) (a b : Nat) :
    cmpVal .eq (.uint t a) (.uint t b) = .ok (decide (a = b)) := by
  simp [cmpVal, LibValues.compare, Ssz.compare, resolveUint_self', cmpInt]
  by_cases e : a = b <;> simp [e] <;> omega

theorem cmp_bytes_eq (c : Name) (a b : List UInt8) :
    cmpVal .eq (.bytes c a) (.bytes c b) = .ok (decide (a = b)) := by
  simp [cmpVal, LibValues.compare, Ssz.compare, pyCmp]
  by_cases e : a = b <;> simp [e]

theorem deepEq_Eth1Data (d : Nat) {h : Heap} {v0 v1 : Value} {x0 x1 : Eth1Data}
    (hd0 : dec_Eth1Data h v0 = some x0) (hd1 : dec_Eth1Data h v1 = some x1)
    (hs0 : Shaped h v0) (hs1 : Shaped h v1) :
    deepEq (d + 2) h v0 v1 = .ok (decide (x0 = x1)) := by
  obtain ⟨a0, rfl⟩ : ∃ a, v0 = .ref a := by
    cases v0 <;> simp_all [dec_Eth1Data, containerFieldsT]
  obtain ⟨a1, rfl⟩ : ∃ a, v1 = .ref a := by
    cases v1 <;> simp_all [dec_Eth1Data, containerFieldsT]
  -- The objects and their fields.
  have key : ∀ a (x : Eth1Data), dec_Eth1Data h (.ref a) = some x → Shaped h (.ref a) →
      ∃ w0 w1 w2, h.objs a = some (.container Scope.Id.«Eth1Data» [w0, w1, w2]) ∧
        w0 = .bytes Scope.Id.«Root» x.deposit_root.data ∧
        w1 = .uint (.width 64) x.deposit_count.val ∧
        w2 = .bytes Scope.Id.«Hash32» x.block_hash.data := by
    intro a x hd hs
    simp only [dec_Eth1Data, containerFieldsT, Option.bind_eq_bind] at hd
    cases ho : h.objs a with
    | none => simp [ho] at hd
    | some o =>
      cases o with
      | container ty fs =>
        simp only [ho] at hd
        by_cases hty : ty = Scope.Id.«Eth1Data»
        · subst hty
          have hl := shaped_fields hs ho (by rfl)
          simp only [if_true, Option.bind_some] at hd
          match fs, hl with
          | [w0, w1, w2], _ =>
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_some,
              Option.bind_eq_some_iff] at hd
            obtain ⟨r0, h0, r1, h1, r2, h2, hx⟩ := hd
            have hx' : x = ⟨r0, r1, r2⟩ := (Option.some.inj hx).symm
            subst hx'
            refine ⟨w0, w1, w2, rfl, decBytesT_some h0, ?_, decBytesT_some h2⟩
            exact (decUintT_eq.mp h1).1
        · simp [hty] at hd
      | _ => simp [ho] at hd
  obtain ⟨w0, w1, w2, ho0, e0, e1, e2⟩ := key a0 x0 hd0 hs0
  obtain ⟨u0, u1, u2, ho1, f0, f1, f2⟩ := key a1 x1 hd1 hs1
  subst e0 e1 e2 f0 f1 f2
  by_cases hab : a0 = a1
  · subst hab
    rw [hd0] at hd1; cases hd1
    simp [deepEq]
  · rcases x0 with ⟨⟨r0⟩, ⟨c0⟩, ⟨b0⟩⟩
    rcases x1 with ⟨⟨r1⟩, ⟨c1⟩, ⟨b1⟩⟩
    simp only [deepEq, hab, if_false, ho0, ho1, eqLists, cmp_uint_eq, cmp_bytes_eq, bind,
      Except.bind, pure, Except.pure]
    by_cases q0 : r0 = r1 <;> by_cases q1 : c0 = c1 <;> by_cases q2 : b0 = b1 <;>
      simp [q0, q1, q2, deepEq, cmp_uint_eq, cmp_bytes_eq, eqLists]

theorem deepEq_Checkpoint (d : Nat) {h : Heap} {v0 v1 : Value} {x0 x1 : Checkpoint}
    (hd0 : dec_Checkpoint h v0 = some x0) (hd1 : dec_Checkpoint h v1 = some x1)
    (hs0 : Shaped h v0) (hs1 : Shaped h v1) :
    deepEq (d + 2) h v0 v1 = .ok (decide (x0 = x1)) := by
  obtain ⟨a0, rfl⟩ : ∃ a, v0 = .ref a := by
    cases v0 <;> simp_all [dec_Checkpoint, containerFieldsT]
  obtain ⟨a1, rfl⟩ : ∃ a, v1 = .ref a := by
    cases v1 <;> simp_all [dec_Checkpoint, containerFieldsT]
  have key : ∀ a (x : Checkpoint), dec_Checkpoint h (.ref a) = some x → Shaped h (.ref a) →
      ∃ w0 w1, h.objs a = some (.container Scope.Id.«Checkpoint» [w0, w1]) ∧
        w0 = .uint (.nominal Scope.Id.«Epoch» 64) x.epoch.val ∧
        w1 = .bytes Scope.Id.«Root» x.root.data := by
    intro a x hd hs
    simp only [dec_Checkpoint, containerFieldsT, Option.bind_eq_bind] at hd
    cases ho : h.objs a with
    | none => simp [ho] at hd
    | some o =>
      cases o with
      | container ty fs =>
        simp only [ho] at hd
        by_cases hty : ty = Scope.Id.«Checkpoint»
        · subst hty
          have hl := shaped_fields hs ho (by rfl)
          simp only [if_true, Option.bind_some] at hd
          match fs, hl with
          | [w0, w1], _ =>
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_some,
              Option.bind_eq_some_iff] at hd
            obtain ⟨r0, h0, r1, h1, hx⟩ := hd
            have hx' : x = ⟨r0, r1⟩ := (Option.some.inj hx).symm
            subst hx'
            exact ⟨w0, w1, rfl, (decUintT_eq.mp h0).1, decBytesT_some h1⟩
        · simp [hty] at hd
      | _ => simp [ho] at hd
  obtain ⟨w0, w1, ho0, e0, e1⟩ := key a0 x0 hd0 hs0
  obtain ⟨u0, u1, ho1, f0, f1⟩ := key a1 x1 hd1 hs1
  subst e0 e1 f0 f1
  by_cases hab : a0 = a1
  · subst hab
    rw [hd0] at hd1; cases hd1
    simp [deepEq]
  · rcases x0 with ⟨⟨c0⟩, ⟨r0⟩⟩
    rcases x1 with ⟨⟨c1⟩, ⟨r1⟩⟩
    simp only [deepEq, hab, if_false, ho0, ho1, eqLists, bind, Except.bind, pure, Except.pure]
    by_cases q0 : c0 = c1 <;> by_cases q1 : r0 = r1 <;>
      simp [q0, q1, deepEq, cmp_uint_eq, cmp_bytes_eq, eqLists, resolveUint_self', cmpInt] <;> omega

theorem deepEq_AttestationData (d : Nat) {h : Heap} {v0 v1 : Value} {x0 x1 : AttestationData}
    (hd0 : dec_AttestationData h v0 = some x0) (hd1 : dec_AttestationData h v1 = some x1)
    (hs0 : Shaped h v0) (hs1 : Shaped h v1) :
    deepEq (d + 3) h v0 v1 = .ok (decide (x0 = x1)) := by
  obtain ⟨a0, rfl⟩ : ∃ a, v0 = .ref a := by
    cases v0 <;> simp_all [dec_AttestationData, containerFieldsT]
  obtain ⟨a1, rfl⟩ : ∃ a, v1 = .ref a := by
    cases v1 <;> simp_all [dec_AttestationData, containerFieldsT]
  have key : ∀ a (x : AttestationData), dec_AttestationData h (.ref a) = some x →
      Shaped h (.ref a) →
      ∃ w0 w1 w2 w3 w4, h.objs a = some (.container Scope.Id.«AttestationData» [w0, w1, w2, w3, w4]) ∧
        w0 = .uint (.nominal Scope.Id.«Slot» 64) x.slot.val ∧
        w1 = .uint (.nominal Scope.Id.«CommitteeIndex» 64) x.index.val ∧
        w2 = .bytes Scope.Id.«Root» x.beacon_block_root.data ∧
        dec_Checkpoint h w3 = some x.source ∧ Shaped h w3 ∧
        dec_Checkpoint h w4 = some x.target ∧ Shaped h w4 := by
    intro a x hd hs
    simp only [dec_AttestationData, containerFieldsT, Option.bind_eq_bind] at hd
    cases ho : h.objs a with
    | none => simp [ho] at hd
    | some o =>
      cases o with
      | container ty fs =>
        simp only [ho] at hd
        by_cases hty : ty = Scope.Id.«AttestationData»
        · subst hty
          have hl := shaped_fields hs ho (by rfl)
          simp only [if_true, Option.bind_some] at hd
          match fs, hl with
          | [w0, w1, w2, w3, w4], _ =>
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_some,
              Option.bind_eq_some_iff] at hd
            obtain ⟨r0, h0, r1, h1, r2, h2, r3, h3, r4, h4, hx⟩ := hd
            have hx' : x = ⟨r0, r1, r2, r3, r4⟩ := (Option.some.inj hx).symm
            subst hx'
            exact ⟨w0, w1, w2, w3, w4, rfl, (decUintT_eq.mp h0).1, (decUintT_eq.mp h1).1,
              decBytesT_some h2, h3, shaped_item hs ho (i := 3) rfl, h4,
              shaped_item hs ho (i := 4) rfl⟩
        · simp [hty] at hd
      | _ => simp [ho] at hd
  obtain ⟨w0, w1, w2, w3, w4, ho0, e0, e1, e2, g3, s3, g4, s4⟩ := key a0 x0 hd0 hs0
  obtain ⟨u0, u1, u2, u3, u4, ho1, f0, f1, f2, k3, t3, k4, t4⟩ := key a1 x1 hd1 hs1
  subst e0 e1 e2 f0 f1 f2
  by_cases hab : a0 = a1
  · subst hab
    rw [hd0] at hd1; cases hd1
    simp [deepEq]
  · have c3 := deepEq_Checkpoint d g3 k3 s3 t3
    have c4 := deepEq_Checkpoint d g4 k4 s4 t4
    rcases x0 with ⟨⟨sl0⟩, ⟨ix0⟩, ⟨r0⟩, src0, tgt0⟩
    rcases x1 with ⟨⟨sl1⟩, ⟨ix1⟩, ⟨r1⟩, src1, tgt1⟩
    simp only [deepEq, hab, if_false, ho0, ho1, eqLists, bind, Except.bind, pure, Except.pure]
    simp only at c3 c4
    by_cases q0 : sl0 = sl1 <;> by_cases q1 : ix0 = ix1 <;> by_cases q2 : r0 = r1 <;>
      by_cases q3 : src0 = src1 <;> by_cases q4 : tgt0 = tgt1 <;>
      simp [q0, q1, q2, q3, q4, deepEq, cmp_uint_eq, cmp_bytes_eq, eqLists, c3, c4, resolveUint_self', cmpInt] <;> omega

end SpecLean.Validation.HtrBridge
