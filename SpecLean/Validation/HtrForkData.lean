import SpecLean.Validation.HtrBridge
import SpecLean.Validation.Alloc
import SpecLean.Validation.Tactic

/-!
# `compute_fork_data_root` end to end

The interpreter builds a `ForkData` object and calls the oracle on it. The readable Lean calls
`htr` on its encoding. `htr_ForkData` links the two under `OracleHtr`. `root_noOof` covers the
error case: a root never runs out of fuel.
-/

namespace SpecLean.Validation.HtrBridge

open SpecLean SpecLean.Rd SpecLean.Rd.Gen SpecLean.Encode SpecLean.Validation.Tactic

variable (sha : Oracle) [Spec]

attribute [local instance] Cfg.default

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem compute_fork_data_root_run (ho : OracleHtr sha) (gfp : Footprint) (h : Heap)
    (hwf : HeapWF h) (x0 x1 : List UInt8) (h0 : x0.length = 4) (h1 : x1.length = 32) (k : Nat) :
    ResultMatches gfp [] h [(.bytes Scope.Id.«Version» x0), (.bytes Scope.Id.«Root» x1)]
      (fun (r : Root) h' v => v = (enc_Root r h').1 ∧ (BytesC.data r).length = 32)
      (interp (Scope.env sha) (k + 64) Scope.Id.«compute_fork_data_root»
        [(.bytes Scope.Id.«Version» x0), (.bytes Scope.Id.«Root» x1)] h)
      (compute_fork_data_root (⟨x0⟩ : Version) (⟨x1⟩ : Root)) := by
  have hctor : ∀ m (h' : Heap), callValue (Scope.env sha) m (.glob 158) []
      [(157, .bytes Scope.Id.«Version» x0), (144, .bytes Scope.Id.«Root» x1)] h' =
      .ok (.ref h'.next, (h'.alloc (.container 158
        [.bytes Scope.Id.«Version» x0, .bytes Scope.Id.«Root» x1])).2) := by
    intro m h'
    rw [callValue.eq_def]
    simp [Scope.env, lookup_lit, LibModel.construct, Ssz.construct, ctorFields, kwArg,
      Ssz.construct.build, depthBound, Ssz.coerceH, coerceField, h0, h1]
    rfl
  have hhtr : ∀ m (h' : Heap) (a : Nat), callValue (Scope.env sha) m (.glob 159) [.ref a] [] h' =
      (fun r => (Value.bytes 146 r, h')) <$> sha.hashTreeRoot h' (.ref a) := by
    intro m h' a
    rw [callValue.eq_def]
    simp [Scope.env, lookup_lit, applyBuiltin, LibModel.builtin, Ssz.builtin]
    cases sha.hashTreeRoot h' (.ref a) <;> rfl
  simp only [Scope.env] at hctor hhtr
  rw [interp, callName, callValue.eq_def]
  simp [hctor, hhtr, lookup_lit, Scope.fn_compute_fork_data_root, Scope.env, callFn, bindArgs, evalList,
    bindArgs.go, execBlock, execStmt, evalExpr, evalArgs, lookupName]
  -- The new object and its readable value.
  let o : HeapObj := .container 158 [.bytes Scope.Id.«Version» x0, .bytes Scope.Id.«Root» x1]
  let x : ForkData := { current_version := ⟨x0⟩, genesis_validators_root := ⟨x1⟩ }
  have hdec : dec_ForkData (h.alloc o).2 (.ref h.next) = some x := by
    simp [o, x, dec_ForkData, containerFieldsT, Where.objs_alloc_self, decBytesT, h0, h1,
      BytesC.len, BytesC.ofBytes]
  have hsh : Shaped (h.alloc o).2 (.ref h.next) := by
    intro q c ty fs tys hf hoc hl
    cases q with
    | nil =>
      simp only [Encode.follow, Option.some.injEq, Value.ref.injEq] at hf
      subst hf
      rw [Where.objs_alloc_self] at hoc
      simp only [o, Option.some.injEq, HeapObj.container.injEq] at hoc
      obtain ⟨rfl, rfl⟩ := hoc
      have h2 : (Scope.containers.lookup 158).map List.length = some 2 := rfl
      rw [hl] at h2
      simp at h2
      simp [h2]
    | cons j p =>
      simp only [Encode.follow, Where.objs_alloc_self, o] at hf
      cases j with
      | zero => cases p <;> simp_all [Encode.follow]
      | succ j => cases j <;> cases p <;> simp_all [Encode.follow]
  have hbr := htr_ForkData ho hsh hdec
  have haw : ArgsWF h [(.bytes Scope.Id.«Version» x0), (.bytes Scope.Id.«Root» x1)] := by
    intro kk q a e
    simp only [at?] at e
    match kk, q with
    | 0, [] => simp [Encode.follow] at e
    | 1, [] => simp [Encode.follow] at e
    | 0, j :: q => simp [Encode.follow] at e
    | 1, j :: q => simp [Encode.follow] at e
    | n + 2, _ => simp at e
  have hc := alloc_contract gfp [] (vs := [(.bytes Scope.Id.«Version» x0), (.bytes Scope.Id.«Root» x1)])
    o hwf haw
  have hrd : compute_fork_data_root (⟨x0⟩ : Version) (⟨x1⟩ : Root) =
      (htr enc_ForkData x >>= fun b => bytesOf Root b) := by
    rw [compute_fork_data_root]
    congr 1
    funext b
    exact bind_pure _
  rw [hrd, ← hbr]
  revert hc
  generalize hR : sha.hashTreeRoot (h.alloc o).2 (.ref h.next) = R
  intro hc
  rcases R with e | r
  · have hne : e ≠ .outOfFuel := fun he => by
      subst he; rw [ho.htr] at hR; exact root_noOof hasher 64 _ _ hR
    simp [erase, Except.mapError, ResultMatches, hne]
  · have hl := ho.len _ _ _ hR
    simp [erase, Except.mapError, ResultMatches, bytesOf, hl, BytesC.len, enc_Root, encBytesN,
      BytesC.data, BytesC.ofBytes]
    exact ⟨hc.base.frame, hc.base.fresh, hc.base.paths⟩
