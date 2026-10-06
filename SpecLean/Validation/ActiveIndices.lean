import SpecLean.DecodeLemmas
import SpecLean.Validation.Tactic
import SpecLean.Validation.Comp
import SpecLean.Validation.Gen.Leaves

/-!
# `get_active_validator_indices` through the comprehension lemma

```python
return [ValidatorIndex(i) for i, v in enumerate(state.validators) if is_active_validator(v, epoch)]
```

`comp_sim` runs the items. One item (`gavi_item`) calls `is_active_validator` through its own
theorem and builds the index. The heap does not change until the result list is made, so each
item has the empty contract (`CContract.refl`).
-/

namespace SpecLean.Validation
open SpecLean SpecLean.Rd SpecLean.Rd.Gen SpecLean.Encode SpecLean.Validation.Tactic
open SpecLean.Validation.Where SpecLean.Validation.Grow

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable [Spec]
attribute [local instance] Cfg.default

theorem decListT_some {α : Type} {k : ListKind} {e : SszTy} {l : Option Nat} {f : Dec α}
    {h : Heap} {v : Value} {ys : List α} (hd : decListT k e l f h v = some ys) :
    ∃ a xs, v = .ref a ∧ h.objs a = some (.list k e l xs) ∧ xs.mapM (f h) = some ys := by
  unfold decListT at hd
  split at hd
  · rename_i a
    split at hd
    · rename_i k' e' l' xs ho
      split at hd
      · rename_i hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact ⟨a, xs, rfl, ho, hd⟩
      · simp at hd
    · simp at hd
  · simp at hd

theorem containerFieldsT_some {ty : Name} {h : Heap} {v : Value} {fs : List Value}
    (hd : containerFieldsT ty h v = some fs) :
    ∃ a, v = .ref a ∧ h.objs a = some (.container ty fs) := by
  unfold containerFieldsT at hd
  split at hd
  · rename_i a
    split at hd
    · rename_i ty' fs' ho
      split at hd
      · rename_i hc; subst hc; cases hd; exact ⟨a, rfl, ho⟩
      · simp at hd
    · simp at hd
  · simp at hd

theorem dec_state_validators {h : Heap} {r0 : Nat} {x0 : BeaconState}
    (hy0 : dec_BeaconState h (.ref r0) = some x0) :
    ∃ fs va vrefs, h.objs r0 = some (.container Scope.Id.«BeaconState» fs) ∧
      fs[11]? = some (.ref va) ∧
      h.objs va = some (.list .progressiveList (.container Scope.Id.«Validator») none vrefs) ∧
      vrefs.mapM (dec_Validator h) = some x0.validators := by
  unfold dec_BeaconState at hy0
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hy0
  obtain ⟨fs, hfs, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
    vals, ⟨vv, hvv, hdv⟩, hrest⟩ := hy0
  obtain ⟨r, hr, ho⟩ := containerFieldsT_some hfs
  cases hr
  obtain ⟨va, vrefs, rfl, hov, hm⟩ := decListT_some hdv
  rd_split_hyps
  exact ⟨fs, va, vrefs, ho, hvv, hov, hm⟩

variable (sha : Oracle)

theorem wrap_vi {n : Nat} (hn : n < 2 ^ 64) :
    wrapUint (.nominal Scope.Id.«ValidatorIndex» 64) (n : Int) =
      .ok (.uint (.nominal Scope.Id.«ValidatorIndex» 64) n) := by
  unfold wrapUint
  rw [if_pos (by simp [UintTy.bits]; omega)]
  rfl

theorem wrap_vi_err {n : Nat} (hn : ¬ n < 2 ^ 64) :
    wrapUint (.nominal Scope.Id.«ValidatorIndex» 64) (n : Int) = .error .sszValue := by
  unfold wrapUint
  rw [if_neg (by simp [UintTy.bits]; omega)]

theorem uOf_vi {n : Nat} (hn : n < 2 ^ 64) : uOf ValidatorIndex (n : Int) = .ok ⟨n⟩ := by
  unfold uOf
  rw [if_pos (by simp [UintC.bits]; omega)]
  rfl

theorem uOf_vi_err {n : Nat} (hn : ¬ n < 2 ^ 64) : uOf ValidatorIndex (n : Int) = .error .bug := by
  unfold uOf
  rw [if_neg (by simp [UintC.bits]; omega)]
  rfl

theorem wrap_uOf_vi (n : Nat) :
    (wrapUint (.nominal Scope.Id.«ValidatorIndex» 64) (n : Int) =
        .ok (.uint (.nominal Scope.Id.«ValidatorIndex» 64) n) ∧ uOf ValidatorIndex (n : Int) = .ok ⟨n⟩) ∨
    (wrapUint (.nominal Scope.Id.«ValidatorIndex» 64) (n : Int) = .error .sszValue ∧
      uOf ValidatorIndex (n : Int) = .error .bug) := by
  rcases Nat.lt_or_ge n (2 ^ 64) with hr | hr
  · exact .inl ⟨wrap_vi hr, uOf_vi hr⟩
  · exact .inr ⟨wrap_vi_err (Nat.not_lt_of_ge hr), uOf_vi_err (Nat.not_lt_of_ge hr)⟩

theorem gavi_item (gfp : Footprint) (vs : List Value) (n i : Nat) (L : Locals) (h : Heap) (r : Nat)
    (v : Validator) (x1 : Nat) (hc : CContract gfp [] vs h h)
    (hdv : dec_Validator h (.ref r) = some v)
    (hL103 : L 103 = some (.uint (.nominal Scope.Id.«Epoch» 64) x1)) (hL215 : L 215 = none)
    (hL82 : L 82 = none) :
    ItemRel (CContract gfp [] vs h)
      (fun L' h' => h' = h ∧ L' 103 = some (.uint (.nominal Scope.Id.«Epoch» 64) x1) ∧
        L' 215 = none ∧ L' 82 = none)
      (fun v (b : ValidatorIndex) _ => v = .uint (.nominal Scope.Id.«ValidatorIndex» 64) b.val)
      (compItem (Scope.env sha) (n + 66) L h (.tuple 1474 [(.name 1474 115), (.name 1474 78)])
        [(.call 1474 (.name 1474 215) [(.pos (.name 1474 78)), (.pos (.name 1474 103))])]
        (.call 1474 (.name 1474 82) [(.pos (.name 1474 115))]) (enumItem i (.ref r)))
      (do if (← is_active_validator v ⟨x1⟩) then (do pure (some (← uOf ValidatorIndex (i : Int)))) else pure none) := by
  have hrun := SpecLean.Validation.Gen.is_active_validator_run sha gfp h r v hdv x1 (n + 1)
  obtain ⟨b, hb⟩ : ∃ b, is_active_validator v ⟨x1⟩ = .ok b := ⟨_, rfl⟩
  have hcall : callStop (Scope.env sha) (n + 65) 215
      [.ref r, .uint (.nominal Scope.Id.«Epoch» 64) x1] h =
      .ok (.bool b, h) := by
    rw [callStop_def]
    rw [show n + 1 + 64 = n + 65 by omega, hb] at hrun
    revert hrun
    rcases interp (Scope.env sha) (n + 65) Scope.Id.«is_active_validator» _ h with e | ⟨w, h'⟩
    · simp [ResultMatches]
    · simp only [ResultMatches]
      rintro ⟨⟨rfl, rfl⟩, -⟩; rfl
  have hvi : ∀ (m : Nat) (h' : Heap), callValue (Scope.env sha) m (.glob 82) [.int (i : Int)] [] h' =
      (fun w => (w, h')) <$> wrapUint (.nominal Scope.Id.«ValidatorIndex» 64) i := by
    intro m h'
    rw [callValue.eq_def]
    simp [Scope.env, lookup_lit, LibModel.construct, Ssz.construct]
    cases wrapUint (.nominal Scope.Id.«ValidatorIndex» 64) i <;> rfl
  simp only [Scope.env] at hcall hvi
  unfold compItem
  simp [hvi, truthyH, truthy, LibValues.truthy, Ssz.truthy, pyTruthy, enumItem, assignTarget, assignTargets, evalIfs, call_through, evalExpr, evalArgs,
    lookupName, hL103, hL215, hL82, Scope.env, lookup_lit, hb, hcall]
  have hQ : ((L.set 115 (.int (i : Int))).set 78 (.ref r)) 103 = some (.uint (.nominal Scope.Id.«Epoch» 64) x1) ∧
      ((L.set 115 (.int (i : Int))).set 78 (.ref r)) 215 = none ∧
      ((L.set 115 (.int (i : Int))).set 78 (.ref r)) 82 = none := by
    simp [Locals.set_apply, hL103, hL215, hL82]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Except.bind_ok', ItemRel]
    exact ⟨hc, trivial, hQ⟩
  · simp only [↓reduceIte, Except.bind_ok']
    generalize hw : wrapUint (.nominal Scope.Id.«ValidatorIndex» 64) (i : Int) = W
    generalize hu : uOf ValidatorIndex (i : Int) = U
    rcases wrap_uOf_vi i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hw; rw [h2] at hu; subst hw hu
      simp only [Except.bind_ok', Except.pure_ok', ItemRel]
      exact ⟨hc, ⟨trivial, hQ⟩, trivial⟩
    · rw [h1] at hw; rw [h2] at hu; subst hw hu
      simp only [Except.bind_error', ItemRel]
      exact ⟨by decide, rfl⟩

theorem listRel_uint {vals : List Value} {bs : List ValidatorIndex}
    (hr : ListRel (fun v (b : ValidatorIndex) => v = .uint (.nominal Scope.Id.«ValidatorIndex» 64) b.val)
      vals bs) :
    vals = bs.map fun x => .uint (.nominal Scope.Id.«ValidatorIndex» 64) x.val := by
  induction hr with
  | nil => rfl
  | cons hab _ ih => rw [hab, ih]; rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem gavi_run (gfp : Footprint) (h : Heap) (r0 : Nat) (x0 : BeaconState)
    (hy0 : dec_BeaconState h (.ref r0) = some x0) (x1 : Nat) (hwf : HeapWF h)
    (haw : ArgsWF h [(.ref r0), (.uint (.nominal Scope.Id.«Epoch» 64) x1)]) (k : Nat) :
    ResultMatches gfp [] h [(.ref r0), (.uint (.nominal Scope.Id.«Epoch» 64) x1)]
      (fun (rs : List ValidatorIndex) h' v => ∃ a, v = .ref a ∧ h'.objs a =
        some (.list .pyList .any none (rs.map fun x => .uint (.nominal Scope.Id.«ValidatorIndex» 64) x.val)))
      (interp (Scope.env sha) (k + x0.validators.length + 80) Scope.Id.«get_active_validator_indices»
        [(.ref r0), (.uint (.nominal Scope.Id.«Epoch» 64) x1)] h)
      (get_active_validator_indices x0 ⟨x1⟩) := by
  obtain ⟨fs, va, vrefs, ho, hfv, hov, hm⟩ := dec_state_validators hy0
  have henum : ∀ m (h' : Heap), callValue (Scope.env sha) m (.glob 216) [.ref va] [] h' =
      .ok (.enumView (.ref va), h') := by
    intro m h'
    rw [callValue.eq_def]
    simp [Scope.env, lookup_lit, applyBuiltin, LibModel.builtin, Ssz.builtin]
  simp only [Scope.env] at henum
  rw [interp, callName, callValue.eq_def]
  simp [Scope.env, lookup_lit, frame_eq, callFn, Scope.fn_get_active_validator_indices, bindArgs,
    bindArgs.go, execBlock, execStmt, evalExpr, evalArgs, evalList, lookupName, compLoop,
    getAttr, ho, hfv, fieldIndex_lit, applyBuiltin, LibModel.builtin, Ssz.builtin, iterSource, toSeq, hov, henum]
  let ys := x0.validators.zipIdx.map fun (v, i) => ((i : Int), v)
  let f : Int × Validator → SpecM (Option ValidatorIndex) := fun (i, v) => do
    if (← is_active_validator v ⟨x1⟩) then (do pure (some (← uOf ValidatorIndex i))) else pure none
  have hys : ys.length = x0.validators.length := by simp [ys]
  have hvlen : vrefs.length = x0.validators.length := ((mapM_some_iff _ _).mp hm).1.symm
  have hll : ∀ (h' : Heap), h' = h → ListLen h' va x0.validators.length :=
    fun h' e => by subst e; exact ⟨_, _, _, _, hov, hvlen⟩
  let args : List Value := [(.ref r0), (.uint (.nominal Scope.Id.«Epoch» 64) x1)]
  have hcomp := comp_sim (Scope.env sha) (.tuple 1474 [(.name 1474 115), (.name 1474 78)])
    [(.call 1474 (.name 1474 215) [(.pos (.name 1474 78)), (.pos (.name 1474 103))])]
    (.call 1474 (.name 1474 82) [(.pos (.name 1474 115))]) (.enum (.live va)) 66 ys f
    (fun v (b : ValidatorIndex) _ => v = .uint (.nominal Scope.Id.«ValidatorIndex» 64) b.val)
    (gfp := gfp) (fpf := []) (vs := args) (by simp) hwf
    (fun _ L h' => h' = h ∧ L 103 = some (.uint (.nominal Scope.Id.«Epoch» 64) x1) ∧
      L 215 = none ∧ L 82 = none)
    (fun i L h' hq hi => by
      obtain ⟨x, hx⟩ := seqItem_live_some (hll h' hq.1) (by rw [← hys]; exact hi)
      exact ⟨enumItem i x, by simp [iterItem, hx]⟩)
    (fun i L h' hq hi => by
      simp [iterItem, seqItem_live_none (hll h' hq.1) (by rw [← hys]; exact hi)])
    ?hstep (fun _ _ _ _ e _ => e) (k + x0.validators.length + 10) 0
    ((Locals.empty.set 1 (Value.ref r0)).set 103 (Value.uint (UintTy.nominal Scope.Id.«Epoch» 64) x1)) h
    ⟨rfl, by simp, by simp, by simp⟩ (CContract.refl _ _ _ h hwf haw) (by omega)
  case hstep =>
    intro n i L h' x y hq hy hx
    obtain ⟨rfl, hL103, hL215, hL82⟩ := hq
    have hi : i < x0.validators.length := by
      have := (List.getElem?_eq_some_iff.mp hy).1; rw [hys] at this; exact this
    have hy' : y = ((i : Int), x0.validators[i]) := by
      simp [ys, List.getElem?_map, List.getElem?_zipIdx] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      rw [List.getElem?_eq_getElem hi] at ha; cases ha; rfl
    subst hy'
    have hvi : i < vrefs.length := by rw [hvlen]; exact hi
    have hdw := ((mapM_some_iff _ _).mp hm).2 i vrefs[i] (List.getElem?_eq_getElem hvi)
    rw [List.getElem?_eq_getElem hi] at hdw
    have hx' : x = enumItem i vrefs[i] := by
      simp [iterItem, seqItem_live_eq (i := i) hov (by simp), List.getElem?_eq_getElem hvi] at hx
      exact hx.symm
    subst hx'
    revert hdw
    generalize vrefs[i] = w
    intro hdw
    cases w with
    | ref r =>
      exact gavi_item sha gfp args n i L h' r x0.validators[i] x1 (CContract.refl _ _ _ h' hwf haw)
        hdw hL103 hL215 hL82
    | _ => simp [dec_Validator, containerFieldsT] at hdw
  simp only [Scope.env, List.drop_zero] at hcomp
  rw [show k + x0.validators.length + 10 + 66 + 1 = k + x0.validators.length + 77 by omega] at hcomp
  have hrd : get_active_validator_indices x0 ⟨x1⟩ = (ys.filterMapM f >>= fun r => pure r) := rfl
  rw [hrd]
  revert hcomp
  generalize compItems _ _ _ _ _ _ _ _ _ _ _ = R
  generalize ys.filterMapM f = F
  intro hcomp
  rcases R with e | ⟨vals, st, h'⟩ <;> rcases F with e' | bs
  · obtain ⟨he, hf⟩ := hcomp
    simp [ResultMatches, he, hf]
  · exact hcomp.elim
  · cases st <;> exact hcomp.elim
  · cases st
    · obtain ⟨hrel, hc, -, j, L', ⟨rfl, -⟩, -⟩ := hcomp
      have hv := listRel_uint hrel
      subst hv
      simp only [Except.bind_ok', Except.pure_ok', ResultMatches, allocPyList]
      refine ⟨⟨_, rfl, by rw [alloc_fst]; exact objs_alloc_self⟩, frame_alloc (Frame_refl _ _ _) hwf (Fresh_refl _),
        fresh_alloc (Fresh_refl _), noNewPaths_of_reach (reach_of_grows hwf haw ?_)⟩
      exact grows_alloc (grows_refl _ _ hwf (Nat.le_refl _)) (Nat.le_refl _) hwf
        (newObj_list (newVals_map_uint _ _ _ _))
    · exact hcomp.elim

theorem get_active_validator_indices_valid (gfp : Footprint) (h : Heap) (r0 : Nat) (x0 : BeaconState)
    (hy0 : dec_BeaconState h (.ref r0) = some x0) (x1 : Nat) (hwf : HeapWF h)
    (haw : ArgsWF h [(.ref r0), (.uint (.nominal Scope.Id.«Epoch» 64) x1)]) :
    ∃ N, ∀ fuel ≥ N,
      ResultMatches gfp [] h [(.ref r0), (.uint (.nominal Scope.Id.«Epoch» 64) x1)]
        (fun (rs : List ValidatorIndex) h' v => ∃ a, v = .ref a ∧ h'.objs a =
          some (.list .pyList .any none (rs.map fun x => .uint (.nominal Scope.Id.«ValidatorIndex» 64) x.val)))
        (interp (Scope.env sha) fuel Scope.Id.«get_active_validator_indices»
          [(.ref r0), (.uint (.nominal Scope.Id.«Epoch» 64) x1)] h)
        (get_active_validator_indices x0 ⟨x1⟩) :=
  ⟨x0.validators.length + 80, fun fuel hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    rw [← Nat.add_assoc]
    exact gavi_run sha gfp h r0 x0 hy0 x1 hwf haw k⟩

end SpecLean.Validation
