import SpecLean.Layer4.Fn
import SpecLean.Layer4.Steps
import SpecLean.Gen.Readable
import SpecLean.Validation.Tactic
import SpecLean.Bridge

/-!
# Layer 4 spike: two real spec functions

`denote_sound` instantiated on `is_active_validator` (reads only) and `increase_balance`
(`state.balances[index] += delta`, a write under `WTree`). For each function:

- `*_denote`: the denotation of the generated syntax tree (`SpecLean/Gen/Scope.lean`) equals the
  generated readable function (`SpecLean/Gen/Readable.lean`), on decoded values, by `simp`.
- `*_l4`: the contract of SPEC 9.2 against the interpreter, from `denote_sound` and `*_denote`.
  No step of the interpreter is unfolded here.

`increase_balance` needs no decoder of the whole `BeaconState`: its hypothesis is on the decoded
tree (`dec`), and the readable state enters only through `balances`. A full bridge from the typed
decoders (`dec_BeaconState`) to `dec` is per type, not per function; `dec_vdv` shows it for
`Validator`.
-/

namespace SpecLean.Layer4.Examples

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd SpecLean.Rd.Gen

-- The value rules as the denotation and the interpreter see them, not the global SSZ instance.
attribute [local instance high] LibModel.toLibValues

/-! ## The SSZ library coerces a flat value without the heap -/

theorem coerceFlat_ssz (env : Env) : CoerceFlat env := by
  intro field h t v hv
  simp only [coerceWith, LibModel.coerce, Ssz.coerce]
  cases t with
  | any => rfl
  | _ =>
    simp only [depthBound]
    rw [Ssz.coerceH.eq_def, Ssz.coerceH.eq_def]
    cases v <;> simp [Flat] at hv <;> (cases field <;> simp <;> rfl)

/-- A typed result: the denotation result is `f` of the readable result. -/
theorem resultMatches_map {gfp fp : Footprint} {h : Heap} {vs : List Value}
    {E : α → Heap → Value → Prop} {E' : β → Heap → Value → Prop} {f : β → α}
    {res : Res (Value × Heap)} {r : SpecM β} (hE : ∀ x h' v, E (f x) h' v → E' x h' v)
    (hm : ResultMatches gfp fp h vs E res (f <$> r)) : ResultMatches gfp fp h vs E' res r := by
  cases res with
  | ok p =>
    obtain ⟨v, h'⟩ := p
    cases r with
    | ok x => obtain ⟨he, rest⟩ := hm; exact ⟨hE x h' v he, rest⟩
    | error e => exact hm
  | error e => cases r with
    | ok x => exact hm
    | error e' => exact hm

theorem wtree_nil (h : Heap) (vs : List Value) : WTree h vs [] := by
  intro k pat hpat; simp at hpat

/-! ## `is_active_validator` -/

abbrev epochTy : UintTy := .nominal Scope.Id.«Epoch» 64

@[simp] theorem val_epoch (y : Epoch) : UintC.val y = y.val := rfl
@[simp] theorem val_gwei (y : Gwei) : UintC.val y = y.val := rfl

/-- The decoded tree of a `Validator`. -/
def vdv (x : Validator) : DV :=
  .cont Scope.Id.«Validator»
    [.leaf (.bytes Scope.Id.«BLSPubkey» (bd x.pubkey)),
     .leaf (.bytes Scope.Id.«Bytes32» (bd x.withdrawal_credentials)),
     .leaf (.uint (.nominal Scope.Id.«Gwei» 64) x.effective_balance.val),
     .leaf (.boolean x.slashed.val),
     .leaf (.uint epochTy x.activation_eligibility_epoch.val),
     .leaf (.uint epochTy x.activation_epoch.val),
     .leaf (.uint epochTy x.exit_epoch.val),
     .leaf (.uint epochTy x.withdrawable_epoch.val)]

/-- The denotation of the syntax tree is the readable function. -/
theorem is_active_validator_denote (sha : Oracle) (x : Validator) (e : Nat) :
    (denoteFn (Scope.env sha) [] Scope.fn_is_active_validator [vdv x, .leaf (.uint epochTy e)]).map
        (Except.mapError SpecError.fail) =
      some ((fun b => (Value.bool b, [vdv x, .leaf (.uint epochTy e)])) <$>
        is_active_validator x ⟨e⟩) := by
  simp [denoteFn, Scope.fn_is_active_validator, initLoc, slot, setLoc, dBlock, dStmt, dExpr, dCmp,
    dAttr, DSt.deref, subAt, vdv, DM.bind, DM.ok, Validation.Tactic.fieldIndex_lit, ofChild, cmpF,
    lift, resolveUint, cmpInt]
  by_cases h1 : x.activation_epoch.val ≤ e <;> by_cases h2 : e < x.exit_epoch.val <;>
    simp [h1, h2, Rd.Gen.is_active_validator, uv, Except.mapError, val_epoch] <;> omega

theorem decUintT_some [UintC α] {t : UintTy} {h : Heap} {v : Value} {y : α}
    (hy : decUintT t h v = some y) : v = .uint t (UintC.val y) := by
  unfold decUintT at hy
  split at hy
  · next t' n =>
    split at hy
    · next hc => cases hy; rw [hc.1, UintC.val_ofNat]
    · cases hy
  · cases hy

theorem decBytesT_some [BytesC α] {cls : Name} {h : Heap} {v : Value} {y : α}
    (hy : decBytesT cls h v = some y) : v = .bytes cls (BytesC.data y) := by
  unfold decBytesT at hy
  split at hy
  · next c b =>
    split at hy
    · next hc => cases hy; rw [hc.1, BytesC.data_ofBytes]
    · cases hy
  · cases hy

theorem decBooleanV_some {h : Heap} {v : Value} {y : Boolean} (hy : decBooleanV h v = some y) :
    v = .boolean y.val := by
  unfold decBooleanV at hy
  split at hy
  · cases hy; rfl
  · cases hy

/-- The typed decoder and `dec` agree on a `Validator` with its eight fields. -/
theorem dec_vdv (h : Heap) (r0 : Nat) (x : Validator) (fs : List Value)
    (hfs : h.objs r0 = some (.container Scope.Id.«Validator» fs)) (hl : fs.length = 8)
    (hy : dec_Validator h (.ref r0) = some x) : dec h 1 (.ref r0) = some (vdv x) := by
  match fs, hl with
  | [f0, f1, f2, f3, f4, f5, f6, f7], _ =>
    simp only [dec_Validator, containerFieldsT, hfs, Option.bind_eq_bind, Option.bind_eq_some_iff,
      ↓reduceIte, Option.some.injEq, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.bind_some, Option.pure_def, exists_eq_left'] at hy
    obtain ⟨a0, h0, a1, h1, a2, h2, a3, h3, a4, h4, a5, h5, a6, h6, a7, h7, rfl⟩ := hy
    rw [decBytesT_some h0, decBytesT_some h1, decUintT_some h2, decBooleanV_some h3,
      decUintT_some h4, decUintT_some h5, decUintT_some h6, decUintT_some h7] at hfs
    simp [dec, hfs, vdv, Flat, bd]

/-- SPEC 9.2 for `is_active_validator`, from the fragment theorem. -/
theorem is_active_validator_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (r0 : Nat)
    (x : Validator) (e : Nat) (fs : List Value)
    (hfs : h.objs r0 = some (.container Scope.Id.«Validator» fs)) (hl : fs.length = 8)
    (hy : dec_Validator h (.ref r0) = some x) :
    ∀ fuel, 5 ≤ fuel →
      ResultMatches gfp [] h [.ref r0, .uint epochTy e] (fun (b : Bool) _ v => v = .bool b)
        (interp (Scope.env sha) fuel Scope.Id.«is_active_validator» [.ref r0, .uint epochTy e] h)
        (is_active_validator x ⟨e⟩) := by
  intro fuel hf
  have hden := is_active_validator_denote sha x e
  cases hdn : denoteFn (Scope.env sha) [] Scope.fn_is_active_validator
      [vdv x, .leaf (.uint epochTy e)] with
  | none => simp [hdn] at hden
  | some r =>
    rw [hdn] at hden
    simp only [Option.map_some, Option.some.injEq] at hden
    have hdec : DecArgs h [.ref r0, .uint epochTy e] [vdv x, .leaf (.uint epochTy e)] := by
      refine ⟨rfl, fun k v d hv hd => ?_⟩
      match k, hv, hd with
      | 0, hv, hd =>
        simp at hv hd; subst hv; subst hd
        exact ⟨1, dec_vdv h r0 x fs hfs hl hy⟩
      | 1, hv, hd =>
        simp at hv hd; subst hv; subst hd
        exact ⟨0, dec_flat rfl 0⟩
      | _ + 2, hv, _ => simp at hv
    have hm := denote_sound (Scope.env sha) (coerceFlat_ssz _) gfp [] (f := Scope.Id.«is_active_validator»)
      (by simp only [Scope.env, Validation.Tactic.lookup_lit]) hdec
      (wtree_nil h _) hdn fuel (by simp [Scope.fn_is_active_validator, bDep, sDep, eDep, cDep]; omega)
    rw [hden] at hm
    exact resultMatches_map (fun b h' v he => he.1) hm

/-! ## `increase_balance` -/

abbrev gweiTy : UintTy := .nominal Scope.Id.«Gwei» 64
abbrev vidxTy : UintTy := .nominal Scope.Id.«ValidatorIndex» 64

/-- A decoded balance. -/
def gleaf (g : Gwei) : DV := .leaf (.uint gweiTy g.val)

/-- `Footprint increase_balance`: the balances list of the state. -/
def ibFp : Footprint := [⟨Scope.Id.«BeaconState», [.exact 12]⟩]

@[simp] theorem val_vidx (y : ValidatorIndex) : UintC.val y = y.val := rfl

theorem add_gwei (a b : Nat) :
    @binopVal LibModel.toLibValues .add (.uint gweiTy a) (.uint gweiTy b) =
      if a + b < 2 ^ 64 then .ok (.uint gweiTy (a + b)) else .error .sszValue := by
  have := binop_add (t := gweiTy) (t' := gweiTy) (r := gweiTy) rfl rfl a b
  unfold chkAdd chkRange at this
  by_cases hab : a + b < 2 ^ 64
  · rw [if_pos hab] at this ⊢; exact this
  · rw [if_neg hab] at this ⊢; exact this

theorem coerceH_gwei (env : Env) (n : Nat) :
    Ssz.coerceH env false depthBound Heap.empty (.uint gweiTy) (.uint gweiTy n) =
      .ok (.uint gweiTy n, Heap.empty) := by
  rw [show depthBound = 63 + 1 from rfl, coerceH_plain _ _ _ _ _ _ (fun _ e => by cases e)]
  simp [coerceElem]

theorem uOp_add_gwei (a b : Nat) :
    (uOp .add (a : Int) (b : Int) : SpecM Gwei) =
      if a + b < 2 ^ 64 then .ok ⟨a + b⟩ else .error .bug := by
  unfold uOp uOf
  simp only [intArith, erase, Except.mapError]
  by_cases h : a + b < 2 ^ 64
  · rw [if_pos h]
    have : (0 : Int) ≤ a + b ∧ (a : Int) + b < 2 ^ UintC.bits Gwei := ⟨by omega, by
      show (a : Int) + b < 2 ^ 64; exact_mod_cast h⟩
    simp only [Except.bind_ok', this, and_self, ↓reduceIte]
    rfl
  · rw [if_neg h]
    have : ¬ ((0 : Int) ≤ a + b ∧ (a : Int) + b < 2 ^ UintC.bits Gwei) := fun hc => h (by
      have := hc.2; change (a : Int) + b < 2 ^ 64 at this; exact_mod_cast this)
    simp only [Except.bind_ok', this, ↓reduceIte]
    rfl

/-! The three cases of `increase_balance`, on each side. -/

theorem ib_den_ok (sha : Oracle) (ds : List DV) (k : ListKind) (l : Option Nat) (st : BeaconState)
    (i δ : Nat)
    (hb : ds[12]? = some (.list k (.uint gweiTy) l (st.balances.map gleaf)))
    (hi : i < st.balances.length) (hov : st.balances[i].val + δ < 2 ^ 64) :
    denoteFn (Scope.env sha) ibFp Scope.fn_increase_balance
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)] =
      some (.ok (Value.none,
        [.cont Scope.Id.«BeaconState» (ds.set 12 (.list k (.uint gweiTy) l
            ((st.balances.set i ⟨st.balances[i].val + δ⟩).map gleaf))),
          .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)])) := by
  have hm : (List.map gleaf st.balances)[i]? = some (.leaf (.uint gweiTy st.balances[i].val)) := by
    simp [List.getElem?_eq_getElem hi, gleaf]
  have hadd : binopVal .add (.uint gweiTy st.balances[i].val) (.uint gweiTy δ) =
      .ok (.uint gweiTy (st.balances[i].val + δ)) := by rw [add_gwei, if_pos hov]
  simp only [denoteFn, Scope.fn_increase_balance, dBlock, dStmt]
  rw [dAugIndex_eval (k := 0) (p := [12]) (kd := k) (el := .uint gweiTy) (ll := l)
    (ds := List.map gleaf st.balances) (iv := .uint vidxTy i) (j := (i : Int)) (m := i)
    (cur := .uint gweiTy st.balances[i].val) (rv := .uint gweiTy δ)
    (v := .uint gweiTy (st.balances[i].val + δ)) (v' := .uint gweiTy (st.balances[i].val + δ))
    (by simp [dExpr, dAttr, initLoc, setLoc, slot, DSt.deref, subAt, DV.kids, DM.bind, DM.ok,
      Validation.Tactic.fieldIndex_lit, hb, ofChild])
    (by simp [dExpr, initLoc, setLoc, slot, DM.ok])
    (by simp [DSt.deref, subAt, DV.kids, hb])
    (by simp [isByteList])
    (by simp)
    (by simp [normIndex_nat, hi])
    hm
    (by simp [dExpr, initLoc, setLoc, slot, DM.ok])
    hadd
    rfl
    (by simp [dCoerce, lift, coerceWith, LibModel.coerce, Ssz.coerce, coerceH_gwei])]
  simp [dWrite, Flat, fpOk, ibFp, rootIs, matchesB, leafAt, subAt, DV.kids, hb, hm, updAt,
    DM.bind, DM.ok, List.map_set, gleaf]

theorem ib_den_overflow (sha : Oracle) (ds : List DV) (k : ListKind) (l : Option Nat) (st : BeaconState)
    (i δ : Nat)
    (hb : ds[12]? = some (.list k (.uint gweiTy) l (st.balances.map gleaf)))
    (hi : i < st.balances.length) (hov : ¬ st.balances[i].val + δ < 2 ^ 64) :
    denoteFn (Scope.env sha) ibFp Scope.fn_increase_balance
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)] = some (.error .sszValue) := by
  have hm : (List.map gleaf st.balances)[i]? = some (.leaf (.uint gweiTy st.balances[i].val)) := by
    simp [List.getElem?_eq_getElem hi, gleaf]
  have hadd : binopVal .add (.uint gweiTy st.balances[i].val) (.uint gweiTy δ) = .error .sszValue := by
    rw [add_gwei, if_neg hov]
  simp only [denoteFn, Scope.fn_increase_balance, dBlock, dStmt]
  rw [dAugIndex_err (k := 0) (p := [12]) (kd := k) (el := .uint gweiTy) (ll := l)
    (ds := List.map gleaf st.balances) (iv := .uint vidxTy i) (j := (i : Int))
    (by simp [dExpr, dAttr, initLoc, setLoc, slot, DSt.deref, subAt, DM.bind, DM.ok,
      Validation.Tactic.fieldIndex_lit, hb, ofChild])
    (by simp [dExpr, initLoc, setLoc, slot, DM.ok])
    (by simp [DSt.deref, subAt, DV.kids, hb])
    (by simp [isByteList])
    (by simp)
    (by simp [normIndex_nat, hi]) hm (by simp [dExpr, initLoc, setLoc, slot, DM.ok]) hadd (by decide)]
  simp [DM.bind]

theorem ib_den_index (sha : Oracle) (ds : List DV) (k : ListKind) (l : Option Nat) (st : BeaconState)
    (i δ : Nat)
    (hb : ds[12]? = some (.list k (.uint gweiTy) l (st.balances.map gleaf)))
    (hi : ¬ i < st.balances.length) :
    denoteFn (Scope.env sha) ibFp Scope.fn_increase_balance
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)] = some (.error .indexError) := by
  simp only [denoteFn, Scope.fn_increase_balance, dBlock, dStmt]
  rw [dAugIndex_oob (k := 0) (p := [12]) (kd := k) (el := .uint gweiTy) (ll := l)
    (ds := List.map gleaf st.balances) (iv := .uint vidxTy i) (j := (i : Int))
    (by simp [dExpr, dAttr, initLoc, setLoc, slot, DSt.deref, subAt, DM.bind, DM.ok,
      Validation.Tactic.fieldIndex_lit, hb, ofChild])
    (by simp [dExpr, initLoc, setLoc, slot, DM.ok])
    (by simp [DSt.deref, subAt, DV.kids, hb])
    (by simp [isByteList])
    (by simp)
    (by simp [normIndex_nat, hi])]
  simp [DM.bind]

theorem ib_read_ok (st : BeaconState) (i δ : Nat) (hi : i < st.balances.length)
    (hov : st.balances[i].val + δ < 2 ^ 64) :
    increase_balance st ⟨i⟩ ⟨δ⟩ = .ok { st with balances := st.balances.set i ⟨st.balances[i].val + δ⟩ } := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  have hov' : st.balances[i].val + δ < 18446744073709551616 := hov
  simp [increase_balance, lget, lset, Rd.pyIndex, uv, uOp_add_gwei, hneg, hi, hov',
    List.getElem?_eq_getElem hi]

theorem ib_read_overflow (st : BeaconState) (i δ : Nat) (hi : i < st.balances.length)
    (hov : ¬ st.balances[i].val + δ < 2 ^ 64) : increase_balance st ⟨i⟩ ⟨δ⟩ = .error .bug := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  have hov' : ¬ st.balances[i].val + δ < 18446744073709551616 := hov
  simp [increase_balance, lget, lset, Rd.pyIndex, uv, uOp_add_gwei, hneg, hi, hov',
    List.getElem?_eq_getElem hi]

theorem ib_read_index (st : BeaconState) (i δ : Nat) (hi : ¬ i < st.balances.length) :
    increase_balance st ⟨i⟩ ⟨δ⟩ = .error .invalid := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  simp [increase_balance, lget, Rd.pyIndex, uv, hneg, hi]

/-- The denotation of the syntax tree is the readable function, on the balances field. Every
other field of the state is unchanged on both sides. -/
theorem increase_balance_denote (sha : Oracle) (ds : List DV) (k : ListKind) (l : Option Nat) (st : BeaconState)
    (i δ : Nat)
    (hb : ds[12]? = some (.list k (.uint gweiTy) l (st.balances.map gleaf))) :
    (denoteFn (Scope.env sha) ibFp Scope.fn_increase_balance
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)]).map (Except.mapError SpecError.fail) =
      some ((fun st' : BeaconState => (Value.none,
        [.cont Scope.Id.«BeaconState» (ds.set 12 (.list k (.uint gweiTy) l (st'.balances.map gleaf))),
          .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)])) <$> increase_balance st ⟨i⟩ ⟨δ⟩) := by
  by_cases hi : i < st.balances.length
  · by_cases hov : st.balances[i].val + δ < 2 ^ 64
    · rw [ib_den_ok sha ds k l st i δ hb hi hov, ib_read_ok st i δ hi hov]; rfl
    · rw [ib_den_overflow sha ds k l st i δ hb hi hov, ib_read_overflow st i δ hi hov]; rfl
  · rw [ib_den_index sha ds k l st i δ hb hi, ib_read_index st i δ hi]; rfl

/-- SPEC 9.2 for `increase_balance`, from the fragment theorem: under `WTree` over its footprint,
the result heap decodes to the state tree with the readable result's balances. -/
theorem increase_balance_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (r0 : Nat) (n : Nat)
    (ds : List DV) (k : ListKind) (l : Option Nat) (st : BeaconState) (i δ : Nat)
    (hd : dec h n (.ref r0) = some (.cont Scope.Id.«BeaconState» ds))
    (hb : ds[12]? = some (.list k (.uint gweiTy) l (st.balances.map gleaf)))
    (hw : WTree h [.ref r0, .uint vidxTy i, .uint gweiTy δ] ibFp) :
    ∀ fuel, 5 ≤ fuel →
      ResultMatches gfp ibFp h [.ref r0, .uint vidxTy i, .uint gweiTy δ]
        (fun (st' : BeaconState) h' v => v = .none ∧
          ∃ m, dec h' m (.ref r0) =
            some (.cont Scope.Id.«BeaconState» (ds.set 12 (.list k (.uint gweiTy) l (st'.balances.map gleaf)))))
        (interp (Scope.env sha) fuel Scope.Id.«increase_balance» [.ref r0, .uint vidxTy i, .uint gweiTy δ] h)
        (increase_balance st ⟨i⟩ ⟨δ⟩) := by
  intro fuel hf
  have hden := increase_balance_denote sha ds k l st i δ hb
  cases hdn : denoteFn (Scope.env sha) ibFp Scope.fn_increase_balance
      [.cont Scope.Id.«BeaconState» ds, .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)] with
  | none => simp [hdn] at hden
  | some r =>
    rw [hdn] at hden
    simp only [Option.map_some, Option.some.injEq] at hden
    have hdec : DecArgs h [.ref r0, .uint vidxTy i, .uint gweiTy δ]
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint vidxTy i), .leaf (.uint gweiTy δ)] := by
      refine ⟨rfl, fun k v d hv hd' => ?_⟩
      match k, hv, hd' with
      | 0, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨n, hd⟩
      | 1, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨0, dec_flat rfl 0⟩
      | 2, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨0, dec_flat rfl 0⟩
      | _ + 3, hv, _ => simp at hv
    have hm := denote_sound (Scope.env sha) (coerceFlat_ssz _) gfp ibFp (f := Scope.Id.«increase_balance»)
      (by simp only [Scope.env, Validation.Tactic.lookup_lit]) hdec hw hdn fuel
      (by simp [Scope.fn_increase_balance, bDep, sDep, eDep, tDep]; omega)
    rw [hden] at hm
    refine resultMatches_map (fun st' h' v he => ⟨he.1, ?_⟩) hm
    obtain ⟨-, hr⟩ := he.2
    exact hr 0 (.ref r0) _ rfl rfl

end SpecLean.Layer4.Examples
