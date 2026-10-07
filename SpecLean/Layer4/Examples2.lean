import SpecLean.Layer4.DenStmt
import SpecLean.Layer4.DenSteps
import SpecLean.Layer4.Examples
import SpecLean.FuelMono

/-!
# Layer 4: three spec functions with calls

`denote_sound_calls` instantiated on three functions of the generated scope. Each callee has a
summary lemma at any fuel from a bound on: its denotation on decoded arguments. A caller's proof
rewrites with the summaries of its callees and never unfolds them, as Aeneas does with function
specifications.

- `get_current_epoch` calls `compute_epoch_at_slot`, which calls the class `Epoch`.
- `get_previous_epoch` calls `saturating_sub(get_current_epoch(state), 1)`: nested calls, with the
  state passed to a callee as a place.
- `decrease_balance` writes `state.balances[index]` with the result of a call of
  `saturating_sub`.

For each: `*_den` (the summary), `*_read` (the readable function on the same inputs), `*_denote`
(the denotation equals the readable function) and `*_l4` (SPEC 9.2 against the interpreter at any
fuel from the bound on).

`fpsEx` is the footprint table: `decrease_balance` writes the balances list, the others write
nothing.
-/

namespace SpecLean.Layer4.Examples2

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd SpecLean.Rd.Gen

/-! ## The SSZ library -/

theorem bind_pair (h : Heap) (W : Res Value) :
    (do pure (← W, h) : Res (Value × Heap)) =
      (fun x => (x.1, h)) <$> (do pure (← W, Heap.empty) : Res (Value × Heap)) := by
  cases W <;> rfl

theorem constructFlat_ssz (env : Env) : ConstructFlat env := by
  intro h t vs hc hv
  cases t
  case bytes ty len =>
    simp only [LibModel.construct, Ssz.construct]
    match vs, hv with
    | [], _ => rfl
    | [v], hv =>
      have hfv : Flat v = true := hv v (by simp)
      cases v <;> simp [Flat] at hfv <;> simp [iterElems, iterBase] <;> (try split) <;> rfl
    | a :: b :: c, _ => split <;> first | rfl | (simp_all; done) | (exfalso; simp_all)
  all_goals (simp [ctorFlat] at hc <;> simp only [LibModel.construct, Ssz.construct] <;>
    split <;> first | rfl | exact bind_pair h _ | contradiction | (simp_all; done) | (exfalso; simp_all))

theorem coerceH_flat2 (env : Env) (b : Bool) (d : Nat) (h : Heap) (t : SszTy) (v : Value)
    (ht : ∀ ty, t ≠ .container ty) (hl : ∀ k e l, t ≠ .list k e l) (ha : t ≠ .any)
    (hv : ∀ a, v ≠ .ref a) (hv' : ∀ xs, v ≠ .tuple xs) :
    Ssz.coerceH env b (d + 1) h t v =
      (fun x => (x, h)) <$> (if b then coerceField t v else coerceElem t v) := by
  rw [Ssz.coerceH.eq_def]
  cases t <;> first
    | exact absurd rfl (ht _) | exact absurd rfl (hl _ _ _) | exact absurd rfl ha
    | (cases v <;> first | exact absurd rfl (hv _) | exact absurd rfl (hv' _) |
        (cases b <;> simp <;> rfl))

/-- The fields of a container from keyword arguments, as `construct` builds them. -/
theorem build_kw (env : Env) (h : Heap) (kvs : List (Name × Value)) :
    ∀ (fs : List (Name × SszTy)) (r : Res (List Value)), kwFields kvs fs = some r →
      Ssz.construct.build env h (fs.zip (fs.map fun f => kwArg kvs f.1)) = (fun ws => (ws, h)) <$> r
  | [], r, hk => by simp [kwFields, DM.ok] at hk; subst hk; rfl
  | (f, ft) :: fs, r, hk => by
    simp only [kwFields] at hk
    split at hk
    · next v hv =>
      split at hk
      · next hft =>
        simp only [Bool.and_eq_true] at hft
        obtain ⟨hft, hfv⟩ := hft
        have hc : Ssz.coerceH env true depthBound h ft v = (fun x => (x, h)) <$> coerceField ft v := by
          have := coerceH_flat2 env true 63 h ft v
            (by intro ty e; subst e; simp [flatTy] at hft) (by intro k e l e'; subst e'; simp [flatTy] at hft)
            (by intro e; subst e; simp [flatTy] at hft) (flat_nonref hfv)
            (by intro xs e; subst e; simp [Flat] at hfv)
          simpa [depthBound] using this
        have hv' : kwArg kvs f = some v := hv
        simp only [List.map_cons, List.zip_cons_cons, Ssz.construct.build, hv', hc]
        rcases bind_case hk with ⟨err, hl, rfl⟩ | ⟨w, hl, hk2⟩
        · obtain ⟨hr, -⟩ := lift_some hl
          rw [← hr]; rfl
        · obtain ⟨hr, -⟩ := lift_some hl
          rw [← hr]
          split at hk2
          · rcases bind_case hk2 with ⟨err, hl2, rfl⟩ | ⟨ws, hl2, hk3⟩
            · simp only [show ((fun x => (x, h)) <$> (Except.ok w : Except SpecError Value)) = .ok (w, h)
                from rfl, Except.bind_ok']
              rw [build_kw env h kvs fs _ hl2]; rfl
            · simp [DM.ok] at hk3; subst hk3
              simp only [show ((fun x => (x, h)) <$> (Except.ok w : Except SpecError Value)) = .ok (w, h)
                from rfl, Except.bind_ok']
              rw [build_kw env h kvs fs _ hl2]; rfl
          · cases hk2
      · cases hk
    · cases hk

theorem kwctor_ssz (env : Env) (h : Heap) (ty : Name) (fs : List (Name × SszTy))
    (kvs : List (Name × Value)) (r : Res (List Value)) (hfs : env.containers.lookup ty = some fs)
    (hall : kvs.all (fun kv => (fs.map (·.1)).contains kv.1) = true) (hk : kwFields kvs fs = some r) :
    LibModel.construct env h (.container ty) [] kvs =
      (fun ws => (Value.ref (h.alloc (.container ty ws)).1, (h.alloc (.container ty ws)).2)) <$> r := by
  show Ssz.construct env h (.container ty) [] kvs = _
  have hcf : ctorFields (fs.map (·.1)) [] kvs = .ok (fs.map fun f => kwArg kvs f.1) := by
    have hany : kvs.any (fun kv => !(fs.map (·.1)).contains kv.1) = false := by
      simpa [List.all_eq, List.any_eq] using hall
    simp only [ctorFields, List.length_nil, List.length_map, Nat.not_lt_zero, ↓reduceIte]
    simp only [List.any_eq_false, Bool.not_eq_true'] at hany
    have : (kvs.any fun x => !(fs.map (·.1)).contains x.1) = false := by
      simpa [List.any_eq_false] using hany
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq]
    apply List.ext_getElem? ; intro i
    simp [List.getElem?_map, List.getElem?_zipIdx]
    cases fs[i]? <;> rfl
  simp only [Ssz.construct, hfs, hcf, Except.bind_ok', build_kw env h kvs fs r hk]
  cases r <;> rfl

/-! The arity of the callees of the examples. -/

@[simp] theorem exlen_apply_withdrawals : Scope.fn_apply_withdrawals.params.names.length = 2 := Eq.trans rfl rfl
@[simp] theorem exdef_apply_withdrawals : Scope.fn_apply_withdrawals.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_compute_epoch_at_slot : Scope.fn_compute_epoch_at_slot.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_compute_epoch_at_slot : Scope.fn_compute_epoch_at_slot.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_convert_validator_index_to_builder_index : Scope.fn_convert_validator_index_to_builder_index.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_convert_validator_index_to_builder_index : Scope.fn_convert_validator_index_to_builder_index.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_decrease_balance : Scope.fn_decrease_balance.params.names.length = 3 := Eq.trans rfl rfl
@[simp] theorem exdef_decrease_balance : Scope.fn_decrease_balance.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_get_active_validator_indices : Scope.fn_get_active_validator_indices.params.names.length = 2 := Eq.trans rfl rfl
@[simp] theorem exdef_get_active_validator_indices : Scope.fn_get_active_validator_indices.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_get_current_epoch : Scope.fn_get_current_epoch.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_get_current_epoch : Scope.fn_get_current_epoch.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_get_max_effective_balance : Scope.fn_get_max_effective_balance.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_get_max_effective_balance : Scope.fn_get_max_effective_balance.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_get_previous_epoch : Scope.fn_get_previous_epoch.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_get_previous_epoch : Scope.fn_get_previous_epoch.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_has_compounding_withdrawal_credential : Scope.fn_has_compounding_withdrawal_credential.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_has_compounding_withdrawal_credential : Scope.fn_has_compounding_withdrawal_credential.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_increase_balance : Scope.fn_increase_balance.params.names.length = 3 := Eq.trans rfl rfl
@[simp] theorem exdef_increase_balance : Scope.fn_increase_balance.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_is_active_validator : Scope.fn_is_active_validator.params.names.length = 2 := Eq.trans rfl rfl
@[simp] theorem exdef_is_active_validator : Scope.fn_is_active_validator.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_is_builder_index : Scope.fn_is_builder_index.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_is_builder_index : Scope.fn_is_builder_index.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_is_compounding_withdrawal_credential : Scope.fn_is_compounding_withdrawal_credential.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_is_compounding_withdrawal_credential : Scope.fn_is_compounding_withdrawal_credential.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_process_effective_balance_updates : Scope.fn_process_effective_balance_updates.params.names.length = 1 := Eq.trans rfl rfl
@[simp] theorem exdef_process_effective_balance_updates : Scope.fn_process_effective_balance_updates.params.defaults.length = 0 := Eq.trans rfl rfl
@[simp] theorem exlen_saturating_sub : Scope.fn_saturating_sub.params.names.length = 2 := Eq.trans rfl rfl
@[simp] theorem exdef_saturating_sub : Scope.fn_saturating_sub.params.defaults.length = 0 := Eq.trans rfl rfl

/-- The method names that the SSZ model checks before `append` differ from it. -/
def NmOK (env : Env) : Prop :=
  env.nm.append ≠ env.nm.extend ∧ env.nm.append ≠ env.nm.copy ∧ env.nm.append ≠ env.nm.hashTreeRoot

theorem append_ssz (env : Env) (hn : NmOK env) (h : Heap) (a : Nat) (k : ListKind) (e : SszTy)
    (l : Option Nat) (xs : List Value) (v : Value) (ho : h.objs a = some (.list k e l xs))
    (hap : appendable k e = true) :
    applyMethod env h (.ref a) env.nm.append [v] =
      (coerceWith env false h e v).bind fun x =>
        (Ssz.checkLength k l (xs.length + 1)).bind fun _ =>
          .ok (.none, x.2.set a (.list k e l (xs ++ [x.1]))) := by
  obtain ⟨n1, n2, n3⟩ := hn
  simp only [appendable, decide_eq_true_eq] at hap
  obtain ⟨hk, he, hb⟩ := hap
  have hpy : k ≠ .pyList := by rcases hk with rfl | rfl <;> simp
  have hm : LibModel.method env h (.ref a) env.nm.append [v] = none := by
    show Ssz.method env h (.ref a) env.nm.append [v] = none
    simp [Ssz.method, ho, n1, n2, n3]
  have hc : coerceWith env false h e v = Ssz.coerceH env false depthBound h e v := by
    unfold coerceWith
    show (match Ssz.coerce env false h e v with | some r => r | none => .ok (v, h)) = _
    cases e <;> first | exact absurd rfl he | rfl
  have happ : appendItem env h a v =
      (coerceWith env false h e v).bind fun x =>
        (Ssz.checkLength k l (xs.length + 1)).bind fun _ => .ok (x.2.set a (.list k e l (xs ++ [x.1]))) := by
    unfold appendItem
    show (match Ssz.append env h a v with | some r => r | none => _) = _
    rw [hc]
    rcases hk with rfl | rfl
    · have : ¬ (e = .uint (.width 8)) := fun h' => hb ⟨rfl, h'⟩
      simp only [Ssz.append, ho]
      split
      · simp_all
      · rfl
    · simp only [Ssz.append, ho]; rfl
  unfold applyMethod
  rw [hm]
  simp only [ho]
  split
  · next heq =>
    simp only [Option.some.injEq, HeapObj.list.injEq] at heq
    exact absurd ⟨heq.1, heq.2.1⟩ hb
  · next heq =>
    simp only [Option.some.injEq, HeapObj.list.injEq] at heq
    obtain ⟨-, -, -, rfl⟩ := heq
    simp only [if_true, happ]
    cases coerceWith env false h e v with
    | error _ => rfl
    | ok x =>
      cases Ssz.checkLength k l (xs.length + 1) <;> rfl
  all_goals (simp_all <;> (exfalso; rename_i hx; exact hx _ _ _ _ rfl rfl rfl rfl))

theorem coerceCont_ssz (env : Env) (h : Heap) (b : Nat) (ty : Name) (fs : List Value)
    (ho : h.objs b = some (.container ty fs)) :
    coerceWith env false h (.container ty) (.ref b) = .ok (.ref b, h) := by
  show (match Ssz.coerce env false h (.container ty) (.ref b) with
    | some r => r | none => Except.ok (Value.ref b, h)) = _
  simp only [Ssz.coerce]
  rw [show depthBound = 63 + 1 from rfl, Ssz.coerceH]
  simp [ho]

theorem nmOK_scope (sha : Oracle) : NmOK (Scope.env sha) := by
  simp only [NmOK, Scope.env]; decide

/-- The `hash_tree_root` oracle reads only the decoded content of a value. -/
def HtrDec (env : Env) : Prop :=
  ∀ h v h' v' n n' d, dec h n v = some d → dec h' n' v' = some d →
    env.hashTreeRoot h v = env.hashTreeRoot h' v'

theorem libFlat_ssz (env : Env) (hn : NmOK env) (hh : HtrDec env) : LibFlat env :=
  ⟨Examples.coerceFlat_ssz env, constructFlat_ssz env, fun h b args kws hb => by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [LibModel.builtin, Ssz.builtin],
   fun h ty fs kvs r hfs hall hk => kwctor_ssz env h ty fs kvs r hfs hall hk,
   fun h a k e l xs v ho hap => append_ssz env hn h a k e l xs v ho hap,
   fun h g args hg => by show Ssz.method env h (.glob g) env.nm.fromBytes args = none; simp [Ssz.method, hg],
   fun h v => rfl, hh,
   fun h b ty fs ho => coerceCont_ssz env h b ty fs ho⟩

-- The value rules as the denotation and the interpreter see them.
attribute [local instance high] LibModel.toLibValues

/-! ## `get_current_epoch` -/

abbrev slotTy : UintTy := .nominal Scope.Id.«Slot» 64
abbrev epTy : UintTy := .nominal Scope.Id.«Epoch» 64

/-- The footprints of the examples, by name id: `decrease_balance` (89) writes the balances,
`process_effective_balance_updates` (532) each validator, `apply_withdrawals` (90) the balances
and each builder. The others write nothing. -/
def fpsEx : Name → Footprint := fun g =>
  if g = 89 then [⟨Scope.Id.«BeaconState», [.exact 12]⟩]
  else if g = 532 then [⟨Scope.Id.«BeaconState», [.exact 11, .any]⟩]
  else if g = 90 then [⟨Scope.Id.«BeaconState», [.exact 12]⟩, ⟨Scope.Id.«BeaconState», [.exact 38, .any]⟩]
  else []

theorem div_slot (a : Nat) (ha : a < 2 ^ 64) :
    @binopVal LibModel.toLibValues .floorDiv (.uint slotTy a) (.uint slotTy 8) = .ok (.uint slotTy (a / 8)) := by
  have := binop_floorDiv (t := slotTy) (t' := slotTy) (r := slotTy) rfl rfl a 8
  rw [chkDiv, if_neg (by decide), chkRange_ok (by omega)] at this
  exact this

theorem ctor_epoch (env : Env) (h : Heap) (x : Nat) (hx : x < 2 ^ 64) :
    LibModel.construct env h (.uint epTy) [.uint slotTy x] [] = .ok (.uint epTy x, h) := by
  show (do pure (← wrapUint epTy x, h)) = _
  rw [wrap_nat (t := epTy) rfl, chkRange_ok hx]; rfl

theorem ceas_den (sha : Oracle) (fp : Footprint) (m a : Nat) (ha : a < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 8)).fn fp Scope.fn_compute_epoch_at_slot [.leaf (.uint slotTy a)] =
      some (.ok (.val (.uint epTy (a / 8)), [.leaf (.uint slotTy a)])) := by
  have hd : a / 8 < 2 ^ 64 := by omega
  have hb : dBinop .floorDiv (.val (.uint slotTy a)) (.val (.uint (.nominal 196 64) 8)) =
      some (.ok (.val (.uint slotTy (a / 8)))) := dBinop_eval (div_slot a ha) rfl
  have hc : dCtor (Scope.env sha) (.uint (.nominal 140 64)) [.val (.uint slotTy (a / 8))] =
      some (.ok (.val (.uint epTy (a / 8)))) := dCtor_eval rfl rfl (ctor_epoch _ _ _ hd) rfl
  simp [fnStep, noneDefaults, Scope.fn_compute_epoch_at_slot, Sem.block, blockOf, stmtStep, exprStep, callHead,
    callable, Validation.Tactic.lookup_lit, DM.bind, DM.ok, initLoc, setLoc, slot,
    argsOf, dCallRO, padNone, dGlobal, hb, hc, Flat]

theorem gce_den (sha : Oracle) (fp : Footprint) (m : Nat) (ds : List DV) (a : Nat)
    (hs : ds[2]? = some (.leaf (.uint slotTy a))) (ha : a < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 12)).fn fp Scope.fn_get_current_epoch [.cont Scope.Id.«BeaconState» ds] =
      some (.ok (.val (.uint epTy (a / 8)), [.cont Scope.Id.«BeaconState» ds])) := by
  have hc := ceas_den sha [] (m + 1) a ha
  rw [show m + 1 + 8 = m + 9 by omega] at hc
  rw [den_fn]
  simp [-den_fn, hc, fnStep, noneDefaults, Scope.fn_get_current_epoch, Sem.block, blockOf, stmtStep, exprStep, callHead,
    callable, Validation.Tactic.lookup_lit, DM.bind, DM.ok, initLoc, setLoc, slot,
    argsOf, dCallRO, padNone, dAttr, DSt.deref, subAt, DV.kids, hs, ofChild, fpsEx, argRoot, Scope.Id.«decrease_balance»,
    Validation.Tactic.fieldIndex_lit, Flat]

theorem uOf_ok [UintC α] (n : Nat) (hn : n < 2 ^ UintC.bits α) :
    (uOf α (n : Int) : SpecM α) = .ok (UintC.ofNat n) := by
  unfold uOf
  rw [if_pos ⟨Int.natCast_nonneg n, by exact_mod_cast hn⟩]
  simp

theorem fdiv_nat (a b : Nat) : (a : Int).fdiv (b : Int) = ((a / b : Nat) : Int) := by
  rw [Int.fdiv_eq_ediv, if_pos (.inl (Int.natCast_nonneg b))]
  simp only [Int.sub_zero]
  exact (Int.natCast_ediv a b).symm

theorem ceas_read (a : Nat) (ha : a < 2 ^ 64) : compute_epoch_at_slot ⟨a⟩ = .ok ⟨a / 8⟩ := by
  have hi : intArith .floorDiv (uv (⟨a⟩ : Slot)) (uv SLOTS_PER_EPOCH) = .ok ((a / 8 : Nat) : Int) := by
    show intArith .floorDiv (a : Int) ((8 : Nat) : Int) = _
    simp only [intArith]
    rw [if_neg (by decide), fdiv_nat]
  have h1 : (uOp .floorDiv (uv (⟨a⟩ : Slot)) (uv SLOTS_PER_EPOCH) : SpecM Slot) = .ok ⟨a / 8⟩ := by
    unfold uOp
    rw [hi, show erase (.ok ((a / 8 : Nat) : Int) : Res Int) = (.ok _ : SpecM Int) from rfl,
      Except.bind_ok', uOf_ok (α := Slot) (a / 8) (by show a / 8 < 2 ^ 64; omega)]
    rfl
  have h2 : (uCast Epoch (⟨a / 8⟩ : Slot) : SpecM Epoch) = .ok ⟨a / 8⟩ :=
    uOf_ok (α := Epoch) (a / 8) (by show a / 8 < 2 ^ 64; omega)
  unfold compute_epoch_at_slot
  rw [h1]
  simp only [Except.bind_ok']
  rw [h2]
  rfl

theorem gce_read (st : BeaconState) (ha : st.slot.val < 2 ^ 64) :
    get_current_epoch st = .ok ⟨st.slot.val / 8⟩ := by
  unfold get_current_epoch
  rw [show st.slot = ⟨st.slot.val⟩ from rfl, ceas_read _ ha]
  rfl

/-- The denotation of `get_current_epoch` is the readable function. -/
theorem get_current_epoch_denote (sha : Oracle) (fp : Footprint) (m : Nat) (ds : List DV)
    (st : BeaconState) (hs : ds[2]? = some (.leaf (.uint slotTy st.slot.val)))
    (ha : st.slot.val < 2 ^ 64) :
    ((den (Scope.env sha) fpsEx (m + 12)).fn fp Scope.fn_get_current_epoch
        [.cont Scope.Id.«BeaconState» ds]).map (Except.mapError SpecError.fail) =
      some ((fun e : Epoch => (DRes.val (Value.uint epTy e.val), [DV.cont Scope.Id.«BeaconState» ds])) <$>
        get_current_epoch st) := by
  rw [gce_den sha fp m ds _ hs ha, gce_read st ha]; rfl

/-- More fuel gives the same result. -/
theorem resultMatches_mono {env : Env} {gfp fp : Footprint} {h : Heap} {vs : List Value}
    {E : α → Heap → Value → Prop} {f : Name} {n fuel : Nat} (hf : n ≤ fuel) {r : SpecM α}
    (hm : ResultMatches gfp fp h vs E (interp env n f vs h) r) :
    ResultMatches gfp fp h vs E (interp env fuel f vs h) r := by
  have hne : interp env n f vs h ≠ .error .outOfFuel := by
    intro e; rw [e] at hm
    cases r with
    | ok _ => exact hm
    | error _ => exact hm.1 rfl
  rw [SpecLean.Mono.interp_fuel_mono env n fuel hf f vs h hne]; exact hm

/-- SPEC 9.2 for `get_current_epoch`, through its call of `compute_epoch_at_slot`. -/
theorem get_current_epoch_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h)
    (hh : HtrDec (Scope.env sha)) (r0 n : Nat)
    (ds : List DV) (st : BeaconState) (hd : dec h n (.ref r0) = some (.cont Scope.Id.«BeaconState» ds))
    (hs : ds[2]? = some (.leaf (.uint slotTy st.slot.val))) (ha : st.slot.val < 2 ^ 64) :
    ∀ fuel, 12 ≤ fuel →
      ResultMatches gfp [] h [.ref r0] (fun (e : Epoch) _ v => v = .uint epTy e.val)
        (interp (Scope.env sha) fuel Scope.Id.«get_current_epoch» [.ref r0] h)
        (get_current_epoch st) := by
  intro fuel hf
  have hden := gce_den sha [] 0 ds _ hs ha
  rw [Nat.zero_add] at hden
  have hdec : DecArgs h [.ref r0] [.cont Scope.Id.«BeaconState» ds] := by
    refine ⟨rfl, fun k v d hv hd' => ?_⟩
    match k, hv, hd' with
    | 0, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨n, hd⟩
    | _ + 1, hv, _ => simp at hv
  have hm := denote_sound_calls (Scope.env sha) fpsEx (libFlat_ssz _ (nmOK_scope _) hh) gfp []
    (f := Scope.Id.«get_current_epoch») (by simp only [Scope.env, Validation.Tactic.lookup_lit])
    hdec (Examples.wtree_nil h _) hwf hden
  refine resultMatches_mono hf (Examples.resultMatches_map
    (f := fun e : Epoch => (DRes.val (Value.uint epTy e.val), [DV.cont Scope.Id.«BeaconState» ds]))
    (E := fun (x : DRes × List DV) h' v => ERel h' [.ref r0] x.1 v ∧ DecArgs h' [.ref r0] x.2)
    (fun e h' v he => he.1.1) ?_)
  rw [gce_read st ha]
  exact hm

/-! ## `saturating_sub` -/

theorem sub_ui (t : UintTy) (ht : t.bits = 64) (x : Nat) (h1 : 1 < x) (hx : x < 2 ^ 64) :
    @binopVal LibModel.toLibValues .sub (.uint t x) (.int 1) = .ok (.uint t (x - 1)) := by
  have := binop_uint_int .sub t x 1
  rw [show intArith .sub (x : Int) 1 = .ok (((x - 1 : Nat)) : Int) by
    simp only [intArith]; congr 1; omega] at this
  rw [Except.bind_ok', wrap_nat ht, chkRange_ok (by omega)] at this
  exact this

theorem sub_uu (t : UintTy) (ht : t.bits = 64) (hr : resolveUint t t = .ok t) (x y : Nat)
    (hyx : y ≤ x) (hx : x < 2 ^ 64) :
    @binopVal LibModel.toLibValues .sub (.uint t x) (.uint t y) = .ok (.uint t (x - y)) := by
  have := binop_sub (t := t) (t' := t) (r := t) hr ht x y
  rw [chkSub_ok x y hyx hx] at this
  exact this

theorem gt_ui (t : UintTy) (x : Nat) :
    @cmpVal LibModel.toLibValues .gt (.uint t x) (.int 1) = .ok (decide (1 < x)) := by
  show (Except.ok (cmpInt .gt (x : Int) 1) : Res Bool) = _
  simp only [cmpInt, Except.ok.injEq, decide_eq_decide]
  omega

theorem gt_uu (t : UintTy) (hr : resolveUint t t = .ok t) (x y : Nat) :
    @cmpVal LibModel.toLibValues .gt (.uint t x) (.uint t y) = .ok (decide (y < x)) := by
  show (do let _ ← resolveUint t t; pure (cmpInt .gt (x : Int) y) : Res Bool) = _
  rw [hr]; simp [cmpInt]

theorem truthy_b (b : Bool) : @truthy LibModel.toLibValues (.bool b) = .ok b := rfl

/-- `saturating_sub(epoch, 1)`. -/
theorem sat_den_ei (sha : Oracle) (fp : Footprint) (m x : Nat) (hx : x < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 8)).fn fp Scope.fn_saturating_sub
        [.leaf (.uint epTy x), .leaf (.int 1)] =
      some (.ok (.val (.uint epTy (if 1 < x then x - 1 else 0)), [.leaf (.uint epTy x), .leaf (.int 1)])) := by
  have hc : cmpF .gt (.uint epTy x) (.int 1) = some (.ok (decide (1 < x))) :=
    cmpF_eval (gt_ui epTy x) (by simp)
  by_cases h1 : 1 < x
  · have hb : dBinop .sub (.val (.uint epTy x)) (.val (.int 1)) = some (.ok (.val (.uint epTy (x - 1)))) :=
      dBinop_eval (sub_ui epTy rfl x h1 hx) rfl
    simp [fnStep, noneDefaults, Scope.fn_saturating_sub, Sem.block, blockOf, stmtStep, exprStep, DM.bind, DM.ok,
      initLoc, setLoc, slot, cmpOf, hc, hb, h1, truthy_lift (truthy_b true), Flat]
  · have hb : dBinop .sub (.val (.uint epTy x)) (.val (.uint epTy x)) = some (.ok (.val (.uint epTy 0))) := by
      have := dBinop_eval (sub_uu epTy rfl (by simp [resolveUint]) x x (Nat.le_refl x) hx) rfl
      simpa using this
    simp [fnStep, noneDefaults, Scope.fn_saturating_sub, Sem.block, blockOf, stmtStep, exprStep, DM.bind, DM.ok,
      initLoc, setLoc, slot, cmpOf, hc, hb, h1, truthy_lift (truthy_b false), Flat]

/-! ## `get_previous_epoch` -/

theorem gpe_den (sha : Oracle) (fp : Footprint) (m : Nat) (ds : List DV) (a : Nat)
    (hs : ds[2]? = some (.leaf (.uint slotTy a))) (ha : a < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 16)).fn fp Scope.fn_get_previous_epoch [.cont Scope.Id.«BeaconState» ds] =
      some (.ok (.val (.uint epTy (if 1 < a / 8 then a / 8 - 1 else 0)), [.cont Scope.Id.«BeaconState» ds])) := by
  have hg := gce_den sha [] m ds a hs ha
  have hsat := sat_den_ei sha [] (m + 5) (a / 8) (by omega)
  rw [show m + 5 + 8 = m + 13 by omega] at hsat
  rw [den_fn]
  simp [-den_fn, hg, hsat, fnStep, noneDefaults, Scope.fn_get_previous_epoch, Sem.block, blockOf, stmtStep,
    exprStep, callHead, callable, Validation.Tactic.lookup_lit, DM.bind, DM.ok, initLoc, setLoc,
    slot, argsOf, dCallRO, padNone, fpsEx, argRoot, Scope.Id.«decrease_balance», DSt.deref, subAt, Flat]

theorem sat_read_i (x : Nat) (hx : x < 2 ^ 64) :
    saturating_sub (⟨x⟩ : Uint64) (1 : Int) = .ok ⟨if 1 < x then x - 1 else 0⟩ := by
  unfold saturating_sub
  by_cases h1 : 1 < x
  · have hi : intArith .sub (uv (⟨x⟩ : Uint64)) (1 : Int) = .ok ((x - 1 : Nat) : Int) := by
      show intArith .sub (x : Int) 1 = _
      simp only [intArith]; congr 1; omega
    have hd : decide (uv (⟨x⟩ : Uint64) > (1 : Int)) = true := by
      show decide ((x : Int) > 1) = true; simp; omega
    rw [hd, if_pos rfl]
    unfold uOp
    rw [hi, show erase (.ok ((x - 1 : Nat) : Int) : Res Int) = (.ok _ : SpecM Int) from rfl,
      Except.bind_ok', uOf_ok (α := Uint64) (x - 1) (by show x - 1 < 2 ^ 64; omega)]
    simp [h1]; rfl
  · have hi : intArith .sub (uv (⟨x⟩ : Uint64)) (uv (⟨x⟩ : Uint64)) = .ok ((0 : Nat) : Int) := by
      show intArith .sub (x : Int) (x : Int) = _
      simp [intArith]
    have hd : decide (uv (⟨x⟩ : Uint64) > (1 : Int)) = false := by
      show decide ((x : Int) > 1) = false; simp; omega
    rw [hd, if_neg (by simp)]
    unfold uOp
    rw [hi, show erase (.ok ((0 : Nat) : Int) : Res Int) = (.ok _ : SpecM Int) from rfl,
      Except.bind_ok', uOf_ok (α := Uint64) 0 (by show 0 < 2 ^ 64; omega)]
    simp [h1]; rfl

theorem gpe_read (st : BeaconState) (ha : st.slot.val < 2 ^ 64) :
    get_previous_epoch st =
      .ok ⟨if 1 < st.slot.val / 8 then st.slot.val / 8 - 1 else 0⟩ := by
  unfold get_previous_epoch
  rw [gce_read st ha]
  simp only [Except.bind_ok']
  rw [sat_read_i _ (by omega)]
  rfl

theorem get_previous_epoch_denote (sha : Oracle) (fp : Footprint) (m : Nat) (ds : List DV)
    (st : BeaconState) (hs : ds[2]? = some (.leaf (.uint slotTy st.slot.val)))
    (ha : st.slot.val < 2 ^ 64) :
    ((den (Scope.env sha) fpsEx (m + 16)).fn fp Scope.fn_get_previous_epoch
        [.cont Scope.Id.«BeaconState» ds]).map (Except.mapError SpecError.fail) =
      some ((fun e : Epoch => (DRes.val (Value.uint epTy e.val), [DV.cont Scope.Id.«BeaconState» ds])) <$>
        get_previous_epoch st) := by
  rw [gpe_den sha fp m ds _ hs ha, gpe_read st ha]; rfl

/-! ## `decrease_balance`: a writing caller of `saturating_sub` -/

abbrev gwTy : UintTy := .nominal Scope.Id.«Gwei» 64
abbrev viTy : UintTy := .nominal Scope.Id.«ValidatorIndex» 64

theorem sat_den_gg (sha : Oracle) (fp : Footprint) (m b d : Nat) (hb : b < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 8)).fn fp Scope.fn_saturating_sub
        [.leaf (.uint gwTy b), .leaf (.uint gwTy d)] =
      some (.ok (.val (.uint gwTy (if d < b then b - d else 0)),
        [.leaf (.uint gwTy b), .leaf (.uint gwTy d)])) := by
  have hr : resolveUint gwTy gwTy = .ok gwTy := by simp [resolveUint]
  have hc : cmpF .gt (.uint gwTy b) (.uint gwTy d) = some (.ok (decide (d < b))) :=
    cmpF_eval (gt_uu gwTy hr b d) (by simp)
  by_cases h1 : d < b
  · have hs : dBinop .sub (.val (.uint gwTy b)) (.val (.uint gwTy d)) =
        some (.ok (.val (.uint gwTy (b - d)))) :=
      dBinop_eval (sub_uu gwTy rfl hr b d (by omega) hb) rfl
    simp [fnStep, noneDefaults, Scope.fn_saturating_sub, Sem.block, blockOf, stmtStep, exprStep, DM.bind, DM.ok,
      initLoc, setLoc, slot, cmpOf, hc, hs, h1, truthy_lift (truthy_b true), Flat]
  · have hs : dBinop .sub (.val (.uint gwTy b)) (.val (.uint gwTy b)) =
        some (.ok (.val (.uint gwTy 0))) := by
      have := dBinop_eval (sub_uu gwTy rfl hr b b (Nat.le_refl b) hb) rfl
      simpa using this
    simp [fnStep, noneDefaults, Scope.fn_saturating_sub, Sem.block, blockOf, stmtStep, exprStep, DM.bind, DM.ok,
      initLoc, setLoc, slot, cmpOf, hc, hs, h1, truthy_lift (truthy_b false), Flat]

theorem dCoerce_gwei (sha : Oracle) (n : Nat) :
    dCoerce (Scope.env sha) false (.uint gwTy) (.uint gwTy n) = some (.ok (.uint gwTy n)) := by
  simp [dCoerce, coerceWith, LibModel.coerce, Ssz.coerce, Examples.coerceH_gwei, lift_ok]

theorem dbal_den_ok (sha : Oracle) (m : Nat) (ds : List DV) (k : ListKind) (l : Option Nat)
    (bal : List Gwei) (i δ : Nat) (hb : ds[12]? = some (.list k (.uint gwTy) l (bal.map Examples.gleaf)))
    (hi : i < bal.length) (hbi : bal[i].val < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 14)).fn Examples.ibFp Scope.fn_decrease_balance
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint viTy i), .leaf (.uint gwTy δ)] =
      some (.ok (.val (.none), [.cont Scope.Id.«BeaconState» (ds.set 12 (.list k (.uint gwTy) l
          ((bal.set i ⟨if δ < bal[i].val then bal[i].val - δ else 0⟩).map Examples.gleaf))),
        .leaf (.uint viTy i), .leaf (.uint gwTy δ)])) := by
  have hsat := sat_den_gg sha [] (m + 3) bal[i].val δ hbi
  rw [show m + 3 + 8 = m + 11 by omega] at hsat
  have hm : (List.map Examples.gleaf bal)[i]? = some (.leaf (.uint gwTy bal[i].val)) := by
    simp [List.getElem?_eq_getElem hi, Examples.gleaf]
  rw [den_fn]
  simp [-den_fn, hsat, fnStep, noneDefaults, Scope.fn_decrease_balance, Sem.block, blockOf, stmtStep,
    exprStep, callStep, appendOf, callHead, callable, Validation.Tactic.lookup_lit, DM.bind, DM.ok, initLoc,
    setLoc, slot, argsOf, dCallRO, padNone, dCallW, fpsEx, argRoot, Scope.Id.«decrease_balance»,
    Scope.Id.«saturating_sub», DSt.deref, subAt, DV.kids, dAttr, dIndex, ofChild, hb, hm,
    Validation.Tactic.fieldIndex_lit, isByteList, normIndex_nat, hi, targetStep, dCoerce_gwei,
    dWriteD, dWrite, Except.map, Flat, fpOk, Examples.ibFp, rootIs, matchesB, leafAt, updAt, List.map_set, Examples.gleaf]

theorem dbal_den_idx (sha : Oracle) (m : Nat) (ds : List DV) (k : ListKind) (l : Option Nat)
    (bal : List Gwei) (i δ : Nat) (hb : ds[12]? = some (.list k (.uint gwTy) l (bal.map Examples.gleaf)))
    (hi : ¬ i < bal.length) :
    (den (Scope.env sha) fpsEx (m + 14)).fn Examples.ibFp Scope.fn_decrease_balance
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint viTy i), .leaf (.uint gwTy δ)] =
      some (.error .indexError) := by
  rw [den_fn]
  simp [-den_fn, fnStep, noneDefaults, Scope.fn_decrease_balance, Sem.block, blockOf, stmtStep,
    exprStep, callStep, appendOf, callHead, callable, Validation.Tactic.lookup_lit, DM.bind, DM.ok, initLoc,
    setLoc, slot, argsOf, DSt.deref, subAt, DV.kids, dAttr, dIndex, ofChild, hb,
    Validation.Tactic.fieldIndex_lit, isByteList, normIndex_nat, hi]

theorem sat_read_g (b d : Nat) (hb : b < 2 ^ 64) :
    saturating_sub (⟨b⟩ : Uint64) (d : Int) = .ok ⟨if d < b then b - d else 0⟩ := by
  unfold saturating_sub
  by_cases h1 : d < b
  · have hi : intArith .sub (uv (⟨b⟩ : Uint64)) (d : Int) = .ok ((b - d : Nat) : Int) := by
      show intArith .sub (b : Int) (d : Int) = _
      simp only [intArith]; congr 1; omega
    have hd : decide (uv (⟨b⟩ : Uint64) > (d : Int)) = true := by
      show decide ((b : Int) > d) = true; simp; omega
    rw [hd, if_pos rfl]
    unfold uOp
    rw [hi, show erase (.ok ((b - d : Nat) : Int) : Res Int) = (.ok _ : SpecM Int) from rfl,
      Except.bind_ok', uOf_ok (α := Uint64) (b - d) (by show b - d < 2 ^ 64; omega)]
    simp [h1]; rfl
  · have hi : intArith .sub (uv (⟨b⟩ : Uint64)) (uv (⟨b⟩ : Uint64)) = .ok ((0 : Nat) : Int) := by
      show intArith .sub (b : Int) (b : Int) = _
      simp [intArith]
    have hd : decide (uv (⟨b⟩ : Uint64) > (d : Int)) = false := by
      show decide ((b : Int) > d) = false; simp; omega
    rw [hd, if_neg (by simp)]
    unfold uOp
    rw [hi, show erase (.ok ((0 : Nat) : Int) : Res Int) = (.ok _ : SpecM Int) from rfl,
      Except.bind_ok', uOf_ok (α := Uint64) 0 (by show 0 < 2 ^ 64; omega)]
    simp [h1]; rfl

theorem dbal_read_ok (st : BeaconState) (i δ : Nat) (hi : i < st.balances.length)
    (hbi : st.balances[i].val < 2 ^ 64) :
    decrease_balance st ⟨i⟩ ⟨δ⟩ = .ok { st with balances := (st.balances.set i
      ⟨if δ < st.balances[i].val then st.balances[i].val - δ else 0⟩) } := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  simp [decrease_balance, lget, lset, Rd.pyIndex, uv, hneg, hi, List.getElem?_eq_getElem hi,
    sat_read_g _ δ hbi]

theorem dbal_read_idx (st : BeaconState) (i δ : Nat) (hi : ¬ i < st.balances.length) :
    decrease_balance st ⟨i⟩ ⟨δ⟩ = .error .invalid := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  simp [decrease_balance, lget, Rd.pyIndex, uv, hneg, hi]

/-- The denotation of `decrease_balance` is the readable function, on the balances field. -/
theorem decrease_balance_denote (sha : Oracle) (m : Nat) (ds : List DV) (k : ListKind)
    (l : Option Nat) (st : BeaconState) (i δ : Nat)
    (hb : ds[12]? = some (.list k (.uint gwTy) l (st.balances.map Examples.gleaf)))
    (hbal : ∀ g ∈ st.balances, g.val < 2 ^ 64) :
    ((den (Scope.env sha) fpsEx (m + 14)).fn Examples.ibFp Scope.fn_decrease_balance
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint viTy i), .leaf (.uint gwTy δ)]).map
        (Except.mapError SpecError.fail) =
      some ((fun st' : BeaconState => (DRes.val (Value.none),
        [.cont Scope.Id.«BeaconState» (ds.set 12 (.list k (.uint gwTy) l (st'.balances.map Examples.gleaf))),
          .leaf (.uint viTy i), .leaf (.uint gwTy δ)])) <$> decrease_balance st ⟨i⟩ ⟨δ⟩) := by
  by_cases hi : i < st.balances.length
  · have hbi := hbal _ (List.getElem_mem hi)
    rw [dbal_den_ok sha m ds k l st.balances i δ hb hi hbi, dbal_read_ok st i δ hi hbi]; rfl
  · rw [dbal_den_idx sha m ds k l st.balances i δ hb hi, dbal_read_idx st i δ hi]; rfl

/-- SPEC 9.2 for `get_previous_epoch`: nested calls, and the state passed as a place. -/
theorem get_previous_epoch_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h)
    (hh : HtrDec (Scope.env sha)) (r0 n : Nat)
    (ds : List DV) (st : BeaconState) (hd : dec h n (.ref r0) = some (.cont Scope.Id.«BeaconState» ds))
    (hs : ds[2]? = some (.leaf (.uint slotTy st.slot.val))) (ha : st.slot.val < 2 ^ 64) :
    ∀ fuel, 16 ≤ fuel →
      ResultMatches gfp [] h [.ref r0] (fun (e : Epoch) _ v => v = .uint epTy e.val)
        (interp (Scope.env sha) fuel Scope.Id.«get_previous_epoch» [.ref r0] h)
        (get_previous_epoch st) := by
  intro fuel hf
  have hden := gpe_den sha [] 0 ds _ hs ha
  rw [Nat.zero_add] at hden
  have hdec : DecArgs h [.ref r0] [.cont Scope.Id.«BeaconState» ds] := by
    refine ⟨rfl, fun k v d hv hd' => ?_⟩
    match k, hv, hd' with
    | 0, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨n, hd⟩
    | _ + 1, hv, _ => simp at hv
  have hm := denote_sound_calls (Scope.env sha) fpsEx (libFlat_ssz _ (nmOK_scope _) hh) gfp []
    (f := Scope.Id.«get_previous_epoch») (by simp only [Scope.env, Validation.Tactic.lookup_lit])
    hdec (Examples.wtree_nil h _) hwf hden
  refine resultMatches_mono hf (Examples.resultMatches_map
    (f := fun e : Epoch => (DRes.val (Value.uint epTy e.val), [DV.cont Scope.Id.«BeaconState» ds]))
    (E := fun (x : DRes × List DV) h' v => ERel h' [.ref r0] x.1 v ∧ DecArgs h' [.ref r0] x.2)
    (fun e h' v he => he.1.1) ?_)
  rw [gpe_read st ha]
  exact hm

/-- SPEC 9.2 for `decrease_balance`: a write under `WTree`, after a call. The result heap decodes
to the state tree with the readable result's balances, every other field unchanged. -/
theorem decrease_balance_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h)
    (hh : HtrDec (Scope.env sha)) (r0 n : Nat)
    (ds : List DV) (k : ListKind) (l : Option Nat) (st : BeaconState) (i δ : Nat)
    (hd : dec h n (.ref r0) = some (.cont Scope.Id.«BeaconState» ds))
    (hb : ds[12]? = some (.list k (.uint gwTy) l (st.balances.map Examples.gleaf)))
    (hbal : ∀ g ∈ st.balances, g.val < 2 ^ 64)
    (hw : WTree h [.ref r0, .uint viTy i, .uint gwTy δ] Examples.ibFp) :
    ∀ fuel, 14 ≤ fuel →
      ResultMatches gfp Examples.ibFp h [.ref r0, .uint viTy i, .uint gwTy δ]
        (fun (st' : BeaconState) h' v => v = .none ∧
          ∃ m, dec h' m (.ref r0) = some (.cont Scope.Id.«BeaconState»
            (ds.set 12 (.list k (.uint gwTy) l (st'.balances.map Examples.gleaf)))))
        (interp (Scope.env sha) fuel Scope.Id.«decrease_balance» [.ref r0, .uint viTy i, .uint gwTy δ] h)
        (decrease_balance st ⟨i⟩ ⟨δ⟩) := by
  intro fuel hf
  have hden := decrease_balance_denote sha 0 ds k l st i δ hb hbal
  rw [Nat.zero_add] at hden
  cases hdn : (den (Scope.env sha) fpsEx 14).fn Examples.ibFp Scope.fn_decrease_balance
      [.cont Scope.Id.«BeaconState» ds, .leaf (.uint viTy i), .leaf (.uint gwTy δ)] with
  | none => rw [hdn] at hden; cases hden
  | some r =>
    rw [hdn] at hden
    simp only [Option.map_some, Option.some.injEq] at hden
    have hdec : DecArgs h [.ref r0, .uint viTy i, .uint gwTy δ]
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint viTy i), .leaf (.uint gwTy δ)] := by
      refine ⟨rfl, fun k v d hv hd' => ?_⟩
      match k, hv, hd' with
      | 0, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨n, hd⟩
      | 1, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨0, dec_flat rfl 0⟩
      | 2, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨0, dec_flat rfl 0⟩
      | _ + 3, hv, _ => simp at hv
    have hm := denote_sound_calls (Scope.env sha) fpsEx (libFlat_ssz _ (nmOK_scope _) hh) gfp Examples.ibFp
      (f := Scope.Id.«decrease_balance») (by simp only [Scope.env, Validation.Tactic.lookup_lit])
      hdec hw hwf hdn
    rw [hden] at hm
    refine resultMatches_mono hf (Examples.resultMatches_map (fun st' h' v he => ⟨he.1.1, ?_⟩) hm)
    obtain ⟨-, hr⟩ := he.2
    exact hr 0 (.ref r0) _ rfl rfl

end SpecLean.Layer4.Examples2
