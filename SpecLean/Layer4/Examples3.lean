import SpecLean.Layer4.Examples2

/-!
# Layer 4: a loop end to end (`process_effective_balance_updates`)

The loop `for index, validator in enumerate(state.validators)` reads the live list at each step and
writes `validator.effective_balance` through the loop variable.

- `pebu_iter`: one iteration of the body at fuel `m + 21`, statement by statement, from the
  summaries of the callees (`get_max_effective_balance`, `min`, `Uint64`).
- `pebu_loop`: the loop at fuel `m + 22 + d`, by induction on `d`, the items left.
- `pebu_den`: the function at fuel `m + 24 + len`.
- `pebu_read`: the readable function is the same pure loop `pebuLoop`.
- `process_effective_balance_updates_denote` and `process_effective_balance_updates_l4`.

The sums with literals stay abstract (`dt`, `ut`) until the last step. Lean evaluates such sums in
unary under `whnf`.
-/

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd SpecLean.Rd.Gen SpecLean.Layer4.Examples2

attribute [local instance high] LibModel.toLibValues

namespace SpecLean.Layer4.Examples3


abbrev b32 : Name := Scope.Id.«Bytes32»

theorem cmpF_eq_bytes (c d : Name) (x y : List UInt8) :
    cmpF .eq (.bytes c x) (.bytes d y) = some (.ok (x == y)) := rfl

theorem take_bound (wc : List UInt8) : List.take (sliceBound wc.length 1) wc = wc.take 1 := by
  unfold sliceBound
  simp

theorem icwc_den (sha : Oracle) (fp : Footprint) (m : Nat) (wc : List UInt8) :
    (den (Scope.env sha) fpsEx (m + 8)).fn fp Scope.fn_is_compounding_withdrawal_credential
        [.leaf (.bytes b32 wc)] =
      some (.ok (.bool (wc.take 1 == [2]), [.leaf (.bytes b32 wc)])) := by
  simp [fnStep, Scope.fn_is_compounding_withdrawal_credential, Sem.block, blockOf, stmtStep,
    exprStep, DM.bind, DM.ok, initLoc, setLoc, slot, cmpOf, optOf, dGlobal,
    Validation.Tactic.lookup_lit, Flat, cmpF_eq_bytes, take_bound]
  by_cases h2 : List.take 1 wc = [2] <;> simp [h2]

/-- Is the credential compounding. -/
def comp (x : Validator) : Bool := (bd x.withdrawal_credentials).take 1 == [2]

theorem hcwc_den (sha : Oracle) (fp : Footprint) (m : Nat) (x : Validator) :
    (den (Scope.env sha) fpsEx (m + 12)).fn fp Scope.fn_has_compounding_withdrawal_credential
        [Examples.vdv x] = some (.ok (.bool (comp x), [Examples.vdv x])) := by
  have hc := icwc_den sha [] (m + 1) (bd x.withdrawal_credentials)
  rw [show m + 1 + 8 = m + 9 by omega] at hc
  rw [den_fn]
  simp [-den_fn, hc, fnStep, Scope.fn_has_compounding_withdrawal_credential, Sem.block, blockOf,
    stmtStep, exprStep, callHead, callable, Validation.Tactic.lookup_lit, DM.bind, DM.ok, initLoc,
    setLoc, slot, argsOf, dCallRO, fpsEx, argRoot, dAttr, DSt.deref, subAt, DV.kids, ofChild,
    Validation.Tactic.fieldIndex_lit, Examples.vdv, Flat, comp]

theorem slot_vdv (x : Validator) : slot [Examples.vdv x] 0 = .place 0 [] := rfl

/-- The max effective balance. -/
def meb (x : Validator) : Nat := if comp x then 2048000000000 else 32000000000

theorem gmeb_den (sha : Oracle) (fp : Footprint) (m : Nat) (x : Validator) :
    (den (Scope.env sha) fpsEx (m + 16)).fn fp Scope.fn_get_max_effective_balance
        [Examples.vdv x] = some (.ok (.uint gwTy (meb x), [Examples.vdv x])) := by
  have hc := hcwc_den sha [] (m + 1) x
  rw [show m + 1 + 12 = m + 13 by omega] at hc
  rw [den_fn]
  cases hcx : comp x <;>
  simp [-den_fn, hc, hcx, fnStep, Scope.fn_get_max_effective_balance, Sem.block, blockOf,
    stmtStep, exprStep, callHead, callable, Validation.Tactic.lookup_lit, DM.bind, DM.ok, initLoc,
    setLoc, slot_vdv, argsOf, dCallRO, fpsEx, argRoot, DSt.deref, subAt, Flat, meb, dGlobal,
    truthy_lift (truthy_b true), truthy_lift (truthy_b false)]

theorem icwc_read (wc : Bytes32) :
    is_compounding_withdrawal_credential wc = .ok ((bd wc).take 1 == [2]) := by
  simp [is_compounding_withdrawal_credential, lslice, sliceBound', COMPOUNDING_WITHDRAWAL_PREFIX]
  show (List.take (min 1 (bd wc).length) (bd wc) == [2]) = _
  rw [show List.take (min 1 (bd wc).length) (bd wc) = (bd wc).take 1 by
    cases bd wc <;> simp]

theorem gmeb_read (x : Validator) : get_max_effective_balance x = .ok ⟨meb x⟩ := by
  unfold get_max_effective_balance has_compounding_withdrawal_credential
  rw [icwc_read]
  cases hc : comp x
  · simp [comp] at hc; simp [hc, meb, comp, MIN_ACTIVATION_BALANCE]
  · simp [comp] at hc; simp [hc, meb, comp, MAX_EFFECTIVE_BALANCE_ELECTRA]

/-! ## The loop body of `process_effective_balance_updates` -/

abbrev u64 : UintTy := .width 64

theorem add_gw_u64 (a c : Nat) :
    @binopVal LibModel.toLibValues .add (.uint gwTy a) (.uint u64 c) =
      if a + c < 2 ^ 64 then .ok (.uint gwTy (a + c)) else .error .sszValue := by
  have := binop_add (t := gwTy) (t' := u64) (r := gwTy) rfl rfl a c
  unfold chkAdd chkRange at this
  by_cases h : a + c < 2 ^ 64
  · rw [if_pos h] at this ⊢; exact this
  · rw [if_neg h] at this ⊢; exact this

theorem lt_gw (a b : Nat) :
    cmpF .lt (.uint gwTy a) (.uint gwTy b) = some (.ok (decide (a < b))) := by
  refine cmpF_eval ?_ (by simp)
  show (do let _ ← resolveUint gwTy gwTy; pure (cmpInt .lt (a : Int) b) : Res Bool) = _
  simp [resolveUint, cmpInt]

theorem mod_gw (a : Nat) :
    @binopVal LibModel.toLibValues .mod (.uint gwTy a) (.uint gwTy 1000000000) =
      .ok (.uint gwTy (a % 1000000000)) := by
  have := binop_mod (t := gwTy) (t' := gwTy) (r := gwTy) (by simp [resolveUint]) rfl a 1000000000
  rw [chkMod_ok _ _ (by decide) (by decide)] at this
  exact this

/-- The new effective balance. -/
def newEb (b M : Nat) : Nat := if M < b - b % 1000000000 then M else b - b % 1000000000

theorem min_gw (s : DSt) (v M : Nat) :
    dBuiltin s .min [.val (.uint gwTy v), .val (.uint gwTy M)] =
      some (.ok (.val (.uint gwTy (if M < v then M else v)))) := by
  have hl : @cmpVal LibModel.toLibValues .lt (.uint gwTy M) (.uint gwTy v) = .ok (decide (M < v)) := by
    show (do let _ ← resolveUint gwTy gwTy; pure (cmpInt .lt (M : Int) v) : Res Bool) = _
    simp [resolveUint, cmpInt]
  by_cases h : M < v <;>
    simp [dBuiltin, allVals, pickBest, resolveUint, cmpInt, h, lift_ok, DM.bind, DM.ok, Flat]

theorem coerce_field_gw (sha : Oracle) (v : Nat) (hv : v < 2 ^ 64) :
    dCoerce (Scope.env sha) true (.uint gwTy) (.uint gwTy v) = some (.ok (.uint gwTy v)) := by
  simp only [dCoerce, coerceWith, LibModel.coerce, Ssz.coerce]
  rw [show depthBound = 63 + 1 from rfl, coerceH_plain _ _ _ _ _ _ (fun _ e => by cases e)]
  simp [coerceField, UintTy.subOf]
  rw [if_pos (show v < 2 ^ gwTy.bits from hv)]; rfl

def pebuBody : List Stmt := [
      (.assign 1241 [(.name 1241 9)] (.index 1241 (.attr 1241 (.name 1241 1) 28) (.name 1241 23))),
      (.assign 1242 [(.name 1242 526)] (.call 1242 (.name 1242 32) [(.pos (.binop 1242 .floorDiv (.name 1242 211) (.name 1242 527)))])),
      (.assign 1243 [(.name 1243 528)] (.binop 1243 .mul (.name 1243 526) (.name 1243 529))),
      (.assign 1244 [(.name 1244 530)] (.binop 1244 .mul (.name 1244 526) (.name 1244 531))),
      (.assign 1246 [(.name 1246 397)] (.call 1246 (.name 1246 361) [(.pos (.name 1246 25))])),
      (.ifStmt 1248 (.boolop 1249 .or [(.compare 1249 (.binop 1249 .add (.name 1249 9) (.name 1249 528)) [(.lt, (.attr 1249 (.name 1249 25) 113))]), (.compare 1250 (.binop 1250 .add (.attr 1250 (.name 1250 25) 113) (.name 1250 530)) [(.lt, (.name 1250 9))])]) [
        (.assign 1252 [(.attr 1252 (.name 1252 25) 113)] (.call 1252 (.name 1252 213) [(.pos (.binop 1253 .sub (.name 1253 9) (.binop 1253 .mod (.name 1253 9) (.name 1253 211)))), (.pos (.name 1253 397))]))] [])]

def pebuTarget : Target := .tuple 1240 [(.name 1240 23), (.name 1240 25)]
def pebuIter : Expr := .call 1240 (.name 1240 216) [(.pos (.attr 1240 (.name 1240 1) 27))]

theorem pebu_body_eq : Scope.fn_process_effective_balance_updates.body =
    [.forStmt 1240 pebuTarget pebuIter pebuBody] := rfl

/-- The footprint of `process_effective_balance_updates`. -/
abbrev pebuFp : Footprint := fpsEx 532

/-- The state tree: the validators at field 11, the balances at field 12. -/
def pebuRoot (ds : List DV) (kV : ListKind) (lV : Option Nat) (vals : List Validator) : DV :=
  .cont Scope.Id.«BeaconState» (ds.set 11 (.list kV (.container Scope.Id.«Validator») lV (vals.map Examples.vdv)))

/-- The locals that the body does not bind: `state`, and the globals it reads. -/
structure LocOK (loc : Name → Option DRes) : Prop where
  st : loc 1 = some (.place 0 [])
  g211 : loc 211 = none
  g527 : loc 527 = none
  g529 : loc 529 = none
  g531 : loc 531 = none
  g213 : loc 213 = none
  g361 : loc 361 = none
  g32 : loc 32 = none

theorem LocOK.set {loc : Name → Option DRes} (h : LocOK loc) (x : Name) (r : DRes)
    (hx : x ≠ 1 ∧ x ≠ 211 ∧ x ≠ 527 ∧ x ≠ 529 ∧ x ≠ 531 ∧ x ≠ 213 ∧ x ≠ 361 ∧ x ≠ 32) :
    LocOK (setLoc loc x r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  exact ⟨by simp [setLoc, Ne.symm h1, h.st], by simp [setLoc, Ne.symm h2, h.g211],
    by simp [setLoc, Ne.symm h3, h.g527], by simp [setLoc, Ne.symm h4, h.g529],
    by simp [setLoc, Ne.symm h5, h.g531], by simp [setLoc, Ne.symm h6, h.g213],
    by simp [setLoc, Ne.symm h7, h.g361], by simp [setLoc, Ne.symm h8, h.g32]⟩

theorem c_div : dBinop .floorDiv (.val (.uint gwTy 1000000000)) (.val (.uint u64 4)) =
    some (.ok (.val (.uint gwTy 250000000))) := dBinop_eval rfl rfl
theorem c_ctor (sha : Oracle) : dCtor (Scope.env sha) (.uint u64) [.val (.uint gwTy 250000000)] =
    some (.ok (.val (.uint u64 250000000))) := dCtor_eval rfl rfl rfl rfl
theorem c_mul1 : dBinop .mul (.val (.uint u64 250000000)) (.val (.uint u64 1)) =
    some (.ok (.val (.uint u64 250000000))) := dBinop_eval rfl rfl
theorem c_mul5 : dBinop .mul (.val (.uint u64 250000000)) (.val (.uint u64 5)) =
    some (.ok (.val (.uint u64 1250000000))) := dBinop_eval rfl rfl

/-- The trees of a state in the loop. -/
structure Ctx (s : DSt) (ds : List DV) (kV : ListKind) (lV : Option Nat) (kB : ListKind)
    (lB : Option Nat) (vals : List Validator) (bals : List Gwei) : Prop where
  roots : s.roots = [pebuRoot ds kV lV vals]
  b12 : ds[12]? = some (.list kB (.uint gwTy) lB (bals.map Examples.gleaf))
  l11 : 11 < ds.length

section body
variable (sha : Oracle) (m : Nat) {ds : List DV} {kV : ListKind} {lV : Option Nat} {kB : ListKind}
  {lB : Option Nat} {vals : List Validator} {bals : List Gwei} {s : DSt}

theorem e_balance (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hib : i < bals.length)
    (h1 : s.loc 1 = some (.place 0 [])) (h23 : s.loc 23 = some (.val (.int i))) :
    (den (Scope.env sha) fpsEx (m + 19)).expr pebuFp s
      (.index 1241 (.attr 1241 (.name 1241 1) 28) (.name 1241 23)) =
      some (.ok (.val (.uint gwTy bals[i].val))) := by
  have hb : (bals.map Examples.gleaf)[i]? = some (.leaf (.uint gwTy bals[i].val)) := by
    simp [List.getElem?_eq_getElem hib, Examples.gleaf]
  simp [exprStep, DM.bind, DM.ok, h1, h23, dAttr, dIndex, DSt.deref, subAt, DV.kids, ofChild,
    hc.roots, pebuRoot, Validation.Tactic.fieldIndex_lit, List.getElem?_set, hc.b12, isByteList,
    normIndex_nat, hib, hb, Examples.gleaf]

theorem e_hi (h32 : s.loc 32 = none) (h211 : s.loc 211 = none) (h527 : s.loc 527 = none) :
    (den (Scope.env sha) fpsEx (m + 19)).expr pebuFp s
      (.call 1242 (.name 1242 32) [(.pos (.binop 1242 .floorDiv (.name 1242 211) (.name 1242 527)))]) =
      some (.ok (.val (.uint u64 250000000))) := by
  simp [exprStep, DM.bind, DM.ok, callHead, callable, Validation.Tactic.lookup_lit, h32, h211, h527,
    argsOf, dGlobal, Flat, dCallRO, c_div, c_ctor sha]

theorem e_mul (x c r : Nat) (h526 : s.loc 526 = some (.val (.uint u64 250000000))) (hx : s.loc x = none)
    (hc : (Scope.env sha).globals.lookup x = some (.const (.uint u64 c)))
    (hm : dBinop .mul (.val (.uint u64 250000000)) (.val (.uint u64 c)) = some (.ok (.val (.uint u64 r)))) :
    (den (Scope.env sha) fpsEx (m + 19)).expr pebuFp s (.binop l .mul (.name l 526) (.name l x)) =
      some (.ok (.val (.uint u64 r))) := by
  simp [exprStep, DM.bind, DM.ok, h526, hx, dGlobal, hc, Flat, hm]

theorem e_meb (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hi : i < vals.length)
    (h361 : s.loc 361 = none) (h25 : s.loc 25 = some (.place 0 [11, i])) :
    (den (Scope.env sha) fpsEx (m + 19)).expr pebuFp s (.call 1246 (.name 1246 361) [(.pos (.name 1246 25))]) =
      some (.ok (.val (.uint gwTy (meb vals[i])))) := by
  have hg := gmeb_den sha [] (m + 2) vals[i]
  rw [show m + 2 + 16 = m + 18 by omega] at hg
  have hv : (vals.map Examples.vdv)[i]? = some (Examples.vdv vals[i]) := by
    simp [List.getElem?_eq_getElem hi]
  simp [-den_fn, exprStep, DM.bind, DM.ok, callHead, callable, Validation.Tactic.lookup_lit, h361,
    h25, argsOf, dCallRO, fpsEx, argRoot, DSt.deref, subAt, DV.kids, hc.roots, pebuRoot,
    List.getElem?_set, hc.l11, hv, hg, Flat]


/-- The value of the hysteresis condition, with the thresholds `dt` and `ut` kept abstract: a
literal in a sum would make `decide` run it in unary. -/
def condRes (b eb dt ut : Nat) : Res DRes :=
  if b + dt < 2 ^ 64 then
    if b + dt < eb then .ok (.val (.bool true))
    else if eb + ut < 2 ^ 64 then .ok (.val (.bool (decide (eb + ut < b))))
    else .error .sszValue
  else .error .sszValue

theorem dadd (a c : Nat) :
    dBinop .add (.val (.uint gwTy a)) (.val (.uint u64 c)) =
      some (if a + c < 2 ^ 64 then .ok (.val (.uint gwTy (a + c))) else .error .sszValue) := by
  by_cases h : a + c < 2 ^ 64
  · have := add_gw_u64 a c; rw [if_pos h] at this; rw [dBinop_eval this rfl, if_pos h]
  · have := add_gw_u64 a c; rw [if_neg h] at this; rw [dBinop_err this (by decide), if_neg h]

theorem e_min {b M : Nat} (hb : b < 2 ^ 64) (h213 : s.loc 213 = none) (h211 : s.loc 211 = none)
    (h9 : s.loc 9 = some (.val (.uint gwTy b))) (h397 : s.loc 397 = some (.val (.uint gwTy M))) :
    (den (Scope.env sha) fpsEx (m + 19)).expr pebuFp s
      (.call 1252 (.name 1252 213) [(.pos (.binop 1253 .sub (.name 1253 9) (.binop 1253 .mod (.name 1253 9) (.name 1253 211)))), (.pos (.name 1253 397))]) =
      some (.ok (.val (.uint gwTy (newEb b M)))) := by
  have hmod : dBinop .mod (.val (.uint gwTy b)) (.val (.uint gwTy 1000000000)) =
      some (.ok (.val (.uint gwTy (b % 1000000000)))) := dBinop_eval (mod_gw b) rfl
  have hsub : dBinop .sub (.val (.uint gwTy b)) (.val (.uint gwTy (b % 1000000000))) =
      some (.ok (.val (.uint gwTy (b - b % 1000000000)))) :=
    dBinop_eval (sub_uu gwTy rfl (by simp [resolveUint]) b _ (Nat.mod_le _ _) hb) rfl
  simp [exprStep, DM.bind, DM.ok, callHead, callable, Validation.Tactic.lookup_lit, h213, h211,
    h9, h397, argsOf, dGlobal, Flat, dCallRO, hmod, hsub, min_gw, newEb]
theorem e_eb (n : Nat) (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hi : i < vals.length)
    (h25 : s.loc 25 = some (.place 0 [11, i])) :
    (den (Scope.env sha) fpsEx (n + 2)).expr pebuFp s (.attr l (.name l' 25) 113) =
      some (.ok (.val (.uint gwTy vals[i].effective_balance.val))) := by
  have hv : (vals.map Examples.vdv)[i]? = some (Examples.vdv vals[i]) := by
    simp [List.getElem?_eq_getElem hi]
  simp [exprStep, DM.bind, DM.ok, h25, dAttr, DSt.deref, subAt, DV.kids, ofChild, hc.roots,
    pebuRoot, List.getElem?_set, hc.l11, hv]
  simp only [Examples.vdv]
  have hf : fieldIndex (Scope.env sha) Scope.Id.«Validator» 113 = some (2, .uint gwTy) := by
    simp only [Validation.Tactic.fieldIndex_lit]
  simp only [hf]
  rfl

theorem e_cmp1 (n : Nat) (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hi : i < vals.length)
    {b dt : Nat} (h9 : s.loc 9 = some (.val (.uint gwTy b)))
    (h528 : s.loc 528 = some (.val (.uint u64 dt)))
    (h25 : s.loc 25 = some (.place 0 [11, i])) :
    (den (Scope.env sha) fpsEx (n + 3)).expr pebuFp s
      (.compare 1249 (.binop 1249 .add (.name 1249 9) (.name 1249 528)) [(.lt, (.attr 1249 (.name 1249 25) 113))]) =
      some (if b + dt < 2 ^ 64 then
        .ok (.val (.bool (decide (b + dt < vals[i].effective_balance.val))))
        else .error .sszValue) := by
  have he := e_eb sha n hc hi h25 (l := 1249) (l' := 1249)
  have hb : (den (Scope.env sha) fpsEx (n + 2)).expr pebuFp s
      (.binop 1249 .add (.name 1249 9) (.name 1249 528)) =
      some (if b + dt < 2 ^ 64 then .ok (.val (.uint gwTy (b + dt))) else .error .sszValue) := by
    have hn9 : (den (Scope.env sha) fpsEx (n + 1)).expr pebuFp s (.name 1249 9) =
        some (.ok (.val (.uint gwTy b))) := by rw [den_expr]; simp only [exprStep, h9]; rfl
    have hn5 : (den (Scope.env sha) fpsEx (n + 1)).expr pebuFp s (.name 1249 528) =
        some (.ok (.val (.uint u64 dt))) := by rw [den_expr]; simp only [exprStep, h528]; rfl
    rw [den_expr]; simp only [exprStep]; rw [hn9]; simp only [DM.bind]; rw [hn5]
    simp only [dadd]
  rw [den_expr]
  simp only [exprStep]
  rw [hb]
  by_cases h1 : b + dt < 2 ^ 64
  · simp only [if_pos h1, DM.bind, cmpOf]
    rw [he]
    simp only [lt_gw]
    by_cases h2 : b + dt < vals[i].effective_balance.val
    · simp only [h2, decide_true, if_true]; rfl
    · simp only [h2, decide_false, Bool.false_eq_true, if_false]; rfl
  · simp only [if_neg h1, DM.bind]

theorem e_cmp2 (n : Nat) (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hi : i < vals.length)
    {b ut : Nat} (h9 : s.loc 9 = some (.val (.uint gwTy b)))
    (h530 : s.loc 530 = some (.val (.uint u64 ut)))
    (h25 : s.loc 25 = some (.place 0 [11, i])) :
    (den (Scope.env sha) fpsEx (n + 4)).expr pebuFp s
      (.compare 1250 (.binop 1250 .add (.attr 1250 (.name 1250 25) 113) (.name 1250 530)) [(.lt, (.name 1250 9))]) =
      some (if vals[i].effective_balance.val + ut < 2 ^ 64 then
        .ok (.val (.bool (decide (vals[i].effective_balance.val + ut < b))))
        else .error .sszValue) := by
  have he := e_eb sha n hc hi h25 (l := 1250) (l' := 1250)
  have hb : (den (Scope.env sha) fpsEx (n + 3)).expr pebuFp s
      (.binop 1250 .add (.attr 1250 (.name 1250 25) 113) (.name 1250 530)) =
      some (if vals[i].effective_balance.val + ut < 2 ^ 64 then
        .ok (.val (.uint gwTy (vals[i].effective_balance.val + ut))) else .error .sszValue) := by
    have hn : (den (Scope.env sha) fpsEx (n + 2)).expr pebuFp s (.name 1250 530) =
        some (.ok (.val (.uint u64 ut))) := by
      rw [den_expr]; simp only [exprStep, h530]; rfl
    rw [den_expr]; simp only [exprStep]; rw [he]; simp only [DM.bind]; rw [hn]
    simp only [dadd]
  rw [den_expr]
  simp only [exprStep]
  rw [hb]
  by_cases h3 : vals[i].effective_balance.val + ut < 2 ^ 64
  · simp only [if_pos h3, DM.bind, cmpOf]
    have hn : (den (Scope.env sha) fpsEx (n + 3)).expr pebuFp s (.name 1250 9) =
        some (.ok (.val (.uint gwTy b))) := by
      rw [den_expr]; simp only [exprStep, h9]; rfl
    rw [hn]
    simp only [lt_gw]
    by_cases h4 : vals[i].effective_balance.val + ut < b
    · simp only [h4, decide_true, if_true]; rfl
    · simp only [h4, decide_false, Bool.false_eq_true, if_false]; rfl
  · simp only [if_neg h3, DM.bind]

theorem e_cond (m : Nat) (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hi : i < vals.length)
    {b dt ut : Nat} (h9 : s.loc 9 = some (.val (.uint gwTy b)))
    (h528 : s.loc 528 = some (.val (.uint u64 dt)))
    (h530 : s.loc 530 = some (.val (.uint u64 ut)))
    (h25 : s.loc 25 = some (.place 0 [11, i])) :
    (den (Scope.env sha) fpsEx (m + 19)).expr pebuFp s
      (.boolop 1249 .or [(.compare 1249 (.binop 1249 .add (.name 1249 9) (.name 1249 528)) [(.lt, (.attr 1249 (.name 1249 25) 113))]), (.compare 1250 (.binop 1250 .add (.attr 1250 (.name 1250 25) 113) (.name 1250 530)) [(.lt, (.name 1250 9))])]) =
      some (condRes b vals[i].effective_balance.val dt ut) := by
  have c1 := e_cmp1 sha (m + 15) hc hi h9 h528 h25
  have c2 := e_cmp2 sha (m + 14) hc hi h9 h530 h25
  rw [show m + 15 + 3 = m + 18 by omega] at c1
  rw [show m + 14 + 4 = m + 18 by omega] at c2
  rw [den_expr]
  simp only [exprStep]
  rw [boolOf, c1]
  unfold condRes
  by_cases h1 : b + dt < 2 ^ 64
  · simp only [if_pos h1, DM.bind, List.isEmpty_cons, Bool.false_eq_true, if_false]
    by_cases h2 : b + dt < vals[i].effective_balance.val
    · simp only [h2, decide_true, if_true, truthy_lift (truthy_b true), DM.ok]
    · simp only [h2, decide_false, if_false, truthy_lift (truthy_b false)]
      rw [boolOf, c2]
      by_cases h3 : vals[i].effective_balance.val + ut < 2 ^ 64
      · simp only [if_pos h3, DM.bind, List.isEmpty_nil, if_true, DM.ok]
      · simp only [if_neg h3, DM.bind]
  · simp only [if_neg h1, DM.bind]
end body

theorem call_of_expr {sha : Oracle} {n : Nat} {fp : Footprint} {s : DSt} {e : Expr} {r : Res DRes}
    (hro : ∀ g args, callHead (Scope.env sha) s e = some (g, args) →
      (fpsEx g).isEmpty = true ∨ ∃ t, (Scope.env sha).globals.lookup g = some (.type t))
    (h : (den (Scope.env sha) fpsEx (n + 1)).expr fp s e = some r) :
    (den (Scope.env sha) fpsEx (n + 1)).call fp s e = some (r.map (·, s.roots)) := by
  rw [den_call, call_ro hro]
  rw [den_expr] at h
  rw [h]; rfl

/-- The callees of the body write nothing: their footprints are empty. -/
theorem ro_body {sha : Oracle} {s : DSt} {e : Expr}
    (h : ∀ g args, callHead (Scope.env sha) s e = some (g, args) → g ≠ 89 ∧ g ≠ 532 ∧ g ≠ 90) :
    ∀ g args, callHead (Scope.env sha) s e = some (g, args) →
      (fpsEx g).isEmpty = true ∨ ∃ t, (Scope.env sha).globals.lookup g = some (.type t) := by
  intro g args hc
  obtain ⟨h1, h2, h3⟩ := h g args hc
  left; simp [fpsEx, h1, h2, h3]

theorem callHead_ne {sha : Oracle} {s : DSt} {l l' : Line} {f : Name} {args : List Arg}
    (hf : f ≠ 89 ∧ f ≠ 532 ∧ f ≠ 90) :
    ∀ g a, callHead (Scope.env sha) s (.call l (.name l' f) args) = some (g, a) →
      g ≠ 89 ∧ g ≠ 532 ∧ g ≠ 90 := by
  intro g a hc
  simp only [callHead] at hc
  split at hc
  · simp at hc; obtain ⟨rfl, rfl⟩ := hc; exact hf
  · cases hc

theorem callHead_noncall {sha : Oracle} {s : DSt} {e : Expr} (he : ∀ l f args, e ≠ .call l f args) :
    ∀ g a, callHead (Scope.env sha) s e = some (g, a) → g ≠ 89 ∧ g ≠ 532 ∧ g ≠ 90 := by
  intro g a hc
  unfold callHead at hc
  split at hc
  · next l l' g' args' => exact absurd rfl (he l _ args')
  · cases hc

/-! ## One iteration -/

def L0 (loc : Name → Option DRes) (i : Nat) : Name → Option DRes :=
  setLoc (setLoc loc 23 (.val (.int i))) 25 (.place 0 [11, i])

def L5 (loc : Name → Option DRes) (i b M : Nat) : Name → Option DRes :=
  setLoc (setLoc (setLoc (setLoc (setLoc (L0 loc i) 9 (.val (.uint gwTy b)))
    526 (.val (.uint u64 250000000))) 528 (.val (.uint u64 250000000)))
    530 (.val (.uint u64 1250000000))) 397 (.val (.uint gwTy M))

theorem pebu_write (ds : List DV) (kV : ListKind) (lV : Option Nat) (vals : List Validator)
    (i : Nat) (hi : i < vals.length) (h11 : 11 < ds.length) (v : Nat) :
    updAt [11, i] (pebuRoot ds kV lV vals) 2 (.leaf (.uint gwTy v)) =
      pebuRoot ds kV lV (vals.set i { vals[i] with effective_balance := ⟨v⟩ }) := by
  have hv : (vals.map Examples.vdv)[i]? = some (Examples.vdv vals[i]) := by
    simp [List.getElem?_eq_getElem hi]
  simp [pebuRoot, updAt, List.getElem?_set, h11, hv, List.map_set]
  rfl

theorem t_eb (sha : Oracle) (m : Nat) {ds : List DV} {kV : ListKind} {lV : Option Nat}
    {kB : ListKind} {lB : Option Nat} {vals : List Validator} {bals : List Gwei} {s : DSt}
    (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hi : i < vals.length)
    (h25 : s.loc 25 = some (.place 0 [11, i])) {v : Nat} (hv : v < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 19)).target pebuFp s (.attr 1252 (.name 1252 25) 113)
      (.val (.uint gwTy v)) =
      some (.ok (.normal, ⟨[pebuRoot ds kV lV (vals.set i { vals[i] with effective_balance := ⟨v⟩ })],
        s.loc⟩)) := by
  have hvx : (vals.map Examples.vdv)[i]? = some (Examples.vdv vals[i]) := by
    simp [List.getElem?_eq_getElem hi]
  have hn : (den (Scope.env sha) fpsEx (m + 18)).expr pebuFp s (.name 1252 25) =
      some (.ok (.place 0 [11, i])) := by
    rw [den_expr]; simp only [exprStep, h25]; rfl
  have hdr : s.deref 0 [11, i] = some (Examples.vdv vals[i]) := by
    simp [DSt.deref, subAt, DV.kids, hc.roots, pebuRoot, List.getElem?_set, hc.l11, hvx]
  have hf : fieldIndex (Scope.env sha) Scope.Id.«Validator» 113 = some (2, .uint gwTy) := by
    simp only [Validation.Tactic.fieldIndex_lit]
  rw [den_target]
  simp only [targetStep]
  rw [hn]
  simp only [DM.bind]
  rw [hdr]
  simp only [Examples.vdv]
  rw [hf]
  simp only [coerce_field_gw sha v hv]
  have hroot : s.roots[0]? = some (pebuRoot ds kV lV vals) := by simp [hc.roots]
  simp only [dWrite, hroot]
  have hw := pebu_write ds kV lV vals i hi hc.l11 v
  have hleaf : leafAt (pebuRoot ds kV lV vals) [11, i] 2 = true := by
    simp [leafAt, subAt, DV.kids, pebuRoot, List.getElem?_set, hc.l11, hvx, Examples.vdv]
  have hfp : fpOk pebuFp s.roots 0 [11, i] = true := by
    simp [fpOk, pebuFp, fpsEx, rootIs, matchesB, hc.roots, pebuRoot]
  simp only [Flat, hfp, hleaf, Bool.and_self, if_true, DM.ok, hc.roots, List.set_cons_zero, hw]
  rfl

theorem newEb_lt {b M : Nat} (hb : b < 2 ^ 64) : newEb b M < 2 ^ 64 := by
  unfold newEb; split <;> omega

/-- The outcome of the `if` of the body. -/
def ifOut (ds : List DV) (kV : ListKind) (lV : Option Nat) (vals : List Validator) (i : Nat)
    (x : Validator) (b M dt ut : Nat) (s : DSt) : Res (Outcome × DSt) :=
  let T : Res (Outcome × DSt) :=
    .ok (.normal, ⟨[pebuRoot ds kV lV (vals.set i { x with effective_balance := ⟨newEb b M⟩ })], s.loc⟩)
  if b + dt < 2 ^ 64 then
    if b + dt < x.effective_balance.val then T
    else if x.effective_balance.val + ut < 2 ^ 64 then
      (if x.effective_balance.val + ut < b then T else .ok (.normal, s))
    else .error .sszValue
  else .error .sszValue

theorem st_if (sha : Oracle) (m : Nat) {ds : List DV} {kV : ListKind} {lV : Option Nat}
    {kB : ListKind} {lB : Option Nat} {vals : List Validator} {bals : List Gwei} {s : DSt}
    (hc : Ctx s ds kV lV kB lB vals bals) {i : Nat} (hi : i < vals.length) {b M dt ut : Nat}
    (hbr : b < 2 ^ 64) (h9 : s.loc 9 = some (.val (.uint gwTy b)))
    (h528 : s.loc 528 = some (.val (.uint u64 dt)))
    (h530 : s.loc 530 = some (.val (.uint u64 ut)))
    (h25 : s.loc 25 = some (.place 0 [11, i])) (h397 : s.loc 397 = some (.val (.uint gwTy M)))
    (h213 : s.loc 213 = none) (h211 : s.loc 211 = none) :
    (den (Scope.env sha) fpsEx (m + 21)).stmt pebuFp s
      (.ifStmt 1248 (.boolop 1249 .or [(.compare 1249 (.binop 1249 .add (.name 1249 9) (.name 1249 528)) [(.lt, (.attr 1249 (.name 1249 25) 113))]), (.compare 1250 (.binop 1250 .add (.attr 1250 (.name 1250 25) 113) (.name 1250 530)) [(.lt, (.name 1250 9))])]) [
        (.assign 1252 [(.attr 1252 (.name 1252 25) 113)] (.call 1252 (.name 1252 213) [(.pos (.binop 1253 .sub (.name 1253 9) (.binop 1253 .mod (.name 1253 9) (.name 1253 211)))), (.pos (.name 1253 397))]))] []) =
      some (ifOut ds kV lV vals i vals[i] b M dt ut s) := by
  have hcond := e_cond sha (m + 1) hc hi h9 h528 h530 h25
  rw [show m + 1 + 19 = m + 20 by omega] at hcond
  have hmin := e_min sha m (s := s) hbr h213 h211 h9 h397
  have hcall := call_of_expr (ro_body (callHead_ne (by decide))) hmin
  have ht := t_eb sha m hc hi h25 (newEb_lt (M := M) hbr)
  have hst : (den (Scope.env sha) fpsEx (m + 20)).stmt pebuFp s
      (.assign 1252 [(.attr 1252 (.name 1252 25) 113)] (.call 1252 (.name 1252 213) [(.pos (.binop 1253 .sub (.name 1253 9) (.binop 1253 .mod (.name 1253 9) (.name 1253 211)))), (.pos (.name 1253 397))])) =
      some (.ok (.normal, ⟨[pebuRoot ds kV lV (vals.set i { vals[i] with effective_balance := ⟨newEb b M⟩ })], s.loc⟩)) := by
    rw [den_stmt]
    simp only [stmtStep]
    rw [hcall]
    exact ht
  have hthen : (den (Scope.env sha) fpsEx (m + 20)).block pebuFp s
      [.assign 1252 [(.attr 1252 (.name 1252 25) 113)] (.call 1252 (.name 1252 213) [(.pos (.binop 1253 .sub (.name 1253 9) (.binop 1253 .mod (.name 1253 9) (.name 1253 211)))), (.pos (.name 1253 397))])] =
      some (.ok (.normal, ⟨[pebuRoot ds kV lV (vals.set i { vals[i] with effective_balance := ⟨newEb b M⟩ })], s.loc⟩)) :=
    (blockOf_ok hst).trans blockOf_nil
  rw [den_stmt]
  simp only [stmtStep]
  rw [hcond]
  simp only [ifOut, condRes]
  by_cases h1 : b + dt < 2 ^ 64
  · simp only [if_pos h1]
    by_cases h2 : b + dt < vals[i].effective_balance.val
    · simp only [if_pos h2, DM.bind, truthy_lift (truthy_b true), if_true]
      exact hthen
    · simp only [if_neg h2]
      by_cases h3 : vals[i].effective_balance.val + ut < 2 ^ 64
      · simp only [if_pos h3, DM.bind]
        by_cases h4 : vals[i].effective_balance.val + ut < b
        · simp only [h4, decide_true, if_true, truthy_lift (truthy_b true)]
          exact hthen
        · simp only [h4, decide_false, if_false, truthy_lift (truthy_b false)]
          exact blockOf_nil (stmt := (den (Scope.env sha) fpsEx (m + 20)).stmt pebuFp)
      · simp only [if_neg h3, DM.bind]
  · simp only [if_neg h1, DM.bind]

theorem ifOut_normal {ds : List DV} {kV : ListKind} {lV : Option Nat} {vals : List Validator}
    {i : Nat} {x : Validator} {b M dt ut : Nat} {s : DSt} :
    ∀ o s', ifOut ds kV lV vals i x b M dt ut s = .ok (o, s') → o = .normal := by
  intro o s' h
  simp only [ifOut] at h
  split at h
  · split at h
    · cases h; rfl
    · split at h
      · split at h <;> (cases h; rfl)
      · cases h
  · cases h

/-- The state after one iteration. -/
def iterOut (ds : List DV) (kV : ListKind) (lV : Option Nat) (vals : List Validator) (i : Nat)
    (x : Validator) (b : Nat) (loc : Name → Option DRes) : Res (Outcome × DSt) :=
  ifOut ds kV lV vals i x b (meb x) 250000000 1250000000 ⟨[pebuRoot ds kV lV vals], L5 loc i b (meb x)⟩

theorem pebu_iter (sha : Oracle) (m : Nat) {ds : List DV} {kV : ListKind} {lV : Option Nat}
    {kB : ListKind} {lB : Option Nat} {vals : List Validator} {bals : List Gwei}
    (hb12 : ds[12]? = some (.list kB (.uint gwTy) lB (bals.map Examples.gleaf)))
    (h11 : 11 < ds.length) {i : Nat} (hi : i < vals.length) (hib : i < bals.length)
    (hbr : bals[i].val < 2 ^ 64) {loc : Name → Option DRes} (hloc : LocOK loc) :
    (den (Scope.env sha) fpsEx (m + 21)).block pebuFp ⟨[pebuRoot ds kV lV vals], L0 loc i⟩ pebuBody =
      some (iterOut ds kV lV vals i vals[i] bals[i].val loc) := by
  have hc : ∀ l, Ctx ⟨[pebuRoot ds kV lV vals], l⟩ ds kV lV kB lB vals bals := fun _ => ⟨rfl, hb12, h11⟩
  -- Statement 1: `balance = state.balances[index]`.
  have e1 := e_balance sha (m + 1) (hc (L0 loc i)) hib (by simp [L0, setLoc, hloc.st]) (by simp [L0, setLoc])
  rw [show m + 1 + 19 = m + 20 by omega] at e1
  have st1 := assign_name (n := m + 19) (l := 1241) (l' := 1241) (x := 9)
    (call_of_expr (ro_body (callHead_noncall (by intro l f args h; cases h))) e1)
  rw [show m + 19 + 2 = m + 21 by omega] at st1
  rw [Sem.block, pebuBody]
  refine (blockOf_ok st1).trans ?_
  -- Statement 2: `HYSTERESIS_INCREMENT = Uint64(EFFECTIVE_BALANCE_INCREMENT // HYSTERESIS_QUOTIENT)`.
  have e2 := e_hi sha (m + 1) (s := ⟨[pebuRoot ds kV lV vals], setLoc (L0 loc i) 9 (.val (.uint gwTy bals[i].val))⟩)
    (by simp [L0, setLoc, hloc.g32]) (by simp [L0, setLoc, hloc.g211]) (by simp [L0, setLoc, hloc.g527])
  rw [show m + 1 + 19 = m + 20 by omega] at e2
  have st2 := assign_name (n := m + 19) (l := 1242) (l' := 1242) (x := 526)
    (call_of_expr (ro_body (callHead_ne (by decide))) e2)
  rw [show m + 19 + 2 = m + 21 by omega] at st2
  refine (blockOf_ok st2).trans ?_
  -- Statements 3 and 4: the thresholds.
  have e3 := e_mul sha (m + 1) (l := 1243) (s := ⟨[pebuRoot ds kV lV vals], setLoc (setLoc (L0 loc i) 9 (.val (.uint gwTy bals[i].val))) 526 (.val (.uint u64 250000000))⟩)
    529 1 250000000 (by simp [setLoc]) (by simp [L0, setLoc, hloc.g529])
    (by simp only [Scope.env, Validation.Tactic.lookup_lit]) c_mul1
  rw [show m + 1 + 19 = m + 20 by omega] at e3
  have st3 := assign_name (n := m + 19) (l := 1243) (l' := 1243) (x := 528)
    (call_of_expr (ro_body (callHead_noncall (by intro l f args h; cases h))) e3)
  rw [show m + 19 + 2 = m + 21 by omega] at st3
  refine (blockOf_ok st3).trans ?_
  have e4 := e_mul sha (m + 1) (l := 1244) (s := ⟨[pebuRoot ds kV lV vals], setLoc (setLoc (setLoc (L0 loc i) 9 (.val (.uint gwTy bals[i].val))) 526 (.val (.uint u64 250000000))) 528 (.val (.uint u64 250000000))⟩)
    531 5 1250000000 (by simp [setLoc]) (by simp [L0, setLoc, hloc.g531])
    (by simp only [Scope.env, Validation.Tactic.lookup_lit]) c_mul5
  rw [show m + 1 + 19 = m + 20 by omega] at e4
  have st4 := assign_name (n := m + 19) (l := 1244) (l' := 1244) (x := 530)
    (call_of_expr (ro_body (callHead_noncall (by intro l f args h; cases h))) e4)
  rw [show m + 19 + 2 = m + 21 by omega] at st4
  refine (blockOf_ok st4).trans ?_
  -- Statement 5: `max_effective_balance = get_max_effective_balance(validator)`.
  have e5 := e_meb sha (m + 1) (hc _) hi (by simp [L0, setLoc, hloc.g361]) (by simp [L0, setLoc])
    (s := ⟨[pebuRoot ds kV lV vals], setLoc (setLoc (setLoc (setLoc (L0 loc i) 9 (.val (.uint gwTy bals[i].val))) 526 (.val (.uint u64 250000000))) 528 (.val (.uint u64 250000000))) 530 (.val (.uint u64 1250000000))⟩)
  rw [show m + 1 + 19 = m + 20 by omega] at e5
  have st5 := assign_name (n := m + 19) (l := 1246) (l' := 1246) (x := 397)
    (call_of_expr (ro_body (callHead_ne (by decide))) e5)
  rw [show m + 19 + 2 = m + 21 by omega] at st5
  refine (blockOf_ok st5).trans ?_
  -- Statement 6: the `if`.
  have hcx : Ctx ⟨[pebuRoot ds kV lV vals], L5 loc i bals[i].val (meb vals[i])⟩ ds kV lV kB lB vals bals := hc _
  have st6 := st_if sha m hcx hi (M := meb vals[i]) (dt := 250000000) (ut := 1250000000) hbr
    (by simp [L5, setLoc]) (by simp [L5, setLoc]) (by simp [L5, setLoc])
    (by simp [L5, L0, setLoc]) (by simp [L5, setLoc])
    (by simp [L5, L0, setLoc, hloc.g213]) (by simp [L5, L0, setLoc, hloc.g211])
  exact blockOf_one st6 ifOut_normal

/-- One iteration of the loop on the validator list. -/
def pebuStep (vals : List Validator) (i : Nat) (x : Validator) (b dt ut : Nat) : Res (List Validator) :=
  if b + dt < 2 ^ 64 then
    if b + dt < x.effective_balance.val then
      .ok (vals.set i { x with effective_balance := ⟨newEb b (meb x)⟩ })
    else if x.effective_balance.val + ut < 2 ^ 64 then
      (if x.effective_balance.val + ut < b then
        .ok (vals.set i { x with effective_balance := ⟨newEb b (meb x)⟩ }) else .ok vals)
    else .error .sszValue
  else .error .sszValue

/-- The loop on the validator list, from item `i`. -/
def pebuLoop (n : Nat) (bals : List Gwei) (dt ut : Nat) (vals : List Validator) (i : Nat) :
    Res (List Validator) :=
  if i < n then
    match vals[i]?, bals[i]? with
    | some x, some g =>
      match pebuStep vals i x g.val dt ut with
      | .error e => .error e
      | .ok v => pebuLoop n bals dt ut v (i + 1)
    | _, _ => .ok vals
  else .ok vals
termination_by n - i

theorem pebuLoop_ge {n : Nat} {bals : List Gwei} {dt ut : Nat} {vals : List Validator} {i : Nat}
    (h : ¬ i < n) : pebuLoop n bals dt ut vals i = .ok vals := by
  rw [pebuLoop, if_neg h]

theorem pebuLoop_lt {n : Nat} {bals : List Gwei} {dt ut : Nat} {vals : List Validator} {i : Nat}
    (h : i < n) (hi : i < vals.length) (hib : i < bals.length) :
    pebuLoop n bals dt ut vals i =
      match pebuStep vals i vals[i] bals[i].val dt ut with
      | .error e => .error e
      | .ok v => pebuLoop n bals dt ut v (i + 1) := by
  rw [pebuLoop, if_pos h, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hib]

theorem ifOut_step (ds : List DV) (kV : ListKind) (lV : Option Nat) (vals : List Validator) (i : Nat)
    (x : Validator) (b dt ut : Nat) (l : Name → Option DRes) :
    ifOut ds kV lV vals i x b (meb x) dt ut ⟨[pebuRoot ds kV lV vals], l⟩ =
      (fun v => (Outcome.normal, (⟨[pebuRoot ds kV lV v], l⟩ : DSt))) <$> pebuStep vals i x b dt ut := by
  simp only [ifOut, pebuStep]
  by_cases h1 : b + dt < 2 ^ 64
  · simp only [if_pos h1]
    by_cases h2 : b + dt < x.effective_balance.val
    · simp only [if_pos h2]; rfl
    · simp only [if_neg h2]
      by_cases h3 : x.effective_balance.val + ut < 2 ^ 64
      · simp only [if_pos h3]
        by_cases h4 : x.effective_balance.val + ut < b
        · simp only [if_pos h4]; rfl
        · simp only [if_neg h4]; rfl
      · simp only [if_neg h3]; rfl
  · simp only [if_neg h1]; rfl

theorem pebuStep_len {vals : List Validator} {i : Nat} {x : Validator} {b dt ut : Nat}
    {v : List Validator} (h : pebuStep vals i x b dt ut = .ok v) : v.length = vals.length := by
  unfold pebuStep at h
  by_cases h1 : b + dt < 2 ^ 64
  · simp only [if_pos h1] at h
    by_cases h2 : b + dt < x.effective_balance.val
    · simp only [if_pos h2] at h; cases h; simp
    · simp only [if_neg h2] at h
      by_cases h3 : x.effective_balance.val + ut < 2 ^ 64
      · simp only [if_pos h3] at h
        by_cases h4 : x.effective_balance.val + ut < b
        · simp only [if_pos h4] at h; cases h; simp
        · simp only [if_neg h4] at h; cases h; rfl
      · simp only [if_neg h3] at h; cases h
  · simp only [if_neg h1] at h; cases h

theorem locOK_L5 {loc : Name → Option DRes} (h : LocOK loc) (i b M : Nat) : LocOK (L5 loc i b M) := by
  unfold L5 L0
  refine LocOK.set (LocOK.set (LocOK.set (LocOK.set (LocOK.set (LocOK.set (LocOK.set h _ _ ?_) _ _ ?_)
    _ _ ?_) _ _ ?_) _ _ ?_) _ _ ?_) _ _ ?_ <;> decide

theorem deref_vals (ds : List DV) (kV : ListKind) (lV : Option Nat) (vals : List Validator)
    (h11 : 11 < ds.length) (l : Name → Option DRes) :
    DSt.deref ⟨[pebuRoot ds kV lV vals], l⟩ 0 [11] =
      some (.list kV (.container Scope.Id.«Validator») lV (vals.map Examples.vdv)) := by
  simp [DSt.deref, subAt, pebuRoot, DV.kids, List.getElem?_set, h11]

theorem pebu_loop (sha : Oracle) (m : Nat) {ds : List DV} {kV : ListKind} {lV : Option Nat}
    {kB : ListKind} {lB : Option Nat} {bals : List Gwei}
    (hb12 : ds[12]? = some (.list kB (.uint gwTy) lB (bals.map Examples.gleaf)))
    (h11 : 11 < ds.length) (hbr : ∀ g ∈ bals, g.val < 2 ^ 64) :
    ∀ d i (vals : List Validator) (loc : Name → Option DRes), vals.length = bals.length →
      d = vals.length - i → LocOK loc →
      ∃ loc', (den (Scope.env sha) fpsEx (m + 22 + d)).loop pebuFp ⟨[pebuRoot ds kV lV vals], loc⟩
          pebuTarget ⟨0, [11], true⟩ i pebuBody =
        some ((fun v => (Outcome.normal, (⟨[pebuRoot ds kV lV v], loc'⟩ : DSt))) <$>
          pebuLoop bals.length bals 250000000 1250000000 vals i) := by
  intro d
  induction d with
  | zero =>
    intro i vals loc hl hd _
    refine ⟨loc, ?_⟩
    have hi : ¬ i < vals.length := by omega
    rw [show m + 22 + 0 = (m + 21) + 1 by omega, den_loop]
    unfold loopStep
    rw [deref_vals ds kV lV vals h11, pebuLoop_ge (by omega)]
    have hn : (vals.map Examples.vdv)[i]? = none := by simp [hi]
    simp only [isByteList, hn]
    simp
    rfl
  | succ d ih =>
    intro i vals loc hl hd hloc
    have hi : i < vals.length := by omega
    have hib : i < bals.length := by omega
    rw [show m + 22 + (d + 1) = (m + 20 + d + 2) + 1 by omega, den_loop]
    unfold loopStep
    rw [deref_vals ds kV lV vals h11]
    have hv : (vals.map Examples.vdv)[i]? = some (Examples.vdv vals[i]) := by
      simp [List.getElem?_eq_getElem hi]
    have hnb : decide (kV = ListKind.list ∧ SszTy.container Scope.Id.«Validator» = SszTy.uint (UintTy.width 8)) = false := by
      simp
    have hbl : bindLoop (m + 20 + d + 2) true ⟨[pebuRoot ds kV lV vals], loc⟩ pebuTarget i
        (ofChild 0 ([11] ++ [i]) (Examples.vdv vals[i])) = some ⟨[pebuRoot ds kV lV vals], L0 loc i⟩ := rfl
    have hit := pebu_iter sha (m + d + 1) (kV := kV) (lV := lV) hb12 h11 hi hib
      (hbr _ (List.getElem_mem hib)) hloc
    rw [show m + d + 1 + 21 = m + 20 + d + 2 by omega] at hit
    simp only [isByteList, hv, hnb, Bool.false_eq_true, if_false, hbl]
    rw [Sem.block] at hit
    rw [Sem.block, hit, iterOut, ifOut_step]
    rw [pebuLoop_lt hib hi hib]
    cases hps : pebuStep vals i vals[i] bals[i].val 250000000 1250000000 with
    | error e => exact ⟨loc, rfl⟩
    | ok v =>
      have hvl := pebuStep_len hps
      obtain ⟨loc', hl'⟩ := ih (i + 1) v (L5 loc i bals[i].val (meb vals[i])) (by omega) (by omega)
        (locOK_L5 hloc _ _ _)
      rw [show m + 22 + d = m + 20 + d + 2 by omega] at hl'
      refine ⟨loc', ?_⟩
      simp only [Functor.map, Except.map, DM.bind]
      exact hl'

theorem root_eq {ds : List DV} {kV : ListKind} {lV : Option Nat} {vals : List Validator}
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (vals.map Examples.vdv))) :
    DV.cont Scope.Id.«BeaconState» ds = pebuRoot ds kV lV vals := by
  have h11 : 11 < ds.length := by
    rcases Nat.lt_or_ge 11 ds.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv; cases hv
  rw [List.getElem?_eq_getElem h11, Option.some.injEq] at hv
  simp only [pebuRoot, ← hv, List.set_getElem_self]

theorem e_vals (sha : Oracle) (n : Nat) {s : DSt} {ds : List DV} {kV : ListKind} {lV : Option Nat}
    {vals : List Validator} (hr : s.roots = [pebuRoot ds kV lV vals]) (h11 : 11 < ds.length)
    (h1 : s.loc 1 = some (.place 0 [])) :
    (den (Scope.env sha) fpsEx (n + 2)).expr pebuFp s (.attr 1240 (.name 1240 1) 27) =
      some (.ok (.place 0 [11])) := by
  simp [exprStep, DM.bind, DM.ok, h1, dAttr, DSt.deref, subAt, DV.kids, ofChild, hr, pebuRoot,
    Validation.Tactic.fieldIndex_lit, List.getElem?_set, h11]

theorem pebu_iterSrc (sha : Oracle) (n : Nat) {s : DSt} {ds : List DV} {kV : ListKind}
    {lV : Option Nat} {vals : List Validator} (hr : s.roots = [pebuRoot ds kV lV vals])
    (h11 : 11 < ds.length) (h1 : s.loc 1 = some (.place 0 [])) (h216 : s.loc 216 = none) :
    (den (Scope.env sha) fpsEx (n + 3)).iter pebuFp s pebuIter = some (.ok ⟨0, [11], true⟩) := by
  have he := e_vals sha n hr h11 h1
  have hen : isEnumerate (Scope.env sha) 216 = true := by
    simp only [isEnumerate, Scope.env, Validation.Tactic.lookup_lit]
  have hlp : listPlace s 0 [11] = true := by
    simp [listPlace, DSt.deref, subAt, DV.kids, hr, pebuRoot, List.getElem?_set, h11, isByteList]
  rw [den_iter, pebuIter]
  simp only [iterStep, h216, Option.isNone_none, hen, Bool.and_self, if_true, DM.bind, he, hlp]
  rfl

theorem pebu_den (sha : Oracle) (m : Nat) {ds : List DV} {kV : ListKind} {lV : Option Nat}
    {kB : ListKind} {lB : Option Nat} {vals : List Validator} {bals : List Gwei}
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (vals.map Examples.vdv)))
    (hb12 : ds[12]? = some (.list kB (.uint gwTy) lB (bals.map Examples.gleaf)))
    (hl : vals.length = bals.length) (hbr : ∀ g ∈ bals, g.val < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 24 + vals.length)).fn pebuFp
        Scope.fn_process_effective_balance_updates [.cont Scope.Id.«BeaconState» ds] =
      some ((fun v => (Value.none, [pebuRoot ds kV lV v])) <$>
        pebuLoop bals.length bals 250000000 1250000000 vals 0) := by
  have h11 : 11 < ds.length := by
    rcases Nat.lt_or_ge 11 ds.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv; cases hv
  rw [root_eq hv]
  let loc0 : Name → Option DRes := setLoc (fun _ => none) 1 (.place 0 [])
  have hloc : LocOK loc0 := ⟨by simp [loc0, setLoc], by simp [loc0, setLoc], by simp [loc0, setLoc],
    by simp [loc0, setLoc], by simp [loc0, setLoc], by simp [loc0, setLoc], by simp [loc0, setLoc],
    by simp [loc0, setLoc]⟩
  obtain ⟨loc', hlp⟩ := pebu_loop sha m (kV := kV) (lV := lV) hb12 h11 hbr vals.length 0 vals loc0 hl
    (by omega) hloc
  have hit := pebu_iterSrc sha (m + 19 + vals.length) (s := ⟨[pebuRoot ds kV lV vals], loc0⟩)
    rfl h11 (by simp [loc0, setLoc]) (by simp [loc0, setLoc])
  rw [show m + 19 + vals.length + 3 = m + 22 + vals.length by omega] at hit
  have hst : (den (Scope.env sha) fpsEx (m + 23 + vals.length)).stmt pebuFp
      ⟨[pebuRoot ds kV lV vals], loc0⟩ (.forStmt 1240 pebuTarget pebuIter pebuBody) =
      some ((fun v => (Outcome.normal, (⟨[pebuRoot ds kV lV v], loc'⟩ : DSt))) <$>
        pebuLoop bals.length bals 250000000 1250000000 vals 0) := by
    rw [show m + 23 + vals.length = (m + 22 + vals.length) + 1 by omega, den_stmt]
    simp only [stmtStep, hit, DM.bind]
    exact hlp
  rw [show m + 24 + vals.length = (m + 23 + vals.length) + 1 by omega, den_fn]
  have hinit : initLoc [pebuRoot ds kV lV vals] (fun _ => none)
      Scope.fn_process_effective_balance_updates.params.names.zipIdx = loc0 := rfl
  simp only [fnStep]
  rw [if_pos ⟨rfl, rfl, rfl⟩, hinit, pebu_body_eq, Sem.block]
  cases hpl : pebuLoop bals.length bals 250000000 1250000000 vals 0 with
  | error e =>
    rw [hpl] at hst
    rw [blockOf_err hst]
    rfl
  | ok v =>
    rw [hpl] at hst
    rw [blockOf_ok hst, blockOf_nil]
    rfl

theorem rd_lget {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    lget xs (i : Int) = pure xs[i] := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  have hl : (i : Int) < (xs.length : Int) := by omega
  simp [lget, Rd.pyIndex, hneg, hl, List.getElem?_eq_getElem h]

theorem rd_lset {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) (x : α) :
    lset xs (i : Int) x = pure (xs.set i x) := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  have hl : (i : Int) < (xs.length : Int) := by omega
  simp [lset, Rd.pyIndex, hneg, hl]

theorem rd_hi : (uOp .floorDiv (uv EFFECTIVE_BALANCE_INCREMENT) (uv HYSTERESIS_QUOTIENT) : SpecM Gwei) =
    pure ⟨250000000⟩ := by
  simp [uOp, uOf, erase, intArith, uv, EFFECTIVE_BALANCE_INCREMENT, HYSTERESIS_QUOTIENT, Int.fdiv,
    Except.mapError, UintC.val, UintC.bits, UintC.ofNat]

theorem rd_cast : (uCast Uint64 (⟨250000000⟩ : Gwei)) = pure ⟨250000000⟩ := by
  simp [uCast, uOf, uv, UintC.val, UintC.bits, UintC.ofNat]

theorem rd_mul1 : (uOp .mul (uv (⟨250000000⟩ : Uint64)) (uv HYSTERESIS_DOWNWARD_MULTIPLIER) : SpecM Uint64) =
    pure ⟨250000000⟩ := by
  simp [uOp, uOf, erase, intArith, uv, HYSTERESIS_DOWNWARD_MULTIPLIER, Except.mapError, UintC.val,
    UintC.bits, UintC.ofNat]

theorem rd_mul5 : (uOp .mul (uv (⟨250000000⟩ : Uint64)) (uv HYSTERESIS_UPWARD_MULTIPLIER) : SpecM Uint64) =
    pure ⟨1250000000⟩ := by
  simp [uOp, uOf, erase, intArith, uv, HYSTERESIS_UPWARD_MULTIPLIER, Except.mapError, UintC.val,
    UintC.bits, UintC.ofNat]

theorem rd_add (a : Gwei) (c : Uint64) :
    (uOp .add (uv a) (uv c) : SpecM Gwei) =
      if a.val + c.val < 2 ^ 64 then pure ⟨a.val + c.val⟩ else throw .bug := by
  by_cases h : a.val + c.val < 2 ^ 64
  · have h' : (a.val : Int) + c.val < 2 ^ 64 := by omega
    simp [uOp, uOf, erase, intArith, uv, Except.mapError, UintC.val, UintC.bits, UintC.ofNat, h]
    rw [if_pos (by omega)]
    congr 2
  · have h' : ¬ (a.val : Int) + c.val < 2 ^ 64 := by omega
    simp [uOp, uOf, erase, intArith, uv, Except.mapError, UintC.val, UintC.bits, UintC.ofNat, h]
    omega

theorem rd_mod (a : Gwei) (ha : a.val < 2 ^ 64) :
    (uOp .mod (uv a) (uv EFFECTIVE_BALANCE_INCREMENT) : SpecM Gwei) = pure ⟨a.val % 1000000000⟩ := by
  simp [uOp, uOf, erase, intArith, uv, Except.mapError, UintC.val, UintC.bits, UintC.ofNat,
    EFFECTIVE_BALANCE_INCREMENT]
  have hf : (a.val : Int).fmod 1000000000 = ((a.val % 1000000000 : Nat) : Int) := by
    rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]; omega
  rw [hf, if_pos (by omega)]
  rfl

theorem rd_sub (a : Gwei) (c : Nat) (hc : c ≤ a.val) (ha : a.val < 2 ^ 64) :
    (uOp .sub (uv a) (uv (⟨c⟩ : Gwei)) : SpecM Gwei) = pure ⟨a.val - c⟩ := by
  simp [uOp, uOf, erase, intArith, uv, Except.mapError, UintC.val, UintC.bits, UintC.ofNat]
  exact ⟨hc, by omega⟩

theorem rd_min (a M : Gwei) : pyMin [a, M] = pure (if M.val < a.val then M else a) := by
  simp [pyMin, PyOrd.lt]

theorem uval_u64 (n : Nat) : UintC.val (Uint64.mk n) = n := rfl
theorem uval_gw (n : Nat) : UintC.val (Gwei.mk n) = n := rfl

theorem rd_min_neweb (g : Gwei) (M : Nat) :
    pyMin [(⟨g.val - g.val % 1000000000⟩ : Gwei), (⟨M⟩ : Gwei)] = pure (⟨newEb g.val M⟩ : Gwei) := by
  rw [rd_min]
  unfold newEb
  simp only []
  by_cases h : M < g.val - g.val % 1000000000
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

theorem rd_neweb (b M : Nat) (hb : b < 2 ^ 64) :
    (do
      let r ← (uOp .mod (uv (⟨b⟩ : Gwei)) (uv EFFECTIVE_BALANCE_INCREMENT) : SpecM Gwei)
      let d ← (uOp .sub (uv (⟨b⟩ : Gwei)) (uv r) : SpecM Gwei)
      pyMin [d, (⟨M⟩ : Gwei)]) = pure (⟨newEb b M⟩ : Gwei) := by
  rw [rd_mod ⟨b⟩ hb, pure_bind, rd_sub ⟨b⟩ _ (Nat.mod_le _ _) hb, pure_bind, rd_min]
  unfold newEb
  simp only []
  by_cases h : M < b - b % 1000000000
  · simp only [if_pos h]
  · simp only [if_neg h]

section pstep
variable {vals : List Validator} {i : Nat} {x : Validator} {b dt ut : Nat}

theorem pebuStep_e1 (h1 : ¬ b + dt < 2 ^ 64) : pebuStep vals i x b dt ut = .error .sszValue := by
  simp only [pebuStep, if_neg h1]

theorem pebuStep_t1 (h1 : b + dt < 2 ^ 64) (h2 : b + dt < x.effective_balance.val) :
    pebuStep vals i x b dt ut = .ok (vals.set i { x with effective_balance := ⟨newEb b (meb x)⟩ }) := by
  simp only [pebuStep, if_pos h1, if_pos h2]

theorem pebuStep_e2 (h1 : b + dt < 2 ^ 64) (h2 : ¬ b + dt < x.effective_balance.val)
    (h3 : ¬ x.effective_balance.val + ut < 2 ^ 64) : pebuStep vals i x b dt ut = .error .sszValue := by
  simp only [pebuStep, if_pos h1, if_neg h2, if_neg h3]

theorem pebuStep_t2 (h1 : b + dt < 2 ^ 64) (h2 : ¬ b + dt < x.effective_balance.val)
    (h3 : x.effective_balance.val + ut < 2 ^ 64) (h4 : x.effective_balance.val + ut < b) :
    pebuStep vals i x b dt ut = .ok (vals.set i { x with effective_balance := ⟨newEb b (meb x)⟩ }) := by
  simp only [pebuStep, if_pos h1, if_neg h2, if_pos h3, if_pos h4]

theorem pebuStep_f (h1 : b + dt < 2 ^ 64) (h2 : ¬ b + dt < x.effective_balance.val)
    (h3 : x.effective_balance.val + ut < 2 ^ 64) (h4 : ¬ x.effective_balance.val + ut < b) :
    pebuStep vals i x b dt ut = .ok vals := by
  simp only [pebuStep, if_pos h1, if_neg h2, if_pos h3, if_neg h4]
end pstep

theorem rd_iter (n1 i : Nat) (D H U : Uint64) (b M : Gwei) (st : BeaconState) (hi : i < n1)
    (hv : i < st.validators.length) (hb : i < st.balances.length) (hbr : st.balances[i].val < 2 ^ 64) :
    process_effective_balance_updates.loop1 n1 i D H U b M st =
      match pebuStep st.validators i st.validators[i] st.balances[i].val 250000000 1250000000 with
      | .error _ => throw .bug
      | .ok v => process_effective_balance_updates.loop1 n1 (i + 1) ⟨250000000⟩ ⟨250000000⟩
          ⟨1250000000⟩ st.balances[i] ⟨meb st.validators[i]⟩ { st with validators := v } := by
  rw [process_effective_balance_updates.loop1, dif_pos hi]
  simp only [rd_lget _ _ hb, rd_lget _ _ hv, rd_hi, rd_cast, rd_mul1, rd_mul5, gmeb_read, pure_bind,
    rd_add, ok_bind]
  by_cases h1 : st.balances[i].val + 250000000 < 2 ^ 64
  · rw [if_pos h1, pure_bind]
    have hthen : ∀ (k : List Validator → SpecM (Uint64 × Uint64 × Uint64 × Gwei × Gwei × BeaconState)),
        (do
          let r ← (uOp .mod (uv st.balances[i]) (uv EFFECTIVE_BALANCE_INCREMENT) : SpecM Gwei)
          let d ← (uOp .sub (uv st.balances[i]) (uv r) : SpecM Gwei)
          let e ← pyMin [d, (⟨meb st.validators[i]⟩ : Gwei)]
          let v ← lset st.validators (i : Int) { st.validators[i] with effective_balance := e }
          k v) = k (st.validators.set i { st.validators[i] with
            effective_balance := ⟨newEb st.balances[i].val (meb st.validators[i])⟩ }) := by
      intro k
      rw [rd_mod _ hbr, pure_bind, rd_sub _ _ (Nat.mod_le _ _) hbr, pure_bind, rd_min_neweb, pure_bind,
        rd_lset _ _ hv, pure_bind]
    by_cases h2 : st.balances[i].val + 250000000 < st.validators[i].effective_balance.val
    · have h2' : uv (⟨st.balances[i].val + 250000000⟩ : Gwei) < uv st.validators[i].effective_balance := by
        show ((st.balances[i].val + 250000000 : Nat) : Int) < (st.validators[i].effective_balance.val : Int)
        omega
      rw [decide_eq_true h2', if_pos rfl, pure_bind, if_pos rfl, pebuStep_t1 h1 h2]
      exact hthen _
    · have h2' : ¬ uv (⟨st.balances[i].val + 250000000⟩ : Gwei) < uv st.validators[i].effective_balance := by
        show ¬ ((st.balances[i].val + 250000000 : Nat) : Int) < (st.validators[i].effective_balance.val : Int)
        omega
      rw [decide_eq_false h2']
      simp only [Bool.false_eq_true, if_false]
      by_cases h3 : st.validators[i].effective_balance.val + 1250000000 < 2 ^ 64
      · rw [if_pos h3, pure_bind, pure_bind]
        by_cases h4 : st.validators[i].effective_balance.val + 1250000000 < st.balances[i].val
        · have h4' : uv (⟨st.validators[i].effective_balance.val + 1250000000⟩ : Gwei) < uv st.balances[i] := by
            show ((st.validators[i].effective_balance.val + 1250000000 : Nat) : Int) < (st.balances[i].val : Int)
            omega
          rw [decide_eq_true h4', if_pos rfl, pebuStep_t2 h1 h2 h3 h4]
          exact hthen _
        · have h4' : ¬ uv (⟨st.validators[i].effective_balance.val + 1250000000⟩ : Gwei) < uv st.balances[i] := by
            show ¬ ((st.validators[i].effective_balance.val + 1250000000 : Nat) : Int) < (st.balances[i].val : Int)
            omega
          rw [decide_eq_false h4', pebuStep_f h1 h2 h3 h4]
          simp only [Bool.false_eq_true, if_false]
      · rw [if_neg h3, pebuStep_e2 h1 h2 h3]
        rfl
  · rw [if_neg h1, pebuStep_e1 h1]
    rfl

theorem pebuStep_err {vals : List Validator} {i : Nat} {x : Validator} {b dt ut : Nat} {e : SpecError}
    (h : pebuStep vals i x b dt ut = .error e) : e = .sszValue := by
  by_cases h1 : b + dt < 2 ^ 64
  · by_cases h2 : b + dt < x.effective_balance.val
    · rw [pebuStep_t1 h1 h2] at h; cases h
    · by_cases h3 : x.effective_balance.val + ut < 2 ^ 64
      · by_cases h4 : x.effective_balance.val + ut < b
        · rw [pebuStep_t2 h1 h2 h3 h4] at h; cases h
        · rw [pebuStep_f h1 h2 h3 h4] at h; cases h
      · rw [pebuStep_e2 h1 h2 h3] at h; cases h; rfl
  · rw [pebuStep_e1 h1] at h; cases h; rfl

theorem rd_loop (bals : List Gwei) (hbr : ∀ g ∈ bals, g.val < 2 ^ 64) (n1 : Nat) :
    ∀ d i (st : BeaconState) D H U b M, st.balances = bals → st.validators.length = bals.length →
      n1 = bals.length → d = n1 - i →
      (fun r => r.2.2.2.2.2) <$> process_effective_balance_updates.loop1 n1 i D H U b M st =
        erase ((fun v => { st with validators := v }) <$>
          pebuLoop bals.length bals 250000000 1250000000 st.validators i) := by
  intro d
  induction d with
  | zero =>
    intro i st D H U b M hb hl hn hd
    rw [process_effective_balance_updates.loop1, dif_neg (by omega), pebuLoop_ge (by omega)]
    rfl
  | succ d ih =>
    intro i st D H U b M hb hl hn hd
    have hv : i < st.validators.length := by omega
    have hib : i < st.balances.length := by rw [hb]; omega
    have hbi : st.balances[i].val < 2 ^ 64 := hbr _ (by simp only [← hb]; exact List.getElem_mem hib)
    rw [rd_iter n1 i D H U b M st (by omega) hv hib hbi]
    have hlt := pebuLoop_lt (n := bals.length) (bals := bals) (dt := 250000000) (ut := 1250000000)
      (vals := st.validators) (by omega) hv (by omega)
    have hgi : bals[i]'(by omega) = st.balances[i] := by simp only [hb]
    rw [hlt, hgi]
    cases hps : pebuStep st.validators i st.validators[i] st.balances[i].val 250000000 1250000000 with
    | error e =>
      rw [pebuStep_err hps]
      rfl
    | ok v =>
      have hvl := pebuStep_len hps
      exact ih (i + 1) { st with validators := v } _ _ _ _ _ hb (by simp only []; omega) hn (by omega)

theorem pebu_read (st : BeaconState) (hl : st.validators.length = st.balances.length)
    (hbr : ∀ g ∈ st.balances, g.val < 2 ^ 64) :
    process_effective_balance_updates st =
      erase ((fun v => { st with validators := v }) <$>
        pebuLoop st.balances.length st.balances 250000000 1250000000 st.validators 0) := by
  have h := rd_loop st.balances hbr st.validators.length _ 0 st default default default default default
    rfl hl hl rfl
  rw [← h]
  simp only [process_effective_balance_updates, bind_pure_comp]

/-- The validator list field after the loop. -/
def pebuOut (ds : List DV) (kV : ListKind) (lV : Option Nat) (st' : BeaconState) : DV :=
  .cont Scope.Id.«BeaconState»
    (ds.set 11 (.list kV (.container Scope.Id.«Validator») lV (st'.validators.map Examples.vdv)))

/-- The denotation of `process_effective_balance_updates` is the readable function, on the
validators field. -/
theorem process_effective_balance_updates_denote (sha : Oracle) (m : Nat) (ds : List DV)
    (kV : ListKind) (lV : Option Nat) (kB : ListKind) (lB : Option Nat) (st : BeaconState)
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (st.validators.map Examples.vdv)))
    (hb : ds[12]? = some (.list kB (.uint gwTy) lB (st.balances.map Examples.gleaf)))
    (hl : st.validators.length = st.balances.length) (hbr : ∀ g ∈ st.balances, g.val < 2 ^ 64) :
    ((den (Scope.env sha) fpsEx (m + 24 + st.validators.length)).fn pebuFp
        Scope.fn_process_effective_balance_updates [.cont Scope.Id.«BeaconState» ds]).map
        (Except.mapError SpecError.fail) =
      some ((fun st' : BeaconState => (Value.none, [pebuOut ds kV lV st'])) <$>
        process_effective_balance_updates st) := by
  rw [pebu_den sha m hv hb hl hbr, pebu_read st hl hbr]
  cases pebuLoop st.balances.length st.balances 250000000 1250000000 st.validators 0 <;> rfl

/-- SPEC 9.2 for `process_effective_balance_updates`: a loop over a live list, with a write
through the loop variable. -/
theorem process_effective_balance_updates_l4 (sha : Oracle) (gfp : Footprint) (h : Heap)
    (r0 n : Nat) (ds : List DV) (kV : ListKind) (lV : Option Nat) (kB : ListKind) (lB : Option Nat)
    (st : BeaconState) (hd : dec h n (.ref r0) = some (.cont Scope.Id.«BeaconState» ds))
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (st.validators.map Examples.vdv)))
    (hb : ds[12]? = some (.list kB (.uint gwTy) lB (st.balances.map Examples.gleaf)))
    (hl : st.validators.length = st.balances.length) (hbr : ∀ g ∈ st.balances, g.val < 2 ^ 64)
    (hw : WTree h [.ref r0] pebuFp) :
    ∀ fuel, 24 + st.validators.length ≤ fuel →
      ResultMatches gfp pebuFp h [.ref r0]
        (fun (st' : BeaconState) h' v => v = .none ∧
          ∃ m, dec h' m (.ref r0) = some (pebuOut ds kV lV st'))
        (interp (Scope.env sha) fuel Scope.Id.«process_effective_balance_updates» [.ref r0] h)
        (process_effective_balance_updates st) := by
  intro fuel hf
  have hden := process_effective_balance_updates_denote sha 0 ds kV lV kB lB st hv hb hl hbr
  rw [Nat.zero_add] at hden
  cases hdn : (den (Scope.env sha) fpsEx (24 + st.validators.length)).fn pebuFp
      Scope.fn_process_effective_balance_updates [.cont Scope.Id.«BeaconState» ds] with
  | none => rw [hdn] at hden; cases hden
  | some r =>
    rw [hdn] at hden
    simp only [Option.map_some, Option.some.injEq] at hden
    have hdec : DecArgs h [.ref r0] [.cont Scope.Id.«BeaconState» ds] := by
      refine ⟨rfl, fun k v d hv hd' => ?_⟩
      match k, hv, hd' with
      | 0, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨n, hd⟩
      | _ + 1, hv, _ => simp at hv
    have hm := denote_sound_calls (Scope.env sha) fpsEx (libFlat_ssz _) gfp pebuFp
      (f := Scope.Id.«process_effective_balance_updates»)
      (by simp only [Scope.env, Validation.Tactic.lookup_lit]) hdec hw hdn
    rw [hden] at hm
    refine resultMatches_mono hf (Examples.resultMatches_map (fun st' h' v he => ⟨he.1, ?_⟩) hm)
    obtain ⟨-, hr⟩ := he.2
    exact hr 0 (.ref r0) _ rfl rfl

end SpecLean.Layer4.Examples3
