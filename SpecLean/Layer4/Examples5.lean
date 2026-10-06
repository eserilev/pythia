import SpecLean.Layer4.Examples4

/-!
# Layer 4: a function that makes a new list (`get_active_validator_indices`)

`return [ValidatorIndex(i) for i, v in enumerate(state.validators) if is_active_validator(v, epoch)]`

The comprehension makes a new Python list of flat values. The denotation gives its tree
(`DRes.tree`), and the soundness theorem relates it to the interpreter's new reference by
decoding: the result list decodes to the readable list, and the state is unchanged.

- `iav_den`: the summary of `is_active_validator`, a chained comparison.
- `gavi_items`: the items of the comprehension, by induction on the items left, one fuel unit
  per item. The pure list is `gaviL`.
- `gavi_den`, `gavi_read`, `get_active_validator_indices_denote`, `get_active_validator_indices_l4`.
-/

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd SpecLean.Rd.Gen SpecLean.Layer4.Examples2
  SpecLean.Layer4.Examples3 SpecLean.Layer4.Examples4

attribute [local instance high] LibModel.toLibValues

namespace SpecLean.Layer4.Examples5


abbrev epTy' : UintTy := Examples.epochTy

/-- Is validator `x` active at epoch `e`. -/
def act (x : Validator) (e : Nat) : Bool :=
  decide (x.activation_epoch.val ≤ e) && decide (e < x.exit_epoch.val)

theorem le_ep (a b : Nat) : cmpF .ltE (.uint epTy' a) (.uint epTy' b) = some (.ok (decide (a ≤ b))) := by
  refine cmpF_eval ?_ (by simp)
  show (do let _ ← resolveUint epTy' epTy'; pure (cmpInt .ltE (a : Int) b) : Res Bool) = _
  simp [resolveUint, cmpInt]

theorem lt_ep (a b : Nat) : cmpF .lt (.uint epTy' a) (.uint epTy' b) = some (.ok (decide (a < b))) := by
  refine cmpF_eval ?_ (by simp)
  show (do let _ ← resolveUint epTy' epTy'; pure (cmpInt .lt (a : Int) b) : Res Bool) = _
  simp [resolveUint, cmpInt]

theorem iav_cmp (sha : Oracle) (fp : Footprint) (m : Nat) {s : DSt} (x : Validator) (e : Nat)
    (hr : s.roots = [Examples.vdv x, .leaf (.uint epTy' e)])
    (h25 : s.loc 25 = some (.place 0 [])) (h103 : s.loc 103 = some (.val (.uint epTy' e))) :
    (den (Scope.env sha) fpsEx (m + 4)).expr fp s
      (.compare 1095 (.attr 1095 (.name 1095 25) 394) [(.ltE, (.name 1095 103)), (.lt, (.attr 1095 (.name 1095 25) 395))]) =
      some (.ok (.val (.bool (act x e)))) := by
  unfold act
  have hf1 := le_ep x.activation_epoch.val e
  have hf2 := lt_ep e x.exit_epoch.val
  by_cases h1 : x.activation_epoch.val ≤ e
  · simp [exprStep, DM.bind, DM.ok, h25, h103, dAttr, DSt.deref, subAt, DV.kids, ofChild, hr,
      Examples.vdv, Validation.Tactic.fieldIndex_lit, cmpOf, hf1, h1, hf2]
    by_cases h2 : e < x.exit_epoch.val <;> simp [h2]
  · simp [exprStep, DM.bind, DM.ok, h25, h103, dAttr, DSt.deref, subAt, DV.kids, ofChild, hr,
      Examples.vdv, Validation.Tactic.fieldIndex_lit, cmpOf, hf1, h1]

theorem iav_den (sha : Oracle) (fp : Footprint) (m : Nat) (x : Validator) (e : Nat) :
    (den (Scope.env sha) fpsEx (m + 6)).fn fp Scope.fn_is_active_validator
        [Examples.vdv x, .leaf (.uint epTy' e)] =
      some (.ok (.val (.bool (act x e)), [Examples.vdv x, .leaf (.uint epTy' e)])) := by
  let s0 : DSt := ⟨[Examples.vdv x, .leaf (.uint epTy' e)],
    setLoc (setLoc (fun _ => none) 25 (.place 0 [])) 103 (.val (.uint epTy' e))⟩
  have hc := iav_cmp sha fp m x e (s := s0) rfl (by simp [s0, setLoc]) (by simp [s0, setLoc])
  have hr : (den (Scope.env sha) fpsEx (m + 5)).stmt fp s0
      (.ret 1095 (some (.compare 1095 (.attr 1095 (.name 1095 25) 394) [(.ltE, (.name 1095 103)), (.lt, (.attr 1095 (.name 1095 25) 395))]))) =
      some (.ok (.ret (.val (.bool (act x e))), s0)) := by
    rw [show m + 5 = (m + 4) + 1 by omega, den_stmt]; simp only [stmtStep]; rw [hc]; rfl
  have hb : (den (Scope.env sha) fpsEx (m + 5)).block fp
      ⟨[Examples.vdv x, .leaf (.uint epTy' e)], initLoc [Examples.vdv x, .leaf (.uint epTy' e)] (fun _ => none)
        Scope.fn_is_active_validator.params.names.zipIdx⟩ Scope.fn_is_active_validator.body =
      some (.ok (.ret (.val (.bool (act x e))), s0)) :=
    blockOf_ret hr
  rw [show m + 6 = (m + 5) + 1 by omega, den_fn]
  simp only [fnStep]
  rw [if_pos ⟨rfl, rfl, rfl⟩, hb]
  rfl

theorem ctor_vi_int (env : Env) (h : Heap) (j : Nat) (hj : j < 2 ^ 64) :
    LibModel.construct env h (.uint viTy) [.int (j : Int)] [] = .ok (.uint viTy j, h) := by
  show (do pure (← wrapUint viTy (j : Int), h)) = _
  have h' : (0 : Int) ≤ (j : Int) ∧ (j : Int) < 2 ^ viTy.bits := by show _ ∧ _ < 2 ^ 64; omega
  simp only [wrapUint, if_pos h', Int.toNat_natCast]
  rfl

theorem c_iav (sha : Oracle) (fp : Footprint) (n : Nat) {s : DSt} {x : Validator} {j e : Nat}
    (h78 : s.loc 78 = some (.place 0 [11, j])) (hdr : s.deref 0 [11, j] = some (Examples.vdv x))
    (h103 : s.loc 103 = some (.val (.uint epTy' e))) (h215 : s.loc 215 = none) :
    (den (Scope.env sha) fpsEx (n + 8)).expr fp s
      (.call 1474 (.name 1474 215) [(.pos (.name 1474 78)), (.pos (.name 1474 103))]) =
      some (.ok (.val (.bool (act x e)))) := by
  have a1 : (den (Scope.env sha) fpsEx (n + 7)).expr fp s (.name 1474 78) = some (.ok (.place 0 [11, j])) := by
    rw [show n + 7 = (n + 6) + 1 by omega, den_expr]; simp only [exprStep, h78]; rfl
  have a2 : (den (Scope.env sha) fpsEx (n + 7)).expr fp s (.name 1474 103) = some (.ok (.val (.uint epTy' e))) := by
    rw [show n + 7 = (n + 6) + 1 by omega, den_expr]; simp only [exprStep, h103]; rfl
  have hr : [DRes.place 0 [11, j], DRes.val (.uint epTy' e)].mapM (argRoot s) =
      some [Examples.vdv x, .leaf (.uint epTy' e)] := by
    simp [List.mapM, List.mapM.loop, argRoot, hdr]
  exact e_callfn (n := n + 6) (by simp only [Scope.env, Validation.Tactic.lookup_lit]) (by decide) h215
    (args2 a1 a2) hr (iav_den sha [] (n + 1) x e) rfl

theorem c_vi (sha : Oracle) (fp : Footprint) (n : Nat) {s : DSt} {j : Nat} (hj : j < 2 ^ 64)
    (h115 : s.loc 115 = some (.val (.int (j : Int)))) (h82 : s.loc 82 = none) :
    (den (Scope.env sha) fpsEx (n + 3)).expr fp s (.call 1474 (.name 1474 82) [(.pos (.name 1474 115))]) =
      some (.ok (.val (.uint viTy j))) := by
  have a1 : (den (Scope.env sha) fpsEx (n + 2)).expr fp s (.name 1474 115) = some (.ok (.val (.int (j : Int)))) := by
    rw [show n + 2 = (n + 1) + 1 by omega, den_expr]; simp only [exprStep, h115]; rfl
  have hh : callHead (Scope.env sha) s (.call 1474 (.name 1474 82) [(.pos (.name 1474 115))]) =
      some (82, [(.pos (.name 1474 115))]) := by
    simp [callHead, h82, callable, Scope.env, Validation.Tactic.lookup_lit]
  have hl : (Scope.env sha).globals.lookup 82 = some (.type (.uint viTy)) := by
    simp only [Scope.env, Validation.Tactic.lookup_lit]
  have hc := dCtor_eval (env := Scope.env sha) (t := .uint viTy) (rs := [.val (.int (j : Int))]) rfl rfl
    (ctor_vi_int _ _ j hj) rfl
  rw [show n + 3 = (n + 2) + 1 by omega, den_expr]
  simp only [exprStep, hh]
  rw [args1 a1, dm_bind_ok]
  simp only [dCallRO, hl]
  exact hc

/-- The active indices of `xs`, numbered from `j`. -/
def gaviL (e : Nat) : List Validator → Nat → List Nat
  | [], _ => []
  | x :: xs, j => (if act x e then [j] else []) ++ gaviL e xs (j + 1)

def viLeaf (k : Nat) : DV := .leaf (.uint viTy k)

abbrev gaviTarget : Target := .tuple 1474 [(.name 1474 115), (.name 1474 78)]
abbrev gaviIfs : List Expr := [(.call 1474 (.name 1474 215) [(.pos (.name 1474 78)), (.pos (.name 1474 103))])]
abbrev gaviElt : Expr := .call 1474 (.name 1474 82) [(.pos (.name 1474 115))]

theorem gavi_items (sha : Oracle) (fp : Footprint) (M : Nat) {ds : List DV} {kV : ListKind}
    {lV : Option Nat} {vals : List Validator} {e : Nat}
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (vals.map Examples.vdv)))
    (hN : vals.length < 2 ^ 64) :
    ∀ d j (loc : Name → Option DRes), d = vals.length - j → loc 103 = some (.val (.uint epTy' e)) →
      loc 82 = none → loc 215 = none →
      (den (Scope.env sha) fpsEx (M + 9 + d)).items fp
          ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], loc⟩ gaviTarget gaviIfs gaviElt
          ⟨0, [11], true⟩ j =
        some (.ok ((gaviL e (vals.drop j) j).map viLeaf)) := by
  have hderef : ∀ (l : Name → Option DRes),
      DSt.deref ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], l⟩ 0 [11] =
        some (.list kV (.container Scope.Id.«Validator») lV (vals.map Examples.vdv)) := by
    intro l; simp [DSt.deref, subAt, DV.kids, hv]
  intro d
  induction d with
  | zero =>
    intro j loc hd _ _ _
    have hj : ¬ j < vals.length := by omega
    rw [show M + 9 + 0 = (M + 8) + 1 by omega, den_items]
    unfold itemsStep
    rw [hderef]
    have hn : (vals.map Examples.vdv)[j]? = none := by simp [hj]
    simp only [isByteList, hn]
    simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt hj), gaviL, DM.ok]
  | succ d ih =>
    intro j loc hd h103 h82 h215
    have hj : j < vals.length := by omega
    rw [show M + 9 + (d + 1) = (M + 7 + d + 2) + 1 by omega, den_items]
    unfold itemsStep
    rw [hderef]
    have hc : (vals.map Examples.vdv)[j]? = some (Examples.vdv vals[j]) := by
      simp [List.getElem?_eq_getElem hj]
    have hnb : decide (kV = ListKind.list ∧ SszTy.container Scope.Id.«Validator» = SszTy.uint (UintTy.width 8)) = false := by
      simp
    simp only [isByteList, hc, hnb, Bool.false_eq_true, if_false]
    have hbl : bindLoop (M + 7 + d + 2) true ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], loc⟩
        gaviTarget j (ofChild 0 ([11] ++ [j]) (Examples.vdv vals[j])) =
        some ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)],
          setLoc (setLoc loc 115 (.val (.int (j : Int)))) 78 (.place 0 [11, j])⟩ := rfl
    rw [hbl]
    dsimp only
    have hdr : DSt.deref ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)],
        setLoc (setLoc loc 115 (.val (.int (j : Int)))) 78 (.place 0 [11, j])⟩ 0 [11, j] =
        some (Examples.vdv vals[j]) := by
      simp [DSt.deref, subAt, DV.kids, hv, List.getElem?_eq_getElem hj]
    have hcond := c_iav sha fp (M + 1 + d) (x := vals[j]) (j := j) (e := e)
      (s := ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)],
        setLoc (setLoc loc 115 (.val (.int (j : Int)))) 78 (.place 0 [11, j])⟩)
      (by simp [setLoc]) hdr (by simp [setLoc, h103]) (by simp [setLoc, h215])
    rw [show M + 1 + d + 8 = M + 7 + d + 2 by omega] at hcond
    have helt := c_vi sha fp (M + 6 + d) (j := j) (by omega)
      (s := ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)],
        setLoc (setLoc loc 115 (.val (.int (j : Int)))) 78 (.place 0 [11, j])⟩)
      (by simp [setLoc]) (by simp [setLoc, h82])
    rw [show M + 6 + d + 3 = M + 7 + d + 2 by omega] at helt
    have hrest := ih (j + 1) (setLoc (setLoc loc 115 (.val (.int (j : Int)))) 78 (.place 0 [11, j]))
      (by omega) (by simp [setLoc, h103]) (by simp [setLoc, h82]) (by simp [setLoc, h215])
    rw [show M + 9 + d = M + 7 + d + 2 by omega] at hrest
    rw [List.drop_eq_getElem_cons hj]
    simp only [ifsOf, gaviIfs, hcond, dbind_ok, truthy_lift (truthy_b _)]
    cases hact : act vals[j] e with
    | true =>
      simp only [if_true, ifsOf, dbind_ok, DM.ok, helt, Flat, hrest, gaviL, hact]
      rfl
    | false =>
      simp only [Bool.false_eq_true, if_false, DM.ok, dbind_ok, hrest, gaviL, hact]
      rfl

abbrev gaviIter : Expr := .call 1474 (.name 1474 216) [(.pos (.attr 1474 (.name 1474 1) 27))]

theorem g_iterSrc (sha : Oracle) (fp : Footprint) (n : Nat) {s : DSt} {ds : List DV} {kV : ListKind}
    {lV : Option Nat} {xs : List DV} (hr : s.roots[0]? = some (.cont Scope.Id.«BeaconState» ds))
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV xs))
    (h1 : s.loc 1 = some (.place 0 [])) (h216 : s.loc 216 = none) :
    (den (Scope.env sha) fpsEx (n + 3)).iter fp s gaviIter = some (.ok ⟨0, [11], true⟩) := by
  have he : (den (Scope.env sha) fpsEx (n + 2)).expr fp s (.attr 1474 (.name 1474 1) 27) =
      some (.ok (.place 0 [11])) := by
    simp [exprStep, DM.bind, DM.ok, h1, dAttr, DSt.deref, subAt, DV.kids, ofChild, hr, hv,
      Validation.Tactic.fieldIndex_lit]
  have hen : isEnumerate (Scope.env sha) 216 = true := by
    simp only [isEnumerate, Scope.env, Validation.Tactic.lookup_lit]
  have hlp : listPlace s 0 [11] = true := by
    simp [listPlace, DSt.deref, subAt, DV.kids, hr, hv, isByteList]
  rw [den_iter, gaviIter]
  simp only [iterStep, h216, Option.isNone_none, hen, Bool.and_self, if_true, DM.bind, he, hlp]
  rfl

theorem gavi_den (sha : Oracle) (fp : Footprint) (M : Nat) {ds : List DV} {kV : ListKind}
    {lV : Option Nat} {vals : List Validator} {e : Nat}
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (vals.map Examples.vdv)))
    (hN : vals.length < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (M + 12 + vals.length)).fn fp Scope.fn_get_active_validator_indices
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)] =
      some (.ok (.tree (.list .pyList .any none ((gaviL e vals 0).map viLeaf)),
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)])) := by
  let loc0 : Name → Option DRes := setLoc (setLoc (fun _ => none) 1 (.place 0 [])) 103 (.val (.uint epTy' e))
  have hit := g_iterSrc sha fp (M + 6 + vals.length) (s := ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], loc0⟩)
    rfl hv (by simp [loc0, setLoc]) (by simp [loc0, setLoc])
  rw [show M + 6 + vals.length + 3 = M + 9 + vals.length by omega] at hit
  have hits := gavi_items sha fp M (e := e) hv hN vals.length 0 loc0 (by omega) (by simp [loc0, setLoc])
    (by simp [loc0, setLoc]) (by simp [loc0, setLoc])
  have hcomp : (den (Scope.env sha) fpsEx (M + 10 + vals.length)).expr fp
      ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], loc0⟩
      (.comp 1473 .list gaviElt [.mk gaviTarget gaviIter gaviIfs]) =
      some (.ok (.tree (.list .pyList .any none ((gaviL e vals 0).map viLeaf)))) := by
    rw [show M + 10 + vals.length = (M + 9 + vals.length) + 1 by omega, den_expr]
    simp only [exprStep]
    rw [hit, dm_bind_ok, hits, dm_bind_ok]
    simp only [List.drop_zero]
    rfl
  have hst : (den (Scope.env sha) fpsEx (M + 11 + vals.length)).stmt fp
      ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], loc0⟩
      (.ret 1473 (some (.comp 1473 .list gaviElt [.mk gaviTarget gaviIter gaviIfs]))) =
      some (.ok (.ret (.tree (.list .pyList .any none ((gaviL e vals 0).map viLeaf))),
        ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], loc0⟩)) := by
    rw [show M + 11 + vals.length = (M + 10 + vals.length) + 1 by omega, den_stmt]
    simp only [stmtStep]; rw [hcomp]; rfl
  have hb : (den (Scope.env sha) fpsEx (M + 11 + vals.length)).block fp
      ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)],
        initLoc [.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)] (fun _ => none)
          Scope.fn_get_active_validator_indices.params.names.zipIdx⟩
      Scope.fn_get_active_validator_indices.body =
      some (.ok (.ret (.tree (.list .pyList .any none ((gaviL e vals 0).map viLeaf))),
        ⟨[.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)], loc0⟩)) :=
    blockOf_ret hst
  rw [show M + 12 + vals.length = (M + 11 + vals.length) + 1 by omega, den_fn]
  simp only [fnStep]
  rw [if_pos ⟨rfl, rfl, rfl⟩, hb]
  rfl

theorem iav_read (x : Validator) (e : Nat) : is_active_validator x ⟨e⟩ = .ok (act x e) := by
  simp [is_active_validator, act, uv]

theorem uOf_vi (j : Nat) (hj : j < 2 ^ 64) : uOf ValidatorIndex (j : Int) = .ok ⟨j⟩ := by
  have h' : (0 : Int) ≤ (j : Int) ∧ (j : Int) < 2 ^ UintC.bits ValidatorIndex := by
    show _ ∧ _ < 2 ^ 64; omega
  simp only [uOf, if_pos h', Int.toNat_natCast]
  rfl

theorem gavi_read_go (e : Nat) : ∀ (xs : List Validator) (j : Nat), j + xs.length ≤ 2 ^ 64 →
    ((xs.zipIdx j).map fun (v, i) => ((i : Int), v)).filterMapM (fun (i, v) => do
      if (← is_active_validator v ⟨e⟩) then (do pure (some (← uOf ValidatorIndex i))) else pure none) =
      (.ok ((gaviL e xs j).map ValidatorIndex.mk) : SpecM (List ValidatorIndex))
  | [], j, _ => rfl
  | x :: xs, j, hj => by
    have ih := gavi_read_go e xs (j + 1) (by simp at hj; omega)
    simp only [iav_read, Except.bind_ok'] at ih
    simp only [List.zipIdx_cons, List.map_cons, List.filterMapM_cons, iav_read, gaviL]
    cases hact : act x e with
    | true =>
      simp only [Except.bind_ok', if_true, uOf_vi j (by simp at hj; omega), pure_bind, ih]
      rfl
    | false =>
      simp only [Except.bind_ok', Bool.false_eq_true, if_false, pure_bind, ih]
      rfl

theorem gavi_read (st : BeaconState) (e : Nat) (hN : st.validators.length < 2 ^ 64) :
    get_active_validator_indices st ⟨e⟩ = .ok ((gaviL e st.validators 0).map ValidatorIndex.mk) := by
  unfold get_active_validator_indices
  rw [gavi_read_go e st.validators 0 (by omega)]
  rfl

/-- The decoded tree of the result list. -/
def gaviTree (xs : List ValidatorIndex) : DV := .list .pyList .any none (xs.map fun i => viLeaf i.val)

/-- The denotation of `get_active_validator_indices` is the readable function: a new list. -/
theorem get_active_validator_indices_denote (sha : Oracle) (M : Nat) (ds : List DV) (kV : ListKind)
    (lV : Option Nat) (st : BeaconState) (e : Nat)
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (st.validators.map Examples.vdv)))
    (hN : st.validators.length < 2 ^ 64) :
    ((den (Scope.env sha) fpsEx (M + 12 + st.validators.length)).fn [] Scope.fn_get_active_validator_indices
        [.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)]).map (Except.mapError SpecError.fail) =
      some ((fun xs => (DRes.tree (gaviTree xs), [.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)])) <$>
        get_active_validator_indices st ⟨e⟩) := by
  rw [gavi_den sha [] M hv hN, gavi_read st e hN]
  simp [gaviTree, List.map_map, Function.comp_def]
  rfl

/-- SPEC 9.2 for `get_active_validator_indices`: the result is a new list. The interpreter's
result decodes to the readable list, and the state is unchanged. -/
theorem get_active_validator_indices_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h)
    (r0 n : Nat) (ds : List DV) (kV : ListKind) (lV : Option Nat) (st : BeaconState) (e : Nat)
    (hd : dec h n (.ref r0) = some (.cont Scope.Id.«BeaconState» ds))
    (hv : ds[11]? = some (.list kV (.container Scope.Id.«Validator») lV (st.validators.map Examples.vdv)))
    (hN : st.validators.length < 2 ^ 64) :
    ∀ fuel, 12 + st.validators.length ≤ fuel →
      ResultMatches gfp [] h [.ref r0, .uint epTy' e]
        (fun (xs : List ValidatorIndex) h' v => ∃ m, dec h' m v = some (gaviTree xs))
        (interp (Scope.env sha) fuel Scope.Id.«get_active_validator_indices» [.ref r0, .uint epTy' e] h)
        (get_active_validator_indices st ⟨e⟩) := by
  intro fuel hf
  have hden := gavi_den sha [] 0 (e := e) hv hN
  rw [Nat.zero_add] at hden
  have hdec : DecArgs h [.ref r0, .uint epTy' e] [.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)] := by
    refine ⟨rfl, fun k v d hv' hd' => ?_⟩
    match k, hv', hd' with
    | 0, hv', hd' => simp at hv' hd'; subst hv'; subst hd'; exact ⟨n, hd⟩
    | 1, hv', hd' => simp at hv' hd'; subst hv'; subst hd'; exact ⟨0, dec_flat rfl 0⟩
    | _ + 2, hv', _ => simp at hv'
  have hm := denote_sound_calls (Scope.env sha) fpsEx (libFlat_ssz _) gfp []
    (f := Scope.Id.«get_active_validator_indices»)
    (by simp only [Scope.env, Validation.Tactic.lookup_lit]) hdec (Examples.wtree_nil h _) hwf hden
  refine resultMatches_mono hf (Examples.resultMatches_map
    (f := fun xs => (DRes.tree (gaviTree xs), [DV.cont Scope.Id.«BeaconState» ds, .leaf (.uint epTy' e)]))
    (E := fun (x : DRes × List DV) h' v => ERel h' [.ref r0, .uint epTy' e] x.1 v ∧
      DecArgs h' [.ref r0, .uint epTy' e] x.2)
    (fun xs h' v he => he.1.1) ?_)
  rw [gavi_read st e hN]
  have hgl : (gaviL e st.validators 0).map viLeaf = ((gaviL e st.validators 0).map ValidatorIndex.mk).map
      (fun i => viLeaf i.val) := by simp [List.map_map, Function.comp_def]
  simp only [hgl] at hm
  exact hm

end SpecLean.Layer4.Examples5
