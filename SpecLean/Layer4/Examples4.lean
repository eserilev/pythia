import SpecLean.Layer4.Examples3

/-!
# Layer 4: a second loop end to end (`apply_withdrawals`)

`for withdrawal in withdrawals` runs over a parameter list (root 1). The body has an `if`:

- the builder branch calls `convert_validator_index_to_builder_index` and writes
  `state.builders[builder_index].balance` with the result of `saturating_sub`;
- the other branch calls `decrease_balance(state, ...)`, which writes back through the state
  place (the call rule, `dCallW`).

Callee summaries: `ibi_den`, `cvb_den` (bit operations; `FLAG` is `BUILDER_INDEX_FLAG`), and
`sat_den_gg`, `dbal_den_ok`, `dbal_den_idx` from `Examples2`. The pure loop `awLoop` is the
common form of the denotation (`aw_den`) and the readable function (`aw_read`).

Terms with `x &&& FLAG` are rewritten with `rw` and closed with `rfl`. A `simp` that closes
such goals can give a proof that the kernel unfolds into deep recursion.
-/

open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd SpecLean.Rd.Gen SpecLean.Layer4.Examples2
  SpecLean.Layer4.Examples3

attribute [local instance high] LibModel.toLibValues

namespace SpecLean.Layer4.Examples4


abbrev biTy : UintTy := .nominal Scope.Id.«BuilderIndex» 64
local notation "FLAG" => (1099511627776 : Nat)

theorem pyAnd_nat (a b : Nat) : pyAnd (a : Int) (b : Int) = ((a &&& b : Nat) : Int) := rfl
theorem pyAnd_not (a b : Nat) : pyAnd (a : Int) (Int.not (b : Int)) = ((a ^^^ (a &&& b) : Nat) : Int) := rfl

theorem flag_lt : FLAG < 2 ^ 64 := by decide

theorem and_flag_lt (vi : Nat) : vi &&& FLAG < 2 ^ 64 := Nat.and_lt_two_pow _ flag_lt

theorem bi_lt {vi : Nat} (h : vi < 2 ^ 64) : vi ^^^ (vi &&& FLAG) < 2 ^ 64 :=
  Nat.xor_lt_two_pow h (and_flag_lt vi)

theorem and_vi (vi : Nat) :
    @binopVal LibModel.toLibValues .bitAnd (.uint viTy vi) (.uint (.width 64) FLAG) =
      .ok (.uint viTy (vi &&& FLAG)) := by
  show (do let r ← resolveUint viTy (.width 64); wrapUint r (← intArith .bitAnd vi FLAG)) = _
  have h := and_flag_lt vi
  have h' : (0 : Int) ≤ ((vi &&& FLAG : Nat) : Int) ∧ ((vi &&& FLAG : Nat) : Int) < 2 ^ viTy.bits := by
    show _ ∧ _ < 2 ^ 64; omega
  simp only [resolveUint, intArith, pyAnd_nat, wrapUint, if_true, Except.bind_ok']
  rw [if_pos h', Int.toNat_natCast]

theorem hg197 (sha : Oracle) :
    dGlobal (Scope.env sha) 197 = some (.ok (.val (.uint (.width 64) FLAG))) := by
  simp only [dGlobal, Scope.env, Validation.Tactic.lookup_lit]
  rfl

theorem ne0 (t : UintTy) (x : Nat) :
    cmpF .notEq (.uint t x) (.int 0) = some (.ok (x != 0)) := by
  have h : @cmpVal LibModel.toLibValues .eq (.uint t x) (.int 0) = .ok ((x : Int) == 0) := rfl
  simp only [cmpF, h, lift_ok, DM.bind, DM.ok]
  generalize hx : x = y
  cases y <;> rfl

theorem ibi_and (sha : Oracle) (fp : Footprint) (m vi : Nat) {s : DSt}
    (h81 : s.loc 81 = some (.val (.uint viTy vi))) (h197 : s.loc 197 = none) :
    (den (Scope.env sha) fpsEx (m + 3)).expr fp s
      (.binop 1048 .bitAnd (.name 1048 81) (.name 1048 197)) = some (.ok (.val (.uint viTy (vi &&& FLAG)))) := by
  have hb := dBinop_eval (and_vi vi) rfl
  rw [den_expr]
  simp only [exprStep, DM.bind, den_expr, h81, h197, DM.ok, hg197]
  exact hb

theorem ibi_cmp (sha : Oracle) (fp : Footprint) (m vi : Nat) {s : DSt}
    (h81 : s.loc 81 = some (.val (.uint viTy vi))) (h197 : s.loc 197 = none) :
    (den (Scope.env sha) fpsEx (m + 4)).expr fp s
      (.compare 1048 (.binop 1048 .bitAnd (.name 1048 81) (.name 1048 197)) [(.notEq, (.int 1048 (0)))]) =
      some (.ok (.val (.bool (vi &&& FLAG != 0)))) := by
  rw [den_expr]
  simp only [exprStep, DM.bind, ibi_and sha fp m vi h81 h197, cmpOf, den_expr, DM.ok, ne0]
  generalize (vi &&& FLAG != 0) = c
  cases c <;> rfl

theorem ibi_den (sha : Oracle) (fp : Footprint) (m vi : Nat) :
    (den (Scope.env sha) fpsEx (m + 6)).fn fp Scope.fn_is_builder_index [.leaf (.uint viTy vi)] =
      some (.ok (.val (.bool (vi &&& FLAG != 0)), [.leaf (.uint viTy vi)])) := by
  have hc := ibi_cmp sha fp m vi (s := ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩)
    (by simp [setLoc]) (by simp [setLoc])
  have hr : (den (Scope.env sha) fpsEx (m + 5)).stmt fp
      ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩
      (.ret 1048 (some (.compare 1048 (.binop 1048 .bitAnd (.name 1048 81) (.name 1048 197)) [(.notEq, (.int 1048 (0)))]))) =
      some (.ok (.ret (.val (.bool (vi &&& FLAG != 0))), ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩)) := by
    rw [den_stmt]; simp only [stmtStep]; rw [hc]; rfl
  have hb : (den (Scope.env sha) fpsEx (m + 5)).block fp
      ⟨[.leaf (.uint viTy vi)], initLoc [.leaf (.uint viTy vi)] (fun _ => none)
        Scope.fn_is_builder_index.params.names.zipIdx⟩ Scope.fn_is_builder_index.body =
      some (.ok (.ret (.val (.bool (vi &&& FLAG != 0))), ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩)) :=
    blockOf_ret hr
  rw [den_fn]
  simp only [fnStep]
  rw [if_pos ⟨rfl, rfl, rfl⟩, hb]
  rfl

theorem and_not_vi (vi : Nat) (h : vi < 2 ^ 64) :
    @binopVal LibModel.toLibValues .bitAnd (.uint viTy vi) (.int (Int.not (FLAG : Nat))) =
      .ok (.uint viTy (vi ^^^ (vi &&& FLAG))) := by
  have hb := bi_lt h
  have h' : (0 : Int) ≤ ((vi ^^^ (vi &&& FLAG) : Nat) : Int) ∧
      ((vi ^^^ (vi &&& FLAG) : Nat) : Int) < 2 ^ viTy.bits := by
    show _ ∧ _ < 2 ^ 64; omega
  show (do wrapUint viTy (← intArith .bitAnd vi (Int.not (FLAG : Nat)))) = _
  simp only [intArith, pyAnd_not, wrapUint, Except.bind_ok']
  rw [if_pos h', Int.toNat_natCast]

theorem inv_flag : @unopVal LibModel.toLibValues .invert (.uint (.width 64) FLAG) =
    .ok (.int (Int.not (FLAG : Nat))) := rfl

theorem ctor_bi (env : Env) (h : Heap) (x : Nat) (hx : x < 2 ^ 64) :
    LibModel.construct env h (.uint biTy) [.uint viTy x] [] = .ok (.uint biTy x, h) := by
  show (do pure (← wrapUint biTy x, h)) = _
  rw [wrap_nat (t := biTy) rfl, chkRange_ok hx]; rfl

theorem cvb_inv (sha : Oracle) (fp : Footprint) (m : Nat) {s : DSt} (h197 : s.loc 197 = none) :
    (den (Scope.env sha) fpsEx (m + 2)).expr fp s (.unop 1149 .invert (.name 1149 197)) =
      some (.ok (.val (.int (Int.not (FLAG : Nat))))) := by
  rw [den_expr]
  simp only [exprStep, DM.bind, den_expr, h197, hg197]
  rw [inv_flag]
  rfl

theorem cvb_and (sha : Oracle) (fp : Footprint) (m vi : Nat) (hv : vi < 2 ^ 64) {s : DSt}
    (h81 : s.loc 81 = some (.val (.uint viTy vi))) (h197 : s.loc 197 = none) :
    (den (Scope.env sha) fpsEx (m + 3)).expr fp s
      (.binop 1149 .bitAnd (.name 1149 81) (.unop 1149 .invert (.name 1149 197))) =
      some (.ok (.val (.uint viTy (vi ^^^ (vi &&& FLAG))))) := by
  have hb := dBinop_eval (and_not_vi vi hv) rfl
  rw [den_expr]
  simp only [exprStep]
  have h81' : (den (Scope.env sha) fpsEx (m + 2)).expr fp s (.name 1149 81) =
      some (.ok (.val (.uint viTy vi))) := by
    rw [den_expr]; simp only [exprStep, h81]; rfl
  rw [cvb_inv sha fp m h197, h81']
  rw [dm_bind_ok, dm_bind_ok]
  exact hb

theorem cvb_call (sha : Oracle) (fp : Footprint) (m vi : Nat) (hv : vi < 2 ^ 64) {s : DSt}
    (h81 : s.loc 81 = some (.val (.uint viTy vi))) (h197 : s.loc 197 = none) (h199 : s.loc 199 = none) :
    (den (Scope.env sha) fpsEx (m + 5)).expr fp s
      (.call 1149 (.name 1149 199) [(.pos (.binop 1149 .bitAnd (.name 1149 81) (.unop 1149 .invert (.name 1149 197))))]) =
      some (.ok (.val (.uint biTy (vi ^^^ (vi &&& FLAG))))) := by
  have ha := cvb_and sha fp (m + 1) vi hv h81 h197
  rw [show m + 1 + 3 = m + 4 by omega] at ha
  have hhead : callHead (Scope.env sha) s
      (.call 1149 (.name 1149 199) [(.pos (.binop 1149 .bitAnd (.name 1149 81) (.unop 1149 .invert (.name 1149 197))))]) =
      some (199, [(.pos (.binop 1149 .bitAnd (.name 1149 81) (.unop 1149 .invert (.name 1149 197))))]) := by
    simp only [callHead, h199, Option.isNone_none, Bool.true_and, callable, Scope.env,
      Validation.Tactic.lookup_lit, if_true]
  have hc := dCtor_eval (env := Scope.env sha) (t := .uint biTy)
    (rs := [.val (.uint viTy (vi ^^^ (vi &&& FLAG)))]) rfl rfl (ctor_bi _ _ _ (bi_lt hv)) rfl
  have hl : (Scope.env sha).globals.lookup 199 = some (.type (.uint biTy)) := by
    simp only [Scope.env, Validation.Tactic.lookup_lit]
  rw [show m + 5 = (m + 4) + 1 by omega, den_expr]
  simp only [exprStep, hhead, allKw_pos, Bool.false_eq_true, ↓reduceIte]
  simp only [argsOf]
  rw [ha, dm_bind_ok, dm_ok, dm_bind_ok, dm_ok, dm_bind_ok]
  simp only [dCallRO, hl]
  exact hc

theorem cvb_den (sha : Oracle) (fp : Footprint) (m vi : Nat) (hv : vi < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (m + 7)).fn fp Scope.fn_convert_validator_index_to_builder_index
        [.leaf (.uint viTy vi)] =
      some (.ok (.val (.uint biTy (vi ^^^ (vi &&& FLAG))), [.leaf (.uint viTy vi)])) := by
  have hc := cvb_call sha fp m vi hv (s := ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩)
    (by simp [setLoc]) (by simp [setLoc]) (by simp [setLoc])
  have hr : (den (Scope.env sha) fpsEx (m + 6)).stmt fp
      ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩
      (.ret 1149 (some (.call 1149 (.name 1149 199) [(.pos (.binop 1149 .bitAnd (.name 1149 81) (.unop 1149 .invert (.name 1149 197))))]))) =
      some (.ok (.ret (.val (.uint biTy (vi ^^^ (vi &&& FLAG)))), ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩)) := by
    rw [den_stmt]; simp only [stmtStep]; rw [hc]; rfl
  have hb : (den (Scope.env sha) fpsEx (m + 6)).block fp
      ⟨[.leaf (.uint viTy vi)], initLoc [.leaf (.uint viTy vi)] (fun _ => none)
        Scope.fn_convert_validator_index_to_builder_index.params.names.zipIdx⟩
        Scope.fn_convert_validator_index_to_builder_index.body =
      some (.ok (.ret (.val (.uint biTy (vi ^^^ (vi &&& FLAG)))), ⟨[.leaf (.uint viTy vi)], setLoc (fun _ => none) 81 (.val (.uint viTy vi))⟩)) :=
    blockOf_ret hr
  rw [den_fn]
  simp only [fnStep]
  rw [if_pos ⟨rfl, rfl, rfl⟩, hb]
  rfl

theorem mapError_ok (x : Int) : Except.mapError SpecError.fail (Except.ok x : Res Int) = (.ok x : SpecM Int) := rfl

theorem ibi_read (vi : Nat) : is_builder_index ⟨vi⟩ = .ok (vi &&& FLAG != 0) := by
  have h := and_flag_lt vi
  have h' : (0 : Int) ≤ ((vi &&& FLAG : Nat) : Int) ∧ ((vi &&& FLAG : Nat) : Int) < 2 ^ UintC.bits ValidatorIndex := by
    show _ ∧ _ < 2 ^ 64; omega
  have hu : (uOp .bitAnd (uv (⟨vi⟩ : ValidatorIndex)) (uv BUILDER_INDEX_FLAG) : SpecM ValidatorIndex) =
      .ok ⟨vi &&& FLAG⟩ := by
    simp only [uOp, uOf, erase, intArith, uv, BUILDER_INDEX_FLAG, UintC.val]
    rw [pyAnd_nat, mapError_ok, Except.bind_ok', if_pos h', Int.toNat_natCast]
    rfl
  unfold is_builder_index
  rw [hu]
  show Except.ok (((vi &&& FLAG : Nat) : Int) != 0) = _
  generalize vi &&& FLAG = c
  cases c <;> rfl

theorem cvb_read (vi : Nat) (hv : vi < 2 ^ 64) :
    convert_validator_index_to_builder_index ⟨vi⟩ = .ok ⟨vi ^^^ (vi &&& FLAG)⟩ := by
  have hb := bi_lt hv
  have h' : (0 : Int) ≤ ((vi ^^^ (vi &&& FLAG) : Nat) : Int) ∧
      ((vi ^^^ (vi &&& FLAG) : Nat) : Int) < 2 ^ UintC.bits ValidatorIndex := by
    show _ ∧ _ < 2 ^ 64; omega
  have h'' : (0 : Int) ≤ ((vi ^^^ (vi &&& FLAG) : Nat) : Int) ∧
      ((vi ^^^ (vi &&& FLAG) : Nat) : Int) < 2 ^ UintC.bits BuilderIndex := by
    show _ ∧ _ < 2 ^ 64; omega
  have hu : (uOp .bitAnd (uv (⟨vi⟩ : ValidatorIndex)) (Int.not (uv BUILDER_INDEX_FLAG)) : SpecM ValidatorIndex) =
      .ok ⟨vi ^^^ (vi &&& FLAG)⟩ := by
    simp only [uOp, uOf, erase, intArith, uv, BUILDER_INDEX_FLAG, UintC.val]
    rw [pyAnd_not, mapError_ok, Except.bind_ok', if_pos h', Int.toNat_natCast]
    rfl
  unfold convert_validator_index_to_builder_index
  rw [hu]
  simp only [Except.bind_ok', uCast, uOf, uv, UintC.val]
  rw [if_pos h'', Int.toNat_natCast, pure_bind]
  rfl

/-- The decoded tree of a `Builder`. -/
def bdv (b : Builder) : DV :=
  .cont Scope.Id.«Builder»
    [.leaf (.bytes Scope.Id.«BLSPubkey» (bd b.pubkey)),
     .leaf (.uint (.width 8) b.version.val),
     .leaf (.bytes Scope.Id.«ExecutionAddress» (bd b.execution_address)),
     .leaf (.uint gwTy b.balance.val),
     .leaf (.uint Examples.epochTy b.deposit_epoch.val),
     .leaf (.uint Examples.epochTy b.withdrawable_epoch.val)]

/-- The decoded tree of a `Withdrawal`. -/
def wdv (w : Withdrawal) : DV :=
  .cont Scope.Id.«Withdrawal»
    [.leaf (.uint (.nominal Scope.Id.«WithdrawalIndex» 64) w.index.val),
     .leaf (.uint viTy w.validator_index.val),
     .leaf (.bytes Scope.Id.«ExecutionAddress» (bd w.address)),
     .leaf (.uint gwTy w.amount.val)]

/-- The state tree, with the balances and the builders. -/
def awRoot (ds : List DV) (kB : ListKind) (lB : Option Nat) (bals : List Gwei) (kD : ListKind)
    (lD : Option Nat) (bs : List Builder) : DV :=
  .cont Scope.Id.«BeaconState» ((ds.set 12 (.list kB (.uint gwTy) lB (bals.map Examples.gleaf))).set 38
    (.list kD (.container Scope.Id.«Builder») lD (bs.map bdv)))

def wsRoot (kW : ListKind) (lW : Option Nat) (ws : List Withdrawal) : DV :=
  .list kW (.container Scope.Id.«Withdrawal») lW (ws.map wdv)

structure ACtx (s : DSt) (ds : List DV) (kB : ListKind) (lB : Option Nat) (bals : List Gwei)
    (kD : ListKind) (lD : Option Nat) (bs : List Builder) (kW : ListKind) (lW : Option Nat)
    (ws : List Withdrawal) : Prop where
  roots : s.roots = [awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws]
  l38 : 38 < ds.length

section body
variable {sha : Oracle} {fp : Footprint} {s : DSt} {ds : List DV} {kB : ListKind} {lB : Option Nat}
  {bals : List Gwei} {kD : ListKind} {lD : Option Nat} {bs : List Builder} {kW : ListKind}
  {lW : Option Nat} {ws : List Withdrawal}

theorem a_vi (n : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i : Nat} (hi : i < ws.length)
    (h85 : s.loc 85 = some (.place 1 [i])) (l : Line) :
    (den (Scope.env sha) fpsEx (n + 2)).expr fp s (.attr l (.name l 85) 81) =
      some (.ok (.val (.uint viTy ws[i].validator_index.val))) := by
  have hw : (ws.map wdv)[i]? = some (wdv ws[i]) := by simp [List.getElem?_eq_getElem hi]
  simp [exprStep, DM.bind, DM.ok, h85, dAttr, DSt.deref, subAt, DV.kids, ofChild, hc.roots, wsRoot,
    hw, wdv, Validation.Tactic.fieldIndex_lit]

theorem a_amt (n : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i : Nat} (hi : i < ws.length)
    (h85 : s.loc 85 = some (.place 1 [i])) (l : Line) :
    (den (Scope.env sha) fpsEx (n + 2)).expr fp s (.attr l (.name l 85) 5) =
      some (.ok (.val (.uint gwTy ws[i].amount.val))) := by
  have hw : (ws.map wdv)[i]? = some (wdv ws[i]) := by simp [List.getElem?_eq_getElem hi]
  simp [exprStep, DM.bind, DM.ok, h85, dAttr, DSt.deref, subAt, DV.kids, ofChild, hc.roots, wsRoot,
    hw, wdv, Validation.Tactic.fieldIndex_lit]

theorem a_bplace (n : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {bi : Nat}
    (h1 : s.loc 1 = some (.place 0 [])) (h66 : s.loc 66 = some (.val (.uint biTy bi))) (l : Line) :
    (den (Scope.env sha) fpsEx (n + 3)).expr fp s (.index l (.attr l (.name l 1) 7) (.name l 66)) =
      some (if bi < bs.length then .ok (.place 0 [38, bi]) else .error .indexError) := by
  have h38 := hc.l38
  by_cases hb : bi < bs.length
  · have hw : (bs.map bdv)[bi]? = some (bdv bs[bi]) := by simp [List.getElem?_eq_getElem hb]
    simp [exprStep, DM.bind, DM.ok, h1, h66, dAttr, dIndex, DSt.deref, subAt, DV.kids, ofChild,
      hc.roots, awRoot, Validation.Tactic.fieldIndex_lit, List.getElem?_set, h38, isByteList,
      normIndex_nat, hb, hw, bdv]
  · simp [exprStep, DM.bind, DM.ok, h1, h66, dAttr, dIndex, DSt.deref, subAt, DV.kids, ofChild,
      hc.roots, awRoot, Validation.Tactic.fieldIndex_lit, List.getElem?_set, h38, isByteList,
      normIndex_nat, hb]
end body

/-- A call of a spec function with an empty footprint, as an expression. -/
theorem e_callfn {sha : Oracle} {fp : Footprint} {s : DSt} {n : Nat} {l l' : Line} {g : Name}
    {args : List Arg} {d : FunctionDef} {rs : List DRes} {rg : List DV} {v : Value} {rg' : List DV}
    (hl : (Scope.env sha).globals.lookup g = some (.fn d)) (hfp : (fpsEx g).isEmpty = true)
    (hloc : s.loc g = none)
    (ha : argsOf ((den (Scope.env sha) fpsEx (n + 1)).expr fp s) args = some (.ok rs))
    (hr : rs.mapM (argRoot s) = some rg)
    (hf : (den (Scope.env sha) fpsEx (n + 1)).fn [] d rg = some (.ok (.val v, rg'))) (hflat : Flat v = true) :
    (den (Scope.env sha) fpsEx (n + 2)).expr fp s (.call l (.name l' g) args) = some (.ok (.val v)) := by
  have hh : callHead (Scope.env sha) s (.call l (.name l' g) args) = some (g, args) := by
    simp [callHead, hloc, callable, hl]
  rw [den_expr]
  simp only [exprStep, hh, allKw_of_argsOf _ _ ha, Bool.false_eq_true, ↓reduceIte]
  rw [ha, dm_bind_ok]
  simp only [dCallRO, hl, hfp, if_true, hr, hf, dm_bind_ok, hflat]
  rfl


abbrev awFp : Footprint := fpsEx 90

theorem aw_write (ds : List DV) (kB : ListKind) (lB : Option Nat) (bals : List Gwei) (kD : ListKind)
    (lD : Option Nat) (bs : List Builder) (bi : Nat) (hb : bi < bs.length) (h38 : 38 < ds.length) (v : Nat) :
    updAt [38, bi] (awRoot ds kB lB bals kD lD bs) 3 (.leaf (.uint gwTy v)) =
      awRoot ds kB lB bals kD lD (bs.set bi { bs[bi] with balance := ⟨v⟩ }) := by
  have hv : (bs.map bdv)[bi]? = some (bdv bs[bi]) := by
    simp [List.getElem?_eq_getElem hb]
  simp [awRoot, updAt, List.getElem?_set, h38, hv, List.map_set]
  rfl

section body2
variable {sha : Oracle} {fp : Footprint} {s : DSt} {ds : List DV} {kB : ListKind} {lB : Option Nat}
  {bals : List Gwei} {kD : ListKind} {lD : Option Nat} {bs : List Builder} {kW : ListKind}
  {lW : Option Nat} {ws : List Withdrawal}

theorem a_bal (n : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {bi : Nat}
    (h1 : s.loc 1 = some (.place 0 [])) (h66 : s.loc 66 = some (.val (.uint biTy bi))) (l : Line) :
    (den (Scope.env sha) fpsEx (n + 4)).expr fp s
      (.attr l (.index l (.attr l (.name l 1) 7) (.name l 66)) 9) =
      some (if h : bi < bs.length then .ok (.val (.uint gwTy bs[bi].balance.val)) else .error .indexError) := by
  have hp := a_bplace (sha := sha) (fp := fp) n hc h1 h66 l
  rw [den_expr]
  simp only [exprStep]
  rw [hp]
  by_cases hb : bi < bs.length
  · have hw : (bs.map bdv)[bi]? = some (bdv bs[bi]) := by simp [List.getElem?_eq_getElem hb]
    simp only [if_pos hb, dif_pos hb, dm_bind_ok]
    simp [dAttr, DSt.deref, subAt, DV.kids, ofChild, hc.roots, awRoot, List.getElem?_set, hc.l38, hw,
      bdv, Validation.Tactic.fieldIndex_lit, DM.ok]
  · simp only [if_neg hb, dif_neg hb, DM.bind]

theorem c_ibi (m : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i : Nat} (hi : i < ws.length)
    (h85 : s.loc 85 = some (.place 1 [i])) (h86 : s.loc 86 = none) :
    (den (Scope.env sha) fpsEx (m + 7)).expr fp s
      (.call 1941 (.name 1941 86) [(.pos (.attr 1941 (.name 1941 85) 81))]) =
      some (.ok (.val (.bool (ws[i].validator_index.val &&& FLAG != 0)))) := by
  have ha := a_vi (sha := sha) (fp := fp) (m + 4) hc hi h85 1941
  exact e_callfn (n := m + 5) (by simp only [Scope.env, Validation.Tactic.lookup_lit]) (by decide) h86
    (args1 ha) rfl (ibi_den sha [] m _) rfl

theorem c_cvb (m : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i : Nat} (hi : i < ws.length)
    (hv : ws[i].validator_index.val < 2 ^ 64)
    (h85 : s.loc 85 = some (.place 1 [i])) (h87 : s.loc 87 = none) :
    (den (Scope.env sha) fpsEx (m + 8)).expr fp s
      (.call 1942 (.name 1942 87) [(.pos (.attr 1942 (.name 1942 85) 81))]) =
      some (.ok (.val (.uint biTy (ws[i].validator_index.val ^^^ (ws[i].validator_index.val &&& FLAG))))) := by
  have ha := a_vi (sha := sha) (fp := fp) (m + 5) hc hi h85 1942
  exact e_callfn (n := m + 6) (by simp only [Scope.env, Validation.Tactic.lookup_lit]) (by decide) h87
    (args1 ha) rfl (cvb_den sha [] m _ hv) rfl
end body2

/-- `saturating_sub(state.builders[builder_index].balance, withdrawal.amount)`. -/
abbrev satCall : Expr :=
  .call 1943 (.name 1943 88) [(.pos (.attr 1944 (.index 1944 (.attr 1944 (.name 1944 1) 7) (.name 1944 66)) 9)),
    (.pos (.attr 1944 (.name 1944 85) 5))]

abbrev balTarget : Target := .attr 1943 (.index 1943 (.attr 1943 (.name 1943 1) 7) (.name 1943 66)) 9

section body3
variable {sha : Oracle} {fp : Footprint} {s : DSt} {ds : List DV} {kB : ListKind} {lB : Option Nat}
  {bals : List Gwei} {kD : ListKind} {lD : Option Nat} {bs : List Builder} {kW : ListKind}
  {lW : Option Nat} {ws : List Withdrawal}

theorem c_sat (m : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i bi : Nat} (hi : i < ws.length)
    (hb : bi < bs.length) (hbb : bs[bi].balance.val < 2 ^ 64)
    (h1 : s.loc 1 = some (.place 0 [])) (h66 : s.loc 66 = some (.val (.uint biTy bi)))
    (h85 : s.loc 85 = some (.place 1 [i])) (h88 : s.loc 88 = none) :
    (den (Scope.env sha) fpsEx (m + 9)).expr fp s satCall =
      some (.ok (.val (.uint gwTy (if ws[i].amount.val < bs[bi].balance.val
        then bs[bi].balance.val - ws[i].amount.val else 0)))) := by
  have ha := a_bal (sha := sha) (fp := fp) (m + 4) hc h1 h66 1944
  rw [dif_pos hb] at ha
  have hm := a_amt (sha := sha) (fp := fp) (m + 6) hc hi h85 1944
  exact e_callfn (n := m + 7) (by simp only [Scope.env, Validation.Tactic.lookup_lit]) (by decide) h88
    (args2 ha hm) rfl (sat_den_gg sha [] m _ _ hbb) rfl

theorem c_sat_err (m : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {bi : Nat}
    (hb : ¬ bi < bs.length) (h1 : s.loc 1 = some (.place 0 [])) (h66 : s.loc 66 = some (.val (.uint biTy bi)))
    (h88 : s.loc 88 = none) :
    (den (Scope.env sha) fpsEx (m + 9)).expr fp s satCall = some (.error .indexError) := by
  have ha := a_bal (sha := sha) (fp := fp) (m + 4) hc h1 h66 1944
  rw [dif_neg hb] at ha
  have hh : callHead (Scope.env sha) s satCall = some (88, [(.pos (.attr 1944 (.index 1944 (.attr 1944 (.name 1944 1) 7) (.name 1944 66)) 9)),
      (.pos (.attr 1944 (.name 1944 85) 5))]) := by
    simp [callHead, h88, callable, Scope.env, Validation.Tactic.lookup_lit]
  rw [show m + 9 = (m + 8) + 1 by omega, den_expr]
  simp only [exprStep, hh, allKw_pos, Bool.false_eq_true, ↓reduceIte]
  simp only [argsOf]
  rw [ha]
  rfl

theorem t_bal (n : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {bi : Nat} (hb : bi < bs.length)
    (h1 : s.loc 1 = some (.place 0 [])) (h66 : s.loc 66 = some (.val (.uint biTy bi)))
    {v : Nat} (hv : v < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (n + 4)).target awFp s balTarget (.val (.uint gwTy v)) =
      some (.ok (.normal, ⟨[awRoot ds kB lB bals kD lD (bs.set bi { bs[bi] with balance := ⟨v⟩ }),
        wsRoot kW lW ws], s.loc⟩)) := by
  have hp := a_bplace (sha := sha) (fp := awFp) n hc h1 h66 1943
  rw [if_pos hb] at hp
  have hw : (bs.map bdv)[bi]? = some (bdv bs[bi]) := by simp [List.getElem?_eq_getElem hb]
  have hdr : s.deref 0 [38, bi] = some (bdv bs[bi]) := by
    simp [DSt.deref, subAt, DV.kids, hc.roots, awRoot, List.getElem?_set, hc.l38, hw]
  have hf : fieldIndex (Scope.env sha) Scope.Id.«Builder» 9 = some (3, .uint gwTy) := by
    simp only [Validation.Tactic.fieldIndex_lit]
  rw [show n + 4 = (n + 3) + 1 by omega, den_target]
  simp only [targetStep]
  rw [hp]
  simp only [dm_bind_ok]
  rw [hdr]
  simp only [bdv]
  rw [hf]
  simp only [coerce_field_gw sha v hv, dm_bind_ok]
  have hroot : s.roots[0]? = some (awRoot ds kB lB bals kD lD bs) := by simp [hc.roots]
  simp only [dWriteD, dWrite, hroot, Option.map, Except.map]
  have hwr := aw_write ds kB lB bals kD lD bs bi hb hc.l38 v
  have hleaf : leafAt (awRoot ds kB lB bals kD lD bs) [38, bi] 3 = true := by
    simp [leafAt, subAt, DV.kids, awRoot, List.getElem?_set, hc.l38, hw, bdv]
  have hfp : fpOk awFp s.roots 0 [38, bi] = true := by
    simp [fpOk, awFp, fpsEx, rootIs, matchesB, hc.roots, awRoot]
  simp only [Flat, hfp, hleaf, Bool.and_self, if_true, DM.ok, hc.roots, List.set_cons_zero, hwr]
  rfl
end body3

abbrev dbalCall : Expr :=
  .call 1947 (.name 1947 89) [(.pos (.name 1947 1)), (.pos (.attr 1947 (.name 1947 85) 81)),
    (.pos (.attr 1947 (.name 1947 85) 5))]

theorem set_12_38 {α : Type} (L : List α) (X Y X' : α) :
    ((L.set 12 X).set 38 Y).set 12 X' = (L.set 12 X').set 38 Y := by
  rw [List.set_comm _ _ (by decide : (38 : Nat) ≠ 12), List.set_set]

theorem fps89 : fpsEx 89 = Examples.ibFp := rfl

section body4
variable {sha : Oracle} {s : DSt} {ds : List DV} {kB : ListKind} {lB : Option Nat}
  {bals : List Gwei} {kD : ListKind} {lD : Option Nat} {bs : List Builder} {kW : ListKind}
  {lW : Option Nat} {ws : List Withdrawal}

theorem s_else (M : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i : Nat} (hi : i < ws.length)
    (hbr : ∀ g ∈ bals, g.val < 2 ^ 64)
    (h1 : s.loc 1 = some (.place 0 [])) (h85 : s.loc 85 = some (.place 1 [i])) (h89 : s.loc 89 = none) :
    (den (Scope.env sha) fpsEx (M + 16)).stmt awFp s (.exprStmt 1947 dbalCall) =
      some (if h : ws[i].validator_index.val < bals.length then
        .ok (.normal, ⟨[awRoot ds kB lB (bals.set ws[i].validator_index.val
          ⟨if ws[i].amount.val < bals[ws[i].validator_index.val].val
            then bals[ws[i].validator_index.val].val - ws[i].amount.val else 0⟩) kD lD bs,
          wsRoot kW lW ws], s.loc⟩)
        else .error .indexError) := by
  have hv := a_vi (sha := sha) (fp := awFp) (M + 12) hc hi h85 1947
  have hm := a_amt (sha := sha) (fp := awFp) (M + 12) hc hi h85 1947
  have hn1 : (den (Scope.env sha) fpsEx (M + 14)).expr awFp s (.name 1947 1) = some (.ok (.place 0 [])) := by
    rw [den_expr]; simp only [exprStep, h1]; rfl
  have ha : argsOf ((den (Scope.env sha) fpsEx (M + 14)).expr awFp s)
      [(.pos (.name 1947 1)), (.pos (.attr 1947 (.name 1947 85) 81)), (.pos (.attr 1947 (.name 1947 85) 5))] =
      some (.ok [.place 0 [], .val (.uint viTy ws[i].validator_index.val), .val (.uint gwTy ws[i].amount.val)]) := by
    simp only [argsOf, hn1, hv, hm, dm_bind_ok, DM.ok]
  have hh : callHead (Scope.env sha) s dbalCall = some (89, [(.pos (.name 1947 1)),
      (.pos (.attr 1947 (.name 1947 85) 81)), (.pos (.attr 1947 (.name 1947 85) 5))]) := by
    simp [callHead, h89, callable, Scope.env, Validation.Tactic.lookup_lit]
  have hl : (Scope.env sha).globals.lookup 89 = some (.fn Scope.fn_decrease_balance) := by
    simp only [Scope.env, Validation.Tactic.lookup_lit]
  have h12 : 12 < ds.length := by have := hc.l38; omega
  have hd12 : ((ds.set 12 (.list kB (.uint gwTy) lB (bals.map Examples.gleaf))).set 38
      (.list kD (.container Scope.Id.«Builder») lD (bs.map bdv)))[12]? =
      some (.list kB (.uint gwTy) lB (bals.map Examples.gleaf)) := by
    simp [List.getElem?_set, h12]
  have hroot : s.roots[0]? = some (awRoot ds kB lB bals kD lD bs) := by simp [hc.roots]
  have hder : s.deref 0 [] = some (awRoot ds kB lB bals kD lD bs) := by
    simp [DSt.deref, subAt, hc.roots]
  have hcov : coversAll awFp s.roots 0 [] (awRoot ds kB lB bals kD lD bs) (fpsEx 89) = true := by
    simp [coversAll, awFp, fpsEx, rootIs, coversB, genB, hc.roots, awRoot]
  rw [den_stmt]
  simp only [stmtStep]
  rw [show M + 15 = (M + 14) + 1 by omega, den_call]
  simp only [callStep, hh, allKw_pos, Bool.false_eq_true, ↓reduceIte]
  rw [ha, dm_bind_ok]
  rw [fps89] at hcov
  have hmap : List.mapM (argRoot s) [DRes.place 0 [], .val (.uint viTy ws[i].validator_index.val),
      .val (.uint gwTy ws[i].amount.val)] = some [awRoot ds kB lB bals kD lD bs,
      .leaf (.uint viTy ws[i].validator_index.val), .leaf (.uint gwTy ws[i].amount.val)] := by
    simp [List.mapM, List.mapM.loop, argRoot, hder]
  have hne : List.isEmpty Examples.ibFp = false := rfl
  have hne' : (!List.isEmpty awFp) = true := rfl
  simp only [dCallW, hl, fps89, hne, Bool.false_eq_true, if_false, hmap, hder, hroot, hne', hcov,
    Bool.and_self, if_true]
  simp only [show onePlace [DRes.place 0 [], .val (.uint viTy ws[i].validator_index.val),
      .val (.uint gwTy ws[i].amount.val)] = some (0, 0, []) from rfl]
  simp only [hder, hroot, hcov, Bool.true_and, if_true]
  simp only [awRoot]
  by_cases hvi : ws[i].validator_index.val < bals.length
  · have hbi := hbr _ (List.getElem_mem hvi)
    rw [dbal_den_ok sha M _ kB lB bals _ _ hd12 hvi hbi, dif_pos hvi]
    simp only [dm_bind_ok, List.getElem?_cons_zero, Flat, if_true, DM.ok, hc.roots, List.set_cons_zero,
      setAt, set_12_38]
  · rw [dbal_den_idx sha M _ kB lB bals _ _ hd12 hvi, dif_neg hvi]
    rfl
end body4

def sat (b d : Nat) : Nat := if d < b then b - d else 0

/-- One withdrawal on the balances and the builders, with the builder test `c` and index `bi`. -/
def awStepG (bals : List Gwei) (bs : List Builder) (w : Withdrawal) (c : Bool) (bi : Nat) :
    Res (List Gwei × List Builder) :=
  if c then
    if h : bi < bs.length then
      .ok (bals, bs.set bi { bs[bi] with balance := ⟨sat bs[bi].balance.val w.amount.val⟩ })
    else .error .indexError
  else
    if h : w.validator_index.val < bals.length then
      .ok (bals.set w.validator_index.val ⟨sat bals[w.validator_index.val].val w.amount.val⟩, bs)
    else .error .indexError

def awStep (bals : List Gwei) (bs : List Builder) (w : Withdrawal) : Res (List Gwei × List Builder) :=
  awStepG bals bs w (w.validator_index.val &&& FLAG != 0)
    (w.validator_index.val ^^^ (w.validator_index.val &&& FLAG))

abbrev cvbCall : Expr := .call 1942 (.name 1942 87) [(.pos (.attr 1942 (.name 1942 85) 81))]
abbrev ibiCall : Expr := .call 1941 (.name 1941 86) [(.pos (.attr 1941 (.name 1941 85) 81))]
abbrev awThen : List Stmt := [.assign 1942 [.name 1942 66] cvbCall, .assign 1943 [balTarget] satCall]
abbrev awElse : List Stmt := [.exprStmt 1947 dbalCall]

section body5
variable {sha : Oracle} {s : DSt} {ds : List DV} {kB : ListKind} {lB : Option Nat}
  {bals : List Gwei} {kD : ListKind} {lD : Option Nat} {bs : List Builder} {kW : ListKind}
  {lW : Option Nat} {ws : List Withdrawal}

theorem s_t1 (M : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i : Nat} (hi : i < ws.length)
    (hv : ws[i].validator_index.val < 2 ^ 64)
    (h85 : s.loc 85 = some (.place 1 [i])) (h87 : s.loc 87 = none) :
    (den (Scope.env sha) fpsEx (M + 16)).stmt awFp s (.assign 1942 [.name 1942 66] cvbCall) =
      some (.ok (.normal, { s with loc := (setLoc s.loc 66
        (.val (.uint biTy (ws[i].validator_index.val ^^^ (ws[i].validator_index.val &&& FLAG))))) })) := by
  have he := c_cvb (sha := sha) (fp := awFp) (M + 7) hc hi hv h85 h87
  rw [show M + 7 + 8 = (M + 14) + 1 by omega] at he
  exact assign_name (n := M + 14) (call_of_expr (ro_body (callHead_ne (by decide))) he)

theorem s_t2 (M : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i bi : Nat} (hi : i < ws.length)
    (hbb : ∀ b ∈ bs, b.balance.val < 2 ^ 64)
    (h1 : s.loc 1 = some (.place 0 [])) (h66 : s.loc 66 = some (.val (.uint biTy bi)))
    (h85 : s.loc 85 = some (.place 1 [i])) (h88 : s.loc 88 = none) :
    (den (Scope.env sha) fpsEx (M + 16)).stmt awFp s (.assign 1943 [balTarget] satCall) =
      some (if h : bi < bs.length then
        .ok (.normal, ⟨[awRoot ds kB lB bals kD lD
          (bs.set bi { bs[bi] with balance := ⟨sat bs[bi].balance.val ws[i].amount.val⟩ }),
          wsRoot kW lW ws], s.loc⟩)
        else .error .indexError) := by
  by_cases hb : bi < bs.length
  · have hbv := hbb _ (List.getElem_mem hb)
    have he := c_sat (sha := sha) (fp := awFp) (M + 6) hc hi hb hbv h1 h66 h85 h88
    rw [show M + 6 + 9 = (M + 14) + 1 by omega] at he
    have hcall := call_of_expr (ro_body (callHead_ne (by decide))) he
    have ht := t_bal (sha := sha) (M + 11) hc hb h1 h66
      (v := if ws[i].amount.val < bs[bi].balance.val then bs[bi].balance.val - ws[i].amount.val else 0)
      (by split <;> omega)
    rw [show M + 11 + 4 = M + 15 by omega] at ht
    rw [den_stmt]
    simp only [stmtStep]
    rw [hcall, dif_pos hb]
    exact ht
  · have he := c_sat_err (sha := sha) (fp := awFp) (M + 6) hc hb h1 h66 h88
    rw [show M + 6 + 9 = (M + 14) + 1 by omega] at he
    have hcall := call_of_expr (ro_body (callHead_ne (by decide))) he
    rw [den_stmt]
    simp only [stmtStep]
    rw [hcall, dif_neg hb]
    rfl
end body5

/-- The tree state after one iteration, from the pure result. -/
def awOut (ds : List DV) (kB : ListKind) (lB : Option Nat) (kD : ListKind) (lD : Option Nat)
    (kW : ListKind) (lW : Option Nat) (ws : List Withdrawal) (loc : Name → Option DRes)
    (p : List Gwei × List Builder) : DOut × DSt :=
  (.normal, ⟨[awRoot ds kB lB p.1 kD lD p.2, wsRoot kW lW ws], loc⟩)

section body6
variable {sha : Oracle} {s : DSt} {ds : List DV} {kB : ListKind} {lB : Option Nat}
  {bals : List Gwei} {kD : ListKind} {lD : Option Nat} {bs : List Builder} {kW : ListKind}
  {lW : Option Nat} {ws : List Withdrawal}

theorem s_if (M : Nat) (hc : ACtx s ds kB lB bals kD lD bs kW lW ws) {i : Nat} (hi : i < ws.length)
    (hv : ws[i].validator_index.val < 2 ^ 64) (hbb : ∀ b ∈ bs, b.balance.val < 2 ^ 64)
    (hbr : ∀ g ∈ bals, g.val < 2 ^ 64)
    (h1 : s.loc 1 = some (.place 0 [])) (h85 : s.loc 85 = some (.place 1 [i]))
    (h86 : s.loc 86 = none) (h87 : s.loc 87 = none) (h88 : s.loc 88 = none) (h89 : s.loc 89 = none) :
    ∃ loc', (∀ x, x ≠ 66 → loc' x = s.loc x) ∧
      (den (Scope.env sha) fpsEx (M + 17)).stmt awFp s (.ifStmt 1941 ibiCall awThen awElse) =
        some (awOut ds kB lB kD lD kW lW ws loc' <$> awStep bals bs ws[i]) := by
  have hcond := c_ibi (sha := sha) (fp := awFp) (M + 9) hc hi h85 h86
  rw [show M + 9 + 7 = M + 16 by omega] at hcond
  have ht1 := s_t1 (sha := sha) M hc hi hv h85 h87
  rw [den_stmt]
  simp only [stmtStep]
  rw [hcond, dm_bind_ok]
  simp only [truthy_lift (truthy_b _), dm_bind_ok]
  unfold awStep
  generalize ws[i].validator_index.val ^^^ (ws[i].validator_index.val &&& FLAG) = bi at ht1 ⊢
  generalize (ws[i].validator_index.val &&& FLAG != 0) = c
  cases c with
  | true =>
    refine ⟨setLoc s.loc 66 (.val (.uint biTy bi)), fun x hx => by simp [setLoc, hx], ?_⟩
    have hc1 : ACtx { s with loc := setLoc s.loc 66 (.val (.uint biTy bi)) } ds kB lB bals kD lD bs kW lW ws :=
      ⟨hc.roots, hc.l38⟩
    have ht2 := s_t2 (sha := sha) M hc1 hi hbb (bi := bi) (by simp [setLoc, h1]) (by simp [setLoc])
      (by simp [setLoc, h85]) (by simp [setLoc, h88])
    simp only [if_true, Sem.block, awThen]
    rw [blockOf_ok ht1]
    by_cases hb : bi < bs.length
    · rw [dif_pos hb] at ht2
      rw [blockOf_ok ht2, blockOf_nil, awStepG, if_pos (show true = true from rfl), dif_pos hb]
      rfl
    · rw [dif_neg hb] at ht2
      rw [blockOf_err ht2, awStepG, if_pos (show true = true from rfl), dif_neg hb]
      rfl
  | false =>
    refine ⟨s.loc, fun _ _ => rfl, ?_⟩
    have he := s_else (sha := sha) M hc hi hbr h1 h85 h89
    simp only [Bool.false_eq_true, if_false, Sem.block, awElse]
    by_cases hb : ws[i].validator_index.val < bals.length
    · rw [dif_pos hb] at he
      rw [blockOf_ok he, blockOf_nil, awStepG, if_neg (show ¬ (false = true) by simp), dif_pos hb]
      rfl
    · rw [dif_neg hb] at he
      rw [blockOf_err he, awStepG, if_neg (show ¬ (false = true) by simp), dif_neg hb]
      rfl
end body6

abbrev awBody : List Stmt := [.ifStmt 1941 ibiCall awThen awElse]

theorem aw_body_eq : Scope.fn_apply_withdrawals.body = [.forStmt 1939 (.name 1939 85) (.name 1939 41) awBody] := rfl

/-- The loop over the withdrawals, from item `i`. -/
def awLoop (n : Nat) (ws : List Withdrawal) (bals : List Gwei) (bs : List Builder) (i : Nat) :
    Res (List Gwei × List Builder) :=
  if i < n then
    match ws[i]? with
    | some w =>
      match awStep bals bs w with
      | .error e => .error e
      | .ok p => awLoop n ws p.1 p.2 (i + 1)
    | none => .ok (bals, bs)
  else .ok (bals, bs)
termination_by n - i

theorem awLoop_ge {n : Nat} {ws : List Withdrawal} {bals : List Gwei} {bs : List Builder} {i : Nat}
    (h : ¬ i < n) : awLoop n ws bals bs i = .ok (bals, bs) := by
  rw [awLoop, if_neg h]

theorem awLoop_lt {n : Nat} {ws : List Withdrawal} {bals : List Gwei} {bs : List Builder} {i : Nat}
    (h : i < n) (hi : i < ws.length) :
    awLoop n ws bals bs i =
      match awStep bals bs ws[i] with
      | .error e => .error e
      | .ok p => awLoop n ws p.1 p.2 (i + 1) := by
  rw [awLoop, if_pos h, List.getElem?_eq_getElem hi]

theorem sat_le (b d : Nat) : sat b d ≤ b := by unfold sat; split <;> omega

theorem awStep_bounds {bals : List Gwei} {bs : List Builder} {w : Withdrawal} {p : List Gwei × List Builder}
    (h : awStep bals bs w = .ok p) (hbr : ∀ g ∈ bals, g.val < 2 ^ 64) (hbb : ∀ b ∈ bs, b.balance.val < 2 ^ 64) :
    (∀ g ∈ p.1, g.val < 2 ^ 64) ∧ (∀ b ∈ p.2, b.balance.val < 2 ^ 64) := by
  unfold awStep at h
  generalize w.validator_index.val ^^^ (w.validator_index.val &&& FLAG) = bi at h
  generalize (w.validator_index.val &&& FLAG != 0) = c at h
  unfold awStepG at h
  cases c with
  | true =>
    simp only [if_true] at h
    by_cases hb : bi < bs.length
    · rw [dif_pos hb] at h
      cases h
      refine ⟨hbr, fun b hm => ?_⟩
      rcases List.mem_or_eq_of_mem_set hm with hm | rfl
      · exact hbb b hm
      · exact Nat.lt_of_le_of_lt (sat_le _ _) (hbb _ (List.getElem_mem hb))
    · rw [dif_neg hb] at h; cases h
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    by_cases hb : w.validator_index.val < bals.length
    · rw [dif_pos hb] at h
      cases h
      refine ⟨fun g hm => ?_, hbb⟩
      rcases List.mem_or_eq_of_mem_set hm with hm | rfl
      · exact hbr g hm
      · exact Nat.lt_of_le_of_lt (sat_le _ _) (hbr _ (List.getElem_mem hb))
    · rw [dif_neg hb] at h; cases h

structure ALoc (loc : Name → Option DRes) : Prop where
  g1 : loc 1 = some (.place 0 [])
  g86 : loc 86 = none
  g87 : loc 87 = none
  g88 : loc 88 = none
  g89 : loc 89 = none

theorem ALoc.step {loc loc' : Name → Option DRes} (h : ALoc loc) (i : Nat)
    (h' : ∀ x, x ≠ 66 → loc' x = setLoc loc 85 (.place 1 [i]) x) : ALoc loc' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h' 1 (by decide)]; simp [setLoc, h.g1]
  · rw [h' 86 (by decide)]; simp [setLoc, h.g86]
  · rw [h' 87 (by decide)]; simp [setLoc, h.g87]
  · rw [h' 88 (by decide)]; simp [setLoc, h.g88]
  · rw [h' 89 (by decide)]; simp [setLoc, h.g89]

theorem deref_ws (r : DV) (kW : ListKind) (lW : Option Nat) (ws : List Withdrawal) (l : Name → Option DRes) :
    DSt.deref ⟨[r, wsRoot kW lW ws], l⟩ 1 [] = some (wsRoot kW lW ws) := by
  simp [DSt.deref, subAt]

theorem awOut_normal {ds : List DV} {kB : ListKind} {lB : Option Nat} {kD : ListKind} {lD : Option Nat}
    {kW : ListKind} {lW : Option Nat} {ws : List Withdrawal} {loc : Name → Option DRes}
    {r : Res (List Gwei × List Builder)} :
    ∀ o s', (awOut ds kB lB kD lD kW lW ws loc <$> r) = .ok (o, s') → o = .normal := by
  intro o s' h
  cases r with
  | error e => cases h
  | ok p => cases h; rfl

theorem aw_loop (sha : Oracle) (M : Nat) {ds : List DV} {kB : ListKind} {lB : Option Nat} {kD : ListKind}
    {lD : Option Nat} {kW : ListKind} {lW : Option Nat} {ws : List Withdrawal} (h38 : 38 < ds.length)
    (hwv : ∀ w ∈ ws, w.validator_index.val < 2 ^ 64) :
    ∀ d i (bals : List Gwei) (bs : List Builder) (loc : Name → Option DRes), d = ws.length - i →
      ALoc loc → (∀ g ∈ bals, g.val < 2 ^ 64) → (∀ b ∈ bs, b.balance.val < 2 ^ 64) →
      ∃ loc', (den (Scope.env sha) fpsEx (M + 18 + d)).loop awFp
          ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], loc⟩ (.name 1939 85) ⟨1, [], false⟩ i awBody =
        some ((fun p => (DOut.normal, (⟨[awRoot ds kB lB p.1 kD lD p.2, wsRoot kW lW ws], loc'⟩ : DSt))) <$>
          awLoop ws.length ws bals bs i) := by
  intro d
  induction d with
  | zero =>
    intro i bals bs loc hd _ _ _
    refine ⟨loc, ?_⟩
    have hi : ¬ i < ws.length := by omega
    rw [show M + 18 + 0 = (M + 17) + 1 by omega, den_loop]
    unfold loopStep
    rw [deref_ws, awLoop_ge hi]
    have hn : (ws.map wdv)[i]? = none := by simp [hi]
    simp only [wsRoot, isByteList, hn]
    simp
    rfl
  | succ d ih =>
    intro i bals bs loc hd hloc hbr hbb
    have hi : i < ws.length := by omega
    rw [show M + 18 + (d + 1) = (M + 17 + d + 1) + 1 by omega, den_loop]
    unfold loopStep
    rw [deref_ws]
    have hw : (ws.map wdv)[i]? = some (wdv ws[i]) := by simp [List.getElem?_eq_getElem hi]
    have hnb : decide (kW = ListKind.list ∧ SszTy.container Scope.Id.«Withdrawal» = SszTy.uint (UintTy.width 8)) = false := by
      simp
    have hbl : bindLoop (M + 17 + d + 1) false ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], loc⟩
        (.name 1939 85) i (ofChild 1 ([] ++ [i]) (wdv ws[i])) =
        some ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], setLoc loc 85 (.place 1 [i])⟩ := rfl
    simp only [wsRoot, isByteList, hw, hnb, Bool.false_eq_true, if_false]
    rw [show DV.list kW (SszTy.container Scope.Id.«Withdrawal») lW (List.map wdv ws) = wsRoot kW lW ws from rfl]
    rw [hbl]
    have hc : ACtx ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], setLoc loc 85 (.place 1 [i])⟩
        ds kB lB bals kD lD bs kW lW ws := ⟨rfl, h38⟩
    obtain ⟨loc1, hl1, hif⟩ := s_if (sha := sha) (M + d + 1) hc hi (hwv _ (List.getElem_mem hi)) hbb hbr
      (by simp [setLoc, hloc.g1]) (by simp [setLoc]) (by simp [setLoc, hloc.g86]) (by simp [setLoc, hloc.g87])
      (by simp [setLoc, hloc.g88]) (by simp [setLoc, hloc.g89])
    rw [show M + d + 1 + 17 = M + 17 + d + 1 by omega] at hif
    dsimp only
    rw [Sem.block, blockOf_one hif awOut_normal, awLoop_lt hi hi]
    cases hst : awStep bals bs ws[i] with
    | error e => exact ⟨loc, rfl⟩
    | ok p =>
      obtain ⟨hb1, hb2⟩ := awStep_bounds hst hbr hbb
      obtain ⟨loc', hl'⟩ := ih (i + 1) p.1 p.2 loc1 (by omega) (hloc.step i hl1) hb1 hb2
      rw [show M + 18 + d = M + 17 + d + 1 by omega] at hl'
      refine ⟨loc', ?_⟩
      exact hl'

theorem aw_root_eq {ds : List DV} {kB : ListKind} {lB : Option Nat} {bals : List Gwei} {kD : ListKind}
    {lD : Option Nat} {bs : List Builder}
    (h12 : ds[12]? = some (.list kB (.uint gwTy) lB (bals.map Examples.gleaf)))
    (h38 : ds[38]? = some (.list kD (.container Scope.Id.«Builder») lD (bs.map bdv))) :
    DV.cont Scope.Id.«BeaconState» ds = awRoot ds kB lB bals kD lD bs := by
  have hl : 38 < ds.length := by
    rcases Nat.lt_or_ge 38 ds.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at h38; cases h38
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at h12
  rw [List.getElem?_eq_getElem hl, Option.some.injEq] at h38
  simp only [awRoot, ← h12, ← h38, List.set_getElem_self]

theorem aw_den (sha : Oracle) (M : Nat) {ds : List DV} {kB : ListKind} {lB : Option Nat}
    {bals : List Gwei} {kD : ListKind} {lD : Option Nat} {bs : List Builder} {kW : ListKind}
    {lW : Option Nat} {ws : List Withdrawal}
    (h12 : ds[12]? = some (.list kB (.uint gwTy) lB (bals.map Examples.gleaf)))
    (h38 : ds[38]? = some (.list kD (.container Scope.Id.«Builder») lD (bs.map bdv)))
    (hbr : ∀ g ∈ bals, g.val < 2 ^ 64) (hbb : ∀ b ∈ bs, b.balance.val < 2 ^ 64)
    (hwv : ∀ w ∈ ws, w.validator_index.val < 2 ^ 64) :
    (den (Scope.env sha) fpsEx (M + 20 + ws.length)).fn awFp Scope.fn_apply_withdrawals
        [.cont Scope.Id.«BeaconState» ds, wsRoot kW lW ws] =
      some ((fun p => (DRes.val (Value.none), [awRoot ds kB lB p.1 kD lD p.2, wsRoot kW lW ws])) <$>
        awLoop ws.length ws bals bs 0) := by
  have hl38 : 38 < ds.length := by
    rcases Nat.lt_or_ge 38 ds.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at h38; cases h38
  rw [aw_root_eq h12 h38]
  let loc0 : Name → Option DRes := setLoc (setLoc (fun _ => none) 1 (.place 0 [])) 41 (.place 1 [])
  have hloc : ALoc loc0 := ⟨by simp [loc0, setLoc], by simp [loc0, setLoc], by simp [loc0, setLoc],
    by simp [loc0, setLoc], by simp [loc0, setLoc]⟩
  obtain ⟨loc', hlp⟩ := aw_loop sha M (kB := kB) (lB := lB) (kD := kD) (lD := lD) (kW := kW) (lW := lW)
    hl38 hwv ws.length 0 bals bs loc0 (by omega) hloc hbr hbb
  have hn41 : exprStep (Scope.env sha) fpsEx (M + 17 + ws.length) (den (Scope.env sha) fpsEx (M + 17 + ws.length)) awFp
      ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], loc0⟩ (.name 1939 41) = some (.ok (.place 1 [])) := by
    simp only [exprStep, loc0, setLoc]; rfl
  have hlp1 : listPlace ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], loc0⟩ 1 [] = true := by
    simp [listPlace, DSt.deref, subAt, wsRoot, isByteList]
  have hit : (den (Scope.env sha) fpsEx (M + 18 + ws.length)).iter awFp
      ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], loc0⟩ (.name 1939 41) = some (.ok ⟨1, [], false⟩) := by
    rw [show M + 18 + ws.length = (M + 17 + ws.length) + 1 by omega, den_iter]
    simp only [iterStep]
    rw [hn41, dm_bind_ok]
    simp only [hlp1, if_true]
    rfl
  have hst : (den (Scope.env sha) fpsEx (M + 19 + ws.length)).stmt awFp
      ⟨[awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws], loc0⟩ (.forStmt 1939 (.name 1939 85) (.name 1939 41) awBody) =
      some ((fun p => (DOut.normal, (⟨[awRoot ds kB lB p.1 kD lD p.2, wsRoot kW lW ws], loc'⟩ : DSt))) <$>
        awLoop ws.length ws bals bs 0) := by
    rw [show M + 19 + ws.length = (M + 18 + ws.length) + 1 by omega, den_stmt]
    simp only [stmtStep]
    rw [hit, dm_bind_ok]
    exact hlp
  have hinit : initLoc [awRoot ds kB lB bals kD lD bs, wsRoot kW lW ws] (fun _ => none)
      Scope.fn_apply_withdrawals.params.names.zipIdx = loc0 := rfl
  rw [show M + 20 + ws.length = (M + 19 + ws.length) + 1 by omega, den_fn]
  simp only [fnStep]
  rw [if_pos ⟨rfl, rfl, rfl⟩, hinit, aw_body_eq, Sem.block]
  cases hpl : awLoop ws.length ws bals bs 0 with
  | error e =>
    rw [hpl] at hst
    rw [blockOf_err hst]
    rfl
  | ok v =>
    rw [hpl] at hst
    rw [blockOf_ok hst, blockOf_nil]
    rfl

theorem ibi_read' (v : ValidatorIndex) : is_builder_index v = .ok (v.val &&& FLAG != 0) := ibi_read v.val

theorem cvb_read' (v : ValidatorIndex) (hv : v.val < 2 ^ 64) :
    convert_validator_index_to_builder_index v = .ok ⟨v.val ^^^ (v.val &&& FLAG)⟩ := cvb_read v.val hv

theorem uv_bi (n : Nat) : uv (BuilderIndex.mk n) = (n : Int) := rfl

theorem rd_lget_err {α : Type} (xs : List α) (i : Nat) (h : ¬ i < xs.length) :
    lget xs (i : Int) = throw .invalid := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  have hl : ¬ (i : Int) < (xs.length : Int) := by omega
  simp [lget, Rd.pyIndex, hneg, hl]

theorem dbal_read_ok' (st : BeaconState) (v : ValidatorIndex) (a : Gwei) (hi : v.val < st.balances.length)
    (hbi : st.balances[v.val].val < 2 ^ 64) :
    decrease_balance st v a = .ok { st with balances := (st.balances.set v.val
      ⟨sat st.balances[v.val].val a.val⟩) } := by
  cases v; cases a; exact dbal_read_ok st _ _ hi hbi

theorem dbal_read_idx' (st : BeaconState) (v : ValidatorIndex) (a : Gwei) (hi : ¬ v.val < st.balances.length) :
    decrease_balance st v a = .error .invalid := by
  cases v; cases a; exact dbal_read_idx st _ _ hi

theorem rd_aw_loop (ws : List Withdrawal) (hwv : ∀ w ∈ ws, w.validator_index.val < 2 ^ 64) :
    ∀ d i (st : BeaconState) (b : BuilderIndex), d = ws.length - i →
      (∀ g ∈ st.balances, g.val < 2 ^ 64) → (∀ x ∈ st.builders, x.balance.val < 2 ^ 64) →
      (fun r => r.2) <$> apply_withdrawals.loop1 ws ws.length i b st =
        erase ((fun p => { st with balances := p.1, builders := p.2 }) <$>
          awLoop ws.length ws st.balances st.builders i) := by
  intro d
  induction d with
  | zero =>
    intro i st b hd _ _
    rw [apply_withdrawals.loop1, dif_neg (by omega), awLoop_ge (by omega)]
    rfl
  | succ d ih =>
    intro i st b hd hbr hbb
    have hi : i < ws.length := by omega
    have hv := hwv _ (List.getElem_mem hi)
    rw [apply_withdrawals.loop1, dif_pos hi, awLoop_lt hi hi]
    simp only [rd_lget _ _ hi, pure_bind, ibi_read', ok_bind]
    unfold awStep
    generalize hcb : (ws[i].validator_index.val &&& FLAG != 0) = c
    cases c with
    | true =>
      simp only [if_true, cvb_read' _ hv, ok_bind, uv_bi]
      generalize ws[i].validator_index.val ^^^ (ws[i].validator_index.val &&& FLAG) = bi
      by_cases hb : bi < st.builders.length
      · have hbv := hbb _ (List.getElem_mem hb)
        simp only [rd_lget _ _ hb, pure_bind, uv, sat_read_g _ _ hbv, rd_lset _ _ hb]
        rw [awStepG, if_pos (show true = true from rfl), dif_pos hb]
        have hb' : ∀ x ∈ st.builders.set bi { st.builders[bi] with balance := ⟨sat st.builders[bi].balance.val ws[i].amount.val⟩ },
            x.balance.val < 2 ^ 64 := by
          intro x hm
          rcases List.mem_or_eq_of_mem_set hm with hm | rfl
          · exact hbb x hm
          · exact Nat.lt_of_le_of_lt (sat_le _ _) hbv
        have := ih (i + 1) { st with builders := (st.builders.set bi { st.builders[bi] with
          balance := ⟨sat st.builders[bi].balance.val ws[i].amount.val⟩ }) } ⟨bi⟩ (by omega) hbr hb'
        exact this
      · rw [rd_lget_err _ _ hb, awStepG, if_pos (show true = true from rfl), dif_neg hb]
        rfl
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [awStepG, if_neg (show ¬ (false = true) by simp)]
      by_cases hb : ws[i].validator_index.val < st.balances.length
      · have hbv := hbr _ (List.getElem_mem hb)
        rw [dbal_read_ok' _ _ _ hb hbv, ok_bind, dif_pos hb]
        have hb' : ∀ g ∈ st.balances.set ws[i].validator_index.val ⟨sat st.balances[ws[i].validator_index.val].val ws[i].amount.val⟩,
            g.val < 2 ^ 64 := by
          intro g hm
          rcases List.mem_or_eq_of_mem_set hm with hm | rfl
          · exact hbr g hm
          · exact Nat.lt_of_le_of_lt (sat_le _ _) hbv
        exact ih (i + 1) { st with balances := (st.balances.set ws[i].validator_index.val
          ⟨sat st.balances[ws[i].validator_index.val].val ws[i].amount.val⟩) } b (by omega) hb' hbb
      · rw [dbal_read_idx' _ _ _ hb, dif_neg hb]
        rfl

theorem aw_read (st : BeaconState) (ws : List Withdrawal) (hwv : ∀ w ∈ ws, w.validator_index.val < 2 ^ 64)
    (hbr : ∀ g ∈ st.balances, g.val < 2 ^ 64) (hbb : ∀ x ∈ st.builders, x.balance.val < 2 ^ 64) :
    apply_withdrawals st ws =
      erase ((fun p => { st with balances := p.1, builders := p.2 }) <$>
        awLoop ws.length ws st.balances st.builders 0) := by
  have h := rd_aw_loop ws hwv ws.length 0 st default rfl hbr hbb
  rw [← h]
  simp only [apply_withdrawals, bind_pure_comp]

/-- The denotation of `apply_withdrawals` is the readable function, on the balances and the
builders. -/
theorem apply_withdrawals_denote (sha : Oracle) (M : Nat) (ds : List DV) (kB : ListKind) (lB : Option Nat)
    (kD : ListKind) (lD : Option Nat) (kW : ListKind) (lW : Option Nat) (st : BeaconState)
    (ws : List Withdrawal)
    (h12 : ds[12]? = some (.list kB (.uint gwTy) lB (st.balances.map Examples.gleaf)))
    (h38 : ds[38]? = some (.list kD (.container Scope.Id.«Builder») lD (st.builders.map bdv)))
    (hwv : ∀ w ∈ ws, w.validator_index.val < 2 ^ 64)
    (hbr : ∀ g ∈ st.balances, g.val < 2 ^ 64) (hbb : ∀ x ∈ st.builders, x.balance.val < 2 ^ 64) :
    ((den (Scope.env sha) fpsEx (M + 20 + ws.length)).fn awFp Scope.fn_apply_withdrawals
        [.cont Scope.Id.«BeaconState» ds, wsRoot kW lW ws]).map (Except.mapError SpecError.fail) =
      some ((fun st' : BeaconState => (DRes.val (Value.none),
        [awRoot ds kB lB st'.balances kD lD st'.builders, wsRoot kW lW ws])) <$> apply_withdrawals st ws) := by
  rw [aw_den sha M h12 h38 hbr hbb hwv, aw_read st ws hwv hbr hbb]
  cases awLoop ws.length ws st.balances st.builders 0 <;> rfl

/-- SPEC 9.2 for `apply_withdrawals`: a loop over a parameter list, with a write-back call
(`decrease_balance(state, ...)`) and a write through an index (`state.builders[i].balance`). -/
theorem apply_withdrawals_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h) (r0 n nw : Nat) (wv : Value)
    (ds : List DV) (kB : ListKind) (lB : Option Nat) (kD : ListKind) (lD : Option Nat) (kW : ListKind)
    (lW : Option Nat) (st : BeaconState) (ws : List Withdrawal)
    (hd : dec h n (.ref r0) = some (.cont Scope.Id.«BeaconState» ds))
    (hdw : dec h nw wv = some (wsRoot kW lW ws))
    (h12 : ds[12]? = some (.list kB (.uint gwTy) lB (st.balances.map Examples.gleaf)))
    (h38 : ds[38]? = some (.list kD (.container Scope.Id.«Builder») lD (st.builders.map bdv)))
    (hwv : ∀ w ∈ ws, w.validator_index.val < 2 ^ 64)
    (hbr : ∀ g ∈ st.balances, g.val < 2 ^ 64) (hbb : ∀ x ∈ st.builders, x.balance.val < 2 ^ 64)
    (hw : WTree h [.ref r0, wv] awFp) :
    ∀ fuel, 20 + ws.length ≤ fuel →
      ResultMatches gfp awFp h [.ref r0, wv]
        (fun (st' : BeaconState) h' v => v = .none ∧
          ∃ m, dec h' m (.ref r0) = some (awRoot ds kB lB st'.balances kD lD st'.builders))
        (interp (Scope.env sha) fuel Scope.Id.«apply_withdrawals» [.ref r0, wv] h)
        (apply_withdrawals st ws) := by
  intro fuel hf
  have hden := apply_withdrawals_denote sha 0 ds kB lB kD lD kW lW st ws h12 h38 hwv hbr hbb
  rw [Nat.zero_add] at hden
  cases hdn : (den (Scope.env sha) fpsEx (20 + ws.length)).fn awFp Scope.fn_apply_withdrawals
      [.cont Scope.Id.«BeaconState» ds, wsRoot kW lW ws] with
  | none => rw [hdn] at hden; cases hden
  | some r =>
    rw [hdn] at hden
    simp only [Option.map_some, Option.some.injEq] at hden
    have hdec : DecArgs h [.ref r0, wv] [.cont Scope.Id.«BeaconState» ds, wsRoot kW lW ws] := by
      refine ⟨rfl, fun k v d hv hd' => ?_⟩
      match k, hv, hd' with
      | 0, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨n, hd⟩
      | 1, hv, hd' => simp at hv hd'; subst hv; subst hd'; exact ⟨nw, hdw⟩
      | _ + 2, hv, _ => simp at hv
    have hm := denote_sound_calls (Scope.env sha) fpsEx (libFlat_ssz _) gfp awFp
      (f := Scope.Id.«apply_withdrawals»)
      (by simp only [Scope.env, Validation.Tactic.lookup_lit]) hdec hw hwf hdn
    rw [hden] at hm
    refine resultMatches_mono hf (Examples.resultMatches_map (fun st' h' v he => ⟨he.1.1, ?_⟩) hm)
    obtain ⟨-, hr⟩ := he.2
    exact hr 0 (.ref r0) _ rfl rfl

end SpecLean.Layer4.Examples4
