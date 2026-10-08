import Bridge.Lists

/-!
# The bridge tactic

`bridge_run [h₁, …]` proves a goal `Sim f r h` by stepping through both `do` blocks in order. At
a bind it relates the two first steps with a primitive lemma or with one of the `hᵢ` (the
bridge theorems of the callees), and continues with the rest. Pure goals close with
`bridge_close`, range side goals with `bridge_range`.
-/

namespace Pythia.Bridge

/-- A function of the readable Lean (minimal or mainnet). -/
def isGenFn (n : Lean.Name) : Bool :=
  n.getPrefix == `SpecLean.Rd.Gen || n.getPrefix == `SpecLean.Rd.GenMainnet

register_option bridge.stepHeartbeats : Nat := {
  defValue := 2000000, descr := "the heartbeat budget of one bridge_run step" }

register_option bridge.debug : Bool := { defValue := false, descr := "log the steps of bridge_run" }


open SpecLean SpecLean.Rd

theorem uOp_range {α : Type} [UintC α] {op : BinOp} {a b : Int} {x : α}
    (h : (uOp op a b : SpecM α) = .ok x) : UintC.val x < 2 ^ UintC.bits α := by
  unfold uOp at h
  cases hr : erase (intArith op a b) with
  | error e => rw [hr] at h; cases h
  | ok z => rw [hr, ok_bind] at h; exact uOf_range z x h

theorem lget_mem {α : Type} {xs : List α} {i : Int} {x : α} (h : lget xs i = .ok x) : x ∈ xs := by
  unfold lget at h
  split at h
  · rename_i y hy
    cases h
    obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.mp hy
    exact List.mem_of_getElem? hk
  · cases h

theorem uOf_range' {α : Type} [UintC α] {z : Int} {x : α}
    (h : (uOf α z : SpecM α) = .ok x) : UintC.val x < 2 ^ UintC.bits α :=
  uOf_range z x h

theorem uCast_range {α β : Type} [UintC α] [UintC β] {y : α} {x : β}
    (h : (uCast β y : SpecM β) = .ok x) : UintC.val x < 2 ^ UintC.bits β :=
  uOf_range _ _ h

theorem uCast_ok {α β : Type} [UintC α] [UintC β] (x : α) (hb : UintC.bits β = 64)
    (hx : UintC.val x < 2 ^ 64) : (uCast β x : SpecM β) = .ok (UintC.ofNat (UintC.val x)) :=
  uOf_ok _ hb hx

theorem sim_bind_cast {α β : Type} [UintC α] [UintC β] {B : HM Nat} {op : BinOp} {a b : Int}
    (hb : UintC.bits β = 64) (hα : UintC.bits α = 64)
    (hA : Sim UintC.val (uOp op a b : SpecM α) B) :
    Sim UintC.val ((uOp op a b : SpecM α) >>= fun x => (uCast β x : SpecM β)) B := by
  unfold Sim at *
  cases h : (uOp op a b : SpecM α) with
  | error e => rw [h] at hA; rw [err_bind]; exact hA
  | ok x =>
    rw [h] at hA
    have hr := uOp_range h
    rw [hα] at hr
    rw [ok_bind, uCast_ok x hb hr]
    rw [← hA]
    show Except.ok _ = Except.ok _
    rw [UintC.val_ofNat]

/-- Hand type abbreviations of `Nat`. `omega` needs `Nat` itself. -/
macro "bridge_nat" : tactic => `(tactic| try simp only [EpochProofs.Spec.Epoch,
  EpochProofs.Spec.Gwei, EpochProofs.Spec.Slot, EpochProofs.Spec.Uint64,
  EpochProofs.Spec.ValidatorIndex, EpochProofs.Spec.BuilderIndex,
  EpochProofs.Spec.WithdrawalIndex, EpochProofs.Spec.CommitteeIndex] at *)

/-- Relate the first steps of a bind: a primitive lemma or a callee theorem. -/
syntax "bridge_leaf" "[" ident,* "]" : tactic

open Lean Meta Elab Tactic in
/-- Print the main goal to stderr (for debugging the bridge tactic). -/
elab "bridge_dump" : tactic => do
  let g ← getMainGoal
  IO.eprintln s!"bridge_dump: {← ppGoal g}"

/-- Add range facts from the hypotheses `r = .ok x`. -/
syntax "bridge_facts0" : tactic
/-- `bridge_facts0` and the range facts of callee results. -/
syntax "bridge_facts" : tactic
/-- Close a range side goal without the callee facts. -/
syntax "bridge_range0" : tactic
/-- Close a range side goal. -/
syntax "bridge_range" : tactic

open Lean Meta Elab Tactic in
/-- The free variables whose type is `IR_T x`. -/
def irHyps : TacticM (Array FVarId) := withMainContext do
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    let some n := t.getAppFn.constName? | continue
    if (n.getString!.startsWith "IR_" && (`Pythia.Bridge).isPrefixOf n) then out := out.push d.fvarId
  return out

open Lean Meta in
/-- The conjuncts of a proof of `A₁ ∧ … ∧ Aₙ`, as (type, proof) pairs. -/
partial def conjuncts (pf ty : Lean.Expr) : MetaM (List (Lean.Expr × Lean.Expr)) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``And 2 then
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    let l ← conjuncts (← mkAppM ``And.left #[pf]) a
    let r ← conjuncts (← mkAppM ``And.right #[pf]) b
    return l ++ r
  return [(ty, pf)]

open Lean Meta Elab Tactic in
/-- Add one hypothesis per field of each hypothesis `IR_T x`, `depth` levels deep. The
hypotheses `IR_T x` stay. -/
def splitIR (depth : Nat) : TacticM Unit := withMainContext do
  let mut todo : List (Lean.Expr × Lean.Expr) := []
  for fv in ← irHyps do
    todo := (← instantiateMVars (← fv.getType), mkFVar fv) :: todo
  let mut hs : Array Hypothesis := #[]
  for _ in [0:depth] do
    let mut next := []
    for (ty, pf) in todo do
      let some ty' ← unfoldDefinition? ty.consumeMData | continue
      for (cty, cpf) in ← conjuncts pf ty' do
        let cty := cty.headBeta
        hs := hs.push { userName := `ir, type := cty, value := cpf }
        if let some n := cty.consumeMData.getAppFn.constName? then
          if (n.getString!.startsWith "IR_" && (`Pythia.Bridge).isPrefixOf n) then next := (cty, cpf) :: next
    todo := next
  let g ← getMainGoal
  let (_, g') ← g.assertHypotheses hs
  replaceMainGoal [g']

elab "bridge_split" : tactic => splitIR 3

open Lean Meta Elab Tactic in
/-- The local hypotheses that are bridge statements of callees (`h : spec_g`). -/
def specHyps : TacticM (Array Lean.Ident) := withMainContext do
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if let some n := t.getAppFn.constName? then
      if (`Pythia.Bridge).isPrefixOf n && n.getString!.startsWith "spec_" then
        out := out.push (mkIdent d.userName)
  return out

open Lean Meta Elab Tactic in
/-- Add the range facts of the results in the context: `uOp` results are in range, and `lget`
results are members of their list. With `callees`, also the range facts of callee results. -/
def addFacts (callees : Bool) : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  let hs ← if callees then specHyps else pure #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    unless t.isAppOfArity ``Eq 3 do continue
    let lhs := (t.getArg! 1).consumeMData
    let fn := lhs.getAppFn.constName?.getD .anonymous
    let lem := if fn == ``SpecLean.Rd.uOp then some ``uOp_range
      else if fn == ``SpecLean.Rd.lget then some ``lget_mem
      else if fn == ``SpecLean.Rd.uCast then some ``uCast_range
      else if fn == ``SpecLean.Rd.uOf then some ``uOf_range' else none
    if let some lem := lem then
      try
        let pf ← mkAppM lem #[d.toExpr]
        let nm := Lean.Name.mkSimple s!"hr_{(← getLCtx).numIndices}"
        -- A member of a list with a range hypothesis `∀ y ∈ xs, P y`: add `P x` and its fields.
        if lem == ``lget_mem then
          let pty ← inferType pf
          let xs := pty.getArg! 3
          let x := (t.getArg! 2).consumeMData.appArg!
          for d' in (← g.getDecl).lctx do
            if d'.isImplementationDetail then continue
            let t' := (← instantiateMVars d'.type).consumeMData
            if t'.isForall then
              let ok ← g.withContext <| withNewMCtxDepth do
                try
                  let body := t'.bindingBody!.instantiate1 x
                  unless body.isForall do return none
                  unless ← isDefEq body.bindingDomain! pty do return none
                  let pr := mkApp2 d'.toExpr x pf
                  let ty ← inferType pr
                  return some (pr, ty)
                catch _ => return none
              if let some (pr, ty) := ok then
                let ty := ty.headBeta
                let parts ← g.withContext do
                  match ← unfoldDefinition? ty with
                  | some ty' => conjuncts pr ty'
                  | none => pure [(ty, pr)]
                for (cty, cpf) in parts do
                  let (_, g2) ← (← g.assert (Lean.Name.mkSimple s!"hm_{(← getLCtx).numIndices}") cty.headBeta cpf).intro1P
                  g := g2
          let _ := xs
        let (_, g') ← (← g.assert nm (← inferType pf) pf).intro1P
        let gs ← try evalTacticAt (← `(tactic| try simp only [bridge_ir] at $(mkIdent nm):ident)) g'
          catch _ => pure [g']
        g := gs.headD g'
      catch _ => pure ()
    else if callees && isGenFn fn then
      for h in hs do
        let s ← saveState
        try
          let hy ← g.withContext (Term.exprToSyntax d.toExpr)
          let gs ← evalTacticAt (← `(tactic|
            have := simI_post (by apply $h:ident <;> bridge_range0) $hy)) g
          match gs with
          | [g'] => g := g'; break
          | _ => s.restore
        catch _ => s.restore
  replaceMainGoal [g]

elab_rules : tactic | `(tactic| bridge_facts0) => addFacts false
elab_rules : tactic | `(tactic| bridge_facts) => addFacts true

macro_rules | `(tactic| bridge_range0) => `(tactic| first
  | assumption
  | (bridge_facts0
     try simp only [bridge_ir, uv, decide_eq_true_eq, gt_iff_lt, Int.toNat_natCast]
     bridge_nat
     first
     | assumption
     | omega
     | (simp_all only; done)
     | (simp_all; done)
     | (simp_all; omega)))

macro_rules | `(tactic| bridge_range) => `(tactic| first
  | assumption
  | (apply Nat.or_lt_two_pow <;> bridge_range)
  | (apply Nat.lt_of_le_of_lt Nat.and_le_left; bridge_range)
  | (simp only [bridge_simp]; done)
  | decide
  | (simp only [bridge_simp, List.length_map]; first | assumption | omega)
  | (simp only [bridge_ir, bridge_cast]; simp_all; done)
  | (bridge_facts0
     try simp only [bridge_ir, uv, decide_eq_true_eq, gt_iff_lt, Int.toNat_natCast]
     bridge_nat
     first
     | assumption
     | omega
     | (simp_all only; done))
  | (bridge_facts
     try simp only [bridge_ir, uv, decide_eq_true_eq, gt_iff_lt, Int.toNat_natCast]
     bridge_nat
     first
     | assumption
     | omega
     | (simp_all only; done)
     | (simp_all; done)
     | (simp_all; omega)))

/-- Close a pure goal: the alternatives below, tried in order. -/
syntax "bridge_close" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_close) => do
    let alts : Array (Lean.TSyntax `tactic) := #[
      ← `(tactic| with_reducible rfl),
      ← `(tactic| (simp only [bridge_const]; done)),
      ← `(tactic| (subst_vars; with_reducible rfl)),
      ← `(tactic| (subst_vars; with_reducible exact Iff.rfl)),
      ← `(tactic| (subst_vars; simp (disch := omega) only [bridge_simp, uv, bridge_cast]; done)),
      ← `(tactic| (simp only [uv, bridge_cast, bridge_const] at *; rw [uint8_and_beq _ _ (by omega) (by omega)]; simp_all)),
      ← `(tactic| (simp only [uv, bridge_cast, bridge_const] at *; rw [uint8_or _ _ (by omega) (by omega)]; simp_all)),
      ← `(tactic| (simp (disch := first | assumption | decide | omega) only [bridge_simp, bd, lslice_drop_one, toVec_prefix, BytesC.data_ofBytes, List.singleton_append]; done)),
      ← `(tactic| (simp (disch := assumption) only [bridge_simp, uv, lslice_take, lslice_take_one, lslice_drop, lslice_drop_one, List.map_drop, bd, toVec_toList, bridge_cast]; done)),
      ← `(tactic| (simp only [uv, bridge_const, bridge_cast] at *; simp_all only; done)),
      ← `(tactic| (simp only [uv, bridge_const, bridge_cast] at *; omega)),
      ← `(tactic| (rw [Bool.eq_iff_iff]; simp [bridge_simp, uv, and_assoc]; done)),
      ← `(tactic| (subst_vars; rw [Bool.eq_iff_iff]; simp [bridge_simp, uv, and_assoc]; done)),
      ← `(tactic| (subst_vars; rw [Bool.eq_iff_iff]; simp [bridge_simp, uv, and_assoc]; all_goals (intros; bridge_nat; first | omega | (constructor <;> intro <;> omega)))),
      ← `(tactic| (rw [Bool.eq_iff_iff]; simp_all [bridge_simp, uv]; done)),
      ← `(tactic| (simp only [bridge_simp, uv, bridge_cast]; all_goals (bridge_nat; omega))),
      ← `(tactic| (simp only [bridge_simp, uv, bridge_cast]; all_goals (bridge_nat; constructor <;> intro <;> omega))),
      ← `(tactic| (rw [Bool.eq_iff_iff]; simp [bridge_simp, uv, and_assoc]; all_goals (intros; bridge_nat; first | omega | (constructor <;> intro <;> omega)))),
      ← `(tactic| (simp [bridge_simp, uv]; done)),
      ← `(tactic| (simp_all only [bridge_simp, uv]; done)),
      ← `(tactic| (simp_all [bridge_simp, uv]; done))
    ]
    let debug := bridge.debug.get (← getOptions)
    for alt in alts do
      let s ← saveState
      let ok ← tryCatchRuntimeEx
        (do
          evalTactic alt
          pure (← getUnsolvedGoals).isEmpty)
        (fun e => do
          if debug then
            IO.eprintln s!"bridge_close: alternative failed: {((← e.toMessageData.toString).replace "\n" " ").take 300}"
          pure false)
      if ok then return
      s.restore
    throwError "bridge_close: no alternative closes the goal"

/-- Relate a readable call to a hand call with one of the callee theorems. -/
syntax "bridge_callee" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| bridge_callee [$hs,*]) => do
    `(tactic| bridge_leaf [$hs,*])

open Lean Meta Elab Tactic in
/-- The readable and hand sides of a `Sim` goal, after beta. -/
def simSides (g : MVarId) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData
  if t.isAppOfArity ``Sim 5 then
    return some ((t.getArg! 3).headBeta.consumeMData, (t.getArg! 4).headBeta.consumeMData)
  return none

open Lean Meta Elab Tactic in
/-- Run `tac` on `g`. On failure restore the state and return `none`. -/
def tryAt (tac : TacticM Unit) (g : MVarId) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  let budget := bridge.stepHeartbeats.get (← getOptions) * 1000
  let errs (m : MessageLog) : Nat := m.toList.countP (·.severity == .error)
  let before := errs (← getThe Core.State).messages
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
        (fun c => { c with maxHeartbeats := budget }) do
      setGoals [g]
      tac
      let ms := (← getThe Core.State).messages
      if errs ms > before then
        let last := ms.toList.filter (·.severity == .error) |>.getLast?
        let txt ← match last with
          | some m => m.data.toString
          | none => pure ""
        throwError "bridge: the step logged an error: {txt}"
      return some (← getUnsolvedGoals))
    (fun e => do
      let msg ← e.toMessageData.toString
      s.restore
      if bridge.debug.get (← getOptions) then
        logInfo m!"bridge: step failed: {msg.take 600}"
      return none)

open Lean Meta Elab Tactic in
/-- The tactics that may relate the readable step `a` to its hand step, by the head of `a`. -/
def leafTacs (hs : Array Ident) (a hd : Lean.Expr) : TacticM (Array Lean.Syntax) := do
  let a := a.consumeMData
  let hd := hd.consumeMData
  let handPure := hd.isAppOfArity ``Pure.pure 4
  let fn := a.getAppFn.constName?.getD .anonymous
  let close ← `(tactic| all_goals first | with_reducible rfl | decide | bridge_range | bridge_close)
  if fn == ``SpecLean.Rd.uOp && a.getAppNumArgs == 5 then
    let op := (a.getArg! 2).constName?.getD .anonymous
    if handPure then
      let lem := match op with
        | ``SpecLean.BinOp.add => some (mkIdent ``sim_uOp_add_pure)
        | ``SpecLean.BinOp.sub => some (mkIdent ``sim_uOp_sub_pure)
        | ``SpecLean.BinOp.bitAnd => some (mkIdent ``sim_uOp_and_pure)
        | ``SpecLean.BinOp.bitOr => some (mkIdent ``sim_uOp_or_pure)
        | _ => none
      let notArg := (a.getArg! 4).consumeMData.isAppOfArity ``Int.not 1
      if op == ``SpecLean.BinOp.bitAnd && notArg then
        return #[← `(tactic| (apply sim_uOp_andnot_pure; $close))]
      match lem with
      | some l => return #[← `(tactic| (apply $l:ident; $close))]
      | none => return #[]
    let lem := match op with
      | ``SpecLean.BinOp.add => some (mkIdent ``sim_uOp_add)
      | ``SpecLean.BinOp.sub => some (mkIdent ``sim_uOp_sub)
      | ``SpecLean.BinOp.mul => some (mkIdent ``sim_uOp_mul)
      | ``SpecLean.BinOp.floorDiv => some (mkIdent ``sim_uOp_div)
      | ``SpecLean.BinOp.mod => some (mkIdent ``sim_uOp_mod)
      | _ => none
    match lem with
    | some l => return #[← `(tactic| (apply $l:ident; $close))]
    | none => return #[]
  if fn == ``SpecLean.Rd.uCast && handPure then
    return #[← `(tactic| (apply sim_uCast_pure; $close))]
  if fn == ``SpecLean.Rd.uOf && handPure then
    return #[← `(tactic| (apply sim_uOf_pure; $close))]
  if fn == ``SpecLean.Rd.sumU then return #[← `(tactic| (apply sim_sumU; $close))]
  if fn == ``SpecLean.Rd.pyMax then
    return #[← `(tactic| (apply sim_pyMax2; intro _ _; rfl))]
  if fn == ``SpecLean.Rd.lget then return #[← `(tactic| apply sim_lget)]
  if fn == ``SpecLean.Rd.lset then return #[← `(tactic| (apply sim_lset; bridge_close))]
  if a.isAppOfArity ``Bind.bind 6 then
    let k := (a.getArg! 5).consumeMData
    let kb := if k.isLambda then k.bindingBody!.consumeMData else k
    if kb.getAppFn.constName? == some ``SpecLean.Rd.uCast then
      return #[← `(tactic| (apply sim_bind_cast; all_goals first | with_reducible rfl | decide | bridge_leaf [$hs,*]))]
    return #[]
  if isGenFn fn then
    let mut out := #[]
    for h in hs ++ (← specHyps) do
      out := out.push (← `(tactic| (apply simI_sim; apply $h:ident; all_goals bridge_range)))
    return out
  return #[]

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_leaf [$hs,*]) => withMainContext do
    let g ← getMainGoal
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isAppOfArity ``Sim 5 do throwError "bridge_leaf: not a Sim goal"
    let tacs ← leafTacs hs.getElems (t.getArg! 3).headBeta (t.getArg! 4).headBeta
    for tac in tacs do
      let s ← saveState
      try
        evalTactic tac
        if (← getUnsolvedGoals).isEmpty then return
        s.restore
      catch _ => s.restore
    throwError "bridge_leaf: no lemma fits"

open Lean Meta Elab Tactic in
/-- Run `tac` on the goal with tag `tag` among the main goals. Keep the other goals. -/
def onTag (tag : Lean.Name) (tac : Lean.Syntax) : TacticM Unit := do
  let gs ← getGoals
  let mut out := []
  let mut found := false
  for g in gs do
    if !found && (← g.getTag).components.getLast? == some tag then
      found := true
      out := out ++ (← evalTacticAt tac g)
    else
      out := out ++ [g]
  unless found do throwError "bridge: no goal {tag}"
  setGoals out

open Lean Meta Elab Tactic in
/-- Prove one `Sim` goal step by step. Returns the goals it could not prove. -/
partial def bridgeGoal (hs : Array Ident) (g : MVarId) : TacticM (List MVarId) := do
  if ← g.isAssigned then return []
  if (← whnfR (← g.getType)).isForall then
    if let some gs ← tryAt (evalTactic (← `(tactic| intros))) g then
      let mut out := []
      for g' in gs do out := out ++ (← bridgeGoal hs g')
      return out
  let some (r, h) ← g.withContext (simSides g) | return [g]
  if bridge.debug.get (← getOptions) then
    logInfo m!"bridge: {r.getAppFn} {r.getAppNumArgs} | {h.getAppFn} {h.getAppNumArgs}"
  let isBind (e : Lean.Expr) := e.isAppOfArity ``Bind.bind 6
  let isPure (e : Lean.Expr) := e.isAppOfArity ``Pure.pure 4
  let isIte (e : Lean.Expr) := e.isAppOfArity ``ite 5
  let leaf : TacticM Unit := evalTactic (← `(tactic| bridge_leaf [$hs,*]))
  let continueWith (gs : Option (List MVarId)) : TacticM (Option (List MVarId)) := do
    match gs with
    | none => return none
    | some gs =>
      let mut rest := []
      for g' in gs do
        let gs' := (← tryAt (evalTactic (← `(tactic| try dsimp only))) g').getD [g']
        for g'' in gs' do
          rest := rest ++ (← bridgeGoal hs g'')
      return some rest
  -- a hand `pure (if c then a else b)`: split it
  if isPure h && isIte (h.getArg! 3).consumeMData.headBeta then
    if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| apply sim_pure_ite))) g) then
      return gs
  -- a hand `pure (a || b)` or `pure (a && b)` against a readable `if`: split it
  if isIte r && isPure h then
    let v := (h.getArg! 3).consumeMData.headBeta
    if v.isAppOfArity ``or 2 then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| apply sim_pure_or))) g) then
        return gs
    if v.isAppOfArity ``and 2 then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| apply sim_pure_and))) g) then
        return gs
  -- pure on both sides
  if isPure r && isPure h then
    if let some gs ← tryAt (evalTactic (← `(tactic| exact sim_pure _ _ _ (by bridge_close)))) g then
      return gs
    return [g]
  if isBind r && isIte h &&
      (r.getArg! 4).consumeMData.getAppFn.constName? == some ``SpecLean.Rd.iOp then
    let tacP : TacticM Unit := do
      evalTactic (← `(tactic| apply sim_pow_uOf))
      onTag `hb (← `(tactic| decide))
      onTag `hk (← `(tactic| bridge_range))
      onTag `hK (← `(tactic| intro _))
    if let some gs ← continueWith (← tryAt tacP g) then return gs
  if isBind r && isIte h &&
      (r.getArg! 4).consumeMData.getAppFn.constName? == some ``SpecLean.Rd.assert then
    let tacA : TacticM Unit := do
      evalTactic (← `(tactic| apply sim_assert))
      onTag `hc (← `(tactic| bridge_close))
      onTag `hK (← `(tactic| intro _))
    if let some gs ← continueWith (← tryAt tacA g) then return gs
  if isBind r then
    let a := (r.getArg! 4).consumeMData
    -- a readable step that is `pure _`
    if isPure a then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| refine sim_bind_l _ rfl ?_))) g) then
        return gs
    if isBind h && a.isAppOfArity ``List.mapM 5 then
      let tacM : TacticM Unit := do
        evalTactic (← `(tactic| apply sim_bind))
        onTag `hA (← `(tactic| apply sim_mapM))
        onTag `hK (← `(tactic| intro x hx))
      if let some gs ← continueWith (← tryAt tacM g) then return gs
    if isBind h then
      let tac : TacticM Unit := do
        evalTactic (← `(tactic| apply sim_bind))
        onTag `hA (← `(tactic| bridge_leaf [$hs,*]))
        onTag `hK (← `(tactic| intro x hx))
      if let some gs ← continueWith (← tryAt tac g) then return gs
    -- a readable call whose hand side is a plain value
    let aFn := a.getAppFn.constName?.getD .anonymous
    let tac2 : TacticM Unit := do
      unless isGenFn aFn || aFn == ``SpecLean.Rd.uOp do
        throwError "bridge: not a call"
      let k := (r.getArg! 5).consumeMData
      let kb := if k.isLambda then k.bindingBody!.consumeMData else k
      if kb.getAppFn.constName? == some ``SpecLean.Rd.uCast then
        throwError "bridge: a cast follows"
      evalTactic (← `(tactic| apply sim_bind_val))
      onTag `hA (← `(tactic| bridge_callee [$hs,*]))
      onTag `hK (← `(tactic| intro x hx hfx))
    if let some gs ← continueWith (← tryAt tac2 g) then return gs
    -- a readable `mod` or `//` by a nonzero value: it cannot fail, so it may come before or after
    -- the hand step
    if aFn == ``SpecLean.Rd.uOp && isBind h then
      let tac7 : TacticM Unit :=
        evalTactic (← `(tactic| first
          | refine sim_bind_l _ (uOp_mod_ok (by decide) _ _ (by bridge_range) (by bridge_range)) ?_
          | refine sim_bind_l _ (uOp_div_ok (by decide) _ _ (by bridge_range) (by bridge_range)) ?_))
      if let some gs ← continueWith (← tryAt tac7 g) then return gs
    -- a readable `bytesOf` of the right length
    if aFn == ``SpecLean.Rd.bytesOf then
      let tac9 : TacticM Unit :=
        evalTactic (← `(tactic| refine sim_bind_l _ (bytesOf_ok _ (by
          bridge_facts0
          simp only [bridge_simp, bd, lslice_drop_one, List.length_append, List.length_drop,
            List.length_cons, List.length_nil]
          first | omega | (bridge_dump; omega))) ?_))
      if let some gs ← continueWith (← tryAt tac9 g) then return gs
    -- a readable step that cannot fail: an append or a list of no limit
    if aFn == ``SpecLean.Rd.lappend || aFn == ``SpecLean.Rd.lfrom then
      let tac6 : TacticM Unit :=
        evalTactic (← `(tactic| first
          | refine sim_bind_l _ (lappend_none _ _) ?_
          | refine sim_bind_l _ (lfrom_none _) ?_))
      if let some gs ← continueWith (← tryAt tac6 g) then return gs
    -- a readable step whose result is already known (a second read of the same place)
    let tac5 : TacticM Unit :=
      evalTactic (← `(tactic| refine sim_bind_l _ (by assumption) ?_))
    if let some gs ← continueWith (← tryAt tac5 g) then return gs
    -- a readable `uOf` of a value in range
    let tac4 : TacticM Unit :=
      evalTactic (← `(tactic| refine sim_bind_l _ (uOf_ok _ (by rfl) (by bridge_range)) ?_))
    if let some gs ← continueWith (← tryAt tac4 g) then return gs
    -- a readable cast that cannot fail
    let tac3 : TacticM Unit :=
      evalTactic (← `(tactic| refine sim_bind_l _ (uCast_ok _ (by rfl) (by bridge_range)) ?_))
    if let some gs ← continueWith (← tryAt tac3 g) then return gs
  if isBind h then
    let b := (h.getArg! 4).consumeMData
    let bFn := b.getAppFn.constName?.getD .anonymous
    if bFn == ``EpochProofs.Spec.uint64Mod || bFn == ``EpochProofs.Spec.uint64Div then
      let tac8 : TacticM Unit :=
        evalTactic (← `(tactic| first
          | refine sim_bind_r _ (uint64Mod_ok _ _ (by bridge_range)) ?_
          | refine sim_bind_r _ (uint64Div_ok _ _ (by bridge_range)) ?_))
      if let some gs ← continueWith (← tryAt tac8 g) then return gs
    if isPure b then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| refine sim_bind_r _ rfl ?_))) g) then
        return gs
  if isIte r && isIte h then
    let tac : TacticM Unit := do
      evalTactic (← `(tactic| apply sim_ite))
      onTag `hc (← `(tactic| bridge_close))
      onTag `h1 (← `(tactic| intro _ _))
      onTag `h2 (← `(tactic| intro _ _))
    if let some gs ← continueWith (← tryAt tac g) then return gs
  -- a leaf on its own, with the abs map of the goal
  let leafAs : TacticM Unit := do
    evalTactic (← `(tactic| apply sim_congr))
    onTag `hs (← `(tactic| bridge_leaf [$hs,*]))
    onTag `hfg (← `(tactic| (intro _; first | with_reducible rfl | rfl | simp [bridge_simp])))
  if let some gs ← tryAt leafAs g then return gs
  return [g]

/-- Step through both `do` blocks. Fails if a goal is left. -/
syntax "bridge_run" "[" ident,* "]" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_run [$hs,*]) => do
    let g ← getMainGoal
    let rest ← bridgeGoal hs.getElems g
    setGoals rest
    unless rest.isEmpty do
      throwError "bridge_run: {rest.length} goals left\n{Lean.MessageData.joinSep (rest.map Lean.MessageData.ofGoal) "\n"}"

open Lean Meta Elab Tactic in
/-- Prove a goal `Post P r` by walking `r`. Returns the goals it could not prove. -/
partial def bridgePost (g : MVarId) : TacticM (List MVarId) := do
  if ← g.isAssigned then return []
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``Post 3 do return [g]
  let p := (t.getArg! 1).consumeMData
  let r := (t.getArg! 2).headBeta.consumeMData
  if bridge.debug.get (← getOptions) then
    logInfo m!"bridge post: {r.getAppFn} {r.getAppNumArgs}"
  if p.isLambda && p.bindingBody!.consumeMData.isConstOf ``True then
    if let some gs ← tryAt (evalTactic (← `(tactic| exact post_true _))) g then return gs
  let step (tac : Lean.Syntax) : TacticM (Option (List MVarId)) := do
    match ← tryAt (evalTactic tac) g with
    | none => return none
    | some gs =>
      let mut rest := []
      for g' in gs do
        let gs' := (← tryAt (evalTactic (← `(tactic| try dsimp only))) g').getD [g']
        for g'' in gs' do rest := rest ++ (← bridgePost g'')
      return some rest
  if r.isAppOfArity ``Bind.bind 6 then
    if let some gs ← step (← `(tactic| (apply post_bind; intro _ _))) then return gs
  if r.isAppOfArity ``ite 5 then
    if let some gs ← step (← `(tactic| (apply post_ite <;> intro _))) then return gs
  if r.isAppOfArity ``Pure.pure 4 then
    if let some gs ← tryAt (evalTactic (← `(tactic|
        (apply post_pure; (try dsimp only); bridge_range)))) g then return gs
  if r.getAppFn.constName? == some ``MonadExcept.throw then
    if let some gs ← tryAt (evalTactic (← `(tactic| exact post_throw _))) g then return gs
  if let some gs ← tryAt (evalTactic (← `(tactic|
      (intro _ _; (try dsimp only); bridge_range)))) g then
    if bridge.debug.get (← getOptions) then
      logInfo m!"bridge post leaf: {gs.length} goals left"
    return gs
  return [g]

/-- Prove a bridge statement `SimI P f r h`: the `Sim` part with `bridge_run`, the range part
by walking `r`. -/
syntax "bridge_main" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_main) => do
    evalTactic (← `(tactic| refine simI_intro ?_ ?_))
    let gs ← getGoals
    match gs with
    | [g1, g2] =>
      let r1 ← bridgeGoal #[] g1
      let r2 ← bridgePost g2
      let rest := r1 ++ r2
      setGoals rest
      unless rest.isEmpty do
        throwError "bridge_main: {rest.length} goals left\n{Lean.MessageData.joinSep (rest.map Lean.MessageData.ofGoal) "\n"}"
    | _ => throwError "bridge_main: not a SimI goal"

end Pythia.Bridge
