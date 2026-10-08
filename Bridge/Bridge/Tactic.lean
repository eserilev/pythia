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

register_option bridge.closeHeartbeats : Nat := {
  defValue := 250000, descr := "the heartbeat budget of one bridge_close alternative" }

register_option bridge.debug : Bool := { defValue := false, descr := "log the steps of bridge_run" }


open SpecLean SpecLean.Rd

/-- Replace a readable step by an equal one (a callee on a state with fields it does not read). -/
theorem sim_bind_eq_l {α β β' : Type} {g : β → β'} {A A' : SpecM α} {K : α → SpecM β}
    {H : HM β'} (h : A = A') (hs : Sim g (A' >>= K) H) : Sim g (A >>= K) H := by
  subst h; exact hs

theorem sim_assoc_r {α γ β β' : Type} {g : β → β'} {R : SpecM β} {A : HM α} {f : α → HM γ}
    {k : γ → HM β'} (hs : Sim g R (A >>= fun x => f x >>= k)) : Sim g R ((A >>= f) >>= k) := by
  cases A <;> exact hs

theorem sim_assoc_l {α γ β β' : Type} {g : β → β'} {A : SpecM α} {f : α → SpecM γ}
    {k : γ → SpecM β} {H : HM β'} (hs : Sim g (A >>= fun x => f x >>= k) H) :
    Sim g ((A >>= f) >>= k) H := by
  cases A <;> exact hs

theorem sim_ite_bind_r {γ β β' : Type} {g : β → β'} {R : SpecM β} (c : Prop) [Decidable c]
    {A B : HM γ} {k : γ → HM β'} (hs : Sim g R (if c then A >>= k else B >>= k)) :
    Sim g R ((if c then A else B) >>= k) := by
  by_cases h : c
  · rw [if_pos h] at hs ⊢; exact hs
  · rw [if_neg h] at hs ⊢; exact hs

theorem sim_ite_bind_l {γ β β' : Type} {g : β → β'} {H : HM β'} (c : Prop) [Decidable c]
    {A B : SpecM γ} {k : γ → SpecM β} (hs : Sim g (if c then A >>= k else B >>= k) H) :
    Sim g ((if c then A else B) >>= k) H := by
  by_cases h : c
  · rw [if_pos h] at hs ⊢; exact hs
  · rw [if_neg h] at hs ⊢; exact hs

/-- A readable `contains` on a list of uints against the hand membership of the values. -/
theorem contains_iff_mem_val {α : Type} [UintC α] [DecidableEq α] (xs : List α) (a : α) :
    (xs.contains a = true) ↔ (UintC.val a ∈ xs.map UintC.val) := by
  rw [List.contains_iff_mem, List.mem_map]
  constructor
  · intro h; exact ⟨a, h, rfl⟩
  · rintro ⟨b, hb, he⟩
    have : b = a := by rw [← UintC.ofNat_val b, he, UintC.ofNat_val]
    exact this ▸ hb

/-- A readable `assert c` against the hand `if !b then throw` with a `Bool` condition. -/
theorem sim_assert_bool {β β' : Type} {g : β → β'} (c b : Bool)
    {K : Unit → SpecM β} {L : PUnit → HM β'} (hc : c = b) (hK : b = true → Sim g (K ()) (L ())) :
    Sim g (assert c >>= K)
      (if (!b) = true then (throw .assertionFailed >>= L) else (pure PUnit.unit >>= L)) := by
  subst hc
  cases c
  · rfl
  · exact hK rfl

theorem sim_of_bind_pure_r {α β : Type} {f : α → β} {A : SpecM α} {H : HM β}
    (hs : Sim f A (H >>= pure)) : Sim f A H := by
  have : (H >>= pure) = H := by cases H <;> rfl
  rw [this] at hs; exact hs

/-- A readable `if` with no hand `if` to pair with: split it. -/
theorem sim_ite_l {β β' : Type} {g : β → β'} (c : Prop) [Decidable c] {A B : SpecM β} {H : HM β'}
    (h1 : c → Sim g A H) (h2 : ¬c → Sim g B H) : Sim g (if c then A else B) H := by
  by_cases h : c
  · rw [if_pos h]; exact h1 h
  · rw [if_neg h]; exact h2 h

theorem sim_pure_ite_l {β β' : Type} {g : β → β'} (c : Prop) [Decidable c] (a b : β) {H : HM β'}
    (hs : Sim g (if c then pure a else pure b) H) : Sim g (pure (if c then a else b)) H := by
  by_cases h : c
  · rw [if_pos h] at hs ⊢; exact hs
  · rw [if_neg h] at hs ⊢; exact hs

theorem not_contains_iff_not_mem_val {α : Type} [UintC α] [DecidableEq α] (xs : List α) (a : α) :
    ((!xs.contains a) = true) ↔ ¬ (UintC.val a ∈ xs.map UintC.val) := by
  rw [← contains_iff_mem_val]
  cases xs.contains a <;> simp

theorem uv_beq_val {α β : Type} [UintC α] [UintC β] (a : α) (b : β) :
    (uv a == uv b) = (UintC.val a == UintC.val b) := by
  unfold uv
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> omega

/-- `[a, b].contains x` on uints: the values are equal to one of the two. -/
theorem contains_pair_val {α : Type} [UintC α] [DecidableEq α] (a b x : α) :
    [a, b].contains x = (UintC.val x == UintC.val a || UintC.val x == UintC.val b) := by
  have inj : ∀ u v : α, (u == v) = (UintC.val u == UintC.val v) := by
    intro u v
    by_cases h : u = v
    · subst h; simp
    · have : UintC.val u ≠ UintC.val v := fun he => h (by rw [← UintC.ofNat_val u, he, UintC.ofNat_val])
      rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr this]
  simp only [List.contains_cons, List.contains_nil, Bool.or_false]
  rw [inj x a, inj x b]

theorem uOp_range {α : Type} [UintC α] {op : BinOp} {a b : Int} {x : α}
    (h : (uOp op a b : SpecM α) = .ok x) : UintC.val x < 2 ^ UintC.bits α := by
  unfold uOp at h
  cases hr : erase (intArith op a b) with
  | error e => rw [hr] at h; cases h
  | ok z => rw [hr, ok_bind] at h; exact uOf_range z x h

theorem sumU_range {α : Type} [UintC α] {s : α} {xs : List α} {y : α} (h : sumU s xs = .ok y) :
    UintC.val y < 2 ^ UintC.bits α ∨ UintC.val y = UintC.val s := by
  unfold sumU Prim.sum at h
  induction xs generalizing s with
  | nil => cases h; exact Or.inr rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases hz : (uOp .add (uv s) (uv x) : SpecM α) with
    | error e => rw [hz] at h; cases h
    | ok z =>
      rw [hz] at h
      rcases ih h with h1 | h1
      · exact Or.inl h1
      · exact Or.inl (h1 ▸ uOp_range hz)

theorem lget_mem {α : Type} {xs : List α} {i : Int} {x : α} (h : lget xs i = .ok x) : x ∈ xs := by
  unfold lget at h
  split at h
  · rename_i y hy
    cases h
    obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.mp hy
    exact List.mem_of_getElem? hk
  · cases h

theorem lset_length {α : Type} {xs ys : List α} {i : Int} {x : α} (h : lset xs i x = .ok ys) :
    ys.length = xs.length := by
  unfold lset at h
  split at h
  · cases h; simp
  · cases h

theorem ir_lset {α : Type} {P : α → Prop} {xs ys : List α} {i : Int} {x : α}
    (h : lset xs i x = .ok ys) (hxs : xs.length < 2 ^ 64 ∧ ∀ y ∈ xs, P y) (hx : P x) :
    ys.length < 2 ^ 64 ∧ ∀ y ∈ ys, P y := by
  unfold lset at h
  split at h
  · cases h
    refine ⟨by simpa using hxs.1, fun y hy => ?_⟩
    rcases List.mem_or_eq_of_mem_set hy with h1 | h1
    · exact hxs.2 y h1
    · rw [h1]; exact hx
  · cases h

theorem lset_forall {α : Type} {P : α → Prop} {xs ys : List α} {i : Int} {x : α}
    (h : lset xs i x = .ok ys) (hxs : ∀ y ∈ xs, P y) (hx : P x) : ∀ y ∈ ys, P y := by
  unfold lset at h
  split at h
  · cases h
    intro y hy
    rcases List.mem_or_eq_of_mem_set hy with h1 | h1
    · exact hxs y h1
    · subst h1; exact hx
  · cases h

theorem uOf_range' {α : Type} [UintC α] {z : Int} {x : α}
    (h : (uOf α z : SpecM α) = .ok x) : UintC.val x < 2 ^ UintC.bits α :=
  uOf_range z x h

theorem bytesOf_len {β : Type} [BytesC β] {b : List UInt8} {x : β}
    (h : (bytesOf β b : SpecM β) = .ok x) : (BytesC.data x).length = BytesC.len β := by
  unfold bytesOf at h
  split at h
  · cases h; rw [BytesC.data_ofBytes]; assumption
  · cases h

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

/-- `decide` on a goal with no local variables. On other goals `decide` can unfold a large
term until the heartbeat limit. -/
syntax "bridge_decide" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_decide) => withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    if t.hasFVar || t.hasMVar then throwError "bridge_decide: the goal has variables"
    evalTactic (← `(tactic| decide))

/-- Run a tactic and turn a runtime error (recursion limit, heartbeats) into an ordinary failure,
so that `first` tries the next alternative. -/
syntax "bridge_safe" "(" tacticSeq ")" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_safe ($t)) => do
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do evalTactic t; pure true) (fun _ => pure false)
    unless ok do
      s.restore
      throwError "bridge_safe: the tactic failed"

/-- Hand type abbreviations of `Nat`. `omega` needs `Nat` itself. -/
macro "bridge_nat" : tactic => `(tactic| try simp only [EpochProofs.Spec.Epoch,
  EpochProofs.Spec.Gwei, EpochProofs.Spec.Slot, EpochProofs.Spec.Uint64,
  EpochProofs.Spec.ValidatorIndex, EpochProofs.Spec.BuilderIndex,
  EpochProofs.Spec.WithdrawalIndex, EpochProofs.Spec.CommitteeIndex] at *)

/-- Step through both `do` blocks. Fails if a goal is left. -/
syntax "bridge_run" "[" ident,* "]" : tactic

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
/-- The callee hypotheses for the readable function `fn`: `h : spec_f` with `f` the last part of
`fn`. Trying the others makes the unifier unfold large definitions. -/
def specHypsFor (fn : Lean.Name) : TacticM (Array Lean.Ident) := withMainContext do
  let want := s!"spec_{fn.getString!}"
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if let some n := t.getAppFn.constName? then
      if (`Pythia.Bridge).isPrefixOf n && n.getString! == want then
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
      else if fn == ``SpecLean.Rd.uOf then some ``uOf_range'
      else if fn == ``SpecLean.Rd.bytesOf then some ``bytesOf_len
      else if fn == ``SpecLean.Rd.lset then some ``lset_length
      else if fn == ``SpecLean.Rd.sumU then some ``sumU_range
      else if fn == ``SpecLean.Rd.pyMax then some ``pyMax2_val
      else if fn == ``SpecLean.Rd.pyMin then some ``pyMin2_val
      else if fn == ``SpecLean.Rd.pyRange then some ``pyRange_uv_len else none
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
        -- A set into a list with a range hypothesis `∀ y ∈ xs, P y`: add `∀ y ∈ ys, P y` when the
        -- new item has `P` (proved without the callee facts, so this does not recurse).
        if lem == ``lset_length && callees then
          let xs := (lhs.getArg! 1).consumeMData
          for d' in (← g.getDecl).lctx do
            if d'.isImplementationDetail then continue
            let t' := (← instantiateMVars d'.type).consumeMData
            unless t'.isForall do continue
            let body := t'.bindingBody!
            unless body.isForall do continue
            let dom := body.bindingDomain!
            unless dom.isAppOfArity ``Membership.mem 5 && (dom.getArg! 3).consumeMData == xs do continue
            let s ← saveState
            try
              let hS ← g.withContext (Term.exprToSyntax d.toExpr)
              let hS' ← g.withContext (Term.exprToSyntax d'.toExpr)
              let before := (← getThe Core.State).messages.toList.countP (·.severity == .error)
              let gs ← evalTacticAt (← `(tactic|
                have := lset_forall $hS $hS' (by bridge_range0))) g
              let after := (← getThe Core.State).messages.toList.countP (·.severity == .error)
              match gs with
              | [g'] => if after == before then g := g' else s.restore
              | _ => s.restore
            catch _ => s.restore
        let (_, g') ← (← g.assert nm (← inferType pf) pf).intro1P
        let simpT ← if lem == ``pyMax2_val || lem == ``pyMin2_val then
            -- constants as numbers, so `omega` can bound the result
            `(tactic| try simp only [bridge_ir, bridge_const, bridge_simp] at $(mkIdent nm):ident)
          else `(tactic| try simp only [bridge_ir] at $(mkIdent nm):ident)
        let gs ← try evalTacticAt simpT g'
          catch _ => pure [g']
        g := gs.headD g'
      catch _ => pure ()
    else if callees && isGenFn fn then
      for h in ← g.withContext (do setGoals [g]; specHypsFor fn) do
        let s ← saveState
        try
          let hy ← g.withContext (Term.exprToSyntax d.toExpr)
          let before := (← getThe Core.State).messages.toList.countP (·.severity == .error)
          let gs ← evalTacticAt (← `(tactic|
            have := simI_post (by apply $h:ident <;> bridge_range0) $hy)) g
          let after := (← getThe Core.State).messages.toList.countP (·.severity == .error)
          match gs with
          | [g'] => if after == before then g := g'; break else s.restore
          | _ => s.restore
        catch _ => s.restore
  replaceMainGoal [g]

elab_rules : tactic | `(tactic| bridge_facts0) => addFacts false
elab_rules : tactic | `(tactic| bridge_facts) => addFacts true

/-- Close `P a` from `h : ∀ y ∈ xs, P y` and `ha : a ∈ xs` in the context. -/
syntax "bridge_mem" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_mem) => withMainContext <| withTransparency .default do
    let lctx ← getLCtx
    let mut mems : Array (Lean.Expr × Lean.Expr) := #[]
    let mut alls : Array Lean.Expr := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).consumeMData
      if t.isAppOfArity ``Membership.mem 5 then mems := mems.push (d.toExpr, t.getArg! 4)
      else if t.isForall && t.bindingBody!.isForall &&
          t.bindingBody!.bindingDomain!.isAppOfArity ``Membership.mem 5 then
        alls := alls.push d.toExpr
    let g ← getMainGoal
    for h in alls do
      for (m, a) in mems do
        let s ← saveState
        try
          let pf := mkApp2 h a m
          let ty ← inferType pf
          if ← isDefEq ty (← g.getType) then
            g.assign pf
            replaceMainGoal []
            return
          -- a field of an `IR_T a` fact
          let ty' := (← instantiateMVars ty).headBeta
          if let some u ← unfoldDefinition? ty' then
            for (cty, cpf) in ← conjuncts pf u do
              if ← isDefEq cty.headBeta (← g.getType) then
                g.assign cpf
                replaceMainGoal []
                return
          s.restore
        catch _ => s.restore
    throwError "bridge_mem: no fact"

/-- Close `f x = .ok ?b` with a hypothesis `f y = .ok b` of the same head `f`. `assumption` tries
every hypothesis and can unfold large definitions. -/
syntax "bridge_ok_hyp" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_ok_hyp) => withMainContext do
    let t := (← instantiateMVars (← getMainTarget)).consumeMData
    unless t.isAppOfArity ``Eq 3 do throwError "bridge_ok_hyp: not an equation"
    let f := (t.getArg! 1).consumeMData.getAppFn
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``Eq 3 do continue
      unless (ty.getArg! 1).consumeMData.getAppFn == f do continue
      let s ← saveState
      try
        let hS ← Term.exprToSyntax d.toExpr
        evalTactic (← `(tactic| exact $hS))
        return
      catch _ => s.restore
    throwError "bridge_ok_hyp: no hypothesis"

/-- `assumption`, but a goal `call = .ok _` uses only hypotheses about the same call: other
hypotheses make the unifier unfold large definitions. -/
syntax "bridge_assumption" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_assumption) => withMainContext do
    let t := (← instantiateMVars (← getMainTarget)).consumeMData
    if t.isAppOfArity ``Eq 3 && (t.getArg! 2).consumeMData.isAppOfArity ``Except.ok 3 then
      evalTactic (← `(tactic| bridge_ok_hyp))
    else
      let s ← saveState
      -- `assumption` can reach the recursion limit, which `first` does not catch
      let ok ← tryCatchRuntimeEx (do evalTactic (← `(tactic| with_reducible assumption)); pure true)
        (fun _ => pure false)
      unless ok do
        s.restore
        let ok ← tryCatchRuntimeEx (do evalTactic (← `(tactic| assumption)); pure true)
          (fun _ => pure false)
        unless ok do
          s.restore
          throwError "bridge_assumption: no hypothesis"

macro_rules | `(tactic| bridge_range0) => `(tactic| first
  | bridge_assumption
  | bridge_mem
  | (simp only [bridge_simp]; done)
  | bridge_decide
  | (simp only [Option.mem_def, Option.some.injEq, forall_eq', forall_eq]; first | bridge_range0 | (split <;> bridge_range0))
  | (bridge_facts0
     try simp only [bridge_ir, uv, decide_eq_true_eq, gt_iff_lt, Int.toNat_natCast]
     bridge_nat
     first
     | assumption
     | omega
     | (simp_all only; done)
     | (simp_all; done)
     | (simp_all; omega))
  | (bridge_facts0
     simp only [bridge_ir, bridge_cast, bd, bridge_simp, List.length_append, List.length_drop,
       List.length_cons, List.length_nil]
     (repeat' apply And.intro)
     all_goals first | assumption | omega | bridge_mem))

/-- Close the goal with `simpa using h` for a negated hypothesis `h` of the context. -/
syntax "bridge_from_not" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_from_not) => withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).consumeMData
      unless t.isAppOfArity ``Not 1 do continue
      let s ← saveState
      try
        let hS ← Term.exprToSyntax d.toExpr
        evalTactic (← `(tactic| simpa using $hS))
        if (← getUnsolvedGoals).isEmpty then return
        s.restore
      catch _ => s.restore
    throwError "bridge_from_not: no hypothesis"

/-- Close `IR_T ⟨…⟩` for a structure value: one goal per field, each from the context. -/
syntax "bridge_ir_struct" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_ir_struct) => withMainContext do
    let t := (← instantiateMVars (← getMainTarget)).consumeMData
    let some c := t.getAppFn.constName? | throwError "bridge_ir_struct: not an IR goal"
    unless c.getString!.startsWith "IR_" && (`Pythia.Bridge).isPrefixOf c do
      throwError "bridge_ir_struct: not an IR goal"
    unless t.appArg!.consumeMData.getAppFn.isConst do
      throwError "bridge_ir_struct: not a structure value"
    evalTactic (← `(tactic| (bridge_facts; unfold $(mkIdent c):ident; (repeat' apply And.intro); all_goals ((try dsimp only); first | bridge_assumption | omega | (intro _ _; first | bridge_mem | bridge_range0) | bridge_range0))))

macro_rules | `(tactic| bridge_range) => `(tactic| first
  | bridge_assumption
  | bridge_ir_struct
  | (apply ir_dedup; bridge_range)
  | bridge_mem
  | (bridge_facts; simp only [bd, bridge_cast, List.length_append, List.length_take, List.length_drop] at *; omega)
  | (simp only [Option.mem_def, Option.some.injEq, forall_eq', forall_eq]; first | bridge_range | (split <;> bridge_range))
  | (apply Nat.or_lt_two_pow <;> bridge_range)
  | (apply Nat.lt_of_le_of_lt Nat.and_le_left; bridge_range)
  | (simp only [bridge_simp]; done)
  | bridge_decide
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
     | (simp_all; omega))
  | (bridge_facts
     simp only [bridge_ir, uv, bridge_simp, bridge_cast, decide_eq_true_eq, gt_iff_lt]
     bridge_nat
     omega)
  | (simp only [decide_eq_true_eq, gt_iff_lt, Int.ofNat_eq_coe, Int.natCast_pos, ne_eq] at *
     bridge_nat
     omega))

open Lean Meta in
/-- The hypothesis `OracleAgrees o` of the goal, if any. -/
def findOracle (g : MVarId) : MetaM (Option Lean.Expr) := do
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.getAppFn.constName?.map (·.getString!) == some "OracleAgrees" then return some d.toExpr
  return none

/-- Close `a = b` where `a` is the readable side after the oracle rewrite: normalize the byte
reads, rewrite with the facts `toVec n x = v` of the context, then the constants. -/
syntax "bridge_eqv" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_eqv) => withMainContext do
    let mut facts : Array Lean.Term := #[]
    let mut mapFacts : Array Lean.Term := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).consumeMData
      unless t.isAppOfArity ``Eq 3 do continue
      let lhs := (t.getArg! 1).consumeMData.headBeta
      let lhsFn := lhs.getAppFn.constName?
      -- `x.val` or `UintC.val x` of a variable
      let isVal := lhs.isApp && lhs.appArg!.isFVar &&
        (lhsFn.map (·.getString! == "val")).getD false
      if lhsFn == some ``toVec || lhsFn == some ``List.map || isVal ||
          (lhs.isFVar && !(← inferType lhs).isProp) then
        facts := facts.push (← Term.exprToSyntax d.toExpr)
      if lhsFn == some ``List.map then
        mapFacts := mapFacts.push (← Term.exprToSyntax d.toExpr)
    let args ← facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
    -- the facts first in their own form, then again after the goal is normalized
    unless facts.isEmpty do
      evalTactic (← `(tactic| try simp only [$args,*]))
      if (← getUnsolvedGoals).isEmpty then return
    evalTactic (← `(tactic| try simp only [bd, bridge_cast, List.map_map, Function.comp_def, List.length_map]))
    if (← getUnsolvedGoals).isEmpty then return
    unless facts.isEmpty do
      evalTactic (← `(tactic| try simp only [$args,*]))
    if (← getUnsolvedGoals).isEmpty then return
    evalTactic (← `(tactic| try simp only [bridge_const, Option.map_some, Option.map_none]))
    if (← getUnsolvedGoals).isEmpty then return
    -- a hand list that the readable side has only through its length: `length (map f x)`
    for f in mapFacts do
      evalTactic (← `(tactic| try simp only [← $f:term, List.length_map]))
    if (← getUnsolvedGoals).isEmpty then return
    evalTactic (← `(tactic| try simp only [bridge_abs, bridge_cast, Bool.and_assoc, Bool.or_assoc, gt_iff_lt, ge_iff_le]))
    if (← getUnsolvedGoals).isEmpty then return
    evalTactic (← `(tactic| first | with_reducible rfl | (simp [bridge_simp, bridge_cast, uv, apply_ite]; done)))

/-- Rewrite a readable oracle call to the hand oracle with `OracleAgrees`, then close with
`bridge_eqv`. -/
syntax "bridge_oracle" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_oracle) => withMainContext do
    let some ho ← findOracle (← getMainGoal) | throwError "bridge_oracle: no OracleAgrees"
    let hoS ← Term.exprToSyntax ho
    evalTactic (← `(tactic| first
      | refine (($hoS).bls_Verify _ _ _ ?_ ?_ ?_).trans ?_
      | refine (($hoS).bls_FastAggregateVerify _ _ _ ?_ ?_ ?_).trans ?_
      | refine (($hoS).bls_KeyValidate _ ?_).trans ?_))
    evalTactic (← `(tactic| all_goals first
      | (guard_target =~ List.length _ = _; bridge_range)
      | (guard_target =~ ∀ _, _; first | bridge_range | (simp only [List.forall_mem_map, bd, bridge_cast]; simp_all))
      | bridge_eqv))

/-- Close `a = b` with a fact `a = c` of the context, then `rfl` (`c` and `b` equal after the
constants reduce). -/
syntax "bridge_rw_fact" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_rw_fact) => withMainContext do
    let t := (← instantiateMVars (← getMainTarget)).consumeMData
    unless t.isAppOfArity ``Eq 3 do throwError "bridge_rw_fact: not an equation"
    let a := t.getArg! 1
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``Eq 3 do continue
      unless ← withReducible (isDefEq (ty.getArg! 1) a) do continue
      let s ← saveState
      try
        let hS ← Term.exprToSyntax d.toExpr
        evalTactic (← `(tactic| (rw [$hS:term]; rfl)))
        if (← getUnsolvedGoals).isEmpty then return
      catch _ => pure ()
      s.restore
    throwError "bridge_rw_fact: no fact closes the goal"

/-- Close a pure goal: the alternatives below, tried in order. -/
syntax "bridge_close" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_close) => do
    let alts : Array (Lean.TSyntax `tactic) := #[
      ← `(tactic| with_reducible rfl),
      ← `(tactic| exact contains_iff_mem_val _ _),
      ← `(tactic| exact not_contains_iff_not_mem_val _ _),
      ← `(tactic| bridge_rw_fact),
      ← `(tactic| (simp only [uv, bridge_cast, Int.ofNat_eq_coe, gt_iff_lt]; bridge_eqv)),
      ← `(tactic| (simp (disch := first | assumption | (intro _ _; bridge_mem)) only [bridge_abs, bd, bridge_cast, List.map_map, Function.comp_def, List.contains_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not, mem_map_bytes, mem_map_toVec, toVec_bne, toVec_beq]; done)),
      ← `(tactic| (bridge_facts; simp (disch := first | assumption | (simp only [List.length_drop]; omega) | (intro _ _; bridge_mem)) only [bridge_abs, bd, bridge_cast, withdrawalAddress_toVec, toVec_bne, toVec_beq]; done)),
      ← `(tactic| (simp only [bridge_const]; done)),
      ← `(tactic| (subst_vars; with_reducible rfl)),
      ← `(tactic| (subst_vars; with_reducible exact Iff.rfl)),
      ← `(tactic| (subst_vars; simp only [bridge_abs, bridge_const, bridge_cast, List.map_append, List.map_cons, List.map_nil]; done)),
      ← `(tactic| (subst_vars; simp (disch := omega) only [bridge_simp, uv, bridge_cast]; done)),
      ← `(tactic| (simp only [uv, bridge_cast, bridge_const] at *; rw [uint8_and_beq _ _ (by omega) (by omega)]; simp_all)),
      ← `(tactic| (simp only [uv, bridge_cast, bridge_const] at *; rw [uint8_or _ _ (by omega) (by omega)]; simp_all)),
      ← `(tactic| (simp (disch := first | assumption | decide | omega) only [bridge_simp, bd, lslice_drop_one, toVec_prefix, BytesC.data_ofBytes, List.singleton_append]; done)),
      ← `(tactic| (bridge_facts; simp (disch := first | assumption | bridge_decide | omega) only [bridge_simp, bd, lslice_drop_one, toVec_prefix, bridge_cast]; done)),
      ← `(tactic| (simp only [bridge_simp, bd, lslice_take] at *; subst_vars; rw [toVec_domain _ _ (by assumption) (by assumption)])),
      ← `(tactic| (bridge_facts; simp only [bridge_const, bridge_cast, bd, lslice_take] at *; rw [← ‹toVec 32 _ = _›]; exact toVec_domain _ _ (by assumption) (by assumption) _)),
      ← `(tactic| (simp (disch := assumption) only [bridge_simp, uv, lslice_take, lslice_take_one, lslice_drop, lslice_drop_one, List.map_drop, bd, toVec_toList, bridge_cast]; done)),
      ← `(tactic| (simp (disch := assumption) only [bd, bridge_cast, bridge_const, toVec_beq_vec, Int.ofNat_eq_coe, List.length_map]; done)),
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
    let closeBudget := bridge.closeHeartbeats.get (← getOptions) * 1000
    for (alt, i) in alts.toList.zipIdx do
      let s ← saveState
      let hb0 ← IO.getNumHeartbeats
      if debug then IO.eprintln s!"bridge_close: alternative {i} starts at {hb0 / 1000}"
      let ok ← tryCatchRuntimeEx
        -- each alternative has its own budget, so one slow failure does not starve the others
        (withCurrHeartbeats <| withTheReader Core.Context
            (fun c => { c with maxHeartbeats := closeBudget }) do
          evalTactic alt
          pure (← getUnsolvedGoals).isEmpty)
        (fun e => do
          if debug then
            -- the message itself can take long to print, so print only its start for small ones
            let _ := e
            IO.eprintln s!"bridge_close: alternative {i} failed"
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
  let close ← `(tactic| all_goals first | with_reducible rfl | bridge_decide | bridge_range | bridge_close)
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
    | some l => return #[← `(tactic| (apply $l:ident; $close)),
        -- the same when the hand operands are equal only after a rewrite (`length (map f xs)`)
        ← `(tactic| (apply sim_hand_eq; (focus (apply $l:ident; $close)); first | (simp only [bridge_abs, List.length_map, uv, bridge_cast]; done) | bridge_eqv))]
    | none => return #[]
  if fn == ``SpecLean.Rd.bytesOf && handPure then
    return #[← `(tactic| (apply sim_bytesOf_pure; all_goals first | with_reducible rfl | bridge_decide | (guard_target =~ toVec _ _ = _; bridge_facts; simp only [bridge_const, bridge_cast, bd, lslice_take_lit] at *; rw [toVec_domain _ _ (by assumption) (by assumption)]; bridge_eqv) | bridge_range | bridge_close))]
  if fn == ``SpecLean.Rd.uCast && handPure then
    return #[← `(tactic| (apply sim_uCast_pure; $close))]
  if fn == ``SpecLean.Rd.uOf && handPure then
    return #[← `(tactic| (apply sim_uOf_pure; $close))]
  if fn == ``List.mapM then
    return #[← `(tactic| (apply sim_mapM_range (g := UintC.val); intro _ _ _; (try dsimp only); bridge_run [$hs,*])),
      ← `(tactic| (apply sim_mapM_range; intro _ _ _; (try dsimp only); bridge_run [$hs,*]))]
  if fn == ``List.filterMapM then
    return #[← `(tactic| (apply sim_filterMapM_zipIdx (hM := fun _ _ => rfl); intro _ _ _ _ _; (try dsimp only); bridge_run [$hs,*]))]
  if fn == ``SpecLean.Rd.sumU then return #[← `(tactic| (apply sim_sumU; $close))]
  if fn == ``SpecLean.Rd.pyMin then
    return #[← `(tactic| (apply sim_pyMin2; intro _ _; rfl)),
      ← `(tactic| (refine sim_hand_eq (sim_pyMin2 (fun _ _ => rfl) _ _) ?_; first | (simp only [bridge_const, bridge_cast]; done) | bridge_eqv))]
  if fn == ``SpecLean.Rd.pyMax then
    return #[← `(tactic| (apply sim_pyMax2; intro _ _; rfl)),
      ← `(tactic| (refine sim_hand_eq (sim_pyMax2 (fun _ _ => rfl) _ _) ?_; first | (simp only [bridge_const, bridge_cast]; done) | bridge_eqv))]
  if fn == ``SpecLean.Rd.lget && a.getAppNumArgs == 3 then
    let mut out := #[← `(tactic| apply sim_lget), ← `(tactic| apply sim_lget_last)]
    -- the same with the index rewritten: the item map is `abs_T` for the item type `T`
    if let some tn := (a.getArg! 0).consumeMData.getAppFn.constName? then
      let env ← getEnv
      let cands := [`Pythia.Bridge.Mainnet ++ Lean.Name.mkSimple s!"abs_{tn.getString!}",
        `Pythia.Bridge ++ Lean.Name.mkSimple s!"abs_{tn.getString!}"]
      for c in cands do
        if env.contains c then
          out := out.push (← `(tactic| (refine sim_hand_eq (sim_lget $(mkIdent c) _ _) ?_; congr 1; simp (disch := first | assumption | (intro _ _; bridge_mem)) only [uv, bridge_cast, bridge_abs, List.map_map, Function.comp_def, idxOf_map_bytes, idxOf_map_toVec])))
      -- a list of uints: the item map is `UintC.val`, and the index is a value fact
      out := out.push (← `(tactic| (refine sim_hand_eq (sim_lget UintC.val _ _) ?_; congr 1 <;> bridge_eqv)))
    return out
  if fn == ``SpecLean.Rd.lset then return #[← `(tactic| (apply sim_lset; bridge_close))]
  if a.isAppOfArity ``Bind.bind 6 then
    let k := (a.getArg! 5).consumeMData
    let kb := if k.isLambda then k.bindingBody!.consumeMData else k
    if kb.getAppFn.constName? == some ``SpecLean.Rd.uCast then
      return #[← `(tactic| (apply sim_bind_cast; all_goals first | with_reducible rfl | bridge_decide | bridge_leaf [$hs,*])),
        ← `(tactic| (apply sim_hand_eq; (focus (apply sim_bind_cast; all_goals first | with_reducible rfl | bridge_decide | bridge_leaf [$hs,*])); bridge_eqv))]
    return #[]
  if isGenFn fn then
    let mut out := #[]
    let own ← specHypsFor fn
    for h in hs ++ own do
      out := out.push (← `(tactic| (apply simI_sim; apply $h:ident; all_goals bridge_range)))
    -- the hand spec has the callee's result as a parameter, with a hypothesis `call = .ok b`
    for h in hs ++ own do
      out := out.push (← `(tactic| (apply sim_of_ok; (focus (apply simI_sim; apply $h:ident; all_goals bridge_range)); bridge_ok_hyp)))
    -- the same, when the hand arguments are equal to the callee's only after a rewrite
    for h in hs ++ own do
      out := out.push (← `(tactic| (apply sim_hand_eq; (focus (apply simI_sim; apply $h:ident; all_goals bridge_range)); first | bridge_safe (with_reducible rfl) | bridge_safe (simp only [Option.map_some, Option.map_none, uv, bridge_cast, decide_eq_true_eq, Int.ofNat_lt, apply_ite, bridge_abs, List.length_map]; done) | bridge_safe (congr 1 <;> bridge_eqv))))
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
      let ok ← tryCatchRuntimeEx
        (do
          evalTactic tac
          if (← getUnsolvedGoals).isEmpty then return true
          if bridge.debug.get (← getOptions) then
            for g' in ← getUnsolvedGoals do
              IO.eprintln s!"bridge_leaf: goal left: {((← ppGoal g').pretty).takeRight 600}"
          return false)
        (fun e => do
          if bridge.debug.get (← getOptions) then
            IO.eprintln s!"bridge_leaf: alternative failed: {((← e.toMessageData.toString).takeRight 1200)}"
          return false)
      if ok then return
      s.restore
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

open Lean Meta in
/-- The structure `s` of an update `{ s with … }`: a constructor whose fields are projections of
`s`, except the updated ones. -/
partial def updateBase (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let e := e.consumeMData
  let some c := e.getAppFn.constName? | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  let fields := e.getAppArgs.extract ci.numParams e.getAppNumArgs
  for f in fields do
    let f := f.consumeMData
    let base? : Option Lean.Expr := match f with
      | .proj _ _ s => some s
      | _ => none
    let base? ← match base? with
      | some b => pure (some b)
      | none =>
        match f.getAppFn.constName? with
        | some p =>
          if (← getEnv).isProjectionFn p && f.getAppNumArgs ≥ 1 then pure (some f.appArg!)
          else pure none
        | none => pure none
    if let some b := base? then
      -- an update of an update: go to the first structure
      return some ((← updateBase b).getD b)
  return none

open Lean Meta in
/-- The call `a` with each argument `{ s with … }` replaced by `s`, if there is one. -/
def frameCall (a : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let args := a.getAppArgs
  let mut out := #[]
  let mut changed := false
  for arg in args do
    match ← updateBase arg with
    | some b => out := out.push b; changed := true
    | none => out := out.push arg
  return if changed then some (mkAppN a.getAppFn out) else none

/-- `l.Nodup` for a list `l` that a `filterM` or a `filterMapM` keeps from a list with no
duplicates, back to a fact `List.map f l = H` with `H` a hand list of known indices. -/
syntax "bridge_nodup" : tactic
syntax "bridge_nodup_map" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_nodup_map) => withMainContext do
    let t := (← instantiateMVars (← getMainTarget)).consumeMData
    unless t.isAppOfArity ``List.Nodup 2 do throwError "bridge_nodup_map: not Nodup"
    let l := (t.getArg! 1).consumeMData
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      unless ty.isAppOfArity ``Eq 3 do continue
      let lhs := (ty.getArg! 1).consumeMData.headBeta
      unless lhs.isAppOfArity ``List.map 4 && lhs.getArg! 3 == l do continue
      let s ← saveState
      try
        let fS ← Term.exprToSyntax (lhs.getArg! 2)
        let hS ← Term.exprToSyntax d.toExpr
        evalTactic (← `(tactic| (refine nodup_of_map $fS ?_; rw [$hS:term]; first | exact nodup_get_active _ _ | exact nodup_filter_zipIdx_snd _ _ | bridge_nodup)))
        if (← getUnsolvedGoals).isEmpty then return
      catch _ => pure ()
      s.restore
    throwError "bridge_nodup_map: no fact"

/-- The range facts of a list that `dedup`, a `filterM` or a `filterMapM` keeps from a list. -/
syntax "bridge_sub_ir" : tactic
/-- Close the goal with a conjunct of a hypothesis (a callee post condition). -/
syntax "bridge_conj_assumption" : tactic

open Lean Meta in
partial def conjParts (pf ty : Lean.Expr) (depth : Nat) : MetaM (List Lean.Expr) := do
  let ty ← whnfR ty
  if depth > 0 && ty.isAppOfArity ``And 2 then
    let l ← conjParts (← mkAppM ``And.left #[pf]) (ty.getArg! 0) (depth - 1)
    let r ← conjParts (← mkAppM ``And.right #[pf]) (ty.getArg! 1) (depth - 1)
    return l ++ r
  return [pf]

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_conj_assumption) => withMainContext do
    let g ← getMainGoal
    let target ← instantiateMVars (← g.getType)
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless (← whnfR ty).isAppOfArity ``And 2 do continue
      for pf in ← conjParts d.toExpr ty 3 do
        let s ← saveState
        if ← isDefEq (← inferType pf) target then
          g.assign pf
          replaceMainGoal []
          return
        s.restore
    throwError "bridge_conj_assumption: no conjunct fits"

/-- Close the invariant of a loop step (`sim_loop`). The default is the invariant of a loop that
changes one list field: `∃ X, state = { st0 with F := X } ∧ r = X.map conv ∧ ∀ y ∈ X, P y`. -/
syntax "bridge_inv" : tactic
macro_rules
  | `(tactic| bridge_inv) => `(tactic| first
    | (refine ⟨_, rfl, rfl, ?_⟩; bridge_range)
    | (refine ⟨rfl, ?_⟩; first | assumption | bridge_sub_ir)
    | (refine ⟨rfl, rfl, ?_, ?_⟩ <;> first | assumption | bridge_sub_ir)
    | (bridge_facts; refine ⟨_, ?_, rfl, ?_⟩ <;> first | bridge_conj_assumption | bridge_range))

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
  -- a branch that the facts rule out: a hypothesis `false = true`
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isConstOf ``Bool.false && (ty.getArg! 2).isConstOf ``Bool.true then
      let hS ← g.withContext (Term.exprToSyntax d.toExpr)
      if let some gs ← tryAt (evalTactic (← `(tactic| exact absurd $hS Bool.false_ne_true))) g then return gs
  -- the next step of a loop (`sim_loop`): the claim `ih` for step `i + 1`
  if let some fnName := r.getAppFn.constName? then
    if fnName.isStr && fnName.getString!.startsWith "loop" then
      if ((← g.getDecl).lctx.findFromUserName? `ih).isSome then
        let ihId := mkIdent `ih
        if let some gs ← tryAt (evalTactic (← `(tactic| (apply $ihId:ident; bridge_inv)))) g then
          return gs
  -- a bind whose first step is a bind or an `if` (a `for` body, then the rest of the loop)
  if h.isAppOfArity ``Bind.bind 6 then
    let b := (h.getArg! 4).consumeMData.headBeta
    let lem? := if b.isAppOfArity ``Bind.bind 6 then some (mkIdent ``sim_assoc_r)
      else if b.isAppOfArity ``ite 5 then some (mkIdent ``sim_ite_bind_r) else none
    if let some lem := lem? then
      if let some gs ← tryAt (evalTactic (← `(tactic| (apply $lem; try dsimp only)))) g then
        let mut out := []
        for g' in gs do out := out ++ (← bridgeGoal hs g')
        return out
  if r.isAppOfArity ``Bind.bind 6 then
    let b := (r.getArg! 4).consumeMData.headBeta
    let lem? := if b.isAppOfArity ``Bind.bind 6 then some (mkIdent ``sim_assoc_l)
      else if b.isAppOfArity ``ite 5 then some (mkIdent ``sim_ite_bind_l) else none
    if let some lem := lem? then
      if let some gs ← tryAt (evalTactic (← `(tactic| (apply $lem; try dsimp only)))) g then
        let mut out := []
        for g' in gs do out := out ++ (← bridgeGoal hs g')
        return out
  -- a callee on `{ s with … }` that does not read the updated fields: call it on `s`
  if r.isAppOfArity ``Bind.bind 6 then
    let a := (r.getArg! 4).consumeMData
    if isGenFn (a.getAppFn.constName?.getD .anonymous) then
      if let some a' ← g.withContext (frameCall a) then
        let aS ← g.withContext (Term.exprToSyntax a')
        if let some gs ← tryAt (evalTactic (← `(tactic| refine sim_bind_eq_l (A' := $aS) rfl ?_))) g then
          let mut out := []
          for g' in gs do out := out ++ (← bridgeGoal hs g')
          return out
  -- `dedup x` of a list with no duplicates: drop it, with the fact `List.map f x = H`
  if let some dd := r.find? (fun e => e.isAppOfArity ``SpecLean.Rd.dedup 3 && (e.getArg! 2).isFVar) then
    let x := dd.getArg! 2
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let t := (← instantiateMVars d.type).consumeMData
      unless t.isAppOfArity ``Eq 3 do continue
      let l := (t.getArg! 1).consumeMData.headBeta
      unless l.isAppOfArity ``List.map 4 && l.getArg! 3 == x do continue
      let xS ← g.withContext (Term.exprToSyntax x)
      let fS ← g.withContext (Term.exprToSyntax (l.getArg! 2))
      let hS ← g.withContext (Term.exprToSyntax d.toExpr)
      let tacD : TacticM Unit := evalTactic (← `(tactic|
        rw [dedup_of_nodup $xS (nodup_of_map $fS (by rw [$hS:term]; first | exact nodup_get_active _ _ | exact nodup_filter_zipIdx_snd _ _))]))
      if let some gs ← tryAt tacD g then
        let mut out := []
        for g' in gs do out := out ++ (← bridgeGoal hs g')
        return out
    let xS ← g.withContext (Term.exprToSyntax x)
    let tacN : TacticM Unit := evalTactic (← `(tactic| rw [dedup_of_nodup $xS (by bridge_nodup)]))
    if let some gs ← tryAt tacN g then
      let mut out := []
      for g' in gs do out := out ++ (← bridgeGoal hs g')
      return out
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
  -- a readable `pure (if c then a else b)` against a hand `if`
  if isPure r && isIte (r.getArg! 3).consumeMData.headBeta && isIte h then
    if let some gs ← tryAt (evalTactic (← `(tactic| apply sim_pure_ite_l))) g then
      let mut out := []
      for g' in gs do out := out ++ (← bridgeGoal hs g')
      return out
  -- a hand `if` inside the arguments of the first hand step: decide it with the facts
  if isBind h then
    let b := (h.getArg! 4).consumeMData
    if !(isIte b) then
      if let some it := b.getAppArgs.find? (fun e => e.consumeMData.isAppOfArity ``ite 5) then
        let c := (it.consumeMData.getArg! 1)
        let cS ← g.withContext (Term.exprToSyntax c)
        let tacI : TacticM Unit := evalTactic (← `(tactic| first
          | rw [if_pos (show $cS from by first | bridge_close | (simp only [uv_beq_val] at *; assumption))]
          | rw [if_neg (show ¬ $cS from by first | bridge_close | (simp only [uv_beq_val] at *; assumption))]))
        if let some gs ← continueWith (← tryAt tacI g) then return gs
  -- a readable `filterM`: the same as a `filterMapM`
  if isBind r && (r.getArg! 4).consumeMData.isAppOfArity ``List.filterM 5 then
    if let some gs ← tryAt (evalTactic (← `(tactic| rw [filterM_eq_filterMapM]))) g then
      let mut out := []
      for g' in gs do out := out ++ (← bridgeGoal hs g')
      return out
  -- a readable `filterMapM` against a hand `for` loop that appends (`sim_filterMapM_forIn`)
  if isBind r && (r.getArg! 4).consumeMData.isAppOfArity ``List.filterMapM 6 then
    let hf := if isBind h then (h.getArg! 4).consumeMData else h
    if hf.getAppFn.constName? == some ``ForIn.forIn && hf.getAppNumArgs ≥ 3 then
      let hl := (hf.getArg! (hf.getAppNumArgs - 3)).consumeMData
      let mut fS? : Option Lean.Term := none
      let mut rw? : Option Lean.Term := none
      if hl.isAppOfArity ``List.map 4 then
        fS? := some (← g.withContext (Term.exprToSyntax (hl.getArg! 2)))
      else
        for d in (← g.getDecl).lctx do
          if d.isImplementationDetail then continue
          let ty := (← instantiateMVars d.type).consumeMData
          unless ty.isAppOfArity ``Eq 3 do continue
          let lhs := (ty.getArg! 1).consumeMData.headBeta
          unless lhs.isAppOfArity ``List.map 4 do continue
          unless ← g.withContext (withReducible (isDefEq (ty.getArg! 2) hl)) do continue
          fS? := some (← g.withContext (Term.exprToSyntax (lhs.getArg! 2)))
          rw? := some (← g.withContext (Term.exprToSyntax d.toExpr))
          break
      if let some fS := fS? then
        let tacF : TacticM Unit := do
          if let some hS := rw? then evalTactic (← `(tactic| rw [← $hS:term]))
          unless isBind h do evalTactic (← `(tactic| apply sim_of_bind_pure_r))
          evalTactic (← `(tactic| refine sim_bind
            (sim_congr (fun _ => List.nil_append _) (sim_filterMapM_forIn $fS $fS _ _ _ [] ?_)) ?_))
        if let some gs ← continueWith (← tryAt tacF g) then return gs
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
    if let some gs ← tryAt (evalTactic (← `(tactic| exact sim_pure _ _ _ (by bridge_oracle)))) g then
      return gs
    return [g]
  -- `sha256` then `bytesOf`, against the hand `hash`
  if isPure h && r.isAppOfArity ``SpecLean.Rd.bytesOf 3 &&
      (r.getArg! 2).consumeMData.getAppFn.constName? == some ``SpecLean.Rd.Spec.sha256 then
    if let some ho ← findOracle g then
      let hoS ← g.withContext (Term.exprToSyntax ho)
      let tacS : TacticM Unit := do
        evalTactic (← `(tactic| apply sim_congr))
        onTag `hs (← `(tactic| (apply sim_sha256_bytes (by decide) _ ($hoS).hash; bridge_facts; simp (disch := assumption) only [toVec_toList, bd, bridge_cast]; all_goals rfl)))
        onTag `hfg (← `(tactic| (intro _; rfl)))
      if let some gs ← tryAt tacS g then return gs
  -- a readable call with an SSZ object `⟨enc_T x⟩`: add `htr enc_T x = .ok r` and the facts of `r`
  if isBind r then
    let a := (r.getArg! 4).consumeMData
    if isGenFn (a.getAppFn.constName?.getD .anonymous) then
      if let some ho ← findOracle g then
        for arg in a.getAppArgs do
          let arg := arg.consumeMData
          unless arg.isAppOfArity ``SpecLean.Rd.SszObj.mk 1 do continue
          let e := arg.appArg!.consumeMData
          let some en := e.getAppFn.constName? | continue
          unless en.getString!.startsWith "enc_" && e.getAppNumArgs == 1 do continue
          let x := e.appArg!
          let mut known := false
          for d in (← g.getDecl).lctx do
            let t := (← instantiateMVars d.type).consumeMData
            if t.isAppOfArity ``Eq 3 then
              let l := (t.getArg! 1).consumeMData
              if l.getAppFn.constName? == some ``SpecLean.Rd.htr && l.appArg! == x then known := true
          if known then continue
          let fld := mkIdent (Lean.Name.mkSimple s!"htr_{en.getString!.drop 4}")
          let hoS ← g.withContext (Term.exprToSyntax ho)
          let xS ← g.withContext (Term.exprToSyntax x)
          let tacO : TacticM Unit := evalTactic (← `(tactic|
            obtain ⟨_, _, _, _⟩ := ($hoS).$fld:ident $xS (by bridge_range)))
          if let some gs ← tryAt tacO g then
            let mut out := []
            for g' in gs do out := out ++ (← bridgeGoal hs g')
            return out
  -- `hash_tree_root` then `bytesOf`, against the hand oracle: use the oracle agreement
  if isBind r && isPure h then
    let a := (r.getArg! 4).consumeMData
    if a.getAppFn.constName? == some ``SpecLean.Rd.htr then
      let enc := (a.getArg! (a.getAppNumArgs - 2)).consumeMData.getAppFn.constName?.getD .anonymous
      let t := enc.getString!.drop 4
      if let some ho ← findOracle g then
        let hoS ← g.withContext (Term.exprToSyntax ho)
        let fld := mkIdent (Lean.Name.mkSimple s!"htr_{t}")
        let tacH : TacticM Unit := do
          evalTactic (← `(tactic| apply sim_congr))
          onTag `hs (← `(tactic| (apply sim_htr_bytes (by decide); exact ($hoS).$fld:ident _ (by bridge_range))))
          onTag `hfg (← `(tactic| (intro _; rfl)))
        if let some gs ← tryAt tacH g then return gs
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
    let tacB : TacticM Unit := do
      evalTactic (← `(tactic| apply sim_assert_bool))
      onTag `hc (← `(tactic| first | exact contains_pair_val _ _ _ | bridge_close))
      onTag `hK (← `(tactic| intro _))
    if let some gs ← continueWith (← tryAt tacB g) then return gs
  if isBind r then
    let a := (r.getArg! 4).consumeMData
    -- a readable step that ran before with the same arguments (a call, a read of a list): use
    -- its result
    let mut fact? : Option Lean.Expr := none
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if ty.isAppOfArity ``Eq 3 && (ty.getArg! 2).consumeMData.isAppOfArity ``Except.ok 3 then
        if ← g.withContext (withReducible (isDefEq (ty.getArg! 1) a)) then
          fact? := some d.toExpr
          break
    if let some fact := fact? then
      let fS ← g.withContext (Term.exprToSyntax fact)
      let tacK : TacticM Unit := evalTactic (← `(tactic| refine sim_bind_l _ $fS ?_))
      if let some gs ← continueWith (← tryAt tacK g) then return gs
    -- `lindex xs x` with `x ∈ xs` from a negated `contains` check before
    if a.isAppOfArity ``SpecLean.Rd.lindex 4 then
      let xS ← g.withContext (Term.exprToSyntax (a.getArg! 3))
      let xsS ← g.withContext (Term.exprToSyntax (a.getArg! 2))
      let tacI : TacticM Unit := evalTactic (← `(tactic| (have hmem : $xS ∈ $xsS := (by bridge_from_not); have := List.idxOf_lt_length_of_mem hmem; refine sim_bind_l _ (lindex_ok _ _ hmem) ?_)))
      if let some gs ← continueWith (← g.withContext (tryAt tacI g)) then return gs
    -- `range(a, b)` of two uints: a list of known value
    if a.getAppFn.constName? == some ``SpecLean.Rd.pyRange then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| refine sim_bind_l _ (pyRange_nat _ _) ?_))) g) then
        return gs
    -- `uint_to_bytes`: a plain value
    if (a.getAppFn.constName?.map (·.getString!)) == some "uint_to_bytes" then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| refine sim_bind_l _ rfl ?_))) g) then
        return gs
    -- a readable step that is `pure _`
    if isPure a then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| refine sim_bind_l _ rfl ?_))) g) then
        return gs
    if isBind h && (a.isAppOfArity ``List.mapM 5 || a.isAppOfArity ``List.mapM 6) then
      -- first with the item map `UintC.val`: a later `sumU` needs it, and unification cannot
      -- find it from the item goals
      let tacMv : TacticM Unit := do
        evalTactic (← `(tactic| apply sim_bind))
        onTag `hA (← `(tactic| apply sim_mapM (g := UintC.val)))
        onTag `hK (← `(tactic| intro x hx))
      let sM ← saveState
      if let some gs ← continueWith (← tryAt tacMv g) then
        if gs.isEmpty then return gs
        sM.restore
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
      unless isGenFn aFn || aFn == ``SpecLean.Rd.uOp || aFn == ``SpecLean.Rd.pyMax || aFn == ``SpecLean.Rd.pyMin do
        throwError "bridge: not a call"
      let k := (r.getArg! 5).consumeMData
      let kb := if k.isLambda then k.bindingBody!.consumeMData else k
      if kb.getAppFn.constName? == some ``SpecLean.Rd.uCast && aFn != ``SpecLean.Rd.pyMax && aFn != ``SpecLean.Rd.pyMin then
        throwError "bridge: a cast follows"
      evalTactic (← `(tactic| apply sim_bind_val))
      onTag `hA (← `(tactic| bridge_callee [$hs,*]))
      onTag `hK (← `(tactic| intro x hx hfx))
    if let some gs ← continueWith (← tryAt tac2 g) then return gs
    -- a readable `mod` or `//` by a nonzero value: it cannot fail, so it may come before or after
    -- the hand step
    let hFn := h.getAppFn.constName?.getD .anonymous
    if aFn == ``SpecLean.Rd.uOp &&
        !(hFn == ``EpochProofs.Spec.uint64Div || hFn == ``EpochProofs.Spec.uint64Mod) then
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
    -- a hand call that reduces to `pure`, when the readable side has no step to pair with it
    if !isBind r && (bFn.getPrefix == `EpochProofs.Spec) then
      if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| refine sim_bind_r _ rfl ?_))) g) then
        return gs
  if isIte r && isIte h then
    let tac : TacticM Unit := do
      evalTactic (← `(tactic| apply sim_ite))
      onTag `hc (← `(tactic| bridge_close))
      onTag `h1 (← `(tactic| intro _ _))
      onTag `h2 (← `(tactic| intro _ _))
    if let some gs ← continueWith (← tryAt tac g) then return gs
  if isIte r && !isIte h then
    -- decided by a fact of the context (the same test ran before)
    let cS ← g.withContext (Term.exprToSyntax (r.getArg! 1))
    let tacD : TacticM Unit := evalTactic (← `(tactic| first
      | rw [if_pos (show $cS from by assumption)]
      | rw [if_neg (show ¬ $cS from by assumption)]))
    if let some gs ← continueWith (← tryAt tacD g) then return gs
    let tac : TacticM Unit := do
      evalTactic (← `(tactic| apply sim_ite_l))
      onTag `h1 (← `(tactic| intro _))
      onTag `h2 (← `(tactic| intro _))
    if let some gs ← continueWith (← tryAt tac g) then return gs
  -- a readable bind against one hand call (a function that returns its last call): add `>>= pure`
  if isBind r && !isBind h && !isPure h && !isIte h then
    if let some gs ← continueWith (← tryAt (evalTactic (← `(tactic| apply sim_of_bind_pure_r))) g) then
      return gs
  -- a leaf on its own, with the abs map of the goal
  let leafAs : TacticM Unit := do
    evalTactic (← `(tactic| apply sim_congr))
    onTag `hs (← `(tactic| bridge_leaf [$hs,*]))
    onTag `hfg (← `(tactic| (intro _; first | with_reducible rfl | rfl | simp [bridge_simp])))
  if let some gs ← tryAt leafAs g then return gs
  return [g]


open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_run [$hs,*]) => do
    let g ← getMainGoal
    let rest ← bridgeGoal hs.getElems g
    setGoals rest
    unless rest.isEmpty do
      throwError "bridge_run: {rest.length} goals left\n{Lean.MessageData.joinSep (rest.map Lean.MessageData.ofGoal) "\n"}"

/-- `bridge_run` that keeps the goals it cannot prove (a loop, for `bridge_loop`). -/
syntax "bridge_walk" "[" ident,* "]" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_walk [$hs,*]) => do
    let g ← getMainGoal
    let rest ← bridgeGoal hs.getElems g
    setGoals rest

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
  -- the next step of a loop (`post_loop`): the claim `ih` for step `i + 1`
  if let some fnName := r.getAppFn.constName? then
    if fnName.isStr && fnName.getString!.startsWith "loop" then
      if ((← g.getDecl).lctx.findFromUserName? `ih).isSome then
        let ihId := mkIdent `ih
        if let some gs ← tryAt (evalTactic (← `(tactic| (apply $ihId:ident; first | assumption | bridge_sub_ir)))) g then
          return gs
  -- a loop with its own post condition: keep the goal for `bridge_loop_post`
  if r.isAppOfArity ``Bind.bind 6 then
    if let some fnName := (r.getArg! 4).consumeMData.getAppFn.constName? then
      if fnName.isStr && fnName.getString!.startsWith "loop" then
        return [g]
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
        (apply post_pure; (try dsimp only); first | (refine ⟨rfl, ?_⟩; bridge_sub_ir) | bridge_sub_ir)))) g then return gs
  if isGenFn (r.getAppFn.constName?.getD .anonymous) then
    setGoals [g]
    for h in ← specHypsFor (r.getAppFn.constName?.getD .anonymous) do
      let s ← saveState
      if let some gs ← tryAt (evalTactic (← `(tactic| (apply post_simI; apply $h:ident; all_goals bridge_range)))) g then
        if gs.isEmpty then return gs
        s.restore
  if r.getAppFn.constName? == some ``SpecLean.Rd.bytesOf then
    if let some gs ← tryAt (evalTactic (← `(tactic| exact post_bytesOf _))) g then return gs
  if r.getAppFn.constName? == some ``List.mapM then
    if let some gs ← step (← `(tactic| (refine post_mapM_ir _ _ _ (by (try simp only [List.length_map, List.length_range']); bridge_range) ?_; intro _ _; (try dsimp only)))) then return gs
  if r.getAppFn.constName? == some ``List.filterMapM then
    if let some gs ← step (← `(tactic| (refine post_filterMapM_ir _ _ _ (by (try simp only [List.length_map, List.length_zipIdx]); bridge_range) ?_; intro x _; cases x; (try dsimp only)))) then return gs
  if r.getAppFn.constName? == some ``MonadExcept.throw then
    if let some gs ← tryAt (evalTactic (← `(tactic| exact post_throw _))) g then return gs
  if let some gs ← tryAt (evalTactic (← `(tactic|
      (intro _ _; (try dsimp only); bridge_range)))) g then
    if bridge.debug.get (← getOptions) then
      logInfo m!"bridge post leaf: {gs.length} goals left"
    return gs
  return [g]

/-- `bridge_post` that keeps the goals it cannot prove (a loop, for `bridge_loop_post`). -/
syntax "bridge_post_walk" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_post_walk) => do
    let rest ← bridgePost (← getMainGoal)
    setGoals rest

/-- Prove a goal `Post P r` by walking `r`. Fails if a goal is left. -/
syntax "bridge_post" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_post) => do
    let rest ← bridgePost (← getMainGoal)
    setGoals rest
    unless rest.isEmpty do
      throwError "bridge_post: {rest.length} goals left\n{Lean.MessageData.joinSep (rest.map Lean.MessageData.ofGoal) "\n"}"

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

/-- `Post (fun o => ∀ d ∈ o, d = x) (F x)` for a step that returns `some x` or `none`. -/
syntax "bridge_post_self" : tactic
open Lean Meta Elab Tactic in
partial def postSelf (g : MVarId) : TacticM Unit := do
  let gs ← evalTacticAt (← `(tactic| try dsimp only)) g
  for g in gs do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isAppOfArity ``Post 3 do throwError "bridge_post_self: not a Post goal"
    let r := (t.getArg! 2).headBeta.consumeMData
    if r.isAppOfArity ``Pure.pure 4 then
      let _ ← evalTacticAt (← `(tactic| (apply post_pure; intro _ hd; first | (cases hd; rfl) | cases hd | (split at hd <;> first | (cases hd; rfl) | cases hd)))) g
    else if r.isAppOfArity ``ite 5 then
      for g' in ← evalTacticAt (← `(tactic| (apply post_ite <;> intro _))) g do postSelf g'
    else if r.isAppOfArity ``Bind.bind 6 then
      for g' in ← evalTacticAt (← `(tactic| (apply post_bind; intro _ _))) g do postSelf g'
    else
      let _ ← evalTacticAt (← `(tactic| exact post_throw _)) g

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bridge_post_self) => do
    let g ← getMainGoal
    postSelf g
    setGoals []

macro_rules
  | `(tactic| bridge_nodup) => `(tactic| first
    | exact nodup_get_active _ _
    | bridge_nodup_map
    | (refine nodup_of_filterM (by assumption) ?_; bridge_nodup)
    | (refine nodup_of_filterMapM_self (by assumption) (fun _ _ => by bridge_post_self) ?_; bridge_nodup))

macro_rules
  | `(tactic| bridge_sub_ir) => `(tactic| first
    | (refine ir_dedup ?_; bridge_sub_ir)
    | (refine lset_forall (by assumption) ?_ ?_ <;> first | assumption | bridge_range)
    | (refine ir_lset (by assumption) ?_ ?_ <;> first | assumption | bridge_sub_ir)
    | exact uOp_range (by assumption)
    | (refine ir_of_filterM (by assumption) ?_; bridge_sub_ir)
    | (refine ir_of_filterMapM_self (by assumption) (fun _ _ => by bridge_post_self) ?_; bridge_sub_ir)
    | bridge_range)

end Pythia.Bridge
