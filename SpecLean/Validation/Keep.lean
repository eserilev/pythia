import SpecLean.Validation.Alloc
import SpecLean.Validation.Tactic

/-!
# Decodes that survive calls and allocations

A caller decodes an argument in its own heap. After a callee that writes nothing (`Frame` with
the empty footprint) and after a new object, the objects that the argument reaches are the same,
so a decoder that reads only what it reaches (`LocalDec`) gives the same value. `rd_keep` proves
the decode in the new heap from the decode in the old one.
-/

namespace SpecLean.Validation.Keep

open SpecLean SpecLean.Rd SpecLean.Encode SpecLean.Validation.Local SpecLean.Validation.Where

theorem follow_same {h h' : Heap} : ∀ (q : List Nat) (v : Value), Same h h' v →
    follow h' v q = follow h v q
  | [], _, _ => rfl
  | i :: p, v, hs => by
    cases v with
    | ref a =>
      simp only [follow, hs.self]
      split
      · rename_i fs ho
        cases hx : fs[i]? with
        | none => rfl
        | some x =>
          simp only [Option.bind_some]
          exact follow_same p x (hs.field ho hx)
      · rename_i k e l xs ho
        cases hx : xs[i]? with
        | none => rfl
        | some x =>
          simp only [Option.bind_some]
          exact follow_same p x (hs.item ho hx)
      · rfl
    | _ => rfl

theorem same_refl (h : Heap) (v : Value) : Same h h v := fun _ _ _ => rfl

/-- A callee that writes nothing keeps every object of the old heap. -/
theorem same_frame {h0 h h' : Heap} {v : Value} {vs : List Value} (hs : Same h0 h v)
    (hr : ∀ q c, follow h0 v q = some (.ref c) → h0.objs c ≠ none) (hf : Frame h h' vs []) :
    Same h0 h' v := fun q c e => by
  have hc : h.objs c = h0.objs c := hs q c e
  rw [hf c (by rw [hc]; exact hr q c e) (fun ⟨_, _, _, hp, _⟩ => by simp at hp), hc]

/-- A new object is at a free address: the objects that `v` reaches stay. -/
theorem same_alloc {h0 h : Heap} {v : Value} {o : HeapObj} (hs : Same h0 h v)
    (hr : ∀ q c, follow h0 v q = some (.ref c) → h0.objs c ≠ none) (hwf : HeapWF h) :
    Same h0 (h.alloc o).2 v := fun q c e => by
  have hc : h.objs c = h0.objs c := hs q c e
  have hne : c ≠ h.next := fun ec => hr q c e (by rw [← hc]; exact hwf c (by omega))
  rw [objs_alloc_ne hne, hc]

/-- The objects that argument `k` reaches are in the heap. -/
theorem reach_of_args {h : Heap} {vs : List Value} {k : Nat} {v : Value} (haw : ArgsWF h vs)
    (hk : vs[k]? = some v) : ∀ q c, follow h v q = some (.ref c) → h.objs c ≠ none :=
  fun q c e => haw k q c (by simp [at?, hk, e])

theorem reach_of_mem {h : Heap} {vs : List Value} {v : Value} (haw : ArgsWF h vs)
    (hm : v ∈ vs) : ∀ q c, follow h v q = some (.ref c) → h.objs c ≠ none := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hm
  exact reach_of_args haw (k := k) (by simp [hk, e])

theorem heapWF_alloc {h : Heap} {o : HeapObj} (hwf : HeapWF h) : HeapWF (h.alloc o).2 := by
  intro a ha
  have : a ≠ h.next := by simp [alloc_next] at ha; omega
  rw [objs_alloc_ne this]
  exact hwf a (by simp [alloc_next] at ha; omega)

/-- The objects that a value reaches are in the heap. -/
def Reach (h : Heap) (v : Value) : Prop := ∀ q c, follow h v q = some (.ref c) → h.objs c ≠ none

theorem argsWF_nil (h : Heap) : ArgsWF h [] := fun k q a e => by simp [at?] at e

theorem argsWF_cons {h : Heap} {v : Value} {vs : List Value} (hv : Reach h v)
    (hvs : ArgsWF h vs) : ArgsWF h (v :: vs) := fun k q a e => by
  cases k with
  | zero => exact hv q a (by simpa [at?] using e)
  | succ k => exact hvs k q a (by simpa [at?] using e)

theorem reach_same {h0 h : Heap} {v : Value} (hs : Same h0 h v)
    (hr : ∀ q c, follow h0 v q = some (.ref c) → h0.objs c ≠ none) : Reach h v :=
  fun q c e => by
    rw [follow_same q v hs] at e
    rw [hs q c e]
    exact hr q c e

/-- A value with no reference reaches nothing. -/
theorem reach_scalar {h : Heap} {v : Value} (hv : ∀ a, v ≠ .ref a) : Reach h v := by
  intro q c e
  cases q with
  | nil => simp [follow] at e; exact absurd e (hv c)
  | cons i p => cases v <;> simp [follow] at e; exact absurd rfl (hv _)

/-- A new set: `follow` does not go into a set, so the set is all that it reaches. -/
theorem reach_alloc_set {h : Heap} {xs : List Value} :
    Reach (h.alloc (.set xs)).2 (.ref h.next) := by
  intro q c e
  cases q with
  | nil =>
    simp [follow] at e
    subst e
    simp [objs_alloc_self]
  | cons i p => simp [follow, objs_alloc_self] at e

/-- Every object of `h` is the same in `h'`: a run of callees that write nothing and new
objects. -/
def FrameNil (h h' : Heap) : Prop := ∀ a, h.objs a ≠ none → h'.objs a = h.objs a

theorem frameNil_refl (h : Heap) : FrameNil h h := fun _ _ => rfl

theorem frameNil_trans {h1 h2 h3 : Heap} (a : FrameNil h1 h2) (b : FrameNil h2 h3) :
    FrameNil h1 h3 := fun x hx => by rw [b x (by rw [a x hx]; exact hx), a x hx]

theorem frameNil_of_frame {h h' : Heap} {vs : List Value} (hf : Frame h h' vs []) :
    FrameNil h h' := fun x hx => hf x hx (fun ⟨_, _, _, hp, _⟩ => by simp at hp)

theorem frameNil_alloc {h : Heap} {o : HeapObj} (hwf : HeapWF h) : FrameNil h (h.alloc o).2 :=
  fun x hx => objs_alloc_ne (fun e => hx (hwf x (by omega)))

theorem frame_of_frameNil {h h' : Heap} {vs : List Value} {fp : Footprint} (a : FrameNil h h') :
    Frame h h' vs fp := fun x hx _ => a x hx

theorem same_of_frameNil {h h' : Heap} {v : Value} (a : FrameNil h h')
    (hr : ∀ q c, follow h v q = some (.ref c) → h.objs c ≠ none) : Same h h' v :=
  fun q c e => a c (hr q c e)

theorem nnp_of_frameNil {h h' : Heap} {vs : List Value} {gfp : Footprint} (a : FrameNil h h')
    (haw : ArgsWF h vs) : NoNewPaths h h' vs gfp := by
  apply noNewPaths_of_reach
  intro k q b e
  left
  unfold at? at e ⊢
  cases hk : vs[k]? with
  | none => simp [hk] at e
  | some v =>
    simp only [hk, Option.bind_some] at e ⊢
    have hs := same_of_frameNil a (reach_of_args haw hk)
    rwa [follow_same q v hs] at e

end SpecLean.Validation.Keep

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- The subterms of `e` that meet `p`. -/
partial def findAllApps (p : Lean.Expr → Bool) (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  let acc := if p e then acc.push e else acc
  match e with
  | .app f a => findAllApps p a (findAllApps p f acc)
  | .lam _ d b _ | .forallE _ d b _ => findAllApps p b (findAllApps p d acc)
  | .letE _ t v b _ => findAllApps p b (findAllApps p v (findAllApps p t acc))
  | .mdata _ b | .proj _ _ b => findAllApps p b acc
  | _ => acc

/-- `HeapWF h`: a fact, a new object on a well-formed heap, or a `Fresh` step from one. -/
partial def proveHeapWF (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some h := (if t.isAppOfArity ``SpecLean.Encode.HeapWF 1 then some (t.getArg! 0) else none)
    | return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``SpecLean.Encode.HeapWF 1 do continue
    if ← isDefEq (ty.getArg! 0) h then
      g.assign d.toExpr
      return true
  let s ← saveState
  if h.isAppOfArity ``Prod.snd 3 && (h.getArg! 2).isAppOfArity ``SpecLean.Heap.alloc 2 then
    let [g'] ← g.apply (mkConst ``SpecLean.Validation.Keep.heapWF_alloc) | restoreState s; return false
    if ← proveHeapWF g' then return true
    restoreState s
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``SpecLean.Encode.Fresh 2 do continue
    unless ← isDefEq (ty.getArg! 1) h do continue
    let s2 ← saveState
    let g' ← mkFreshExprMVar (mkApp (mkConst ``SpecLean.Encode.HeapWF) (ty.getArg! 0))
    if ← proveHeapWF g'.mvarId! then
      g.assign (mkApp (mkProj ``And 1 d.toExpr) g')
      return true
    restoreState s2
  return false

/-- `Same h0 h v`, back from `h` to `h0` through new objects and callees that write nothing. -/
partial def proveSame (g : MVarId) (hr : Lean.Expr) (depth : Nat := 16) : TacticM Bool :=
  g.withContext do
  if depth == 0 then return false
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SpecLean.Validation.Local.Same 3 do return false
  let h0 := t.getArg! 0
  let h := t.getArg! 1
  let v := t.getArg! 2
  if ← withReducible (isDefEq h0 h) then
    g.assign (← mkAppM ``SpecLean.Validation.Keep.same_refl #[h0, v])
    return true
  if h.isAppOfArity ``Prod.snd 3 && (h.getArg! 2).isAppOfArity ``SpecLean.Heap.alloc 2 then
    let hm := (h.getArg! 2).getArg! 0
    let o := (h.getArg! 2).getArg! 1
    let gs ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Local.Same #[h0, hm, v])
    let gw ← mkFreshExprMVar (mkApp (mkConst ``SpecLean.Encode.HeapWF) hm)
    let s ← saveState
    if (← proveSame gs.mvarId! hr (depth - 1)) && (← proveHeapWF gw.mvarId!) then
      g.assign (← mkAppOptM ``SpecLean.Validation.Keep.same_alloc
        #[h0, hm, v, o, gs, hr, gw])
      return true
    restoreState s
    return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``SpecLean.Encode.Frame 4 do continue
    unless (← withReducible (isDefEq (ty.getArg! 1) h)) do continue
    let fp ← whnfR (ty.getArg! 3)
    unless fp.isAppOf ``List.nil do continue
    let hm := ty.getArg! 0
    if ← withReducible (isDefEq hm h) then continue
    let s ← saveState
    let gs ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Local.Same #[h0, hm, v])
    if ← proveSame gs.mvarId! hr (depth - 1) then
      g.assign (← mkAppM ``SpecLean.Validation.Keep.same_frame #[gs, hr, d.toExpr])
      return true
    restoreState s
  return false

/-- A decode in the heap of the goal from the same decode in an earlier heap: a callee that
writes nothing and new objects keep what the value reaches. -/
elab "rd_keep" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, l, r) := t.eq? | throwError "rd_keep: not a decode"
  let n := l.getAppNumArgs
  unless n ≥ 2 do throwError "rd_keep: not a decode"
  let h := l.getArg! (n - 2)
  let v := l.getArg! (n - 1)
  let f := l.getAppFn
  let fArgs := l.getAppArgs.extract 0 (n - 2)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l', r') := ty.eq? | continue
    unless l'.getAppFn == f && l'.getAppNumArgs == n do continue
    let h0 := l'.getArg! (n - 2)
    if ← withReducible (isDefEq h0 h) then continue
    let s ← saveState
    try
      unless (← withReducible (isDefEq (l'.getArg! (n - 1)) v)) &&
        (← (fArgs.zip (l'.getAppArgs.extract 0 (n - 2))).allM fun (a, b) =>
          withReducible (isDefEq a b)) && (← withReducible (isDefEq r' r)) do
        throwError "no"
      -- The objects that `v` reaches in `h0`: from the write condition of the arguments.
      let mut hr? := none
      for e in ← getLCtx do
        if e.isImplementationDetail then continue
        let ety ← instantiateMVars e.type
        unless ety.isAppOfArity ``SpecLean.Encode.ArgsWF 2 do continue
        unless ← isDefEq (ety.getArg! 0) h0 do continue
        let some (_, vs) := (← whnfR (ety.getArg! 1)).listLit? | continue
        for x in vs do
          if ← withReducible (isDefEq x v) then
            let stx ← `(SpecLean.Validation.Keep.reach_of_mem (v := $(← Term.exprToSyntax v))
              $(← Term.exprToSyntax e.toExpr) (by simp))
            let pf ← Term.withoutErrToSorry do
              let pf ← Term.elabTerm stx none
              Term.synthesizeSyntheticMVarsNoPostponing
              instantiateMVars pf
            hr? := some pf
            break
        if hr?.isSome then break
      let some hr := hr? | throwError "no reach"
      let gs ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Local.Same #[h0, h, v])
      unless ← proveSame gs.mvarId! hr do throwError "no same"
      let inst ← synthInstance (← mkAppM ``SpecLean.Validation.Local.LocalDec #[mkAppN f fArgs])
      let eq ← mkAppOptM ``SpecLean.Validation.Local.LocalDec.local_same
        #[none, mkAppN f fArgs, inst, h0, h, v, gs]
      g.assign (← mkEqTrans eq d.toExpr)
      replaceMainGoal []
      return
    catch e =>
      trace[debug] "rd_keep {d.userName}: {e.toMessageData}"
      restoreState s
  throwError "rd_keep: no earlier decode"

end SpecLean.Validation.Tactic

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- `Reach h v`: a scalar, a new set, or a value that an earlier heap reached with the same
objects. -/
def proveReach (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SpecLean.Validation.Keep.Reach 2 do return false
  let h := t.getArg! 0
  let v := t.getArg! 1
  -- A value that is no reference: its constructor shows it.
  let vw ← whnfR v
  if vw.isApp && vw.getAppFn.isConst && !vw.isAppOf ``SpecLean.Value.ref then
    let s ← saveState
    try
      let gs ← evalTacticAt (← `(tactic|
        exact SpecLean.Validation.Keep.reach_scalar (fun _ e => SpecLean.Value.noConfusion e))) g
      if gs.isEmpty && !(← instantiateMVars (mkMVar g)).hasSorry then return true
    catch _ => pure ()
    restoreState s
  if vw.isAppOf ``SpecLean.Value.ref then
    let s ← saveState
    try
      let gs ← evalTacticAt (← `(tactic| exact SpecLean.Validation.Keep.reach_alloc_set)) g
      if gs.isEmpty then return true
    catch _ => pure ()
    restoreState s
  for e in ← getLCtx do
    if e.isImplementationDetail then continue
    let ety ← instantiateMVars e.type
    unless ety.isAppOfArity ``SpecLean.Encode.ArgsWF 2 do continue
    let h0 := ety.getArg! 0
    let some (_, vs) := (← whnfR (ety.getArg! 1)).listLit? | continue
    unless ← vs.anyM fun x => withReducible (isDefEq x v) do continue
    let s ← saveState
    try
      let stx ← `(SpecLean.Validation.Keep.reach_of_mem (v := $(← Term.exprToSyntax v))
        $(← Term.exprToSyntax e.toExpr) (by simp))
      let hr ← Term.withoutErrToSorry do
        let pf ← Term.elabTerm stx none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars pf
      let gs ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Local.Same #[h0, h, v])
      if ← proveSame gs.mvarId! hr then
        g.assign (← mkAppM ``SpecLean.Validation.Keep.reach_same #[gs, hr])
        return true
    catch _ => pure ()
    restoreState s
  return false

/-- `ArgsWF h vs` of a call: each argument reaches only objects of the heap. -/
elab "rd_argswf" : tactic => withMainContext do
  let mut g ← getMainGoal
  for _ in [0:16] do
    let t ← instantiateMVars (← g.getType)
    unless t.isAppOfArity ``SpecLean.Encode.ArgsWF 2 do throwError "rd_argswf: not ArgsWF"
    let l ← whnfR (t.getArg! 1)
    if l.isAppOf ``List.nil then
      g.assign (mkApp (mkConst ``SpecLean.Validation.Keep.argsWF_nil) (t.getArg! 0))
      replaceMainGoal []
      return
    let [g1, g2] ← g.apply (mkConst ``SpecLean.Validation.Keep.argsWF_cons)
      | throwError "rd_argswf: no step"
    unless ← proveReach g1 do throwError "rd_argswf: no reach for {← g1.getType}"
    g := g2
  throwError "rd_argswf: too many arguments"

/-- `FrameNil h0 h`: back from `h` to `h0` through new objects and callees that write nothing. -/
partial def proveFrameNil (g : MVarId) (depth : Nat := 16) : TacticM Bool := g.withContext do
  if depth == 0 then return false
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SpecLean.Validation.Keep.FrameNil 2 do return false
  let h0 := t.getArg! 0
  let h := t.getArg! 1
  if ← withReducible (isDefEq h0 h) then
    g.assign (mkApp (mkConst ``SpecLean.Validation.Keep.frameNil_refl) h0)
    return true
  let step (hm : Lean.Expr) (last : Lean.Expr) : TacticM Bool := do
    let s ← saveState
    let g1 ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Keep.FrameNil #[h0, hm])
    if ← proveFrameNil g1.mvarId! (depth - 1) then
      g.assign (← mkAppM ``SpecLean.Validation.Keep.frameNil_trans #[g1, last])
      return true
    restoreState s
    return false
  if h.isAppOfArity ``Prod.snd 3 && (h.getArg! 2).isAppOfArity ``SpecLean.Heap.alloc 2 then
    let hm := (h.getArg! 2).getArg! 0
    let gw ← mkFreshExprMVar (mkApp (mkConst ``SpecLean.Encode.HeapWF) hm)
    let s ← saveState
    if ← proveHeapWF gw.mvarId! then
      let last ← mkAppOptM ``SpecLean.Validation.Keep.frameNil_alloc
        #[hm, (h.getArg! 2).getArg! 1, gw]
      if ← step hm last then return true
    restoreState s
    return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``SpecLean.Encode.Frame 4 do continue
    unless (← whnfR (ty.getArg! 3)).isAppOf ``List.nil do continue
    unless ← withReducible (isDefEq (ty.getArg! 1) h) do continue
    let hm := ty.getArg! 0
    if ← withReducible (isDefEq hm h) then continue
    if ← step hm (← mkAppM ``SpecLean.Validation.Keep.frameNil_of_frame #[d.toExpr]) then
      return true
  return false

/-- `Fresh h0 h`: back from `h` to `h0` through new objects and `Fresh` facts. -/
partial def proveFreshChain (g : MVarId) (depth : Nat := 16) : TacticM Bool := g.withContext do
  if depth == 0 then return false
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SpecLean.Encode.Fresh 2 do return false
  let h0 := t.getArg! 0
  let h := t.getArg! 1
  if ← withReducible (isDefEq h0 h) then
    g.assign (mkApp (mkConst ``SpecLean.Encode.Fresh_refl) h0)
    return true
  if h.isAppOfArity ``Prod.snd 3 && (h.getArg! 2).isAppOfArity ``SpecLean.Heap.alloc 2 then
    let hm := (h.getArg! 2).getArg! 0
    let s ← saveState
    let g1 ← mkFreshExprMVar (← mkAppM ``SpecLean.Encode.Fresh #[h0, hm])
    if ← proveFreshChain g1.mvarId! (depth - 1) then
      g.assign (← mkAppOptM ``SpecLean.Validation.Where.fresh_alloc
        #[h0, hm, (h.getArg! 2).getArg! 1, g1])
      return true
    restoreState s
    return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``SpecLean.Encode.Fresh 2 do continue
    unless ← withReducible (isDefEq (ty.getArg! 1) h) do continue
    let hm := ty.getArg! 0
    if ← withReducible (isDefEq hm h) then continue
    let s ← saveState
    let g1 ← mkFreshExprMVar (← mkAppM ``SpecLean.Encode.Fresh #[h0, hm])
    if ← proveFreshChain g1.mvarId! (depth - 1) then
      g.assign (← mkAppM ``SpecLean.Encode.Fresh_trans #[g1, d.toExpr])
      return true
    restoreState s
  return false

/-- The contract of a run of callees that write nothing and new objects: `Frame`, `Fresh` and
`NoNewPaths` from the heap at entry. -/
elab "rd_chain" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if t.isAppOfArity ``SpecLean.Encode.Fresh 2 then
    if ← proveFreshChain g then replaceMainGoal []; return
    throwError "rd_chain: no fresh chain"
  let isFrame := t.isAppOfArity ``SpecLean.Encode.Frame 4
  unless isFrame || t.isAppOfArity ``SpecLean.Encode.NoNewPaths 4 do
    throwError "rd_chain: not a contract goal"
  let h0 := t.getArg! 0
  let gf ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Keep.FrameNil #[h0, t.getArg! 1])
  unless ← proveFrameNil gf.mvarId! do throwError "rd_chain: no frame chain"
  if isFrame then
    g.assign (← mkAppOptM ``SpecLean.Validation.Keep.frame_of_frameNil
      #[none, none, t.getArg! 2, t.getArg! 3, gf])
    replaceMainGoal []
    return
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``SpecLean.Encode.ArgsWF 2 do continue
    unless ← withReducible (isDefEq (ty.getArg! 0) h0) do continue
    unless ← withReducible (isDefEq (ty.getArg! 1) (t.getArg! 2)) do continue
    g.assign (← mkAppOptM ``SpecLean.Validation.Keep.nnp_of_frameNil
      #[none, none, none, t.getArg! 3, gf, d.toExpr])
    replaceMainGoal []
    return
  throwError "rd_chain: no ArgsWF"

end SpecLean.Validation.Tactic

macro_rules | `(tactic| rd_frame) => `(tactic| ((repeat' (first | rd_chain | with_reducible apply And.intro)); done))
macro_rules | `(tactic| rd_callhyp) => `(tactic| rd_keep)
macro_rules | `(tactic| rd_callhyp) => `(tactic| rd_argswf)
macro_rules | `(tactic| rd_callhyp) => `(tactic| (first
  | exact SpecLean.Validation.Keep.heapWF_alloc (by assumption)
  | exact SpecLean.Validation.Keep.heapWF_alloc ((‹SpecLean.Encode.Fresh _ _›).2 (by assumption))))

namespace SpecLean.Validation.Keep

theorem frameNil_objs {h0 h : Heap} {a : Nat} {o : HeapObj} (hf : FrameNil h0 h)
    (ho : h0.objs a = some o) : h.objs a = some o := by
  rw [hf a (by rw [ho]; exact Option.some_ne_none o), ho]

theorem objs_ne_none_of_frameNil {h0 h : Heap} {a : Nat} (hf : FrameNil h0 h)
    (h0a : h0.objs a ≠ none) : h.objs a ≠ none := by
  rw [hf a h0a]; exact h0a

end SpecLean.Validation.Keep

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- A split gave `h.objs a = none` for an argument object of an earlier heap that every step
since then kept: the case is impossible. -/
elab "rd_objs_none" : tactic => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless r.isAppOf ``Option.none && l.isAppOfArity ``SpecLean.Heap.objs 2 do continue
    let h := l.getArg! 0
    let a := l.getArg! 1
    for e in ← getLCtx do
      if e.isImplementationDetail then continue
      let ety ← instantiateMVars e.type
      unless ety.isAppOfArity ``SpecLean.Encode.ArgsWF 2 do continue
      let h0 := ety.getArg! 0
      let s ← saveState
      try
        let v := mkApp (mkConst ``SpecLean.Value.ref) a
        let stx ← `(SpecLean.Validation.Keep.reach_of_mem (v := $(← Term.exprToSyntax v))
          $(← Term.exprToSyntax e.toExpr) (by simp))
        let hr ← Term.withoutErrToSorry do
          let pf ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars pf
        if hr.hasSorry then throwError "no"
        let gf ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Keep.FrameNil #[h0, h])
        unless ← proveFrameNil gf.mvarId! do throwError "no"
        -- The root object itself: the empty path reaches it.
        let h0a ← mkAppM' hr #[← mkAppOptM ``List.nil #[mkConst ``Nat], a, ← mkEqRefl (← mkAppOptM ``Option.some #[none, v])]
        let ne ← mkAppM ``SpecLean.Validation.Keep.objs_ne_none_of_frameNil #[gf, h0a]
        g.assign (← mkFalseElim (← g.getType) (mkApp ne d.toExpr))
        replaceMainGoal []
        return
      catch _ => restoreState s
  throwError "rd_objs_none: none"

/-- An arithmetic error of the interpreter: the operator and its class from `intArith`. -/
elab "rd_interr" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOfArity ``SpecLean.intArith 3 && r.isAppOf ``Except.error do continue
    let s ← saveState
    try
      let (_, g') ← (← getMainGoal).revert #[d.fvarId]
      replaceMainGoal [g']
      evalTactic (← `(tactic| (
        simp only [SpecLean.intArith]
        split <;> intro hie <;> cases hie <;> simp [SpecLean.SpecError.fail] <;> done)))
      return
    catch _ => restoreState s
  throwError "rd_interr: none"

/-- An object of an earlier heap that every step since then kept: read it in the goal's heap
from the fact of the earlier heap. -/
elab "rd_frame_objs" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let reads := findAllApps (fun e => e.isAppOfArity ``SpecLean.Heap.objs 2 && !e.hasLooseBVars) t
  let mut done := false
  for rd in reads do
    let h := rd.getArg! 0
    let a := rd.getArg! 1
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, l, r) := ty.eq? | continue
      unless r.isAppOfArity ``Option.some 2 && l.isAppOfArity ``SpecLean.Heap.objs 2 do continue
      unless ← withReducible (isDefEq (l.getArg! 1) a) do continue
      let h0 := l.getArg! 0
      if ← withReducible (isDefEq h0 h) then continue
      let s ← saveState
      let gf ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Keep.FrameNil #[h0, h])
      if ← proveFrameNil gf.mvarId! then
        let eq ← mkAppM ``SpecLean.Validation.Keep.frameNil_objs #[gf, d.toExpr]
        let g ← getMainGoal
        let r ← g.rewrite (← g.getType) eq
        let g' ← g.replaceTargetEq r.eNew r.eqProof
        replaceMainGoal (g' :: r.mvarIds)
        done := true
        break
      restoreState s
    if done then break
  unless done do throwError "rd_frame_objs: none"

/-- A field read that a split left open: compute the field index, then read the item of the
field list from the facts. In an impossible case the facts contradict the split. -/
elab "rd_fieldidx" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.consumeMData.eq? | continue
    let l := l.consumeMData
    let r := r.consumeMData
    unless l.isAppOfArity ``SpecLean.fieldIndex 3 && r.isAppOfArity ``Option.some 2 do continue
    unless (r.getArg! 1).isFVar do continue
    let s ← saveState
    try
      let (_, g) ← (← getMainGoal).revert #[d.fvarId]
      replaceMainGoal [g]
      evalTactic (← `(tactic| (
        simp only [SpecLean.Validation.Tactic.fieldIndex_lit, Option.some.injEq]
        intro hfi
        subst hfi)))
      -- The item read at the field index: from the facts of the field list.
      let lctx ← withMainContext getLCtx
      for e in lctx.decls.toArray.reverse do
        let some e := e | continue
        if e.isImplementationDetail then continue
        let ety ← instantiateMVars e.type
        let some (_, l2, r2) := ety.consumeMData.eq? | continue
        unless l2.isAppOfArity ``GetElem?.getElem? 7 && (l2.getArg! 5).isAppOf ``List.set do continue
        unless r2.isAppOfArity ``Option.some 2 && (r2.getArg! 1).isFVar do continue
        let s2 ← saveState
        try
          let (_, g2) ← (← getMainGoal).revert #[e.fvarId]
          replaceMainGoal [g2]
          withMainContext <| evalTactic (← `(tactic| (
            simp (disch := decide) only [List.getElem?_set_ne, List.getElem?_set_self',
              Option.map_eq_map, Option.map_some, Option.map_none, Function.const_apply,
              Option.some.injEq, reduceCtorEq, *]
            try intro hit
            try subst hit)))
        catch _ => restoreState s2
        break
      evalTactic (← `(tactic| try rd_contra))
      return
    catch ex =>
      restoreState s
      throwError "rd_fieldidx: {ex.toMessageData}"
  throwError "rd_fieldidx: none"

/-- The object facts of an earlier heap, restated for each later heap of the goal that every
step since then kept, so that `rd_heap` reads the objects there. -/
elab "rd_frame_facts" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let mut heaps : Array Lean.Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isConstOf ``SpecLean.Heap && t.containsFVar d.fvarId then
      heaps := heaps.push d.toExpr
  let mut facts : Array (Lean.Expr × Lean.Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless r.isAppOfArity ``Option.some 2 && l.isAppOfArity ``SpecLean.Heap.objs 2 do continue
    facts := facts.push (l.getArg! 0, d.toExpr)
  let mut n := 0
  for h in heaps do
    for h0 in (facts.map (·.1)).toList.eraseDups do
      if h0 == h then continue
      let s ← saveState
      let gf ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Keep.FrameNil #[h0, h])
      unless ← proveFrameNil gf.mvarId! do restoreState s; continue
      for (h1, pf) in facts do
        unless h1 == h0 do continue
        let eq ← mkAppM ``SpecLean.Validation.Keep.frameNil_objs #[gf, pf]
        let g ← getMainGoal
        let (_, g') ← (← g.assert `hkeep (← inferType eq) eq).intro1P
        replaceMainGoal [g']
        n := n + 1
  if n == 0 then throwError "rd_frame_facts: none"

end SpecLean.Validation.Tactic

macro_rules | `(tactic| rd_finish) => `(tactic| rd_objs_none)
macro_rules | `(tactic| rd_finish) => `(tactic| rd_interr)

namespace SpecLean.Validation.Tactic

open Lean Meta

/-- A proof of `0 ≤ e` for an `Int` built from casts, literals, `max _ 0`, sums and products. -/
partial def intNonneg (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Nat.cast 3 then
    return some (← mkAppM ``Int.natCast_nonneg #[e.getArg! 2])
  if e.isAppOfArity ``Max.max 4 then
    let b := e.getArg! 3
    if (← isDefEq b (mkIntLit 0)) then
      return some (← mkAppM ``Int.le_max_right #[e.getArg! 2, b])
    return none
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let some p ← intNonneg (e.getArg! 4) | return none
    let some q ← intNonneg (e.getArg! 5) | return none
    return some (← mkAppM ``Int.add_nonneg #[p, q])
  if e.isAppOfArity ``HMul.hMul 6 then
    let some p ← intNonneg (e.getArg! 4) | return none
    let some q ← intNonneg (e.getArg! 5) | return none
    return some (← mkAppM ``Int.mul_nonneg #[p, q])
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let t ← mkAppM ``LE.le #[mkIntLit 0, e]
    try
      let p ← mkDecideProof t
      return some p
    catch _ => return none
  return none

/-- `max x 0 = x` when `x` is visibly not negative. -/
simproc [rd_simp] maxZeroNonneg (@Max.max Int _ _ 0) := fun e => do
  unless e.isAppOfArity ``Max.max 4 do return .continue
  unless (← inferType e).isConstOf ``Int do return .continue
  let x := e.getArg! 2
  unless (← isDefEq (e.getArg! 3) (mkIntLit 0)) do return .continue
  let some h ← intNonneg x | return .continue
  return .done { expr := x, proof? := some (← mkAppM ``Int.max_eq_left #[h]) }

end SpecLean.Validation.Tactic
