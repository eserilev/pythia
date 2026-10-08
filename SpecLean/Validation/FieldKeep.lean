import SpecLean.Validation.Keep

/-!
# Fields that a function does not rebind (SPEC 9.2)

`FieldKeep h h' rb`: every container of `h` is a container of the same class in `h'`, and each
field `i` of class `ty` with `(ty, i)` not in `rb` keeps its value. `rb` lists the fields that
the function and its callees assign (`x.f = ...`). A caller that holds an object that it read
through such a field before a call finds the same object there after the call.

`Frame` cannot give this: a container at a footprint path may change, and a callee that
rebinds `state.validators` to a copy would leave the caller's alias outside the state.
-/

namespace SpecLean.Encode

/-- Every container of `h` keeps its class in `h'`, and every field outside `rb` its value. -/
def FieldKeep (h h' : Heap) (rb : List (Name × Nat)) : Prop :=
  ∀ a ty fs, h.objs a = some (.container ty fs) →
    ∃ fs', h'.objs a = some (.container ty fs') ∧ ∀ i, (ty, i) ∉ rb → fs'[i]? = fs[i]?

end SpecLean.Encode

namespace SpecLean.Validation.FieldKeep

open SpecLean SpecLean.Encode SpecLean.Validation.Keep SpecLean.Validation.Where

theorem refl (h : Heap) (rb : List (Name × Nat)) : FieldKeep h h rb :=
  fun _ _ fs ho => ⟨fs, ho, fun _ _ => rfl⟩

theorem trans {h1 h2 h3 : Heap} {rb rb' : List (Name × Nat)} (a : FieldKeep h1 h2 rb)
    (b : FieldKeep h2 h3 rb') (hs : ∀ x ∈ rb', x ∈ rb) : FieldKeep h1 h3 rb := by
  intro x ty fs ho
  obtain ⟨fs2, ho2, hk2⟩ := a x ty fs ho
  obtain ⟨fs3, ho3, hk3⟩ := b x ty fs2 ho2
  exact ⟨fs3, ho3, fun i hi => by rw [hk3 i (fun hm => hi (hs _ hm)), hk2 i hi]⟩

theorem of_frameNil {h h' : Heap} (rb : List (Name × Nat)) (hf : FrameNil h h') :
    FieldKeep h h' rb := fun x _ fs ho =>
  ⟨fs, by rw [hf x (by rw [ho]; exact Option.some_ne_none _), ho], fun _ _ => rfl⟩

theorem alloc {h0 h : Heap} {rb : List (Name × Nat)} {o : HeapObj} (hk : FieldKeep h0 h rb)
    (hwf : HeapWF h) : FieldKeep h0 (h.alloc o).2 rb :=
  fun x ty fs ho => by
    obtain ⟨fs', ho', hk'⟩ := hk x ty fs ho
    refine ⟨fs', ?_, hk'⟩
    rw [frameNil_alloc hwf x (by rw [ho']; exact Option.some_ne_none _), ho']

/-- A write of a container: the fields outside `rb` keep their values. -/
theorem set_container {h0 h : Heap} {rb : List (Name × Nat)} {a : Nat} {ty : Name}
    {fs0 fs : List Value} (hk : FieldKeep h0 h rb) (ho : h.objs a = some (.container ty fs0))
    (hf : ∀ i, (ty, i) ∉ rb → fs[i]? = fs0[i]?) : FieldKeep h0 (h.set a (.container ty fs)) rb :=
  fun x ty' fs' hx => by
    obtain ⟨fs1, ho1, hk1⟩ := hk x ty' fs' hx
    by_cases e : x = a
    · subst e
      rw [ho] at ho1
      cases ho1
      exact ⟨fs, by simp, fun i hi => by rw [hf i hi, hk1 i hi]⟩
    · exact ⟨fs1, by simp [e, ho1], hk1⟩

/-- A write over an object that is not a container. -/
theorem set_other {h0 h : Heap} {rb : List (Name × Nat)} {a : Nat} {o0 o : HeapObj}
    (hk : FieldKeep h0 h rb) (ho : h.objs a = some o0) (hn : ∀ ty fs, o0 ≠ .container ty fs) :
    FieldKeep h0 (h.set a o) rb :=
  fun x ty fs hx => by
    obtain ⟨fs1, ho1, hk1⟩ := hk x ty fs hx
    by_cases e : x = a
    · subst e
      rw [ho] at ho1
      cases ho1
      exact absurd rfl (hn ty fs1)
    · exact ⟨fs1, by simp [e, ho1], hk1⟩

/-- A write to an address that held nothing in the entry heap. -/
theorem set_fresh {h0 h : Heap} {rb : List (Name × Nat)} {a : Nat} {o : HeapObj}
    (hk : FieldKeep h0 h rb) (ha : h0.objs a = none) : FieldKeep h0 (h.set a o) rb :=
  fun x ty fs hx => by
    obtain ⟨fs1, ho1, hk1⟩ := hk x ty fs hx
    have e : x ≠ a := fun e => by subst e; rw [ha] at hx; cases hx
    exact ⟨fs1, by simp [e, ho1], hk1⟩

/-- A field of a container after a call: the value of the entry heap, outside `rb`. -/
theorem field {h h' : Heap} {rb : List (Name × Nat)} {a : Nat} {ty : Name} {fs fs' : List Value}
    (hk : FieldKeep h h' rb) (ho : h.objs a = some (.container ty fs))
    (ho' : h'.objs a = some (.container ty fs')) (i : Nat) (hi : (ty, i) ∉ rb) :
    fs'[i]? = fs[i]? := by
  obtain ⟨fs1, ho1, hk1⟩ := hk a ty fs ho
  rw [ho'] at ho1
  cases ho1
  exact hk1 i hi

/-- The container itself after a call. -/
theorem objs {h h' : Heap} {rb : List (Name × Nat)} {a : Nat} {ty : Name} {fs : List Value}
    (hk : FieldKeep h h' rb) (ho : h.objs a = some (.container ty fs)) :
    ∃ fs', h'.objs a = some (.container ty fs') ∧ ∀ i, (ty, i) ∉ rb → fs'[i]? = fs[i]? :=
  hk a ty fs ho

end SpecLean.Validation.FieldKeep

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- Run a tactic on a new goal of type `ty`; the proof when it closes the goal. -/
def proveBy (ty : Lean.Expr) (tac : TSyntax `tactic) : TacticM (Option Lean.Expr) := do
  let s ← saveState
  try
    let m ← mkFreshExprMVar ty
    let gs ← Term.withoutErrToSorry <| withoutRecover <| evalTacticAt tac m.mvarId!
    unless gs.isEmpty do throwError "open goals"
    let pf ← instantiateMVars m
    if pf.hasExprMVar || pf.hasSorry then throwError "open proof"
    return some pf
  catch _ =>
    restoreState s
    return none

/-- `FieldKeep h0 h rb`: back from `h` to `h0` through writes, new objects and callees. -/
partial def proveFieldKeep (g : MVarId) (depth : Nat := 24) : TacticM Bool := g.withContext do
  if depth == 0 then return false
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``SpecLean.Encode.FieldKeep 3 do return false
  let h0 := t.getArg! 0
  let h := t.getArg! 1
  let rb := t.getArg! 2
  if ← withReducible (isDefEq h0 h) then
    g.assign (← mkAppM ``SpecLean.Validation.FieldKeep.refl #[h0, rb])
    return true
  -- No write to an old object in between: `FrameNil`.
  let s0 ← saveState
  let gf ← mkFreshExprMVar (← mkAppM ``SpecLean.Validation.Keep.FrameNil #[h0, h])
  if ← proveFrameNil gf.mvarId! then
    g.assign (← mkAppM ``SpecLean.Validation.FieldKeep.of_frameNil #[rb, gf])
    return true
  restoreState s0
  let back (hm : Lean.Expr) : TacticM (Option Lean.Expr) := do
    let g1 ← mkFreshExprMVar (← mkAppM ``SpecLean.Encode.FieldKeep #[h0, hm, rb])
    if ← proveFieldKeep g1.mvarId! (depth - 1) then return some g1 else return none
  if h.isAppOfArity ``Prod.snd 3 && (h.getArg! 2).isAppOfArity ``SpecLean.Heap.alloc 2 then
    let hm := (h.getArg! 2).getArg! 0
    let s ← saveState
    let gw ← mkFreshExprMVar (mkApp (mkConst ``SpecLean.Encode.HeapWF) hm)
    if ← proveHeapWF gw.mvarId! then
      if let some g1 ← back hm then
        g.assign (← mkAppOptM ``SpecLean.Validation.FieldKeep.alloc
          #[none, none, none, (h.getArg! 2).getArg! 1, g1, gw])
        return true
    restoreState s
    return false
  if h.isAppOfArity ``SpecLean.Heap.set 3 then
    let hm := h.getArg! 0
    let a := h.getArg! 1
    let o := h.getArg! 2
    let s ← saveState
    let some g1 ← back hm | restoreState s; return false
    let hmS ← Term.exprToSyntax hm
    let aS ← Term.exprToSyntax a
    -- A field write: the old fields, and the one written is in `rb`.
    if o.isAppOfArity ``SpecLean.HeapObj.container 2 then
      let ty := o.getArg! 0
      let fs := o.getArg! 1
      if fs.isAppOfArity ``List.set 4 then
        let fs0 := fs.getArg! 1
        let ho ← proveBy (← mkAppM ``Eq #[← mkAppM ``SpecLean.Heap.objs #[hm, a],
          ← mkAppM ``Option.some #[← mkAppM ``SpecLean.HeapObj.container #[ty, fs0]]])
          (← `(tactic| rd_objs))
        if let some ho := ho then
          let hfT ← withLocalDeclD `i (mkConst ``Nat) fun i => do
            let mem ← mkAppM ``Membership.mem #[rb, ← mkAppM ``Prod.mk #[ty, i]]
            mkForallFVars #[i] (← mkArrow (mkNot mem)
              (← mkAppM ``Eq #[← mkAppM ``GetElem?.getElem? #[fs, i],
                ← mkAppM ``GetElem?.getElem? #[fs0, i]]))
          let hf ← proveBy hfT (← `(tactic| (
            intro i hi
            rw [List.getElem?_set]
            split
            · subst_vars; exact absurd (by decide) hi
            · rfl)))
          if let some hf := hf then
            g.assign (← mkAppM ``SpecLean.Validation.FieldKeep.set_container #[g1, ho, hf])
            return true
    -- A write over an object that is not a container: a list, a dict or a set.
    let ho ← proveBy (← mkAppM ``Ne #[← mkAppM ``SpecLean.Heap.objs #[hm, a],
        ← mkAppOptM ``Option.none #[mkConst ``SpecLean.HeapObj]])
      (← `(tactic| (rd_objs; exact Option.some_ne_none _)))
    let _ := ho
    let stx ← `(SpecLean.Validation.FieldKeep.set_other (h := $hmS) (a := $aS)
        $(← Term.exprToSyntax g1) (by rd_objs) (by intro _ _ e; cases e))
    try
      let pf ← Term.withoutErrToSorry do
        let pf ← Term.elabTermEnsuringType stx t
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars pf
      unless pf.hasSorry || pf.hasExprMVar do
        g.assign pf
        return true
    catch _ => pure ()
    restoreState s
    return false
  -- A callee: its `FieldKeep` fact, or its `Frame` with the empty footprint.
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``SpecLean.Encode.FieldKeep 3 then
      unless ← withReducible (isDefEq (ty.getArg! 1) h) do continue
      let hm := ty.getArg! 0
      if ← withReducible (isDefEq hm h) then continue
      let s ← saveState
      if let some g1 ← back hm then
        let subT ← withLocalDeclD `x ((← whnfR (← inferType rb)).appArg!)
          fun x => do
            mkForallFVars #[x] (← mkArrow (← mkAppM ``Membership.mem #[ty.getArg! 2, x])
              (← mkAppM ``Membership.mem #[rb, x]))
        if let some hs ← proveBy subT (← `(tactic| decide)) then
          g.assign (← mkAppM ``SpecLean.Validation.FieldKeep.trans #[g1, d.toExpr, hs])
          return true
      restoreState s
  return false

/-- `FieldKeep h0 h rb`, by `proveFieldKeep`. -/
elab "rd_fieldkeep" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``SpecLean.Encode.FieldKeep 3 do throwError "rd_fieldkeep: not a goal"
  let g' ← g.replaceTargetDefEq t
  if ← proveFieldKeep g' then replaceMainGoal []; return
  throwError "rd_fieldkeep: no chain"

/-- After a writer with a `FieldKeep` fact: each old container that the context knows keeps
its class, and each of its fields outside `rb` the value that the context knows. -/
elab "rd_keep_fields" : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  let mut keeps := #[]
  let mut objs := #[]
  let mut items := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``SpecLean.Encode.FieldKeep 3 then keeps := keeps.push (d, ty)
    let some (_, l, r) := ty.eq? | continue
    if l.isAppOfArity ``SpecLean.Heap.objs 2 && r.isAppOfArity ``Option.some 2 &&
        (r.getArg! 1).isAppOfArity ``SpecLean.HeapObj.container 2 then
      objs := objs.push (d, l, r.getArg! 1)
    if l.isAppOfArity ``GetElem?.getElem? 7 && r.isAppOfArity ``Option.some 2 then
      items := items.push (l.getArg! 5, l.getArg! 6, d)
  for (dk, kt) in keeps do
    let h0 := kt.getArg! 0
    let h1 := kt.getArg! 1
    let rb := kt.getArg! 2
    for (d0, l0, o0) in objs do
      unless ← withReducible (isDefEq (l0.getArg! 0) h0) do continue
      let a := l0.getArg! 1
      let ty := o0.getArg! 0
      let fs := o0.getArg! 1
      -- The container in `h1`, as the context names it.
      for (d1, l1, o1) in objs do
        unless ← withReducible (isDefEq (l1.getArg! 0) h1) do continue
        unless ← withReducible (isDefEq (l1.getArg! 1) a) do continue
        let fs1 := o1.getArg! 1
        -- A field of `fs` that the context knows, kept and not yet known in `fs1`.
        for (xs, i, di) in items do
          unless ← withReducible (isDefEq xs fs) do continue
          let some iv := (← instantiateMVars i).rawNatLit? <|> (← instantiateMVars i).nat?
            | continue
          -- The fact of the context about the same field in `fs1`, if any.
          let mut other := none
          for d in lctx do
            if d.isImplementationDetail then continue
            let ty ← instantiateMVars d.type
            let some (_, l, r) := ty.eq? | continue
            unless l.isAppOfArity ``GetElem?.getElem? 7 do continue
            unless ← withReducible (isDefEq (l.getArg! 5) fs1) do continue
            let j ← instantiateMVars (l.getArg! 6)
            unless j.nat? == some iv || j.rawNatLit? == some iv do continue
            other := some (d, r)
          let rv := (← instantiateMVars (← inferType di.toExpr)).appArg!
          -- Only a field that holds an object: a caller can hold that object across the call.
          unless (rv.getArg! 1).isAppOfArity ``SpecLean.Value.ref 1 do continue
          if let some (_, r) := other then
            if r == rv then continue
          let memT ← mkAppM ``Membership.mem #[rb, ← mkAppM ``Prod.mk #[ty, i]]
          let some hi ← proveBy (mkNot memT) (← `(tactic| decide)) | continue
          let pf ← mkAppM ``SpecLean.Validation.FieldKeep.field
            #[dk.toExpr, d0.toExpr, d1.toExpr, i, hi]
          let pf ← mkEqTrans pf di.toExpr
          -- Two values of one field: they are equal, and a new name goes.
          if let some (d, _) := other then
            let s ← saveState
            try
              let eqv ← mkAppM ``Option.some.inj #[← mkEqTrans (← mkEqSymm d.toExpr) pf]
              let eqx ← mkAppM ``SpecLean.Value.ref.inj #[eqv]
              let (fx, g2) ← (← g.assert `hkv (← inferType eqx) eqx).intro1P
              let g3 ← substCore g2 fx (symm := false) (tryToSkip := true) <|>
                substCore g2 fx (symm := true) (tryToSkip := true)
              replaceMainGoal [g3.2]
              return
            catch _ => restoreState s
          let (_, g1) ← (← g.assert `hkf (← inferType pf) pf).intro1P
          replaceMainGoal [g1]
          return
  throwError "rd_keep_fields: nothing new"

end SpecLean.Validation.Tactic
