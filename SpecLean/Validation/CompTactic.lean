import SpecLean.Validation.LoopTactic
import SpecLean.Validation.Comp
import SpecLean.Validation.CompSnap
import SpecLean.DecodeLemmas

/-!
# The tactic step of the comprehension rule (SPEC 9.3)

`rd_comp` applies `comp_sim` at a comprehension of the goal: `compItems` on the interpreter side,
`filterMapM` (or `mapM`) on the readable side. The heap does not change during the items, so the
invariant of the items is `h' = h` and the locals that are not targets keep their values. One
item is proved in the context of the caller, by the steps of the tactic.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Encode

/-- A Python set of decoded items: the object is a set, and its elements decode in order. -/
@[rd_dec] def decSetV {α : Type} (f : Rd.Dec α) : Rd.Dec (List α)
  | h, .ref a =>
    match h.objs a with
    | some (.set xs) => xs.mapM (f h)
    | _ => none
  | _, _ => none

/-- An item of a snapshot whose values decode to the readable items. -/
theorem snap_item {α : Type} {dec : Value → Option α} {xs : List Value} {ys : List α} {i : Nat}
    {x : Value} {y : α} (hm : xs.mapM dec = some ys) (hy : ys[i]? = some y)
    (hx : xs[i]? = some x) : dec x = some y := by
  have hlen := (SpecLean.Encode.mapM_some_iff _ _).mp hm
  have := hlen.2 i x hx
  rw [hy] at this
  exact this

theorem snap_len {α : Type} {dec : Value → Option α} {xs : List Value} {ys : List α}
    (hm : xs.mapM dec = some ys) : xs.length = ys.length :=
  ((SpecLean.Encode.mapM_some_iff _ _).mp hm).1.symm

/-- The locals that are not targets keep their values. A definition: `simp` leaves it whole. -/
def KeepLocals (L' L : Locals) (T : List Name) : Prop := ∀ x, x ∉ T → L' x = L x

theorem KeepLocals.refl (L : Locals) (T : List Name) : KeepLocals L L T := fun _ _ => rfl

/-- A local that is not a target keeps its value when a target is set. -/
theorem keep_set {L' L : Locals} {T : List Name} (hL : KeepLocals L' L T) {n : Name}
    (hn : n ∈ T) (v : Value) : KeepLocals (L'.set n v) L T := by
  intro x hx
  have hne : x ≠ n := fun e => hx (by rw [e]; exact hn)
  rw [Locals.set_apply, if_neg hne, hL x hx]

/-- The values of a comprehension are the encodings of the readable items. -/
theorem listRel_enc {β : Type} {enc : β → Value} {P : β → Prop} :
    ∀ {vs : List Value} {bs : List β}, ListRel (fun v b => v = enc b ∧ P b) vs bs →
      vs = bs.map enc ∧ ∀ b ∈ bs, P b
  | _, _, .nil => ⟨rfl, by simp⟩
  | _, _, .cons ⟨rfl, hp⟩ hr => by
    obtain ⟨e, hall⟩ := listRel_enc hr
    refine ⟨by rw [e]; rfl, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hp
    · exact hall b hb

theorem itemRel_error {β : Type} {C : Heap → Prop} {Q : Locals → Heap → Prop}
    {E : Value → β → Heap → Prop} {e : SpecError} {f : Fail} (h : e ≠ .outOfFuel ∧ e.fail = f) :
    ItemRel C Q E (.error e) (.error f) := h

theorem itemRel_some {β : Type} {C : Heap → Prop} {Q : Locals → Heap → Prop}
    {E : Value → β → Heap → Prop} {v : Value} {L : Locals} {h : Heap} {b : β} (hc : C h)
    (hq : Q L h) (he : E v b h) : ItemRel C Q E (.ok (some v, L, h)) (.ok (some b)) :=
  ⟨hc, hq, he⟩

theorem itemRel_none {β : Type} {C : Heap → Prop} {Q : Locals → Heap → Prop}
    {E : Value → β → Heap → Prop} {L : Locals} {h : Heap} (hc : C h) (hq : Q L h) :
    ItemRel C Q E (.ok (none, L, h)) (.ok (none : Option β)) :=
  ⟨hc, hq⟩

/-- An item of `enumerate` over a decoded list: the reference, the readable pair, and the decode
of the item. -/
theorem enum_item {α : Type} {dec : Value → Option α} {h : Heap} {a : Nat} {k : ListKind}
    {e : SszTy} {l : Option Nat} {vrefs : List Value} {xs : List α} {i : Nat} {x : Value}
    {y : Int × α} (ho : h.objs a = some (.list k e l vrefs))
    (hnb : ¬(k = .list ∧ e = .uint (.width 8))) (hm : vrefs.mapM dec = some xs)
    (hy : (List.map (fun p => ((p.snd : Int), p.fst)) xs.zipIdx)[i]? = some y)
    (hx : iterItem h (.enum (.live a)) i = .ok (some x)) :
    ∃ r v, x = enumItem i r ∧ y = ((i : Int), v) ∧ dec r = some v ∧ xs[i]? = some v := by
  have hlen := (SpecLean.Encode.mapM_some_iff _ _).mp hm
  have hi : i < xs.length := by
    have := congrArg Option.isSome hy
    simp [List.getElem?_map, List.getElem?_zipIdx] at this
    exact this
  have hvi : i < vrefs.length := by omega
  have hy' : y = ((i : Int), xs[i]) := by
    simp [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi] at hy
    exact hy.symm
  have hx' : x = enumItem i vrefs[i] := by
    simp [iterItem, seqItem_live_eq ho hnb, List.getElem?_eq_getElem hvi] at hx
    exact hx.symm
  refine ⟨vrefs[i], xs[i], hx', hy', ?_, List.getElem?_eq_getElem hi⟩
  have := hlen.2 i vrefs[i] (List.getElem?_eq_getElem hvi)
  rw [List.getElem?_eq_getElem hi] at this
  exact this

/-- An item of `enumerate` over a list whose object holds the encodings of the readable items. -/
theorem enum_item_map {α : Type} {g : α → Value} {h : Heap} {a : Nat} {k : ListKind}
    {e : SszTy} {l : Option Nat} {xs : List α} {i : Nat} {x : Value} {y : Int × α}
    (ho : h.objs a = some (.list k e l (xs.map g)))
    (hnb : ¬(k = .list ∧ e = .uint (.width 8)))
    (hy : (List.map (fun p => ((p.snd : Int), p.fst)) xs.zipIdx)[i]? = some y)
    (hx : iterItem h (.enum (.live a)) i = .ok (some x)) :
    ∃ v, x = enumItem i (g v) ∧ y = ((i : Int), v) ∧ xs[i]? = some v := by
  have hi : i < xs.length := by
    have := congrArg Option.isSome hy
    simp [List.getElem?_map, List.getElem?_zipIdx] at this
    exact this
  have hy' : y = ((i : Int), xs[i]) := by
    simp [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi] at hy
    exact hy.symm
  have hx' : x = enumItem i (g xs[i]) := by
    simp [iterItem, seqItem_live_eq ho hnb, List.getElem?_map, List.getElem?_eq_getElem hi] at hx
    exact hx.symm
  exact ⟨xs[i], hx', hy', List.getElem?_eq_getElem hi⟩

/-- An item of a list whose object holds references that decode to the readable items. -/
theorem seq_item {α : Type} {dec : Value → Option α} {h : Heap} {a : Nat} {k : ListKind}
    {e : SszTy} {l : Option Nat} {vrefs : List Value} {xs : List α} {i : Nat} {x : Value} {y : α}
    (ho : h.objs a = some (.list k e l vrefs))
    (hnb : ¬(k = .list ∧ e = .uint (.width 8))) (hm : vrefs.mapM dec = some xs)
    (hy : xs[i]? = some y) (hx : iterItem h (.seq (.live a)) i = .ok (some x)) :
    dec x = some y := by
  have hlen := (SpecLean.Encode.mapM_some_iff _ _).mp hm
  simp only [iterItem, seqItem_live_eq ho hnb, Except.ok.injEq] at hx
  have := hlen.2 i x hx
  rw [hy] at this
  exact this

/-- An item of a list whose object holds the encodings of the readable items. -/
theorem seq_item_map {α : Type} {g : α → Value} {h : Heap} {a : Nat} {k : ListKind}
    {e : SszTy} {l : Option Nat} {xs : List α} {i : Nat} {x : Value} {y : α}
    (ho : h.objs a = some (.list k e l (xs.map g)))
    (hnb : ¬(k = .list ∧ e = .uint (.width 8))) (hy : xs[i]? = some y)
    (hx : iterItem h (.seq (.live a)) i = .ok (some x)) : x = g y := by
  simp only [iterItem, seqItem_live_eq ho hnb, List.getElem?_map, hy, Option.map_some,
    Except.ok.injEq, Option.some.injEq] at hx
  exact hx.symm

end SpecLean.Validation

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic SpecLean SpecLean.Encode SpecLean.Validation

/-- The names that a target binds. -/
partial def targetNames (t : Lean.Expr) : MetaM (List Lean.Expr) := do
  if t.isAppOfArity ``SpecLean.Target.name 2 then return [t.getArg! 1]
  if t.isAppOfArity ``SpecLean.Target.tuple 2 then
    let some (_, ts) := (t.getArg! 1).listLit? | throwError "rd_comp: target list"
    return (← ts.mapM targetNames).flatten
  throwError "rd_comp: target {t}"

/-- The relation of a value of the interpreter to a readable item of class `β`. -/
def compE (β : Lean.Expr) : TermElabM Lean.Expr := do
  let βs ← Term.exprToSyntax β
  if β.isConstOf ``Int then
    return ← Term.elabTerm (← `(fun (v : SpecLean.Value) (b : Int) (_ : SpecLean.Heap) =>
      v = SpecLean.Value.int b ∧ True)) none
  let some c := β.constName? | throwError "rd_comp: item class {β}"
  let enc := mkIdent (c.getPrefix ++ Name.mkSimple ("enc_" ++ c.getString!))
  Term.elabTerm (← `(fun (v : SpecLean.Value) (b : $βs) (hh : SpecLean.Heap) =>
      v = ($enc b hh).1 ∧ SpecLean.Rd.UintC.val b < 2 ^ SpecLean.Rd.UintC.bits (α := $βs))) none

/-- The end of one item: an error of the same class, a contradiction, or a kept or dropped item
with the heap unchanged. -/
macro "rd_item_end" : tactic => `(tactic| first
  | (with_reducible apply SpecLean.Validation.itemRel_error
     first
     | assumption
     | (constructor <;> first | assumption | rd_oof | rfl | (simp [SpecError.fail]; done)))
  | (exfalso; omega)
  | with_reducible contradiction
  | (simp only [SpecLean.normIndex_nat] at *
     simp only [ite_eq_right_iff, ite_eq_left_iff, Option.some.injEq, reduceCtorEq, imp_false,
       Nat.not_lt, List.getElem?_eq_none_iff] at *
     omega)
  | (first
      | with_reducible refine SpecLean.Validation.itemRel_some ?_ ?_ ?_
      | with_reducible refine SpecLean.Validation.itemRel_none ?_ ?_
     all_goals first
       | exact SpecLean.Validation.CContract.refl _ _ _ _ ‹_› ‹_›
       | (refine ⟨rfl, ?_⟩
          repeat (refine SpecLean.Validation.keep_set ?_ (by simp) _)
          assumption)
       | (refine ⟨?_, ?_⟩ <;> first | rfl | (simp [rd_simp]; done) | omega | (simp [rd_simp]; omega))))

/-- One item of a comprehension in the context of the caller. -/
macro "rd_comp_step" "[" ls:ident,* "]" : tactic => `(tactic| (
  intro n i L' h' x y hq hy hx
  obtain ⟨hh, hK⟩ := hq
  subst hh
  have hL := hK
  first
  | (obtain ⟨r, v, hxe, hye, hdec, hxs⟩ := SpecLean.Validation.enum_item ‹_› (by intro hc; first | cases hc.1 | cases hc.2) ‹_› hy hx
     subst hxe hye
     have hdecc := hdec
     simp only [rd_dec, Option.bind_eq_bind, Option.bind_eq_some_iff, rd_simp, Option.pure_def,
       Option.some.injEq, Value.ref.injEq, exists_eq_left', exists_eq_right] at hdec
     rd_split_hyps)
  | (obtain ⟨v, hxe, hye, hxs⟩ := SpecLean.Validation.enum_item_map ‹_› (by intro hc; first | cases hc.1 | cases hc.2) hy hx
     subst hxe hye)
  | (have hdec := SpecLean.Validation.seq_item ‹_› (by intro hc; first | cases hc.1 | cases hc.2) ‹_› hy hx
     have hdecc := hdec
     simp only [rd_dec, Option.bind_eq_bind, Option.bind_eq_some_iff, rd_simp, Option.pure_def,
       Option.some.injEq, Value.ref.injEq, exists_eq_left', exists_eq_right] at hdec
     rd_split_hyps)
  | (have hxe := SpecLean.Validation.seq_item_map ‹_› (by intro hc; first | cases hc.1 | cases hc.2) hy hx
     subst hxe)
  | (have hdec := SpecLean.Validation.snap_item ‹_› hy hx
     have hdecc := hdec
     simp only [rd_dec, Option.bind_eq_bind, Option.bind_eq_some_iff, rd_simp, Option.pure_def,
       Option.some.injEq, Value.ref.injEq, exists_eq_left', exists_eq_right] at hdec
     rd_split_hyps)
  | skip
  unfold SpecLean.Validation.compItem
  unfold SpecLean.Validation.KeepLocals at hL
  simp [rd_simp, lookup_lit, unfold_known, fieldIndex_lit, stop_call, stop_call_post, follow,
    assignTarget, assignTargets, evalIfs, enumItem, hL]
  all_goals (try rd_step)
  repeat' (first | rd_call [$ls,*] | (rd_items; (repeat rd_unify); try rd_step) |
    (rd_split <;> (try rd_step)))
  all_goals rd_item_end))

/-- A comprehension: `comp_sim` with the item fuel `kf`, each item by `rd_comp_step`, then both
results split. -/
elab "rd_comp" kf:num "[" ls:ident,* "]" : tactic => withMainContext do
  let t0 ← instantiateMVars (← getMainTarget)
  if (findClosed t0 (·.isAppOfArity ``List.filterMapM 6)).isNone &&
      (findClosed t0 (·.isAppOfArity ``List.mapM 6)).isSome then
    evalTactic (← `(tactic| rw [SpecLean.Validation.mapM_eq_filterMapM]))
  withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some ci := findClosed t (·.isAppOf ``SpecLean.compItems)
    | throwError "rd_comp: no comprehension"
  let some fm := findClosed t (·.isAppOfArity ``List.filterMapM 6)
    | throwError "rd_comp: no readable comprehension"
  let some vs := (if t.isAppOfArity ``SpecLean.Encode.ResultMatches 8 then some (t.getArg! 4)
      else none) | throwError "rd_comp: not a validation goal"
  -- The arguments from the end: an instance may come first.
  let a0 := ci.getAppArgs
  let a := a0.extract (a0.size - 11) a0.size
  let fuel := a[1]!
  let L := a[2]!
  let h := a[3]!
  let tgt := a[4]!
  let fa := fm.getAppArgs
  let f := fa[fa.size - 2]!
  let ys := fa[fa.size - 1]!
  let fmTy ← whnfR (← inferType fm)
  let some lb := fmTy.getAppArgs.back? | throwError "rd_comp: result type"
  let β := lb.getArg! 0
  let E ← Term.withSynthesize (compE β)
  let names ← targetNames tgt
  let nty ← inferType names[0]!
  let T ← mkListLit nty names
  let s := fun (e : Lean.Expr) => Term.exprToSyntax e
  let (envS, tS, ifsS, eltS, srcS) := (← s a[0]!, ← s tgt, ← s a[5]!, ← s a[7]!, ← s a[9]!)
  let (ysS, fS, ES, vsS, LS, hS, TS, fuelS) :=
    (← s ys, ← s f, ← s E, ← s vs, ← s L, ← s h, ← s T, ← s fuel)
  let src := a[9]!
  let some live := (if src.isAppOfArity ``SpecLean.IterSrc.enum 1 || src.isAppOfArity ``SpecLean.IterSrc.seq 1
      then some (src.getArg! 0) else none) | throwError "rd_comp: source {src}"
  let snap := live.isAppOfArity ``SpecLean.Seq.snap 1 && src.isAppOf ``SpecLean.IterSrc.seq
  unless live.isAppOfArity ``SpecLean.Seq.live 1 || snap do throwError "rd_comp: source {src}"
  let aS ← s (live.getArg! 0)
  let itemS ← if src.isAppOf ``SpecLean.IterSrc.enum then `(SpecLean.enumItem i x) else `(x)
  let hc := mkIdent `hcomp
  let gfpI := mkIdent `gfp
  if snap then
    evalTactic (← `(tactic| (
      have $hc:ident := SpecLean.Validation.comp_snap_sim $envS $tS $ifsS $eltS $aS $kf $ysS
        (by first | exact SpecLean.Validation.snap_len ‹_› | (simp <;> omega)) $fS $ES
        (gfp := $gfpI) (fpf := []) (vs := $vsS) (by simp) ‹_›
        (fun _ L' h' => h' = $hS ∧ SpecLean.Validation.KeepLocals L' $LS $TS)
        (by rd_comp_step [$ls,*]) (fun _ _ _ _ e _ => e) ($fuelS - $kf - 1) 0 $LS $hS
        ⟨rfl, SpecLean.Validation.KeepLocals.refl _ _⟩
        (SpecLean.Validation.CContract.refl _ _ _ _ ‹_› ‹_›) (by first | omega | (simp <;> omega)))))
  else
  evalTactic (← `(tactic| (
    have $hc:ident := SpecLean.Validation.comp_sim $envS $tS $ifsS $eltS $srcS $kf $ysS $fS $ES
      (gfp := $gfpI) (fpf := []) (vs := $vsS) (by simp) ‹_›
      (fun _ L' h' => h' = $hS ∧ SpecLean.Validation.KeepLocals L' $LS $TS)
      (fun i L' h' hq hi => by
        rw [hq.1]
        obtain ⟨x, hx⟩ := SpecLean.Validation.seqItem_live_some (a := $aS)
          ⟨_, _, _, _, ‹_›, by first | omega | (simp <;> omega)⟩ hi
        exact ⟨$itemS, by simp [iterItem, hx]⟩)
      (fun i L' h' hq hi => by
        rw [hq.1]
        simp [iterItem, SpecLean.Validation.seqItem_live_none (a := $aS) ⟨_, _, _, _, ‹_›, by first | omega | (simp <;> omega)⟩ hi])
      (by rd_comp_step [$ls,*]) (fun _ _ _ _ e _ => e) ($fuelS - $kf - 1) 0 $LS $hS
      ⟨rfl, SpecLean.Validation.KeepLocals.refl _ _⟩ (SpecLean.Validation.CContract.refl _ _ _ _ ‹_› ‹_›) (by first | omega | (simp <;> omega)))))
  evalTactic (← `(tactic| (
    rw [show $fuelS - $kf - 1 + $kf + 1 = $fuelS by omega, List.drop_zero] at $hc:ident
    revert $hc:ident
    generalize $(← s ci) = rcomp
    generalize $(← s fm) = rdcomp
    intro $hc:ident
    rcases rcomp with _ | ⟨vals, ⟨⟩ | ⟨⟩, hcomp'⟩ <;> rcases rdcomp with _ | bs
    all_goals simp only [SpecLean.Validation.CompOut] at $hc:ident)))
  -- The kept results: the values are the encodings of the readable items.
  let gs ← getGoals
  let mut out := []
  for g in gs do
    let r ← g.withContext do
      let some d := (← getLCtx).findFromUserName? `hcomp | return [g]
      let ty ← instantiateMVars d.type
      unless ty.isAppOfArity ``And 2 && (ty.getArg! 0).isAppOf ``SpecLean.Validation.ListRel do
        return [g]
      evalTacticAt (← `(tactic| (
        obtain ⟨hrel, -, -, -, -, ⟨rfl, -⟩, -⟩ := $hc:ident
        obtain ⟨rfl, hrange⟩ := SpecLean.Validation.listRel_enc hrel))) g
    out := out ++ r
  setGoals out
  evalTactic (← `(tactic| all_goals (try rd_step)))

end SpecLean.Validation.Tactic

/-- The end of a function that returns the new list of a comprehension. -/
macro "rd_list_end" : tactic => `(tactic| (
  simp only [SpecLean.Encode.ResultMatches, SpecLean.allocPyList]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  focus
    simp only [SpecLean.Validation.Steps.listRes_ref, SpecLean.Validation.Where.alloc_fst]
    exact ⟨Nat.le_refl _, SpecLean.Validation.Where.objs_alloc_self⟩
  focus
    intro x hx
    have := ‹∀ b ∈ _, _› x hx
    simpa [SpecLean.Rd.UintC.val, SpecLean.Rd.UintC.bits] using this
  focus rd_writes
  focus rd_writes
  focus rd_writes))

/-- The comprehension failed: the error of the items is the error of the function. -/
macro "rd_comp_err" : tactic => `(tactic| first
  | exact ‹_ ≠ SpecLean.SpecError.outOfFuel ∧ _›
  | exact (‹_ ≠ SpecLean.SpecError.outOfFuel ∧ _›).2)

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- A new list from a callee: its reference and its object, as facts. -/
elab "rd_listres" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOf ``SpecLean.Validation.Steps.ListRes do continue
    -- Give the fact a name, then take it apart: the fact goes away.
    let g ← getMainGoal
    let g ← g.assert `hlres ty d.toExpr
    let (_, g) ← g.intro1P
    let g ← g.clear d.fvarId
    replaceMainGoal [g]
    let hs := mkIdent `hlres
    evalTactic (← `(tactic| obtain ⟨_, hlv, _, _⟩ := $hs:ident))
    evalTactic (← `(tactic| first | subst hlv | cases hlv))
    return
  throwError "rd_listres: none"

end SpecLean.Validation.Tactic
