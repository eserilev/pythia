import SpecLean.Validation.LoopTactic
import SpecLean.Validation.Comp
import SpecLean.Validation.CompSnap
import SpecLean.DecodeLemmas
import SpecLean.Validation.Keep

/-!
# The tactic step of the comprehension rule (SPEC 9.3)

`rd_comp` applies `comp_sim` at a comprehension of the goal: `compItems` on the interpreter side,
`filterMapM` (or `mapM`) on the readable side. The heap does not change during the items, so the
invariant of the items is `h' = h` and the locals that are not targets keep their values. One
item is proved in the context of the caller, by the steps of the tactic.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Encode

section SumRule
open SpecLean.Rd

/-- The interpreter's sum of uints against the readable `sumU`: the same number, or errors of the
same class. The interpreter starts at the `int` `0`, so an empty sum is that `int`. -/
def SumRel {α : Type} [UintC α] (t : UintTy) : Res Value → SpecM α → Prop
  | .ok v, .ok r => (v = .uint t (UintC.val r) ∨ v = .int 0 ∧ UintC.val r = 0) ∧
      UintC.val r < 2 ^ UintC.bits α
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

theorem resolveUint_self (t : UintTy) : resolveUint t t = .ok t := by
  cases t <;> simp [resolveUint]

/-- One more item, from a uint accumulator. -/
theorem sum_uint_acc {α : Type} [UintC α] (t : UintTy) (ht : t.bits = UintC.bits α) :
    ∀ (bs : List α) (acc : α), UintC.val acc < 2 ^ UintC.bits α →
      SumRel t ((bs.map fun b => Value.uint t (UintC.val b)).foldlM (binopVal .add)
          (.uint t (UintC.val acc)))
        (bs.foldlM (fun a x => uOp .add (uv a) (uv x)) acc)
  | [], acc, hacc => by simp [SumRel, hacc]
  | b :: bs, acc, hacc => by
    simp only [List.map_cons, List.foldlM_cons, Ssz.binopVal_uint, resolveUint_self,
      Except.bind_ok', intArith, uOp, uv, erase, uOf, wrapUint, ht]
    by_cases hr : 0 ≤ ((UintC.val acc : Int) + (UintC.val b : Int)) ∧
        ((UintC.val acc : Int) + (UintC.val b : Int)) < 2 ^ UintC.bits α
    · rw [if_pos hr]
      simp only [Except.map, Except.mapError, Except.bind_ok', Except.pure_ok', bind, Except.bind,
        pure, Except.pure, if_pos hr]
      have h2 : UintC.val acc + UintC.val b < 2 ^ UintC.bits α := by
        have := hr.2; exact_mod_cast this
      have := sum_uint_acc t ht bs (UintC.ofNat ((UintC.val acc : Int) + UintC.val b).toNat)
        (by rw [UintC.val_ofNat]; omega)
      rw [UintC.val_ofNat] at this
      exact this
    · rw [if_neg hr]
      simp [Except.mapError, bind, Except.bind, if_neg hr, SumRel, SpecError.fail]

theorem binopVal_int_uint (op : BinOp) (t : UintTy) (a : Int) (b : Nat) :
    binopVal op (.int a) (.uint t b) = (do wrapUint t (← intArith op a b)) := by
  simp only [binopVal, LibValues.binop, Ssz.binop]

/-- The interpreter's `sum` from the `int` `0`, against `sumU` from a readable `0`. -/
theorem sum_uint {α : Type} [UintC α] (t : UintTy) (ht : t.bits = UintC.bits α) (start : α)
    (hs : UintC.val start = 0) :
    ∀ bs : List α, SumRel t ((bs.map fun b => Value.uint t (UintC.val b)).foldlM (binopVal .add)
        (.int 0)) (sumU start bs)
  | [] => by simp [SumRel, sumU, hs]; exact Nat.two_pow_pos _
  | b :: bs => by
    have h0 : ((0 : Nat) : Int) = 0 := rfl
    simp only [sumU, List.map_cons, List.foldlM_cons, binopVal_int_uint, Except.bind_ok', intArith,
      uOp, uv, erase, uOf, wrapUint, ht, hs, h0, Int.zero_add]
    by_cases hr : 0 ≤ (UintC.val b : Int) ∧ (UintC.val b : Int) < 2 ^ UintC.bits α
    · rw [if_pos hr]
      simp only [Except.mapError, bind, Except.bind, pure, Except.pure, if_pos hr]
      have h2 : UintC.val b < 2 ^ UintC.bits α := by have := hr.2; exact_mod_cast this
      have := sum_uint_acc t ht bs (UintC.ofNat (UintC.val b : Int).toNat)
        (by rw [UintC.val_ofNat]; omega)
      rw [UintC.val_ofNat] at this
      exact this
    · rw [if_neg hr]
      have h3 : ¬ ((UintC.val b : Int) < 2 ^ UintC.bits α) := fun h => hr ⟨by omega, h⟩
      simp [Except.mapError, bind, Except.bind, h3, SumRel, SpecError.fail]


end SumRule

/-- A Python set of decoded items: the object is a set, and its elements decode in order. -/
def decSetV {α : Type} (f : Rd.Dec α) : Rd.Dec (List α)
  | h, .ref a =>
    match h.objs a with
    | some (.set xs) => xs.mapM (f h)
    | _ => none
  | _, _ => none

@[rd_dec] theorem decSetV_ref_eq_some {α : Type} (f : Rd.Dec α) (h : Heap) (a : Nat)
    (ys : List α) : decSetV f h (.ref a) = some ys ↔
      ∃ xs, h.objs a = some (.set xs) ∧ xs.mapM (f h) = some ys := by
  show (match h.objs a with
    | some (.set xs) => xs.mapM (f h)
    | _ => none) = some ys ↔ _
  constructor
  · intro e
    cases ho : h.objs a with
    | none => rw [ho] at e; cases e
    | some o =>
      rw [ho] at e
      cases o with
      | set xs => exact ⟨xs, rfl, e⟩
      | _ => cases e
  · rintro ⟨xs, ho, hm⟩
    rw [ho]
    exact hm

/-- An item of a snapshot whose values decode to the readable items. -/
theorem snap_item {α : Type} {dec : Value → Option α} {xs : List Value} {ys : List α} {i : Nat}
    {x : Value} {y : α} (hm : xs.mapM dec = some ys) (hy : ys[i]? = some y)
    (hx : xs[i]? = some x) : dec x = some y := by
  have hlen := (SpecLean.Encode.mapM_some_iff _ _).mp hm
  have := hlen.2 i x hx
  rw [hy] at this
  exact this

/-- An item of a snapshot that holds the encodings of the readable items. -/
theorem snap_item_map {α : Type} {g : α → Value} {ys : List α} {i : Nat} {x : Value} {y : α}
    (hy : ys[i]? = some y) (hx : (ys.map g)[i]? = some x) : x = g y := by
  rw [List.getElem?_map, hy] at hx
  exact (Option.some.inj hx).symm

theorem snap_len {α : Type} {dec : Value → Option α} {xs : List Value} {ys : List α}
    (hm : xs.mapM dec = some ys) : xs.length = ys.length :=
  ((SpecLean.Encode.mapM_some_iff _ _).mp hm).1.symm

/-- A bound on the length of a readable result: a comprehension keeps at most its items. -/
def FMLen {ε β : Type} : Except ε (List β) → Nat → Prop
  | .ok r, n => r.length ≤ n
  | .error _, _ => True

theorem filterMapM_loop_len {ε α β : Type} (f : α → Except ε (Option β)) :
    ∀ (l : List α) (acc : List β), FMLen (List.filterMapM.loop f l acc) (l.length + acc.length)
  | [], acc => by simp [List.filterMapM.loop, FMLen, pure, Except.pure]
  | a :: l, acc => by
    simp only [List.filterMapM.loop]
    rcases hf : f a with e | o
    · simp [bind, Except.bind, FMLen]
    · rcases o with _ | b
      · have := filterMapM_loop_len f l acc
        simp only [bind, Except.bind]; revert this
        generalize List.filterMapM.loop f l acc = r; rcases r <;> simp [FMLen] <;> omega
      · have := filterMapM_loop_len f l (b :: acc)
        simp only [bind, Except.bind]; revert this
        generalize List.filterMapM.loop f l (b :: acc) = r; rcases r <;> simp [FMLen] <;> omega

theorem filterMapM_len {ε α β : Type} (f : α → Except ε (Option β)) (l : List α) :
    FMLen (l.filterMapM f) l.length := by
  have := filterMapM_loop_len f l []
  simpa [List.filterMapM] using this

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

/-! ## Sets of lists -/

section SetRule
open SpecLean.Rd

theorem keyMatch_uint (h : Heap) (t : UintTy) (x y : Nat) :
    keyMatch h (.uint t x) (.uint t y) = .ok (decide (x = y)) := by
  simp [keyMatch, numOf, deepEq, depthBound, cmpInt]
  split <;> simp_all [resolveUint_self] <;> omega

theorem findKey_map {α : Type} [DecidableEq α] (h : Heap) (E : α → Value)
    (hE : ∀ a b, keyMatch h (E a) (E b) = .ok (decide (a = b))) (x : α) :
    ∀ acc : List α, ∃ o, findKey h (E x) (acc.map E) = .ok o ∧ o.isSome = acc.contains x
  | [] => ⟨none, by simp [findKey]⟩
  | y :: ys => by
    obtain ⟨o, ho, hs⟩ := findKey_map h E hE x ys
    by_cases hxy : x = y
    · subst hxy; exact ⟨some 0, by simp [findKey, hE, bind, Except.bind, pure, Except.pure]⟩
    · refine ⟨o.map (· + 1), ?_, ?_⟩
      · simp [findKey, hE, hxy, bind, Except.bind, ho, pure, Except.pure]
      · simp [hs, hxy]

theorem dedupe_map_acc {α : Type} [DecidableEq α] (h : Heap) (E : α → Value)
    (hE : ∀ a b, keyMatch h (E a) (E b) = .ok (decide (a = b))) :
    ∀ (xs acc : List α), dedupe h (acc.map E) (xs.map E) =
      .ok ((xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).map E)
  | [], acc => by simp [dedupe]
  | x :: xs, acc => by
    obtain ⟨o, ho, hs⟩ := findKey_map h E hE x acc
    simp only [List.map_cons, dedupe, bind, Except.bind, ho, List.foldl_cons]
    by_cases hc : acc.contains x
    · simp only [hs, hc, if_true]; exact dedupe_map_acc h E hE xs acc
    · simp only [hs, hc]
      have := dedupe_map_acc h E hE xs (acc ++ [x])
      simpa using this

/-- `set(xs)` of a list of encoded values: the readable `dedup`, when the key rule of the
interpreter is equality of the readable values. -/
theorem dedupe_map {α : Type} [DecidableEq α] (h : Heap) (E : α → Value)
    (hE : ∀ a b, keyMatch h (E a) (E b) = .ok (decide (a = b))) (xs : List α) :
    dedupe h [] (xs.map E) = .ok ((Rd.dedup xs).map E) := by
  have := dedupe_map_acc h E hE xs []
  simpa [Rd.dedup] using this

theorem dedup_length_le {α : Type} [BEq α] (xs : List α) : (Rd.dedup xs).length ≤ xs.length := by
  suffices ∀ acc : List α, (xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).length ≤ acc.length + xs.length by
    simpa [Rd.dedup] using this []
  induction xs with
  | nil => simp
  | cons x xs ih => intro acc; simp only [List.foldl_cons]; split
                    · have := ih acc; simp; omega
                    · have := ih (acc ++ [x]); simp at this ⊢; omega

theorem mem_foldl_dedup {α : Type} [BEq α] {x : α} : ∀ (xs acc : List α),
    x ∈ xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc →
      x ∈ acc ∨ x ∈ xs
  | [], _, h => .inl h
  | y :: ys, acc, h => by
    simp only [List.foldl_cons] at h
    split at h
    · rcases mem_foldl_dedup ys acc h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases mem_foldl_dedup ys _ h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact .inl h
        · simp at h; subst h; exact .inr (List.mem_cons_self ..)
      · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_of_mem_dedup {α : Type} [BEq α] {x : α} {xs : List α} (hx : x ∈ Rd.dedup xs) :
    x ∈ xs :=
  (mem_foldl_dedup xs [] hx).resolve_left (by simp)

/-- An item of a set of uints decodes to the readable item. -/
theorem decUintT_val {α : Type} [UintC α] (t : UintTy) (h : Heap) (y : α)
    (hr : UintC.val y < 2 ^ UintC.bits α) : decUintT t h (.uint t (UintC.val y)) = some y := by
  simp [decUintT, hr, UintC.ofNat_val]

end SetRule

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

/-- `getItem h (.ref a) i` of a list object that a fact of the context names: the item, by
`getItem_list`. -/
elab "rd_getitem" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let some gi := findClosed t (fun e => e.isAppOfArity ``SpecLean.getItem 3 &&
      (e.getArg! 1).isAppOfArity ``SpecLean.Value.ref 1) | throwError "rd_getitem: none"
  let h := gi.getArg! 0
  let a := (gi.getArg! 1).getArg! 0
  let some ho ← findObj h a | throwError "rd_getitem: no object"
  let hs ← Term.exprToSyntax ho
  let idx := gi.getArg! 2
  let lem ← if idx.isAppOf ``SpecLean.Value.uint then `(SpecLean.getItem_list $hs)
    else `(SpecLean.getItem_list_int $hs)
  evalTactic (← `(tactic| rw [$lem:term]))

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
  | (have hxe := SpecLean.Validation.snap_item_map hy hx
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
    (rd_getitem; try rd_step) | (rd_split <;> (try rd_step)))
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
  let haveTac ← if snap then
    `(tactic| (
      have $hc:ident := SpecLean.Validation.comp_snap_sim $envS $tS $ifsS $eltS $aS $kf $ysS
        (by first | exact SpecLean.Validation.snap_len ‹_› | (simp <;> omega)) $fS $ES
        (gfp := $gfpI) (fpf := []) (vs := $vsS) (by simp) ‹_›
        (fun _ L' h' => h' = $hS ∧ SpecLean.Validation.KeepLocals L' $LS $TS)
        (by rd_comp_step [$ls,*]) (fun _ _ _ _ e _ => e) ($fuelS - $kf - 1) 0 $LS $hS
        ⟨rfl, SpecLean.Validation.KeepLocals.refl _ _⟩
        (SpecLean.Validation.CContract.refl _ _ _ _ ‹_› ‹_›) (by first | omega | (simp <;> omega))))
  else
    `(tactic| (
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
      ⟨rfl, SpecLean.Validation.KeepLocals.refl _ _⟩ (SpecLean.Validation.CContract.refl _ _ _ _ ‹_› ‹_›) (by first | omega | (simp <;> omega))))
  evalTactic haveTac
  let hl := mkIdent `hcomplen
  evalTactic (← `(tactic| (
    rw [show $fuelS - $kf - 1 + $kf + 1 = $fuelS by omega, List.drop_zero] at $hc:ident
    have $hl:ident := SpecLean.Validation.filterMapM_len $fS $ysS
    revert $hc:ident
    revert $hl:ident)))
  -- Generalize the two sides by the terms themselves: a term that goes back through syntax may
  -- not match the goal (`generalize` finds terms up to instances only).
  let g ← getMainGoal
  let (fvs, g) ← g.generalize #[{ expr := ci, xName? := `rcomp }, { expr := fm, xName? := `rdcomp }]
  replaceMainGoal [g]
  let rcI := mkIdent `rcomp
  let rdI := mkIdent `rdcomp
  let _ := fvs
  evalTactic (← `(tactic| (
    intro $hl:ident $hc:ident
    rcases $rcI:ident with _ | ⟨vals, ⟨⟩ | ⟨⟩, hcomp'⟩ <;> rcases $rdI:ident with _ | bs
    all_goals simp only [SpecLean.Validation.CompOut] at $hc:ident
    all_goals simp only [SpecLean.Validation.FMLen, List.length_map, List.length_zipIdx,
      List.length_range] at $hl:ident)))
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
        obtain ⟨hrel, -, -, -, -, ⟨hh0, -⟩, -⟩ := $hc:ident
        subst hh0
        obtain ⟨hv0, hrange⟩ := SpecLean.Validation.listRel_enc hrel
        subst hv0))) g
    out := out ++ r
  setGoals out
  -- Only the binds of the results: the next step of the caller comes from the loop of steps.
  evalTactic (← `(tactic| all_goals (try simp only [Except.bind_ok', Except.bind_error'])))

end SpecLean.Validation.Tactic

/-- The end of a function that returns the new list of a comprehension. -/
macro "rd_list_end" : tactic => `(tactic| (
  simp only [SpecLean.Encode.ResultMatches, SpecLean.allocPyList]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  focus
    simp only [SpecLean.Validation.Steps.listRes_ref, SpecLean.Validation.Where.alloc_fst]
    exact ⟨Nat.le_refl _, SpecLean.Validation.Where.objs_alloc_self⟩
  focus
    try refine ⟨?_, ?_⟩
    all_goals first
      | (intro x hx
         have := ‹∀ b ∈ _, _› x hx
         simpa [SpecLean.Rd.UintC.val, SpecLean.Rd.UintC.bits] using this)
      | exact ‹List.length _ ≤ _›
  focus rd_writes
  focus rd_writes
  focus rd_writes))

/-- The comprehension failed: the error of the items is the error of the function. -/
macro "rd_comp_err" : tactic => `(tactic| first
  | exact ‹_ ≠ SpecLean.SpecError.outOfFuel ∧ _›
  | exact (‹_ ≠ SpecLean.SpecError.outOfFuel ∧ _›).2
  | (simp only [SpecLean.Encode.ResultMatches]; exact ‹_ ≠ SpecLean.SpecError.outOfFuel ∧ _›))

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

namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- `sum` of uints in the goal: the interpreter's fold from the `int` `0` and the readable `sumU`
over the same items. `sum_uint` relates them; both results split. -/
elab "rd_sum" : tactic => withMainContext do
  -- A sum of a new list: read the list from the heap first.
  let t0 := (← instantiateMVars (← getMainTarget)).consumeMData
  if (findClosed t0 (·.isAppOf ``SpecLean.allocPyList)).isSome then
    evalTactic (← `(tactic| try simp only [SpecLean.allocPyList, SpecLean.applyBuiltin,
      SpecLean.LibModel.builtin, SpecLean.Ssz.builtin, SpecLean.iterElems, SpecLean.iterBase,
      SpecLean.Validation.Where.alloc_fst, SpecLean.Validation.Where.objs_alloc_self,
      List.headD_nil, Except.bind_ok']))
  withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some run := findClosed t (fun e => e.isAppOfArity ``List.foldlM 7 &&
      (e.getArg! 6).isAppOf ``List.map && (e.getArg! 5).isAppOfArity ``SpecLean.Value.int 1)
    | throwError "rd_sum: no sum"
  let some rd := findClosed t (·.isAppOf ``SpecLean.Rd.sumU) | throwError "rd_sum: no readable sum"
  let runS ← Term.exprToSyntax run
  let rdS ← Term.exprToSyntax rd
  let hs := mkIdent `hsum
  evalTactic (← `(tactic| (
    first
    | (have $hs:ident : SpecLean.Validation.SumRel _ $runS $rdS :=
        SpecLean.Validation.sum_uint _ (by rfl) _ (by rfl) _)
    | fail "rd_sum: the sum does not match"
    revert $hs:ident
    generalize $runS = rsum
    generalize $rdS = rdsum
    intro $hs:ident
    rcases rsum with _ | v <;> rcases rdsum with _ | r
    all_goals simp only [SpecLean.Validation.SumRel] at $hs:ident
    all_goals (try (obtain ⟨hv | ⟨hv, hz⟩, hrange⟩ := $hs:ident <;> subst hv))
    all_goals (try rd_step))))

end SpecLean.Validation.Tactic


namespace SpecLean.Validation.Tactic

open Lean Meta Elab Tactic

/-- `set(xs)` of a list in the heap: the readable `dedup` of its items. -/
elab "rd_set" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let some ib := findClosed t (fun e => e.isAppOfArity ``SpecLean.iterBase 2 &&
      (e.getArg! 1).isAppOfArity ``SpecLean.Value.ref 1)
    | throwError "rd_set: no set"
  unless (findClosed t (·.isAppOf ``SpecLean.dedupe)).isSome do throwError "rd_set: no set"
  let hp := ib.getArg! 0
  let a := (ib.getArg! 1).getArg! 0
  -- The list at the reference: its items are the encodings of a readable list.
  let mut found := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOfArity ``SpecLean.Heap.objs 2 && (← isDefEq (l.getArg! 0) hp) &&
      (← isDefEq (l.getArg! 1) a) do continue
    unless r.isAppOfArity ``Option.some 2 do continue
    let o := r.getArg! 1
    unless o.isAppOfArity ``SpecLean.HeapObj.list 4 do continue
    let xs := o.getArg! 3
    unless xs.isAppOfArity ``List.map 4 do continue
    found := some (d.toExpr, xs.getArg! 2, xs.getArg! 3)
  let some (hobj, E, ys) := found | throwError "rd_set: no list"
  let (hS, pS, aS, ES, yS) := (← Term.exprToSyntax hobj, ← Term.exprToSyntax hp,
    ← Term.exprToSyntax a, ← Term.exprToSyntax E, ← Term.exprToSyntax ys)
  evalTactic (← `(tactic| (
    rw [show SpecLean.iterBase $pS (.ref $aS) = .ok (List.map $ES $yS) by
      simp only [SpecLean.iterBase, $hS:term]]
    simp only [Except.bind_ok']
    rw [SpecLean.Validation.dedupe_map $pS $ES (fun x y => by
      simp only [SpecLean.Validation.keyMatch_uint]; cases x; cases y; simp) $yS]
    simp only [Except.bind_ok'])))

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

/-- The length facts of each `dedup` in the goal, for `omega`. -/
elab "rd_dedup_len" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let mut seen : Array Lean.Expr := #[]
  for e in findAllApps (·.isAppOfArity ``SpecLean.Rd.dedup 3) t do
    if seen.contains e then continue
    seen := seen.push e
    let pf := mkAppN (.const ``SpecLean.Validation.dedup_length_le []) e.getAppArgs
    let g ← getMainGoal
    let (_, g) ← (← g.assert `hdlen (← inferType pf) pf).intro1P
    replaceMainGoal [g]

end SpecLean.Validation.Tactic

macro_rules | `(tactic| rd_callhyp) => `(tactic| (rd_dedup_len; omega))

/-- The set of a `set(...)` call: its items decode to the readable `dedup`. -/
macro_rules | `(tactic| rd_callhyp) => `(tactic| (
  rd_heap
  refine ⟨_, rfl, SpecLean.Validation.Decode.mapM_map_of _ (fun x hx => ?_)⟩
  have hx' := SpecLean.Validation.mem_of_mem_dedup hx
  have := ‹∀ x ∈ _, _› x hx'
  exact SpecLean.Validation.decUintT_val _ _ x
    (by simpa [SpecLean.Rd.UintC.val, SpecLean.Rd.UintC.bits] using this)))
