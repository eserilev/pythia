import SpecLean.Layer4.Inv

/-!
# Layer 4 spike: expressions agree with the interpreter

`expr_sound`: when the denotation of an expression gives a result, the interpreter with enough
fuel gives the same error, or a value that agrees with it (`ERel`), and the heap does not
change. Proved once for every expression of the fragment, by induction on the fuel.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode SpecLean.Validation.Where

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

/-- The interpreter's result of an expression agrees with the denotation's. -/
def ExprOK (h : Heap) (vs : List Value) : Res DRes → Res (Value × Heap) → Prop
  | .ok r, .ok (w, h') => h' = h ∧ ERel h vs r w
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

@[simp] theorem exb_err (e : ε) (f : α → Except ε β) : Except.bind (.error e) f = .error e := rfl
@[simp] theorem exb_ok (a : α) (f : α → Except ε β) : Except.bind (.ok a) f = f a := rfl

theorem bind_case {x : DM α} {f : α → DM β} {r : Res β} (hb : DM.bind x f = some r) :
    (∃ e, x = some (.error e) ∧ r = .error e) ∨ (∃ a, x = some (.ok a) ∧ f a = some r) := by
  cases x with
  | none => cases hb
  | some rr =>
    cases rr with
    | ok a => exact .inr ⟨a, rfl, hb⟩
    | error e => cases hb; exact .inl ⟨e, rfl, rfl⟩

theorem lift_some {x r : Res α} (h : lift x = some r) : r = x ∧ ∀ e, x = .error e → e ≠ .outOfFuel := by
  unfold lift at h
  split at h
  · cases h
  · next hx =>
    cases h
    refine ⟨rfl, fun e he => ?_⟩
    subst he; intro e'; subst e'; exact hx rfl

theorem exprOK_error {h : Heap} {vs : List Value} {e : SpecError} {res : Res (Value × Heap)}
    (hk : ExprOK h vs (.error e) res) : res = .error e ∧ e ≠ .outOfFuel := by
  cases res with
  | error e' => obtain ⟨rfl, hne⟩ := hk; exact ⟨rfl, hne⟩
  | ok p => cases hk

theorem exprOK_ok {h : Heap} {vs : List Value} {r : DRes} {res : Res (Value × Heap)}
    (hk : ExprOK h vs (.ok r) res) : ∃ w, res = .ok (w, h) ∧ ERel h vs r w := by
  cases res with
  | error e' => cases hk
  | ok p => obtain ⟨w, h'⟩ := p; obtain ⟨rfl, hr⟩ := hk; exact ⟨w, rfl, hr⟩

theorem truthyH_flat (h : Heap) {v : Value} (hv : Flat v = true) : truthyH h v = truthy v := by
  cases v <;> first | rfl | simp [Flat] at hv

theorem deepEq_flat (h : Heap) {x y : Value} (hx : Flat x = true) (hy : Flat y = true) :
    deepEq depthBound h x y = cmpVal .eq x y := by
  simp only [depthBound]; rw [deepEq.eq_def]
  cases x <;> cases y <;> first | rfl | simp [Flat] at hx hy

theorem cmpF_sound (h : Heap) {op : CmpOp} {x y : Value} (hx : Flat x = true) (hy : Flat y = true)
    {r : Res Bool} (hc : cmpF op x y = some r) :
    compareOp h op x y = r ∧ ∀ e, r = .error e → e ≠ .outOfFuel := by
  cases op with
  | is => simp [cmpF, DM.ok] at hc; subst hc; simp [compareOp]
  | isNot => simp [cmpF, DM.ok] at hc; subst hc; simp [compareOp]
  | isIn => simp [cmpF] at hc
  | notIn => simp [cmpF] at hc
  | eq =>
    simp only [cmpF] at hc
    obtain ⟨rfl, hne⟩ := lift_some hc
    exact ⟨by simp [compareOp, deepEq_flat h hx hy], hne⟩
  | notEq =>
    simp only [cmpF] at hc
    rcases bind_case hc with ⟨e, he, rfl⟩ | ⟨b, hb, he⟩
    · obtain ⟨hr, hne⟩ := lift_some he
      refine ⟨by simp [compareOp, deepEq_flat h hx hy, ← hr], fun e' he' => ?_⟩
      cases he'; exact hne _ hr.symm
    · obtain ⟨hr, -⟩ := lift_some hb
      simp [DM.ok] at he; subst he
      exact ⟨by simp [compareOp, deepEq_flat h hx hy, ← hr], fun e' he' => by cases he'⟩
  | lt | ltE | gt | gtE =>
    simp only [cmpF] at hc
    obtain ⟨rfl, hne⟩ := lift_some hc
    exact ⟨by simp [compareOp], hne⟩

theorem getItem_list_gen {h : Heap} {a : Nat} {k : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} (ho : h.objs a = some (.list k e l xs)) (hb : isByteList k e = false)
    (iv : Value) :
    getItem h (.ref a) iv = (toIndex iv).bind fun i =>
      match normIndex xs.length i with
      | some m =>
        match xs[m]? with
        | some v => .ok v
        | none => .error .indexError
      | none => .error .indexError := by
  simp only [isByteList, decide_eq_false_iff_not] at hb
  unfold getItem
  rw [ho]
  split
  · next heq => cases heq; exact absurd ⟨rfl, rfl⟩ hb
  · next heq => cases heq; rfl
  all_goals simp_all
  next hne => exact absurd rfl (hne k e l xs rfl rfl rfl)

/-- `seqBinop_none` for any library: the one in `SpecLean/Lemmas.lean` is for the SSZ model. -/
theorem seqBinop_flat {env : Env} {h : Heap} {op : BinOp} {x y : Value}
    (hx : ∀ a, x ≠ .ref a) (hy : ∀ a, y ≠ .ref a) : seqBinop env h op x y = none := by
  unfold seqBinop
  split
  · exact absurd rfl (hx _)
  · exact absurd rfl (hy _)
  · rfl

theorem eDep_pos (e : Expr) : 1 ≤ eDep e := by
  cases e <;> simp [eDep]

/-- Expressions at fuel `n`. -/
def EOK (env : Env) (h : Heap) (vs : List Value) (s : DSt) (L : Locals) (n : Nat) : Prop :=
  ∀ e r, dExpr env s e = some r → eDep e ≤ n → ExprOK h vs r (evalExpr env n L h e)

theorem error_ok {h : Heap} {vs : List Value} {e : SpecError} (hne : e ≠ .outOfFuel) :
    ExprOK h vs (.error e) (.error e) := ⟨rfl, hne⟩

theorem cmp_sound {env : Env} {h : Heap} {vs : List Value} {s : DSt} {L : Locals} {n : Nat}
    (hE : EOK env h vs s L n) :
    ∀ (rest : List (CmpOp × Expr)) (x : Value) (r : Res DRes), Flat x = true →
      dCmp env s x rest = some r → cDep rest ≤ n → ExprOK h vs r (evalCmp env n L h x rest)
  | [], x, r, _, hd, _ => by
    simp [dCmp, DM.ok] at hd; subst hd
    rw [evalCmp]; exact ⟨rfl, rfl, rfl⟩
  | (op, e) :: rest, x, r, hx, hd, hdep => by
    simp only [dCmp] at hd
    simp only [cDep] at hdep
    rw [evalCmp]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ry, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he (by omega))
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he (by omega))
      simp only [hi, Except.bind_ok']
      cases ry with
      | place _ _ => simp at hd2
      | val y =>
        obtain ⟨rfl, hy⟩ := hrel
        simp only at hd2
        rcases bind_case hd2 with ⟨err, hc, rfl⟩ | ⟨b, hc, hd3⟩
        · obtain ⟨hco, hne⟩ := cmpF_sound h hx hy hc
          simp [hco, error_ok (hne err rfl)]
        · obtain ⟨hco, -⟩ := cmpF_sound h hx hy hc
          simp only [hco, Except.bind_ok']
          cases b with
          | true => simp only [↓reduceIte] at hd3 ⊢; exact cmp_sound hE rest _ r hy hd3 (by omega)
          | false =>
            simp [DM.ok] at hd3; subst hd3
            exact ⟨rfl, rfl, rfl⟩

theorem bool_sound {env : Env} {h : Heap} {vs : List Value} {s : DSt} {L : Locals} {n : Nat}
    (hE : EOK env h vs s L n) :
    ∀ (es : List Expr) (op : BoolOp) (r : Res DRes),
      dBool env s op es = some r → lDep es ≤ n → ExprOK h vs r (evalBoolOp env n L h op es)
  | [], _, _, hd, _ => by simp [dBool] at hd
  | e :: es, op, r, hd, hdep => by
    simp only [dBool] at hd
    simp only [lDep] at hdep
    rw [evalBoolOp]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he (by omega))
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he (by omega))
      simp only [hi, Except.bind_ok']
      cases rv with
      | place _ _ => simp at hd2
      | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp only at hd2
        by_cases hes : es.isEmpty = true
        · simp [hes, DM.ok] at hd2; subst hd2
          simp [hes]; exact ⟨rfl, rfl, hv⟩
        · simp only [hes, Bool.false_eq_true, ↓reduceIte] at hd2 ⊢
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [truthyH_flat h hv, ← htr, error_ok (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp only [truthyH_flat h hv, ← htr, Except.bind_ok']
            cases op <;> cases b <;> simp only [DM.ok, Option.some.injEq] at hd3 ⊢ <;>
              first
              | exact bool_sound hE es _ r hd3 (by omega)
              | (subst hd3; exact ⟨rfl, rfl, hv⟩)

theorem name_sound {env : Env} {h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hr : RInv h vs s L) (x : Name) {r : Res DRes} (hd : dExpr env s (.name l x) = some r) :
    ExprOK h vs r ((lookupName env L x).bind fun v => pure (v, h)) := by
  simp only [dExpr] at hd
  have hl := hr.loc x
  cases hx : s.loc x with
  | some rr =>
    rw [hx] at hd hl
    simp [DM.ok] at hd; subst hd
    cases hL : L x with
    | none => rw [hL] at hl; cases hl
    | some w => rw [hL] at hl; simp [lookupName, hL]; exact ⟨rfl, hl⟩
  | none =>
    rw [hx] at hd hl
    simp only at hd
    cases hL : L x with
    | some w => rw [hL] at hl; cases hl
    | none =>
      simp only [lookupName, hL]
      unfold dGlobal at hd
      cases hg : env.globals.lookup x with
      | none => simp [hg] at hd; subst hd; exact ⟨rfl, by decide⟩
      | some g =>
        rw [hg] at hd
        cases g with
        | const v =>
          by_cases hf : Flat v = true
          · simp [hf, DM.ok] at hd; subst hd; exact ⟨rfl, rfl, hf⟩
          · simp [hf] at hd
        | configVar =>
          simp only at hd ⊢
          cases hc : env.config.lookup x with
          | none => simp [hc] at hd; subst hd; exact ⟨rfl, by decide⟩
          | some v =>
            rw [hc] at hd
            by_cases hf : Flat v = true
            · simp [hf, DM.ok] at hd; subst hd; exact ⟨rfl, rfl, hf⟩
            · simp [hf] at hd
        | _ => simp at hd

theorem expr_sound (env : Env) {h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hr : RInv h vs s L) : ∀ n, EOK env h vs s L n
  | 0, e, _, _, hdep => absurd hdep (by have := eDep_pos e; omega)
  | n + 1, e, r, hd, hdep => by
    have ih := expr_sound env hr n
    cases e with
    | name l x =>
      have := name_sound hr x hd
      rw [evalExpr]; exact this
    | int l k =>
      simp [dExpr, DM.ok] at hd; subst hd
      rw [evalExpr]; exact ⟨rfl, rfl, rfl⟩
    | bool l b =>
      simp [dExpr, DM.ok] at hd; subst hd
      rw [evalExpr]; exact ⟨rfl, rfl, rfl⟩
    | noneLit l =>
      simp [dExpr, DM.ok] at hd; subst hd
      rw [evalExpr]; exact ⟨rfl, rfl, rfl⟩
    | attr l o f =>
      simp only [dExpr] at hd
      simp only [eDep] at hdep
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (ih o _ he (by omega))
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih o _ he (by omega))
        simp only [hi, Except.bind_ok']
        cases ro with
        | val _ => simp [dAttr] at hd2
        | place k p =>
          obtain ⟨a, rfl, hat⟩ := hrel
          simp only [dAttr] at hd2
          cases hdr : s.deref k p with
          | none => simp [hdr] at hd2
          | some dd =>
            rw [hdr] at hd2
            cases dd with
            | leaf _ => simp at hd2
            | list _ _ _ _ => simp at hd2
            | cont ty ds =>
              simp only at hd2
              obtain ⟨nn, hn⟩ := deref_dec hr hat hdr
              obtain ⟨a', m, fs, ha, -, ho, hm⟩ := dec_cont hn
              cases ha
              cases hfi : fieldIndex env ty f with
              | none => simp [hfi] at hd2
              | some it =>
                obtain ⟨i, t⟩ := it
                rw [hfi] at hd2
                simp only at hd2
                cases hc : ds[i]? with
                | none => simp [hc] at hd2
                | some c =>
                  simp [hc, DM.ok] at hd2; subst hd2
                  obtain ⟨x, hx, hdx⟩ := mapM_get hm hc
                  simp [getAttr, ho, hfi, hx]
                  exact ⟨rfl, child_rel hat (by simp [okids, ho]) hx hdx⟩
    | index l o ie =>
      simp only [dExpr] at hd
      simp only [eDep] at hdep
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (ih o _ he (by omega))
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih o _ he (by omega))
        simp only [hi, Except.bind_ok']
        rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ri, he2, hd3⟩
        · obtain ⟨hi2, hne⟩ := exprOK_error (ih ie _ he2 (by omega))
          simp [hi2, error_ok hne]
        · obtain ⟨wi, hi2, hrel2⟩ := exprOK_ok (ih ie _ he2 (by omega))
          simp only [hi2, Except.bind_ok']
          cases ro with
          | val _ => simp [dIndex] at hd3
          | place k p =>
          cases ri with
          | place _ _ => simp [dIndex] at hd3
          | val iv =>
          obtain ⟨a, rfl, hat⟩ := hrel
          obtain ⟨rfl, -⟩ := hrel2
          simp only [dIndex] at hd3
          cases hdr : s.deref k p with
          | none => simp [hdr] at hd3
          | some dd =>
            rw [hdr] at hd3
            cases dd with
            | leaf _ => simp at hd3
            | cont _ _ => simp at hd3
            | list kd el ll ds =>
              simp only at hd3
              obtain ⟨nn, hn⟩ := deref_dec hr hat hdr
              obtain ⟨a', m, xs, ha, -, ho, hm⟩ := dec_list hn
              cases ha
              have hlen := ((mapM_some_iff xs ds).mp hm).1
              cases hb : isByteList kd el with
              | true => simp [hb] at hd3
              | false =>
                simp only [hb, Bool.false_eq_true, ↓reduceIte] at hd3
                rw [getItem_list_gen ho hb]
                rcases bind_case hd3 with ⟨err, ht, rfl⟩ | ⟨j, ht, hd4⟩
                · obtain ⟨htr, hne⟩ := lift_some ht
                  simp [← htr, error_ok (hne err htr.symm)]
                · obtain ⟨htr, -⟩ := lift_some ht
                  simp only [← htr, Except.bind_ok']
                  rw [hlen] at hd4
                  cases hni : normIndex xs.length j with
                  | none =>
                    simp [hni] at hd4; subst hd4
                    simp [hni]
                    exact ⟨rfl, by decide⟩
                  | some mm =>
                    simp only [hni] at hd4
                    cases hc : ds[mm]? with
                    | none => simp [hc] at hd4
                    | some c =>
                      simp [hc, DM.ok] at hd4; subst hd4
                      obtain ⟨x, hx, hdx⟩ := mapM_get hm hc
                      simp [hni, hx]
                      exact ⟨rfl, child_rel hat (by simp [okids, ho]) hx hdx⟩
    | binop l op a b =>
      simp only [dExpr] at hd
      simp only [eDep] at hdep
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (ih a _ he (by omega))
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih a _ he (by omega))
        simp only [hi, Except.bind_ok']
        rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨rb, he2, hd3⟩
        · obtain ⟨hi2, hne⟩ := exprOK_error (ih b _ he2 (by omega))
          simp [hi2, error_ok hne]
        · obtain ⟨wb, hi2, hrel2⟩ := exprOK_ok (ih b _ he2 (by omega))
          simp only [hi2, Except.bind_ok']
          cases ra with
          | place _ _ => simp [dBinop] at hd3
          | val x =>
          cases rb with
          | place _ _ => simp [dBinop] at hd3
          | val y =>
          obtain ⟨rfl, hx⟩ := hrel
          obtain ⟨rfl, hy⟩ := hrel2
          simp only [dBinop] at hd3
          rw [seqBinop_flat (flat_nonref hx) (flat_nonref hy)]
          rcases bind_case hd3 with ⟨err, ht, rfl⟩ | ⟨v, ht, hd4⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [← htr, error_ok (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp only [← htr, Except.bind_ok']
            by_cases hv : Flat v = true
            · simp [hv, DM.ok] at hd4; subst hd4; exact ⟨rfl, rfl, hv⟩
            · simp [hv] at hd4
    | compare l a rest =>
      simp only [dExpr] at hd
      simp only [eDep] at hdep
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (ih a _ he (by omega))
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih a _ he (by omega))
        simp only [hi, Except.bind_ok']
        cases ra with
        | place _ _ => simp at hd2
        | val x =>
          obtain ⟨rfl, hx⟩ := hrel
          exact cmp_sound ih rest _ r hx hd2 (by omega)
    | boolop l op es =>
      simp only [dExpr] at hd
      simp only [eDep] at hdep
      rw [evalExpr]
      exact bool_sound ih es op r hd (by omega)
    | _ => simp [dExpr] at hd

end SpecLean.Layer4
