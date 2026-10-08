import SpecLean.Layer4.Expr

/-!
# Layer 4 spike: the fragment theorem

`denote_sound`: for every function of the fragment, every heap and every arguments that decode
to the denotation's inputs, under `WTree` over the footprint `fp`, the interpreter with enough
fuel gives a result that `ResultMatches` the denotation: the same error class, or the return
value and every argument decoded in the result heap, with the frame, fresh addresses and no new
paths. Proved once, by induction on the fuel.

The library must coerce a flat value without the heap (`CoerceFlat`). The SSZ model does
(`SpecLean/Layer4/Examples.lean`).
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

/-- The coercion of a flat value needs no heap. -/
def CoerceFlat (env : Env) : Prop :=
  ∀ field h t v, Flat v = true →
    coerceWith env field h t v = (fun x => (x.1, h)) <$> coerceWith env field Heap.empty t v

/-- The interpreter's result of a statement agrees with the denotation's. -/
def StmtOK (fp : Footprint) (h0 : Heap) (vs : List Value) :
    Res (Outcome × DSt) → Res (Outcome × Locals × Heap) → Prop
  | .ok (o, s'), .ok (o', L', h') => o' = o ∧ SInv fp h0 h' vs s' L'
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem stmtOK_err {fp : Footprint} {h0 : Heap} {vs : List Value} {e : SpecError}
    (hne : e ≠ .outOfFuel) : StmtOK fp h0 vs (.error e) (.error e) := ⟨rfl, hne⟩

theorem dCoerce_some {env : Env} (hcf : CoerceFlat env) {field : Bool} {t : SszTy} {v : Value}
    (hv : Flat v = true) {r : Res Value} (hc : dCoerce env field t v = some r) (h : Heap) :
    (∀ e, r = .error e → coerceWith env field h t v = .error e ∧ e ≠ .outOfFuel) ∧
    (∀ v', r = .ok v' → coerceWith env field h t v = .ok (v', h)) := by
  unfold dCoerce at hc
  obtain ⟨hr, hne⟩ := lift_some hc
  rw [hcf field h t v hv]
  subst hr
  cases hk : coerceWith env field Heap.empty t v with
  | error e =>
    exact ⟨fun e' he' => (by cases he'; exact ⟨rfl, hne e (by rw [hk]; rfl)⟩),
      fun v' hv' => (by cases hv')⟩
  | ok q =>
    exact ⟨fun e' he' => (by cases he'), fun v' hv' => (by cases hv'; rfl)⟩

theorem tDep_pos (t : Target) : 1 ≤ tDep t := by
  cases t <;> simp [tDep]

theorem sDep_pos (s : Stmt) : 1 ≤ sDep s := by
  cases s with
  | assign l ts e => cases ts with
    | nil => simp [sDep]
    | cons t rest => cases rest <;> simp [sDep]
  | ret l e => cases e <;> simp [sDep]
  | _ => simp [sDep]

/-- A write through a place: the interpreter's `h.set` agrees with `dWrite`. -/
theorem dWrite_sound {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : SInv fp h0 h vs s L) {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) {i : Nat} {v' : Value} {res : Res (Outcome × DSt)}
    (hw : dWrite fp s k p i v' = some res) {o : HeapObj} (ho : h.objs a = some o) (hwf0 : HeapWF h0) :
    StmtOK fp h0 vs res (.ok (.normal, L, h.set a (o.setChild i v'))) := by
  unfold dWrite at hw
  cases hrk : s.roots[k]? with
  | none => simp [hrk] at hw
  | some d =>
    rw [hrk] at hw
    simp only at hw
    by_cases hc : (Flat v' && fpOk fp s.roots k p && leafAt d p i) = true
    · rw [if_pos hc] at hw
      simp [DM.ok] at hw; subst hw
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hf, hfp⟩, hl⟩ := hc
      exact ⟨rfl, write_inv hI hat hrk hf hfp hl ho hwf0⟩
    · rw [if_neg hc] at hw; cases hw

/-- Assignment to a target, after the value is evaluated. -/
theorem assign_sound (env : Env) (hcf : CoerceFlat env) {fp : Footprint} {h0 h : Heap}
    {vs : List Value} {s : DSt} {L : Locals} (hI : SInv fp h0 h vs s L) (t : Target) {r : DRes}
    {w : Value} (hr : ERel h vs r w) {res : Res (Outcome × DSt)}
    (hd : dAssign env fp s t r = some res) (n : Nat) (hdep : tDep t ≤ n) (hwf0 : HeapWF h0) :
    StmtOK fp h0 vs res ((assignTarget env n L h t w).bind fun p => pure (.normal, p.1, p.2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := tDep_pos t; omega⟩
  have hE := expr_sound env hI.r m
  cases t with
  | name l x =>
    simp [dAssign, DM.ok] at hd; subst hd
    rw [assignTarget]
    exact ⟨rfl, setLoc_inv hI x hr⟩
  | attr l o f =>
    simp only [tDep] at hdep
    cases r with
    | tree _ => simp [dAssign] at hd
    | place _ _ => simp [dAssign] at hd
    | val v =>
    obtain ⟨rfl, hv⟩ := hr
    simp only [dAssign] at hd
    rw [assignTarget]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE o _ he (by omega))
      simp [hi, stmtOK_err hne]
    · obtain ⟨wo, hi, hrel⟩ := exprOK_ok (hE o _ he (by omega))
      simp only [hi, exb_ok, Except.bind_ok']
      cases ro with
      | tree _ => simp at hd2
      | val _ => simp at hd2
      | place k p =>
      obtain ⟨a, rfl, hat⟩ := hrel
      simp only at hd2
      cases hdr : s.deref k p with
      | none => simp [hdr] at hd2
      | some dd =>
      rw [hdr] at hd2
      cases dd with
      | leaf _ => simp at hd2
      | list _ _ _ _ => simp at hd2
      | cont ty ds =>
      simp only at hd2
      obtain ⟨nn, hn⟩ := deref_dec hI.r hat hdr
      obtain ⟨a', mm, fs, ha, -, ho, -⟩ := dec_cont hn
      cases ha
      cases hfi : fieldIndex env ty f with
      | none => simp [hfi] at hd2
      | some it =>
      obtain ⟨i, ft⟩ := it
      rw [hfi] at hd2
      simp only at hd2
      simp only [setAttr, ho, hfi]
      rcases bind_case hd2 with ⟨err, hc, rfl⟩ | ⟨v', hc, hd3⟩
      · obtain ⟨h1, -⟩ := dCoerce_some hcf hv hc h
        obtain ⟨hco, hne⟩ := h1 err rfl
        simp [hco, stmtOK_err hne]
      · obtain ⟨-, h2⟩ := dCoerce_some hcf hv hc h
        simp only [h2 v' rfl, exb_ok, Except.bind_ok']
        exact dWrite_sound hI hat hd3 (o := .container ty fs) ho hwf0
  | index l o ie =>
    simp only [tDep] at hdep
    cases r with
    | tree _ => simp [dAssign] at hd
    | place _ _ => simp [dAssign] at hd
    | val v =>
    obtain ⟨rfl, hv⟩ := hr
    simp only [dAssign] at hd
    rw [assignTarget]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE o _ he (by omega))
      simp [hi, stmtOK_err hne]
    · obtain ⟨wo, hi, hrel⟩ := exprOK_ok (hE o _ he (by omega))
      simp only [hi, exb_ok, Except.bind_ok']
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ri, he2, hd3⟩
      · obtain ⟨hi2, hne⟩ := exprOK_error (hE ie _ he2 (by omega))
        simp [hi2, stmtOK_err hne]
      · obtain ⟨wi, hi2, hrel2⟩ := exprOK_ok (hE ie _ he2 (by omega))
        simp only [hi2, exb_ok, Except.bind_ok']
        cases ro with
        | tree _ => simp at hd3
        | val _ => simp at hd3
        | place k p =>
        cases ri with
        | tree _ => simp at hd3
        | place _ _ => simp at hd3
        | val iv =>
        obtain ⟨a, rfl, hat⟩ := hrel
        obtain ⟨rfl, -⟩ := hrel2
        simp only at hd3
        cases hdr : s.deref k p with
        | none => simp [hdr] at hd3
        | some dd =>
        rw [hdr] at hd3
        cases dd with
        | leaf _ => simp at hd3
        | cont _ _ => simp at hd3
        | list kd el ll ds =>
        simp only at hd3
        obtain ⟨nn, hn⟩ := deref_dec hI.r hat hdr
        obtain ⟨a', mm, xs, ha, -, ho, hm⟩ := dec_list hn
        cases ha
        have hlen := ((mapM_some_iff xs ds).mp hm).1
        cases hb : isByteList kd el with
        | true => simp [hb] at hd3
        | false =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at hd3
        have hnb : ¬(kd = .list ∧ el = .uint (.width 8)) := by
          simpa [isByteList] using hb
        simp only [setItem, ho, if_neg hnb]
        rcases bind_case hd3 with ⟨err, ht, rfl⟩ | ⟨j, ht, hd4⟩
        · obtain ⟨htr, hne⟩ := lift_some ht
          simp [← htr, stmtOK_err (hne err htr.symm)]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [← htr, exb_ok, Except.bind_ok']
          rcases bind_case hd4 with ⟨err, hc, rfl⟩ | ⟨v', hc, hd5⟩
          · obtain ⟨h1, -⟩ := dCoerce_some hcf hv hc h
            obtain ⟨hco, hne⟩ := h1 err rfl
            simp [hco, stmtOK_err hne]
          · obtain ⟨-, h2⟩ := dCoerce_some hcf hv hc h
            simp only [h2 v' rfl, exb_ok, Except.bind_ok']
            rw [hlen] at hd5
            cases hni : normIndex xs.length j with
            | none =>
              simp [hni] at hd5; subst hd5
              simp; exact stmtOK_err (by decide)
            | some mi =>
              simp only [hni] at hd5 ⊢
              exact dWrite_sound hI hat hd5 (o := .list kd el ll xs) ho hwf0
  | _ => simp [dAssign] at hd

/-- `obj[i] op= e`. -/
theorem aug_sound (env : Env) (hcf : CoerceFlat env) {fp : Footprint} {h0 h : Heap}
    {vs : List Value} {s : DSt} {L : Locals} (hI : SInv fp h0 h vs s L) (l l' : Line) (o ie : Expr)
    (op : BinOp) (e : Expr) {res : Res (Outcome × DSt)}
    (hd : dAugIndex env fp s o ie op e = some res) (n : Nat)
    (hdep : max (eDep o) (eDep ie) ≤ n) (hdep2 : eDep e ≤ n) (hwf0 : HeapWF h0) :
    StmtOK fp h0 vs res (execStmt env (n + 1) L h (.augAssign l (.index l' o ie) op e)) := by
  have hE := expr_sound env hI.r n
  rw [execStmt]
  simp only
  unfold dAugIndex at hd
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
  · obtain ⟨hi, hne⟩ := exprOK_error (hE o _ he (by omega))
    simp [hi, stmtOK_err hne]
  · obtain ⟨wo, hi, hrel⟩ := exprOK_ok (hE o _ he (by omega))
    simp only [hi, exb_ok, Except.bind_ok']
    rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ri, he2, hd3⟩
    · obtain ⟨hi2, hne⟩ := exprOK_error (hE ie _ he2 (by omega))
      simp [hi2, stmtOK_err hne]
    · obtain ⟨wi, hi2, hrel2⟩ := exprOK_ok (hE ie _ he2 (by omega))
      simp only [hi2, exb_ok, Except.bind_ok']
      cases ro with
      | tree _ => simp at hd3
      | val _ => simp at hd3
      | place k p =>
      cases ri with
      | tree _ => simp at hd3
      | place _ _ => simp at hd3
      | val iv =>
      obtain ⟨a, rfl, hat⟩ := hrel
      obtain ⟨rfl, -⟩ := hrel2
      simp only at hd3
      cases hdr : s.deref k p with
      | none => simp [hdr] at hd3
      | some dd =>
      rw [hdr] at hd3
      cases dd with
      | leaf _ => simp at hd3
      | cont _ _ => simp at hd3
      | list kd el ll ds =>
      simp only at hd3
      obtain ⟨nn, hn⟩ := deref_dec hI.r hat hdr
      obtain ⟨a', mm, xs, ha, -, ho, hm⟩ := dec_list hn
      cases ha
      have hlen := ((mapM_some_iff xs ds).mp hm).1
      cases hb : isByteList kd el with
      | true => simp [hb] at hd3
      | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hd3
      have hnb : ¬(kd = .list ∧ el = .uint (.width 8)) := by
        simpa [isByteList] using hb
      rw [getItem_list_gen ho hb]
      rcases bind_case hd3 with ⟨err, ht, rfl⟩ | ⟨j, ht, hd4⟩
      · obtain ⟨htr, hne⟩ := lift_some ht
        simp [← htr, stmtOK_err (hne err htr.symm)]
      · obtain ⟨htr, -⟩ := lift_some ht
        simp only [← htr, exb_ok, Except.bind_ok']
        rw [hlen] at hd4
        cases hni : normIndex xs.length j with
        | none =>
          simp [hni] at hd4; subst hd4
          simp; exact stmtOK_err (by decide)
        | some mi =>
        simp only [hni] at hd4 ⊢
        cases hc : ds[mi]? with
        | none => simp [hc] at hd4
        | some c =>
        cases c with
        | cont _ _ => simp [hc] at hd4
        | list _ _ _ _ => simp [hc] at hd4
        | leaf cur =>
        simp only [hc] at hd4
        obtain ⟨x, hx, hdx⟩ := mapM_get hm hc
        obtain ⟨rfl, -⟩ := dec_leaf hdx
        simp only [hx, exb_ok, Except.bind_ok']
        rcases bind_case hd4 with ⟨err, he3, rfl⟩ | ⟨re, he3, hd5⟩
        · obtain ⟨hi3, hne⟩ := exprOK_error (hE e _ he3 hdep2)
          simp [hi3, stmtOK_err hne]
        · obtain ⟨we, hi3, hrel3⟩ := exprOK_ok (hE e _ he3 hdep2)
          simp only [hi3, exb_ok, Except.bind_ok']
          cases re with
          | tree _ => simp at hd5
          | place _ _ => simp at hd5
          | val rv =>
          obtain ⟨rfl, -⟩ := hrel3
          simp only at hd5
          rcases bind_case hd5 with ⟨err, hbv, rfl⟩ | ⟨v, hbv, hd6⟩
          · obtain ⟨hbr, hne⟩ := lift_some hbv
            simp [← hbr, stmtOK_err (hne err hbr.symm)]
          · obtain ⟨hbr, -⟩ := lift_some hbv
            simp only [← hbr, exb_ok, Except.bind_ok']
            by_cases hv : Flat v = true
            · rw [if_pos hv] at hd6
              simp only [setItem, ho, if_neg hnb, ← htr, exb_ok, Except.bind_ok']
              rcases bind_case hd6 with ⟨err, hcv, rfl⟩ | ⟨v', hcv, hd7⟩
              · obtain ⟨h1, -⟩ := dCoerce_some hcf hv hcv h
                obtain ⟨hco, hne⟩ := h1 err rfl
                simp [hco, stmtOK_err hne]
              · obtain ⟨-, h2⟩ := dCoerce_some hcf hv hcv h
                simp only [h2 v' rfl, exb_ok, hni]
                exact dWrite_sound hI hat hd7 (o := .list kd el ll xs) ho hwf0
            · rw [if_neg hv] at hd6; cases hd6

/-- Statements at fuel `n`. -/
def SOK (env : Env) (fp : Footprint) (h0 : Heap) (vs : List Value) (n : Nat) : Prop :=
  ∀ st s L h r, SInv fp h0 h vs s L → dStmt env fp s st = some r → sDep st ≤ n →
    StmtOK fp h0 vs r (execStmt env n L h st)

def BOK (env : Env) (fp : Footprint) (h0 : Heap) (vs : List Value) (n : Nat) : Prop :=
  ∀ ss s L h r, SInv fp h0 h vs s L → dBlock env fp s ss = some r → bDep ss ≤ n →
    StmtOK fp h0 vs r (execBlock env n L h ss)

theorem block_sound {env : Env} {fp : Footprint} {h0 : Heap} {vs : List Value} {n : Nat}
    (hS : SOK env fp h0 vs n) : BOK env fp h0 vs n
  | [], s, L, h, r, hI, hd, _ => by
    simp [dBlock, DM.ok] at hd; subst hd
    rw [execBlock]; exact ⟨rfl, hI⟩
  | st :: ss, s, L, h, r, hI, hd, hdep => by
    simp only [dBlock] at hd
    simp only [bDep] at hdep
    rw [execBlock]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨⟨o, s1⟩, he, hd2⟩
    · have := hS st s L h _ hI he (by omega)
      revert this
      cases execStmt env n L h st with
      | error e' => rintro ⟨rfl, hne⟩; exact stmtOK_err hne
      | ok q => intro h; cases h
    · have := hS st s L h _ hI he (by omega)
      revert this
      cases hx : execStmt env n L h st with
      | error e' => intro h; cases h
      | ok q =>
        obtain ⟨o', L1, h1⟩ := q
        rintro ⟨rfl, hI1⟩
        simp only [exb_ok, Except.bind_ok']
        cases o' with
        | normal => exact block_sound hS ss s1 L1 h1 r hI1 hd2 (by omega)
        | _ => simp [DM.ok] at hd2; subst hd2; exact ⟨rfl, hI1⟩

theorem stmt_sound (env : Env) (hcf : CoerceFlat env) (fp : Footprint) (h0 : Heap)
    (vs : List Value) (hwf0 : HeapWF h0) : ∀ n, SOK env fp h0 vs n
  | 0, st, _, _, _, _, _, _, hdep => absurd hdep (by have := sDep_pos st; omega)
  | n + 1, st, s, L, h, r, hI, hd, hdep => by
    have hB := block_sound (stmt_sound env hcf fp h0 vs hwf0 n)
    have hE := expr_sound env hI.r n
    cases st with
    | assign l ts e =>
      match ts, hd, hdep with
      | [t], hd, hdep =>
        simp only [dStmt] at hd
        simp only [sDep] at hdep
        rw [execStmt]
        rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
        · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he (by omega))
          simp [hi, stmtOK_err hne]
        · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he (by omega))
          simp only [hi, exb_ok, Except.bind_ok']
          have := assign_sound env hcf hI t hrel hd2 n (by omega) hwf0
          revert this
          cases assignTarget env n L h t w with
          | error e' => simp
          | ok q => simp
      | [], hd, _ => simp [dStmt] at hd
      | _ :: _ :: _, hd, _ => simp [dStmt] at hd
    | annAssign l t e =>
      simp only [dStmt] at hd
      simp only [sDep] at hdep
      rw [execStmt]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he (by omega))
        simp [hi, stmtOK_err hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he (by omega))
        simp only [hi, exb_ok, Except.bind_ok']
        have := assign_sound env hcf hI t hrel hd2 n (by omega) hwf0
        revert this
        cases assignTarget env n L h t w with
        | error e' => simp
        | ok q => simp
    | augAssign l t op e =>
      cases t with
      | index l' o ie =>
        simp only [dStmt] at hd
        simp only [sDep, tDep] at hdep
        exact aug_sound env hcf hI l l' o ie op e hd n (by omega) (by omega) hwf0
      | _ => simp [dStmt] at hd
    | ifStmt l c thn els =>
      simp only [dStmt] at hd
      simp only [sDep] at hdep
      rw [execStmt]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (hE c _ he (by omega))
        simp [hi, stmtOK_err hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE c _ he (by omega))
        simp only [hi, exb_ok, Except.bind_ok']
        cases rv with
        | tree _ => simp at hd2
        | place _ _ => simp at hd2
        | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp only at hd2
        rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
        · obtain ⟨htr, hne⟩ := lift_some ht
          simp [truthyH_flat h hv, ← htr, stmtOK_err (hne err htr.symm)]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [truthyH_flat h hv, ← htr, exb_ok, Except.bind_ok']
          cases b with
          | true => simp only [↓reduceIte] at hd3 ⊢; exact hB thn s L h r hI hd3 (by omega)
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at hd3 ⊢
            exact hB els s L h r hI hd3 (by omega)
    | ret l oe =>
      cases oe with
      | none =>
        simp [dStmt, DM.ok] at hd; subst hd
        rw [execStmt]; exact ⟨rfl, hI⟩
      | some e =>
        simp only [dStmt] at hd
        simp only [sDep] at hdep
        rw [execStmt]
        rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
        · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he (by omega))
          simp [hi, stmtOK_err hne]
        · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he (by omega))
          simp only [hi, exb_ok, Except.bind_ok']
          cases rv with
          | tree _ => simp at hd2
          | place _ _ => simp at hd2
          | val v =>
          obtain ⟨rfl, -⟩ := hrel
          simp [DM.ok] at hd2; subst hd2
          exact ⟨rfl, hI⟩
    | assert l e =>
      simp only [dStmt] at hd
      simp only [sDep] at hdep
      rw [execStmt]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he (by omega))
        simp [hi, stmtOK_err hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he (by omega))
        simp only [hi, exb_ok, Except.bind_ok']
        cases rv with
        | tree _ => simp at hd2
        | place _ _ => simp at hd2
        | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp only at hd2
        rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
        · obtain ⟨htr, hne⟩ := lift_some ht
          simp [truthyH_flat h hv, ← htr, stmtOK_err (hne err htr.symm)]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [truthyH_flat h hv, ← htr, exb_ok, Except.bind_ok']
          cases b with
          | true => simp [DM.ok] at hd3; subst hd3; exact ⟨rfl, hI⟩
          | false => simp at hd3; subst hd3; exact stmtOK_err (by decide)
    | pass l =>
      simp [dStmt, DM.ok] at hd; subst hd
      rw [execStmt]; exact ⟨rfl, hI⟩
    | _ => simp [dStmt] at hd

end SpecLean.Layer4
