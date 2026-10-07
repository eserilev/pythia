import SpecLean.Layer4.DenExpr

/-!
# Layer 4: statements with calls, and the theorem for the fragment with calls

`level_ok`: by induction on the fuel, every part of `den env fps n` agrees with the interpreter
at fuel `n`. A call at statement level may write: `call_rule` puts the callee's tree back into
the caller's. `denote_sound_calls` is the contract of SPEC 9.2 for a function of the fragment.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode SpecLean.Validation.Where

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

theorem orel_cases {lo : Nat} {h : Heap} {vs : List Value} {o : DOut} {o' : Outcome}
    (hr : ORel lo h vs o o') :
    (o = .normal ∧ o' = .normal) ∨ (o = .brk ∧ o' = .brk) ∨ (o = .cont ∧ o' = .cont) ∨
      ∃ r w, o = .ret r ∧ o' = .ret w ∧ ERel h vs r w ∧ TLo lo h r w := by
  cases o <;> cases o' <;> simp_all [ORel]

theorem initLoc_tree {roots : List DV} :
    ∀ (xs : List (Name × Nat)) (dl : Name → Option DRes) (x : Name) (d : DV),
      initLoc roots dl xs x = some (.tree d) → dl x = some (.tree d)
  | [], dl, x, d, h => h
  | (y, i) :: rest, dl, x, d, h => by
    have := initLoc_tree rest _ x d h
    simp only [setLoc] at this
    split at this
    · simp only [slot] at this
      split at this <;> simp at this
    · exact this

/-- A new local keeps the invariant. A tree in it is new. -/
theorem dWrite_csound {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) {k : Nat} {p : List Nat} {a : Nat}
    (hat : at? h vs k p = some (.ref a)) {i : Nat} {v' : Value} {res : Res (DOut × DSt)}
    (hw : dWriteD fp s k p i v' = some res) {o : HeapObj} (ho : h.objs a = some o) :
    CStmtOK fp h0 vs res (.ok (.normal, L, h.set a (o.setChild i v'))) := by
  unfold dWriteD dWrite at hw
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
      exact ⟨trivial, write_cinv hI hat hrk hf hfp hl ho⟩
    · rw [if_neg hc] at hw; cases hw

/-- Assignment to a target, after the value is evaluated. -/
theorem targetStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {m : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L m ((den env fps m).expr fp s)) (t : Target)
    {r : DRes} {w : Value} (hr : ERel h vs r w) (hlo : TLo h0.next h r w) {res : Res (DOut × DSt)}
    (hd : targetStep env (den env fps m) fp s t r = some res) :
    CStmtOK fp h0 vs res ((assignTarget env (m + 1) L h t w).bind fun p => pure (.normal, p.1, p.2)) := by
  cases t with
  | name l x =>
    simp [targetStep, DM.ok] at hd; subst hd
    rw [assignTarget]
    exact ⟨trivial, hI.setLoc x hr hlo⟩
  | attr l o f =>
        cases r with
    | place _ _ => simp [targetStep] at hd
    | tree _ => simp [targetStep] at hd
    | val v =>
    obtain ⟨rfl, hv⟩ := hr
    simp only [targetStep] at hd
    rw [assignTarget]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (ih h hI o _ he)
      simp [hi, cstmtOK_err hne]
    · obtain ⟨wo, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI o _ he)
      have hI1 := hI.ext hx1
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
      obtain ⟨nn, hn⟩ := deref_dec hI1.i.r hat hdr
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
      · obtain ⟨hc1, -⟩ := dCoerce_some hlf.coerce hv hc h1
        obtain ⟨hco, hne⟩ := hc1 err rfl
        simp [hco, cstmtOK_err hne]
      · obtain ⟨-, hc2⟩ := dCoerce_some hlf.coerce hv hc h1
        simp only [hc2 v' rfl, exb_ok, Except.bind_ok']
        exact dWrite_csound hI1 hat hd3 (o := .container ty fs) ho
  | index l o ie =>
        cases r with
    | place _ _ => simp [targetStep] at hd
    | tree _ => simp [targetStep] at hd
    | val v =>
    obtain ⟨rfl, hv⟩ := hr
    simp only [targetStep] at hd
    rw [assignTarget]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (ih h hI o _ he)
      simp [hi, cstmtOK_err hne]
    · obtain ⟨wo, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI o _ he)
      have hI1 := hI.ext hx1
      simp only [hi, exb_ok, Except.bind_ok']
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ri, he2, hd3⟩
      · obtain ⟨hi2, hne⟩ := gok_error (ih h1 hI1 ie _ he2)
        simp [hi2, cstmtOK_err hne]
      · obtain ⟨wi, h2, hi2, hx2, hrel2⟩ := gok_ok (ih h1 hI1 ie _ he2)
        have hI2 := hI1.ext hx2
        simp only [hi2, exb_ok, Except.bind_ok']
        cases ro with
        | tree _ => simp at hd3
        | val _ => simp at hd3
        | place k p =>
        cases ri with
        | tree _ => simp at hd3
        | place _ _ => simp at hd3
        | val iv =>
        obtain ⟨a, rfl, hat⟩ := ERel_ext hI1.wf hI1.below hx2 hrel
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
        obtain ⟨nn, hn⟩ := deref_dec hI2.i.r hat hdr
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
          simp [← htr, cstmtOK_err (hne err htr.symm)]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [← htr, exb_ok, Except.bind_ok']
          rcases bind_case hd4 with ⟨err, hc, rfl⟩ | ⟨v', hc, hd5⟩
          · obtain ⟨hc1, -⟩ := dCoerce_some hlf.coerce hv hc h2
            obtain ⟨hco, hne⟩ := hc1 err rfl
            simp [hco, cstmtOK_err hne]
          · obtain ⟨-, hc2⟩ := dCoerce_some hlf.coerce hv hc h2
            simp only [hc2 v' rfl, exb_ok, Except.bind_ok']
            rw [hlen] at hd5
            cases hni : normIndex xs.length j with
            | none =>
              simp [hni] at hd5; subst hd5
              simp; exact cstmtOK_err (by decide)
            | some mi =>
              simp only [hni] at hd5 ⊢
              exact dWrite_csound hI2 hat hd5 (o := .list kd el ll xs) ho
  | _ => simp [targetStep] at hd

/-- `x op= e` on a local. -/
theorem augName_sound (env : Env) (fps : Name → Footprint) {n : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L n ((den env fps n).expr fp s)) (l l' : Line)
    (x : Name) (op : BinOp) (e : Expr) {res : Res (DOut × DSt)}
    (hd : augName (den env fps n) fp s x op e = some res) :
    CStmtOK fp h0 vs res (execStmt env (n + 1) L h (.augAssign l (.name l' x) op e)) := by
  unfold augName at hd
  cases hx : s.loc x with
  | none => rw [hx] at hd; cases hd
  | some r0 =>
  rw [hx] at hd
  cases r0 with
  | place _ _ => cases hd
  | tree _ => cases hd
  | val cur =>
  simp only at hd
  have hl := hI.i.r.loc x
  rw [hx] at hl
  cases hLx : L x with
  | none => rw [hLx] at hl; exact hl.elim
  | some w0 =>
  rw [hLx] at hl
  obtain ⟨rfl, hcur⟩ := hl
  have hlk : lookupName env L x = .ok w0 := by simp [lookupName, hLx]
  rw [execStmt]
  simp only [hlk, Except.bind_ok']
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rr, he, hd2⟩
  · obtain ⟨hi, hne⟩ := gok_error (ih h hI e _ he)
    simp [hi, cstmtOK_err hne]
  · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI e _ he)
    have hI1 := hI.ext hx1
    simp only [hi, Except.bind_ok']
    cases rr with
    | place _ _ => cases hd2
    | tree _ => cases hd2
    | val rv =>
    obtain ⟨rfl, hrv⟩ := hrel
    simp only at hd2
    have hsa : seqAugAdd h1 op w0 w = none := by
      unfold seqAugAdd; split
      · exact absurd rfl (flat_nonref hcur _)
      · rfl
    rw [hsa, seqBinop_flat (flat_nonref hcur) (flat_nonref hrv)]
    simp only
    rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨v, ht, hd3⟩
    · obtain ⟨htr, hne⟩ := lift_some ht
      simp [← htr, cstmtOK_err (hne err htr.symm)]
    · obtain ⟨htr, -⟩ := lift_some ht
      simp only [← htr, Except.bind_ok']
      by_cases hv : Flat v = true
      · simp [hv, DM.ok] at hd3; subst hd3
        exact ⟨trivial, hI1.setLoc x ⟨rfl, hv⟩ trivial⟩
      · simp [hv] at hd3

/-- `obj[i] op= e`. -/
theorem augStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L n ((den env fps n).expr fp s)) (l l' : Line)
    (o ie : Expr) (op : BinOp) (e : Expr) {res : Res (DOut × DSt)}
    (hd : augStep env (den env fps n) fp s o ie op e = some res) :
    CStmtOK fp h0 vs res (execStmt env (n + 1) L h (.augAssign l (.index l' o ie) op e)) := by
  rw [execStmt]
  simp only
  unfold augStep at hd
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
  · obtain ⟨hi, hne⟩ := gok_error (ih h hI o _ he)
    simp [hi, cstmtOK_err hne]
  · obtain ⟨wo, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI o _ he)
    have hI1 := hI.ext hx1
    simp only [hi, exb_ok, Except.bind_ok']
    rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ri, he2, hd3⟩
    · obtain ⟨hi2, hne⟩ := gok_error (ih h1 hI1 ie _ he2)
      simp [hi2, cstmtOK_err hne]
    · obtain ⟨wi, h2, hi2, hx2, hrel2⟩ := gok_ok (ih h1 hI1 ie _ he2)
      have hI2 := hI1.ext hx2
      simp only [hi2, exb_ok, Except.bind_ok']
      cases ro with
      | tree _ => simp at hd3
      | val _ => simp at hd3
      | place k p =>
      cases ri with
      | tree _ => simp at hd3
      | place _ _ => simp at hd3
      | val iv =>
      obtain ⟨a, rfl, hat⟩ := ERel_ext hI1.wf hI1.below hx2 hrel
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
      obtain ⟨nn, hn⟩ := deref_dec hI2.i.r hat hdr
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
        simp [← htr, cstmtOK_err (hne err htr.symm)]
      · obtain ⟨htr, -⟩ := lift_some ht
        simp only [← htr, exb_ok, Except.bind_ok']
        rw [hlen] at hd4
        cases hni : normIndex xs.length j with
        | none =>
          simp [hni] at hd4; subst hd4
          simp; exact cstmtOK_err (by decide)
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
        · obtain ⟨hi3, hne⟩ := gok_error (ih h2 hI2 e _ he3)
          simp [hi3, cstmtOK_err hne]
        · obtain ⟨we, h3, hi3, hx3, hrel3⟩ := gok_ok (ih h2 hI2 e _ he3)
          have hI3 := hI2.ext hx3
          have hat3 : at? h3 vs k p = some (.ref a) :=
            (at?_Skel (Skel_of_Ext hx3) hI2.below k p a).mpr hat
          have ho3 : h3.objs a = some (.list kd el ll xs) :=
            (hx3.2.2 a (at?_below hI2.below hat)).trans ho
          simp only [hi3, exb_ok, Except.bind_ok']
          cases re with
          | tree _ => simp at hd5
          | place _ _ => simp at hd5
          | val rv =>
          obtain ⟨rfl, -⟩ := hrel3
          simp only at hd5
          rcases bind_case hd5 with ⟨err, hbv, rfl⟩ | ⟨v, hbv, hd6⟩
          · obtain ⟨hbr, hne⟩ := lift_some hbv
            simp [← hbr, cstmtOK_err (hne err hbr.symm)]
          · obtain ⟨hbr, -⟩ := lift_some hbv
            simp only [← hbr, exb_ok, Except.bind_ok']
            by_cases hv : Flat v = true
            · rw [if_pos hv] at hd6
              simp only [setItem, ho3, if_neg hnb, ← htr, exb_ok, Except.bind_ok']
              rcases bind_case hd6 with ⟨err, hcv, rfl⟩ | ⟨v', hcv, hd7⟩
              · obtain ⟨hc1, -⟩ := dCoerce_some hlf.coerce hv hcv h3
                obtain ⟨hco, hne⟩ := hc1 err rfl
                simp [hco, cstmtOK_err hne]
              · obtain ⟨-, hc2⟩ := dCoerce_some hlf.coerce hv hcv h3
                simp only [hc2 v' rfl, exb_ok, hni]
                exact dWrite_csound hI3 hat3 hd7 (o := .list kd el ll xs) ho3
            · rw [if_neg hv] at hd6; cases hd6


theorem bind_map {x : DM α} {f : α → DM β} (g : β → γ) :
    DM.bind x (fun a => (f a).map (·.map g)) = (DM.bind x f).map (·.map g) := by
  cases x with
  | none => rfl
  | some r => cases r <;> rfl

theorem callOK_of_exprOK {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) {r0 : Res DRes} {res : Res (Value × Heap)}
    (he : GOK h0.next h vs r0 res) : CallOK fp h0 vs s L (r0.map (·, s.roots)) res := by
  cases r0 with
  | error e => obtain ⟨hr, hne⟩ := gok_error he; subst hr; exact ⟨rfl, hne⟩
  | ok r =>
    obtain ⟨w, h', hr, hx, hlo, hrel⟩ := gok_ok_lo he; subst hr
    exact ⟨hrel, hlo, hI.ext hx⟩

/-- One fuel step of a statement-level expression: a call may write. -/
theorem callStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L)
    (hEx : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → EvOK env h0.next h vs L n ((den env fps n).expr fp s))
    (hF : FnOK env fps n)
    (hIter : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ it r, (den env fps n).iter fp s it = some r →
      IterRel h vs r (evalExpr env n L h it))
    (hItems : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ t ifs elt ls i r a,
      at? h vs ls.k ls.p = some (.ref a) → (den env fps n).items fp s t ifs elt ls i = some r →
      ItemsOK h r (compItems env n L h t ifs [] elt none (ls.src a) i)) :
    ∀ e r, callStep env fps n (den env fps n) fp s e = some r →
      CallOK fp h0 vs s L r (evalExpr env (n + 1) L h e) := by
  intro e r hd
  have ih : EvF env fp h0 vs s L n ((den env fps n).expr fp s) := fun h1 hI1 => hEx fp h0 h1 vs s L hI1
  have hE1 := exprStep_sound env fps hlf hEx hF hIter hItems hI
  have fallback : (exprStep env fps n (den env fps n) fp s e).map (·.map (·, s.roots)) = some r →
      CallOK fp h0 vs s L r (evalExpr env (n + 1) L h e) := by
    intro hx
    cases he : exprStep env fps n (den env fps n) fp s e with
    | none => simp [he] at hx
    | some r0 =>
      simp [he] at hx; subst hx
      exact callOK_of_exprOK hI (hE1 e r0 he)
  unfold callStep at hd
  split at hd
  · next m g args hch =>
    obtain ⟨l, l', rfl, hloc, hc⟩ := callHead_spec hch
    by_cases hkw : allKw args = true
    · rw [if_pos hkw] at hd
      cases hx : DM.bind (kwsOf ((den env fps (m + 1)).expr fp s) args) (fun kvs => kwCtor env g kvs) with
      | none => rw [hx] at hd; cases hd
      | some r0 =>
        rw [hx] at hd
        have hr : r = r0.map (·, s.roots) := by
          cases r0 <;> simp [DM.bind, DM.ok, Except.map] at hd ⊢ <;> exact hd.symm
        subst hr
        exact callOK_of_exprOK hI (kwCall_sound hlf hI ih hloc hc hx)
    rw [if_neg hkw] at hd
    -- A call that writes nothing goes through `roCall_sound`.
    have ro : ∀ r', DM.bind (argsOf ((den env fps (m + 1)).expr fp s) args)
        (fun rs => dCallRO env fps (den env fps (m + 1)).fn s g rs) = some r' →
        r = r'.map (·, s.roots) → CallOK fp h0 vs s L r (evalExpr env (m + 2) L h
          (.call l (.name l' g) args)) := by
      intro r' h1 h2; subst h2
      exact callOK_of_exprOK hI (roCall_sound hlf hI ih hF hloc hc h1)
    have hL : L g = none := by
      have := hI.i.r.loc g; rw [hloc] at this
      revert this; cases L g <;> simp [LRel]
    obtain ⟨hlk, hany⟩ := callable_lookup hc hL
    unfold dCallW at hd
    cases hg : env.globals.lookup g with
    | none => simp [callable, hg] at hc
    | some gl =>
      cases gl with
      | fn d =>
        simp only [hg] at hd
        by_cases hfe : (fps g).isEmpty = true
        · simp only [hfe, ↓reduceIte] at hd
          have hd' := hd
          rw [show (fun rs => DM.bind (dCallRO env fps (den env fps (m + 1)).fn s g rs)
              fun r => DM.ok (r, s.roots)) = (fun rs => (dCallRO env fps (den env fps (m + 1)).fn s g rs).map
              (·.map (·, s.roots))) from by
                funext rs; cases dCallRO env fps (den env fps (m + 1)).fn s g rs with
                | none => rfl
                | some q => cases q <;> rfl, bind_map] at hd'
          cases hb : DM.bind (argsOf ((den env fps (m + 1)).expr fp s) args)
              (fun rs => dCallRO env fps (den env fps (m + 1)).fn s g rs) with
          | none => rw [hb] at hd'; cases hd'
          | some r' => rw [hb] at hd'; simp at hd'; exact ro r' hb hd'.symm
        · simp only [hfe, Bool.false_eq_true, ↓reduceIte] at hd
          rw [evalExpr]
          have hname : evalExpr env (m + 1) L h (.name l' g) = .ok (.glob g, h) := by
            rw [evalExpr]; simp [hlk]
          simp only [hname, Except.bind_ok', hany]
          rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rs, he, hd2⟩
          · have := argsOf_sound ih args h _ hI he
            revert this
            cases evalArgs env (m + 1) L h args with
            | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
            | ok q => intro hx; cases hx
          · have := argsOf_sound ih args h _ hI he
            revert this
            cases evalArgs env (m + 1) L h args with
            | error e' => intro hx; cases hx
            | ok q =>
              obtain ⟨ws, kws, h2⟩ := q
              rintro ⟨hx2, rfl, hrel⟩
              have hI2 := hI.ext hx2
              simp only [Except.bind_ok']
              rw [callValue_glob_fn _ _ _ hg]
              cases hop : onePlace rs with
              | none => simp [hop] at hd2
              | some ikp =>
              obtain ⟨i, k, p⟩ := ikp
              cases hm : rs.mapM (argRoot s) with
              | none => simp [hop, hm] at hd2
              | some rg =>
              simp only [hop, hm] at hd2
              cases hdk : s.deref k p with
              | none => simp [hdk] at hd2
              | some dk =>
              cases hdr : s.roots[k]? with
              | none => simp [hdk, hdr] at hd2
              | some dr =>
              simp only [hdk, hdr] at hd2
              by_cases hcnd : (!fp.isEmpty && coversAll fp s.roots k p dk (fps g)) = true
              · rw [if_pos hcnd] at hd2
                simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hcnd
                obtain ⟨hfpne, hcov⟩ := hcnd
                have hwt := callee_wtree hI2 hrel hop hdk hcov
                have hfn := hF (fps g) d rg ws h2
                rcases bind_case hd2 with ⟨err, hf, rfl⟩ | ⟨⟨v, rg'⟩, hf, hd3⟩
                · have := hfn _ (argRoots_dec hI2.i.r hrel hm) hwt hI2.wf hf
                  revert this
                  cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty ws [] h2 with
                  | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
                  | ok q => intro hx; cases hx
                · have := hfn _ (argRoots_dec hI2.i.r hrel hm) hwt hI2.wf hf
                  revert this
                  cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty ws [] h2 with
                  | error e' => intro hx; cases hx
                  | ok q =>
                    obtain ⟨w, h'⟩ := q
                    rintro ⟨hrr, -, hda, hfr, hsk, -⟩
                    cases v with
                    | val v =>
                      obtain ⟨rfl, hv⟩ := hrr
                      cases hdi : rg'[i]? with
                      | none => simp [hdi] at hd3
                      | some di =>
                        simp only [hdi] at hd3
                        simp [hv, DM.ok] at hd3; subst hd3
                        exact ⟨⟨rfl, hv⟩, trivial, call_rule hI2 hrel hop hdk hdr hfpne hcov hfr hsk hda hdi⟩
                    | _ => simp at hd3
              · rw [if_neg hcnd] at hd2; cases hd2
      | _ =>
        simp only [hg] at hd
        cases hb : DM.bind (argsOf ((den env fps (m + 1)).expr fp s) args)
            (fun rs => dCallRO env fps (den env fps (m + 1)).fn s g rs) with
        | none =>
          rw [bind_map, hb] at hd; cases hd
        | some r' =>
          rw [bind_map, hb] at hd; simp at hd; exact ro r' hb hd.symm
  · exact fallback hd

/-- The parts at one fuel agree with the interpreter, in every state of the invariant. -/
structure LevelOK (env : Env) (fps : Name → Footprint) (n : Nat) : Prop where
  expr : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → EvOK env h0.next h vs L n ((den env fps n).expr fp s)
  call : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ e r, (den env fps n).call fp s e = some r →
    CallOK fp h0 vs s L r (evalExpr env n L h e)
  target : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ t r w res, ERel h vs r w →
    TLo h0.next h r w → (den env fps n).target fp s t r = some res →
    CStmtOK fp h0 vs res ((assignTarget env n L h t w).bind fun p => pure (.normal, p.1, p.2))
  stmt : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ st res, (den env fps n).stmt fp s st = some res →
    CStmtOK fp h0 vs res (execStmt env n L h st)
  fn : FnOK env fps n
  iter : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ it r, (den env fps n).iter fp s it = some r →
    IterRel h vs r (evalExpr env n L h it)
  loop : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ t ls i body r a,
    at? h vs ls.k ls.p = some (.ref a) → (den env fps n).loop fp s t ls i body = some r →
    CStmtOK fp h0 vs r (execFor env n L h t (ls.src a) i body)
  items : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ t ifs elt ls i r a,
    at? h vs ls.k ls.p = some (.ref a) → (den env fps n).items fp s t ifs elt ls i = some r →
    ItemsOK h r (compItems env n L h t ifs [] elt none (ls.src a) i)

theorem blockOf_sound {env : Env} {fps : Name → Footprint} {n : Nat} (hL : LevelOK env fps n)
    {fp : Footprint} {h0 : Heap} {vs : List Value} :
    ∀ (ss : List Stmt) (s : DSt) (L : Locals) (h : Heap) (r : Res (DOut × DSt)),
      CInv fp h0 h vs s L → (den env fps n).block fp s ss = some r →
      CStmtOK fp h0 vs r (execBlock env n L h ss)
  | [], s, L, h, r, hI, hd => by
    simp [Sem.block, blockOf, DM.ok] at hd; subst hd
    rw [execBlock]; exact ⟨trivial, hI⟩
  | st :: ss, s, L, h, r, hI, hd => by
    simp only [Sem.block, blockOf] at hd
    rw [execBlock]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨⟨o, s1⟩, he, hd2⟩
    · have := hL.stmt fp h0 h vs s L hI st _ he
      revert this
      cases execStmt env n L h st with
      | error e' => rintro ⟨rfl, hne⟩; exact cstmtOK_err hne
      | ok q => intro hx; cases hx
    · have := hL.stmt fp h0 h vs s L hI st _ he
      revert this
      cases hx : execStmt env n L h st with
      | error e' => intro hx; cases hx
      | ok q =>
        obtain ⟨o', L1, h1⟩ := q
        rintro ⟨hor, hI1⟩
        simp only [Except.bind_ok']
        rcases orel_cases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨r', w', rfl, rfl, hrr, hll⟩
        · exact blockOf_sound hL ss s1 L1 h1 r hI1 hd2
        · simp [DM.ok] at hd2; subst hd2; exact ⟨trivial, hI1⟩
        · simp [DM.ok] at hd2; subst hd2; exact ⟨trivial, hI1⟩
        · simp [DM.ok] at hd2; subst hd2; exact ⟨⟨hrr, hll⟩, hI1⟩

theorem stmtStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    (hL : LevelOK env fps n) {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt}
    {L : Locals} (hI : CInv fp h0 h vs s L) :
    ∀ st r, stmtStep env (den env fps n) fp s st = some r →
      CStmtOK fp h0 vs r (execStmt env (n + 1) L h st) := by
  intro st r hd
  have hEF : EvF env fp h0 vs s L n ((den env fps n).expr fp s) :=
    fun h1 hI1 => hL.expr fp h0 h1 vs s L hI1
  have hE := hEF h hI
  have asg : ∀ (e : Expr) (t : Target),
      DM.bind ((den env fps n).call fp s e) (fun x => (den env fps n).target fp
        { s with roots := x.2 } t x.1) = some r →
      CStmtOK fp h0 vs r (do
        let (v, h1) ← evalExpr env n L h e
        let (L1, h2) ← assignTarget env n L h1 t v
        pure (.normal, L1, h2)) := by
    intro e t hd
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨⟨rv, rs⟩, he, hd2⟩
    · have := hL.call fp h0 h vs s L hI e _ he
      revert this
      cases evalExpr env n L h e with
      | error e' => rintro ⟨rfl, hne⟩; exact cstmtOK_err hne
      | ok q => intro hx; cases hx
    · have := hL.call fp h0 h vs s L hI e _ he
      revert this
      cases evalExpr env n L h e with
      | error e' => intro hx; cases hx
      | ok q =>
        obtain ⟨w, h1⟩ := q
        rintro ⟨hrel, hlo, hI1⟩
        simp only [Except.bind_ok']
        have := hL.target fp h0 h1 vs _ L hI1 t rv w _ hrel hlo hd2
        revert this
        cases assignTarget env n L h1 t w with
        | error e' => simp
        | ok q => simp
  cases st with
  | assign l ts e =>
    match ts, hd with
    | [t], hd =>
      simp only [stmtStep] at hd
      rw [execStmt]
      exact asg e t hd
    | [], hd => simp [stmtStep] at hd
    | _ :: _ :: _, hd => simp [stmtStep] at hd
  | annAssign l t e =>
    simp only [stmtStep] at hd
    rw [execStmt]
    exact asg e t hd
  | augAssign l t op e =>
    cases t with
    | index l' o ie =>
      simp only [stmtStep] at hd
      exact augStep_sound env fps hlf hI hEF l l' o ie op e hd
    | name l' x =>
      simp only [stmtStep] at hd
      exact augName_sound env fps hI hEF l l' x op e hd
    | _ => simp [stmtStep] at hd
  | exprStmt l e =>
    simp only [stmtStep] at hd
    rw [execStmt]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨⟨rv, rs⟩, he, hd2⟩
    · have := hL.call fp h0 h vs s L hI e _ he
      revert this
      cases evalExpr env n L h e with
      | error e' => rintro ⟨rfl, hne⟩; exact cstmtOK_err hne
      | ok q => intro hx; cases hx
    · have := hL.call fp h0 h vs s L hI e _ he
      revert this
      cases evalExpr env n L h e with
      | error e' => intro hx; cases hx
      | ok q =>
        obtain ⟨w, h1⟩ := q
        rintro ⟨-, -, hI1⟩
        simp [DM.ok] at hd2; subst hd2
        exact ⟨trivial, hI1⟩
  | ifStmt l c thn els =>
    simp only [stmtStep] at hd
    rw [execStmt]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE c _ he)
      simp [hi, cstmtOK_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE c _ he)
      have hI1 := hI.ext hx1
      simp only [hi, exb_ok, Except.bind_ok']
      cases rv with
      | tree _ => simp at hd2
      | place _ _ => simp at hd2
      | val v =>
      obtain ⟨rfl, hv⟩ := hrel
      simp only at hd2
      rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
      · obtain ⟨htr, hne⟩ := lift_some ht
        simp [truthyH_flat h1 hv, ← htr, cstmtOK_err (hne err htr.symm)]
      · obtain ⟨htr, -⟩ := lift_some ht
        simp only [truthyH_flat h1 hv, ← htr, exb_ok, Except.bind_ok']
        cases b with
        | true =>
          simp only [↓reduceIte] at hd3 ⊢; exact blockOf_sound hL thn s L h1 _ hI1 hd3
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hd3 ⊢
          exact blockOf_sound hL els s L h1 _ hI1 hd3
  | ret l oe =>
    cases oe with
    | none =>
      simp [stmtStep, DM.ok] at hd; subst hd
      rw [execStmt]; exact ⟨⟨⟨rfl, rfl⟩, trivial⟩, hI⟩
    | some e =>
      simp only [stmtStep] at hd
      rw [execStmt]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
      · obtain ⟨hi, hne⟩ := gok_error (hE e _ he)
        simp [hi, cstmtOK_err hne]
      · obtain ⟨w, h1, hi, hx1, hlo, hrel⟩ := gok_ok_lo (hE e _ he)
        simp only [hi, exb_ok, Except.bind_ok']
        cases rv with
        | tree _ =>
          simp [DM.ok] at hd2; subst hd2
          exact ⟨⟨hrel, hlo⟩, hI.ext hx1⟩
        | place _ _ => simp at hd2
        | val v =>
          simp [DM.ok] at hd2; subst hd2
          exact ⟨⟨hrel, hlo⟩, hI.ext hx1⟩
  | assert l e =>
    simp only [stmtStep] at hd
    rw [execStmt]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE e _ he)
      simp [hi, cstmtOK_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE e _ he)
      simp only [hi, exb_ok, Except.bind_ok']
      cases rv with
      | tree _ => simp at hd2
      | place _ _ => simp at hd2
      | val v =>
      obtain ⟨rfl, hv⟩ := hrel
      simp only at hd2
      rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
      · obtain ⟨htr, hne⟩ := lift_some ht
        simp [truthyH_flat h1 hv, ← htr, cstmtOK_err (hne err htr.symm)]
      · obtain ⟨htr, -⟩ := lift_some ht
        simp only [truthyH_flat h1 hv, ← htr, exb_ok, Except.bind_ok']
        cases b with
        | true => simp [DM.ok] at hd3; subst hd3; exact ⟨trivial, hI.ext hx1⟩
        | false => simp at hd3; subst hd3; exact cstmtOK_err (by decide)
  | pass l =>
    simp [stmtStep, DM.ok] at hd; subst hd
    rw [execStmt]; exact ⟨trivial, hI⟩
  | forStmt l t it body =>
    simp only [stmtStep] at hd
    rw [execStmt]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ls, he, hd2⟩
    · have := hL.iter fp h0 h vs s L hI it _ he
      revert this
      cases evalExpr env n L h it with
      | error e' => rintro ⟨rfl, hne⟩; exact cstmtOK_err hne
      | ok q => intro hx; cases hx
    · have := hL.iter fp h0 h vs s L hI it _ he
      revert this
      cases evalExpr env n L h it with
      | error e' => intro hx; cases hx
      | ok q =>
        obtain ⟨iv, h1⟩ := q
        rintro ⟨hx1, a, hat, hsrc⟩
        simp only [Except.bind_ok', hsrc]
        exact hL.loop fp h0 h1 vs s L (hI.ext hx1) t ls 0 body r a hat hd2
  | _ => simp [stmtStep] at hd

/-- `callFn (n + 1)` runs the body at fuel `n`. -/
theorem fnStep_sound (env : Env) {fps : Name → Footprint} {n : Nat} (hL : LevelOK env fps n) :
    FnOK env fps (n + 1) := by
  intro fp d roots vs h r hdec hw hwf hd
  change fnStep (den env fps n) fp d roots = some r at hd
  unfold fnStep at hd
  split at hd
  · next hc =>
    obtain ⟨hdef, hva, hnl⟩ := hc
    have hlen : d.params.names.length = vs.length := hnl.trans hdec.1
    obtain ⟨L0, hgo, hrel⟩ := go_rel hdec d.params.names.zipIdx (fun _ => none) Locals.empty
      (fun x => by simp [LRel])
      (fun q hq => by
        obtain ⟨x, i⟩ := q
        have := (List.mem_zipIdx hq).2.1
        simp at this ⊢; omega)
    have hI : CInv fp h h vs { roots, loc := initLoc roots (fun _ => none) d.params.names.zipIdx }
        L0 := CInv.start ⟨hdec.1, hdec.2, hrel⟩ hw hwf fun x r w hx _ => by
          cases r with
          | tree d' => exact absurd (initLoc_tree _ _ x d' hx) (by simp)
          | _ => trivial
    have hB := fun r => blockOf_sound hL d.body _ L0 h r hI
    dsimp only at hd
    rw [callFn]
    simp only [hdef, evalList, bindArgs, hlen, gt_iff_lt, Nat.lt_irrefl, false_and, ↓reduceIte,
      List.any_nil, Bool.false_eq_true, hgo, hva, Except.bind_ok', Except.pure_ok', exb_ok]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨⟨o, s1⟩, he, hd2⟩
    · have := hB _ he
      revert this
      cases execBlock env n L0 h d.body with
      | error e' => rintro ⟨rfl, hne⟩; simp only [exb_err, Except.bind_error']; exact ⟨rfl, hne⟩
      | ok q => intro hx; cases hx
    · have := hB _ he
      revert this
      cases execBlock env n L0 h d.body with
      | error e' => intro hx; cases hx
      | ok q =>
        obtain ⟨o', L1, h1⟩ := q
        rintro ⟨hor, hI1⟩
        simp only [Except.bind_ok', exb_ok]
        have post : DecArgs h1 vs s1.roots ∧ Frame h h1 vs fp ∧ Skel h h1 ∧ (fp = [] → Ext h h1) :=
          ⟨⟨hI1.i.r.len, hI1.i.r.roots⟩, hI1.i.frame, hI1.skel, hI1.ro⟩
        rcases orel_cases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨r', w', rfl, rfl, hrr, hll⟩
        · simp [DM.ok] at hd2; subst hd2; exact ⟨⟨rfl, rfl⟩, trivial, post⟩
        · simp [DM.ok] at hd2; subst hd2; exact ⟨⟨rfl, rfl⟩, trivial, post⟩
        · simp [DM.ok] at hd2; subst hd2; exact ⟨⟨rfl, rfl⟩, trivial, post⟩
        · simp [DM.ok] at hd2; subst hd2; exact ⟨hrr, hll, post⟩
  · cases hd

theorem iterStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    (hL : LevelOK env fps n) {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt}
    {L : Locals} (hI : CInv fp h0 h vs s L) :
    ∀ it r, iterStep env fps n (den env fps n) fp s it = some r →
      IterRel h vs r (evalExpr env (n + 1) L h it) := by
  intro it r hd
  have hEF : EvF env fp h0 vs s L n ((den env fps n).expr fp s) :=
    fun h1 hI1 => hL.expr fp h0 h1 vs s L hI1
  have hE1 := exprStep_sound env fps hlf hL.expr hL.fn hL.iter hL.items hI
  have place : ∀ (h' : Heap), CInv fp h0 h' vs s L → ∀ (rr : DRes) (w : Value) (enum : Bool),
      ERel h' vs rr w →
      (match rr with
        | .place k p => if listPlace s k p then DM.ok (⟨k, p, enum⟩ : LSrc) else none
        | _ => none) = some r →
      ∃ ls a, r = .ok ls ∧ ls.enum = enum ∧ w = .ref a ∧ at? h' vs ls.k ls.p = some (.ref a) ∧
        toSeq h' (.ref a) = .ok (.live a) := by
    intro h' hI' rr w enum hrel hm
    cases rr with
    | tree _ => simp at hm
    | val _ => simp at hm
    | place k p =>
      obtain ⟨a, rfl, hat⟩ := hrel
      by_cases hlp : listPlace s k p = true
      · simp [hlp, DM.ok] at hm; subst hm
        obtain ⟨kd, e, l, ds, hdr, hb⟩ := listPlace_spec hlp
        obtain ⟨m, xs, ho, -⟩ := listPlace_obj hI'.i.r hat hdr
        exact ⟨_, a, rfl, rfl, rfl, hat, toSeq_live ho hb⟩
      · simp [hlp] at hm
  have dflt : ∀ e, DM.bind (exprStep env fps n (den env fps n) fp s e) (fun r =>
        match r with
        | .place k p => if listPlace s k p then DM.ok (⟨k, p, false⟩ : LSrc) else none
        | _ => none) = some r → IterRel h vs r (evalExpr env (n + 1) L h e) := by
    intro e hd
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rr, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE1 e _ he)
      rw [hi]; exact ⟨rfl, hne⟩
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE1 e _ he)
      rw [hi]
      obtain ⟨ls, a, rfl, hen, rfl, hat, hseq⟩ := place h1 (hI.ext hx1) rr w false hrel hd2
      refine ⟨hx1, a, hat, ?_⟩
      simp [iterSource, hseq, LSrc.src, hen]
  unfold iterStep at hd
  split at hd
  · next _ l l' g e =>
    cases n with
    | zero => simp at hd
    | succ m =>
      simp only at hd
      by_cases hc : ((s.loc g).isNone && isEnumerate env g) = true
      · rw [if_pos hc] at hd
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
        obtain ⟨hloc, hen⟩ := hc
        have hg : env.globals.lookup g = some (.builtin .enumerate) := by
          unfold isEnumerate at hen; split at hen <;> simp_all
        have hLg : L g = none := by
          have := hI.i.r.loc g; rw [hloc] at this
          revert this; cases L g <;> simp [LRel]
        have hname : evalExpr env (m + 1) L h (.name l' g) = .ok (.glob g, h) := by
          rw [evalExpr]; simp [lookupName, hLg, hg]
        have hany : anyAll env (.glob g) = none := by simp [anyAll, hg]
        rw [evalExpr]
        simp only [hname, Except.bind_ok', hany]
        rw [evalArgs]
        simp only
        rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rr, he, hd2⟩
        · obtain ⟨hi, hne⟩ := gok_error (hL.expr fp h0 h vs s L hI e _ he)
          simp [hi]; exact ⟨rfl, hne⟩
        · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hL.expr fp h0 h vs s L hI e _ he)
          obtain ⟨ls, a, rfl, hen', rfl, hat, hseq⟩ := place h1 (hI.ext hx1) rr w true hrel hd2
          simp only [hi, Except.bind_ok']
          rw [evalArgs]
          simp only [Except.bind_ok', Except.pure_ok']
          rw [callValue_builtin _ _ _ hg (by decide) (by decide)]
          simp only [applyBuiltin, hlf.builtin h1 .enumerate _ [] (by simp)]
          refine ⟨hx1, a, hat, ?_⟩
          simp [iterSource, hseq, LSrc.src, hen']
      · rw [if_neg hc] at hd; cases hd
  · exact dflt it hd

theorem loopStep_sound {env : Env} {fps : Name → Footprint} {n : Nat} (hL : LevelOK env fps n)
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) {t : Target} {ls : LSrc} {i : Nat} {body : List Stmt}
    {r : Res (DOut × DSt)} {a : Nat} (hat : at? h vs ls.k ls.p = some (.ref a))
    (hd : loopStep n (den env fps n) fp s t ls i body = some r) :
    CStmtOK fp h0 vs r (execFor env (n + 1) L h t (ls.src a) i body) := by
  unfold loopStep at hd
  cases hdr : s.deref ls.k ls.p with
  | none => simp [hdr] at hd
  | some dd =>
  rw [hdr] at hd
  cases dd with
  | leaf _ => simp at hd
  | cont _ _ => simp at hd
  | list kd el ll ds =>
  simp only at hd
  cases hbyte : isByteList kd el with
  | true => simp [hbyte] at hd
  | false =>
  simp only [hbyte, Bool.false_eq_true, ↓reduceIte] at hd
  obtain ⟨m, xs, ho, hm⟩ := listPlace_obj hI.i.r hat hdr
  have hlen := ((mapM_some_iff xs ds).mp hm).1
  have hitem : iterItem h (ls.src a) i =
      .ok (xs[i]?.map fun x => if ls.enum then enumItem i x else x) := by
    cases hen : ls.enum <;> simp [LSrc.src, hen, iterItem, seqItem_live ho hbyte]
  rw [execFor]
  simp only [hitem, Except.bind_ok']
  cases hc : ds[i]? with
  | none =>
    have : xs[i]? = none := by rw [List.getElem?_eq_none_iff] at hc ⊢; omega
    simp [hc, DM.ok] at hd; subst hd
    simp [this]; exact ⟨trivial, hI⟩
  | some c =>
    obtain ⟨x, hx, hdx⟩ := mapM_get hm hc
    have hrel := child_rel hat (by simp [okids, ho]) hx hdx
    simp only [hc] at hd
    cases hbl : bindLoop n ls.enum s t i (ofChild ls.k (ls.p ++ [i]) c) with
    | none => simp [hbl] at hd
    | some s1 =>
    simp only [hbl] at hd
    obtain ⟨L1, hasg, hI1⟩ := bindLoop_sound hI hrel (tlo_ofChild _ _ _ _) hbl
    simp only [hx, Option.map_some]
    rw [hasg]
    simp only [Except.bind_ok']
    have hB := blockOf_sound hL (fp := fp) (h0 := h0) (vs := vs) body s1 L1 h
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨⟨o, s2⟩, he, hd2⟩
    · have := hB _ hI1 he
      revert this
      cases execBlock env n L1 h body with
      | error e' => rintro ⟨rfl, hne⟩; exact cstmtOK_err hne
      | ok q => intro hx; cases hx
    · have := hB _ hI1 he
      revert this
      cases execBlock env n L1 h body with
      | error e' => intro hx; cases hx
      | ok q =>
        obtain ⟨o', L2, h2⟩ := q
        rintro ⟨hor, hI2⟩
        simp only [Except.bind_ok']
        have hat2 : at? h2 vs ls.k ls.p = some (.ref a) :=
          (hI2.i.refs _ _ a).mpr ((hI.i.refs _ _ a).mp hat)
        rcases orel_cases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨r', w', rfl, rfl, hrr, hll⟩
        · exact hL.loop fp h0 h2 vs s2 L2 hI2 t ls (i + 1) body r a hat2 hd2
        · simp [DM.ok] at hd2; subst hd2; exact ⟨trivial, hI2⟩
        · exact hL.loop fp h0 h2 vs s2 L2 hI2 t ls (i + 1) body r a hat2 hd2
        · simp [DM.ok] at hd2; subst hd2; exact ⟨⟨hrr, hll⟩, hI2⟩

theorem level_zero (env : Env) (fps : Name → Footprint) : LevelOK env fps 0 :=
  ⟨fun _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd,
   fun _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd,
   fun _ _ _ _ _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd,
   fun _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd,
   fun _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd,
   fun _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd,
   fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd,
   fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd => by simp [den] at hd⟩

theorem level_succ (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    (hL : LevelOK env fps n) : LevelOK env fps (n + 1) :=
  ⟨fun fp h0 h vs s L hI =>
     exprStep_sound env fps hlf hL.expr hL.fn hL.iter hL.items hI,
   fun fp h0 h vs s L hI =>
     callStep_sound env fps hlf hI hL.expr hL.fn hL.iter hL.items,
   fun fp h0 h vs s L hI t r w res hr hlo hd =>
     targetStep_sound env fps hlf hI (fun h1 hI1 => hL.expr fp h0 h1 vs s L hI1) t hr hlo hd,
   fun fp h0 h vs s L hI => stmtStep_sound env fps hlf hL hI,
   fnStep_sound env hL,
   fun fp h0 h vs s L hI => iterStep_sound env fps hlf hL hI,
   fun fp h0 h vs s L hI t ls i body r a hat hd => loopStep_sound hL hI hat hd,
   fun fp h0 h vs s L hI t ifs elt ls i r a hat hd => itemsStep_sound hL.expr hL.items hI hat hd⟩

theorem level_ok (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) :
    ∀ n, LevelOK env fps n
  | 0 => level_zero env fps
  | n + 1 => level_succ env fps hlf (level_ok env fps hlf n)

/-- The theorem for the fragment with calls. `fps` gives the footprint of each callee. For a
function `f` whose denotation at fuel `n` gives `r`: under `WTree` over the footprint `fp`, in a
well-formed heap, the interpreter at fuel `n` matches `r`. Reads and calls may allocate. `interp_fuel_mono` gives every larger fuel. -/
theorem denote_sound_calls (env : Env) (fps : Name → Footprint) (hlf : LibFlat env)
    (gfp fp : Footprint) {f : Name} {d : FunctionDef} (hg : env.globals.lookup f = some (.fn d))
    {h : Heap} {vs : List Value} {roots : List DV} (hdec : DecArgs h vs roots)
    (hw : WTree h vs fp) (hwf : HeapWF h) {n : Nat} {r : Res (DRes × List DV)}
    (hd : (den env fps n).fn fp d roots = some r) :
    ResultMatches gfp fp h vs (fun (x : DRes × List DV) h' v => ERel h' vs x.1 v ∧ DecArgs h' vs x.2)
      (interp env n f vs h) (r.mapError SpecError.fail) := by
  have hrel := (level_ok env fps hlf n).fn fp d roots vs h r hdec hw hwf hd
  rw [interp, callName, callValue_glob_fn _ _ _ hg]
  revert hrel
  cases callFn env n d.params (.stmts d.body) Locals.empty vs [] h with
  | error e' =>
    cases r with
    | ok _ => intro hx; cases hx
    | error e => rintro ⟨rfl, hne⟩; exact ⟨hne, rfl⟩
  | ok q =>
    obtain ⟨w, h'⟩ := q
    cases r with
    | error _ => intro hx; cases hx
    | ok x =>
      obtain ⟨v, rs⟩ := x
      rintro ⟨hrr, -, hda, hfr, hsk, -⟩
      exact ⟨⟨hrr, hda⟩, hfr, Fresh_of_Skel hsk,
        noNewPaths_of_reach (Reach_of_Skel hsk (decArgs_below hwf hdec.2 hdec.1))⟩

end SpecLean.Layer4
