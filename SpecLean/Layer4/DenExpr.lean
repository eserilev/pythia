import SpecLean.Layer4.CallRule
import SpecLean.Layer4.Steps

/-!
# Layer 4: expressions with calls agree with the interpreter

`exprStep_sound`: one fuel step of the expression denotation, given the expressions and the
function bodies one fuel below. A call that writes nothing is in an expression: its arguments
are evaluated left to right, then the callee runs (`FnOK`) and leaves the heap as it was.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode SpecLean.Validation.Where

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

/-- A constructor of an SSZ class on flat values needs no heap. -/
def ConstructFlat (env : Env) : Prop :=
  ∀ h t vs, ctorFlat t = true → (∀ v ∈ vs, Flat v = true) →
    LibModel.construct env h t vs [] = (fun x => (x.1, h)) <$> LibModel.construct env Heap.empty t vs []

/-- What the proof needs of the library: flat values coerce and construct without the heap. -/
structure LibFlat (env : Env) : Prop where
  coerce : CoerceFlat env
  ctor : ConstructFlat env
  /-- The library leaves `len`, `min`, `max` and `enumerate` to the core. -/
  builtin : ∀ h b args kws, (b = .len ∨ b = .min ∨ b = .max ∨ b = .enumerate) →
    LibModel.builtin env h b args kws = none

/-- An expression result and the interpreter's: the heap only gains objects (`Ext`), and the
values agree in the new heap. A call of a function that writes nothing can allocate. -/
def GOK (lo : Nat) (h : Heap) (vs : List Value) : Res DRes → Res (Value × Heap) → Prop
  | .ok r, .ok (w, h') => Ext h h' ∧ TLo lo h' r w ∧ ERel h' vs r w
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem gok_ok {lo : Nat} {h : Heap} {vs : List Value} {r : DRes} {res : Res (Value × Heap)}
    (hk : GOK lo h vs (.ok r) res) : ∃ w h', res = .ok (w, h') ∧ Ext h h' ∧ ERel h' vs r w := by
  cases res with
  | error e' => cases hk
  | ok p => obtain ⟨w, h'⟩ := p; exact ⟨w, h', rfl, hk.1, hk.2.2⟩

theorem gok_ok_lo {lo : Nat} {h : Heap} {vs : List Value} {r : DRes} {res : Res (Value × Heap)}
    (hk : GOK lo h vs (.ok r) res) :
    ∃ w h', res = .ok (w, h') ∧ Ext h h' ∧ TLo lo h' r w ∧ ERel h' vs r w := by
  cases res with
  | error e' => cases hk
  | ok p => obtain ⟨w, h'⟩ := p; exact ⟨w, h', rfl, hk⟩

theorem gok_error {lo : Nat} {h : Heap} {vs : List Value} {e : SpecError} {res : Res (Value × Heap)}
    (hk : GOK lo h vs (.error e) res) : res = .error e ∧ e ≠ .outOfFuel := by
  cases res with
  | error e' => obtain ⟨rfl, hne⟩ := hk; exact ⟨rfl, hne⟩
  | ok p => cases hk

theorem gok_err {lo : Nat} {h : Heap} {vs : List Value} {e : SpecError} (hne : e ≠ .outOfFuel) :
    GOK lo h vs (.error e) (.error e) := ⟨rfl, hne⟩

theorem gok_ext {lo : Nat} {h h1 : Heap} {vs : List Value} {r : Res DRes} {res : Res (Value × Heap)}
    (e : Ext h h1) (hk : GOK lo h1 vs r res) : GOK lo h vs r res := by
  cases r <;> cases res
  · exact hk
  · cases hk
  · cases hk
  · obtain ⟨e2, hr⟩ := hk; exact ⟨Ext_trans e e2, hr⟩

theorem gok_of {lo : Nat} {h : Heap} {vs : List Value} {r : Res DRes} {res : Res (Value × Heap)}
    (hk : ExprOK h vs r res) (hlo : ∀ rr w h', r = .ok rr → res = .ok (w, h') → TLo lo h' rr w) :
    GOK lo h vs r res := by
  cases r <;> cases res
  · exact hk
  · cases hk
  · cases hk
  · next a b => obtain ⟨w, h'⟩ := b; obtain ⟨rfl, hr⟩ := hk; exact ⟨Ext_refl _, hlo a w _ rfl rfl, hr⟩

/-- The expressions at fuel `n` agree with the interpreter at heap `h`. -/
def EvOK (env : Env) (lo : Nat) (h : Heap) (vs : List Value) (L : Locals) (n : Nat)
    (ev : Expr → DM DRes) : Prop :=
  ∀ e r, ev e = some r → GOK lo h vs r (evalExpr env n L h e)

/-- `EvOK` at every heap of the invariant. -/
def EvF (env : Env) (fp : Footprint) (h0 : Heap) (vs : List Value) (s : DSt) (L : Locals) (n : Nat)
    (ev : Expr → DM DRes) : Prop :=
  ∀ h, CInv fp h0 h vs s L → EvOK env h0.next h vs L n ev

/-- The function bodies at fuel `n` agree with `callFn n`. -/
def FnOK (env : Env) (fps : Name → Footprint) (n : Nat) : Prop :=
  ∀ (fp : Footprint) (d : FunctionDef) (roots : List DV) (vs : List Value) (h : Heap)
    (r : Res (DRes × List DV)), DecArgs h vs roots → WTree h vs fp → HeapWF h →
    (den env fps n).fn fp d roots = some r →
    FnRel fp h vs r (callFn env n d.params (.stmts d.body) Locals.empty vs [] h)

def ArgsOK (h : Heap) (vs : List Value) :
    Res (List DRes) → Res (List Value × List (Name × Value) × Heap) → Prop
  | .ok rs, .ok (ws, kws, h') => Ext h h' ∧ kws = [] ∧ ERels h' vs rs ws
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

section comb
variable {env : Env} {fp : Footprint} {h0 : Heap} {vs : List Value} {s : DSt} {L : Locals} {n : Nat}
  {ev : Expr → DM DRes}

theorem cmpOf_sound (hE : EvF env fp h0 vs s L n ev) :
    ∀ (rest : List (CmpOp × Expr)) (h : Heap) (x : Value) (r : Res DRes), CInv fp h0 h vs s L →
      Flat x = true → cmpOf ev x rest = some r → GOK h0.next h vs r (evalCmp env n L h x rest)
  | [], h, x, r, _, _, hd => by
    simp [cmpOf, DM.ok] at hd; subst hd
    rw [evalCmp]; exact ⟨Ext_refl h, trivial, rfl, rfl⟩
  | (op, e) :: rest, h, x, r, hI, hx, hd => by
    simp only [cmpOf] at hd
    rw [evalCmp]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ry, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE h hI e _ he)
      simp [hi, gok_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE h hI e _ he)
      simp only [hi, Except.bind_ok']
      refine gok_ext hx1 ?_
      cases ry with
      | tree _ => simp at hd2
      | place _ _ => simp at hd2
      | val y =>
        obtain ⟨rfl, hy⟩ := hrel
        simp only at hd2
        rcases bind_case hd2 with ⟨err, hc, rfl⟩ | ⟨b, hc, hd3⟩
        · obtain ⟨hco, hne⟩ := cmpF_sound h1 hx hy hc
          simp [hco, gok_err (hne err rfl)]
        · obtain ⟨hco, -⟩ := cmpF_sound h1 hx hy hc
          simp only [hco, Except.bind_ok']
          cases b with
          | true =>
            simp only [↓reduceIte] at hd3 ⊢
            exact cmpOf_sound hE rest h1 _ r (hI.ext hx1) hy hd3
          | false =>
            simp [DM.ok] at hd3; subst hd3
            exact ⟨Ext_refl _, trivial, rfl, rfl⟩

theorem boolOf_sound (hE : EvF env fp h0 vs s L n ev) :
    ∀ (es : List Expr) (h : Heap) (op : BoolOp) (r : Res DRes), CInv fp h0 h vs s L →
      boolOf ev op es = some r → GOK h0.next h vs r (evalBoolOp env n L h op es)
  | [], _, _, _, _, hd => by simp [boolOf] at hd
  | e :: es, h, op, r, hI, hd => by
    simp only [boolOf] at hd
    rw [evalBoolOp]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE h hI e _ he)
      simp [hi, gok_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE h hI e _ he)
      simp only [hi, Except.bind_ok']
      refine gok_ext hx1 ?_
      cases rv with
      | tree _ => simp at hd2
      | place _ _ => simp at hd2
      | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp only at hd2
        by_cases hes : es.isEmpty = true
        · simp [hes, DM.ok] at hd2; subst hd2
          simp [hes]; exact ⟨Ext_refl _, trivial, rfl, hv⟩
        · simp only [hes, Bool.false_eq_true, ↓reduceIte] at hd2 ⊢
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [truthyH_flat h1 hv, ← htr, gok_err (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp only [truthyH_flat h1 hv, ← htr, Except.bind_ok']
            cases op <;> cases b <;> simp only [DM.ok, Option.some.injEq] at hd3 ⊢ <;>
              first
              | exact boolOf_sound hE es h1 _ r (hI.ext hx1) hd3
              | (subst hd3; exact ⟨Ext_refl _, trivial, rfl, hv⟩)

theorem argsOf_sound (hE : EvF env fp h0 vs s L n ev) :
    ∀ (args : List Arg) (h : Heap) (r : Res (List DRes)), CInv fp h0 h vs s L →
      argsOf ev args = some r → ArgsOK h vs r (evalArgs env n L h args)
  | [], h, r, _, hd => by
    simp [argsOf, DM.ok] at hd; subst hd
    rw [evalArgs]; exact ⟨Ext_refl h, rfl, trivial⟩
  | .pos e :: as, h, r, hI, hd => by
    simp only [argsOf] at hd
    rw [evalArgs]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE h hI e _ he)
      simp [hi, hne, ArgsOK]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE h hI e _ he)
      have hI1 := hI.ext hx1
      simp only [hi, Except.bind_ok']
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨rs, he2, hd3⟩
      · have := argsOf_sound hE as h1 _ hI1 he2
        revert this
        cases evalArgs env n L h1 as with
        | error e' => rintro ⟨rfl, hne⟩; simp [hne, ArgsOK]
        | ok q => intro hx; cases hx
      · simp [DM.ok] at hd3; subst hd3
        have := argsOf_sound hE as h1 _ hI1 he2
        revert this
        cases evalArgs env n L h1 as with
        | error e' => intro hx; cases hx
        | ok q =>
          obtain ⟨ws, kws, h2⟩ := q
          rintro ⟨hx2, rfl, hr⟩
          simp only [Except.bind_ok', Except.pure_ok']
          exact ⟨Ext_trans hx1 hx2, rfl, And.intro (ERel_ext hI1.wf hI1.below hx2 hrel) hr⟩
  | .starred _ :: _, _, r, _, hd => by simp [argsOf] at hd
  | .kw _ _ :: _, _, r, _, hd => by simp [argsOf] at hd

end comb

theorem allVals_spec {h : Heap} {vs : List Value} :
    ∀ {rs : List DRes} {ws vals : List Value}, ERels h vs rs ws → allVals rs = some vals →
      ws = vals ∧ ∀ v ∈ vals, Flat v = true
  | [], [], vals, _, ha => by simp [allVals] at ha; subst ha; simp
  | .val v :: rs, w :: ws, vals, ⟨⟨hwv, hv⟩, h2⟩, ha => by
    subst hwv
    simp only [allVals, Option.map_eq_some_iff] at ha
    obtain ⟨vals', h1, rfl⟩ := ha
    obtain ⟨rfl, hf⟩ := allVals_spec h2 h1
    exact ⟨rfl, by simp [hv]; exact hf⟩
  | .place _ _ :: _, _ :: _, _, _, ha => by simp [allVals] at ha
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

theorem callHead_spec {env : Env} {s : DSt} {e : Expr} {g : Name} {args : List Arg}
    (h : callHead env s e = some (g, args)) :
    ∃ l l', e = .call l (.name l' g) args ∧ s.loc g = none ∧ callable env g = true := by
  unfold callHead at h
  split at h
  · next l l' g' args' =>
    split at h
    · next hc =>
      simp at h; obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      exact ⟨l, l', rfl, hc.1, hc.2⟩
    · cases h
  · cases h

theorem callValue_type {env : Env} (n : Nat) {g : Name} {t : SszTy} (vs : List Value) (h : Heap)
    (hg : env.globals.lookup g = some (.type t)) :
    callValue env n (.glob g) vs [] h = LibModel.construct env h t vs [] := by
  rw [callValue.eq_def]; simp only [hg]

theorem callable_lookup {env : Env} {L : Locals} {g : Name} (hc : callable env g = true)
    (hL : L g = none) : lookupName env L g = .ok (.glob g) ∧ anyAll env (.glob g) = none := by
  unfold callable at hc
  unfold lookupName anyAll
  rw [hL]
  split at hc <;> simp_all

theorem callValue_builtin {env : Env} (n : Nat) {g : Name} {b : Builtin} (vs : List Value)
    (h : Heap) (hg : env.globals.lookup g = some (.builtin b)) (hf : b ≠ .filter)
    (hs : b ≠ .sorted) : callValue env n (.glob g) vs [] h = applyBuiltin env h b vs [] := by
  rw [callValue.eq_def]; simp only [hg]
  try (cases b <;> first | rfl | simp_all)

theorem pickBest_heap {env : Env} (hlf : LibFlat env) (h : Heap) (isMin : Bool) (x y : Value)
    (ys : List Value) :
    applyBuiltin env h (if isMin then .min else .max) (x :: y :: ys) [] =
      (do pure (← pickBest (!isMin) x (y :: ys), h)) := by
  cases isMin
  · simp [applyBuiltin, hlf.builtin h .max _ [] (by simp)]
  · simp [applyBuiltin, hlf.builtin h .min _ [] (by simp)]

/-- A call that writes nothing, in an expression. -/
theorem roCall_sound {env : Env} {fps : Name → Footprint} (hlf : LibFlat env) {m : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L (m + 1) ((den env fps (m + 1)).expr fp s))
    (hF : FnOK env fps (m + 1)) {g : Name} {l l' : Line} {args : List Arg}
    (hloc : s.loc g = none) (hc : callable env g = true) {r : Res DRes}
    (hd : DM.bind (argsOf ((den env fps (m + 1)).expr fp s) args)
      (fun rs => dCallRO env fps (den env fps (m + 1)).fn s g rs) = some r) :
    GOK h0.next h vs r (evalExpr env (m + 2) L h (.call l (.name l' g) args)) := by
  have hL : L g = none := by
    have := hI.i.r.loc g; rw [hloc] at this
    revert this; cases L g <;> simp [LRel]
  obtain ⟨hlk, hany⟩ := callable_lookup hc hL
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
    cases hea : evalArgs env (m + 1) L h args with
    | error e' => intro hx; cases hx
    | ok q =>
      obtain ⟨ws, kws, h2⟩ := q
      rintro ⟨hx2, rfl, hrel⟩
      have hI2 := hI.ext hx2
      refine gok_ext hx2 ?_
      simp only [Except.bind_ok']
      unfold dCallRO at hd2
      cases hg : env.globals.lookup g with
      | none => simp [hg] at hd2
      | some gl =>
        rw [hg] at hd2
        cases gl with
        | fn d =>
          simp only at hd2
          rw [callValue_glob_fn _ _ _ hg]
          by_cases hfe : (fps g).isEmpty = true
          · rw [if_pos hfe] at hd2
            cases hm : rs.mapM (argRoot s) with
            | none => simp [hm] at hd2
            | some rg =>
              rw [hm] at hd2
              simp only at hd2
              rcases bind_case hd2 with ⟨err, hf, rfl⟩ | ⟨⟨v, rg'⟩, hf, hd3⟩
              · have := hF [] d rg ws h2 _ (argRoots_dec hI2.i.r hrel hm) (fun _ _ hp => by simp at hp) hI2.wf hf
                revert this
                cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty ws [] h2 with
                | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
                | ok q => intro hx; cases hx
              · have := hF [] d rg ws h2 _ (argRoots_dec hI2.i.r hrel hm) (fun _ _ hp => by simp at hp) hI2.wf hf
                revert this
                cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty ws [] h2 with
                | error e' => intro hx; cases hx
                | ok q =>
                  obtain ⟨w, h'⟩ := q
                  rintro ⟨hrr, hlo, -, -, -, hro⟩
                  have hx' := hro rfl
                  cases v with
                  | val v =>
                    obtain ⟨rfl, hfl⟩ := hrr
                    simp [hfl, DM.ok] at hd3; subst hd3; exact ⟨hx', trivial, rfl, hfl⟩
                  | tree t =>
                    simp [DM.ok] at hd3; subst hd3
                    obtain ⟨hdt, -⟩ := hrr
                    refine ⟨hx', fun q a ea => Nat.le_trans hI2.i.fresh.1 (hlo q a ea), hdt,
                      fun q a ea k p ep => ?_⟩
                    have hge := hlo q a ea
                    have hlt := at?_below hI2.below ((at?_Skel (Skel_of_Ext hx') hI2.below k p a).mp ep)
                    omega
                  | place _ _ => simp at hd3
          · rw [if_neg hfe] at hd2; cases hd2
        | type t =>
          simp only at hd2
          rw [callValue_type _ _ _ hg]
          unfold dCtor at hd2
          split at hd2
          · next hct =>
            cases hav : allVals rs with
            | none => simp [hav] at hd2
            | some vals =>
              rw [hav] at hd2
              simp only at hd2
              obtain ⟨rfl, hfl⟩ := allVals_spec hrel hav
              rw [hlf.ctor h2 t ws hct hfl]
              rcases bind_case hd2 with ⟨err, hl, rfl⟩ | ⟨v, hl, hd3⟩
              · obtain ⟨hr, hne⟩ := lift_some hl
                cases hk : LibModel.construct env Heap.empty t ws [] with
                | ok q => rw [hk] at hr; cases hr
                | error e' => rw [hk] at hr; cases hr; exact ⟨rfl, hne _ (by rw [hk]; rfl)⟩
              · obtain ⟨hr, -⟩ := lift_some hl
                cases hk : LibModel.construct env Heap.empty t ws [] with
                | error e' => rw [hk] at hr; cases hr
                | ok q =>
                  rw [hk] at hr; cases hr
                  by_cases hv : Flat q.1 = true
                  · simp [hv, DM.ok] at hd3; subst hd3; exact ⟨Ext_refl _, trivial, rfl, hv⟩
                  · simp [hv] at hd3
          · cases hd2
        | builtin b =>
          simp only at hd2
          have hnf : b ≠ .filter := by rintro rfl; simp [dBuiltin] at hd2
          have hns : b ≠ .sorted := by rintro rfl; simp [dBuiltin] at hd2
          rw [callValue_builtin _ _ _ hg hnf hns]
          have minmax : ∀ (isMin : Bool), dBuiltin s (if isMin then .min else .max) rs = some r →
              GOK h0.next h2 vs r (applyBuiltin env h2 (if isMin then .min else .max) ws []) := by
            intro isMin hd3
            have hb : dBuiltin s (if isMin then .min else .max) rs = (match allVals rs with
                | some (x :: y :: ys) => DM.bind (lift (pickBest (!isMin) x (y :: ys))) fun w =>
                    if Flat w then DM.ok (DRes.val w) else none
                | _ => none) := by
              cases isMin <;> rfl
            rw [hb] at hd3
            cases hav : allVals rs with
            | none => simp [hav] at hd3
            | some vals =>
              rw [hav] at hd3
              obtain ⟨hwv, hfl⟩ := allVals_spec hrel hav
              subst hwv
              match ws, hd3 with
              | x :: y :: ys, hd3 =>
                rw [pickBest_heap hlf]
                rcases bind_case hd3 with ⟨err, hl, rfl⟩ | ⟨w, hl, hd4⟩
                · obtain ⟨hr, hne⟩ := lift_some hl
                  rw [← hr]; exact ⟨rfl, hne err hr.symm⟩
                · obtain ⟨hr, -⟩ := lift_some hl
                  rw [← hr]
                  by_cases hv : Flat w = true
                  · simp [hv, DM.ok] at hd4; subst hd4; exact ⟨Ext_refl _, trivial, rfl, hv⟩
                  · simp [hv] at hd4
              | [], hd3 => simp at hd3
              | [_], hd3 => simp at hd3
          cases b
          case min => exact minmax true hd2
          case max => exact minmax false hd2
          case len =>
            simp only [dBuiltin] at hd2
            match rs, ws, hrel, hd2 with
            | [.place k p], [w], ⟨⟨a, hw, hat⟩, _⟩, hd2 =>
              subst hw
              simp only at hd2
              cases hdr : s.deref k p with
              | none => simp [hdr] at hd2
              | some dd =>
                rw [hdr] at hd2
                cases dd with
                | leaf _ => simp at hd2
                | cont _ _ => simp at hd2
                | list kd el ll ds =>
                  simp [DM.ok] at hd2; subst hd2
                  obtain ⟨nn, hn⟩ := deref_dec hI2.i.r hat hdr
                  obtain ⟨a', mm, xs, ha, -, ho, hm⟩ := dec_list hn
                  cases ha
                  have hlen := ((mapM_some_iff xs ds).mp hm).1
                  simp [applyBuiltin, hlf.builtin h2 .len _ [] (by simp), ho, hlen]
                  exact ⟨Ext_refl _, trivial, rfl, rfl⟩
            | [.val _], _, _, hd2 => simp at hd2
            | [], _, _, hd2 => simp at hd2
            | _ :: _ :: _, _, _, hd2 => simp at hd2
          all_goals simp [dBuiltin] at hd2
        | _ => simp at hd2

def OptOK (h : Heap) : Res (Option Value) → Res (Option Value × Heap) → Prop
  | .ok ov, .ok (ov', h') => Ext h h' ∧ ov' = ov ∧ ∀ v, ov = some v → Flat v = true
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem optOf_sound {env : Env} {fp : Footprint} {h0 : Heap} {vs : List Value} {s : DSt} {L : Locals}
    {n : Nat} {ev : Expr → DM DRes} (hE : EvF env fp h0 vs s L n ev) {h : Heap}
    (hI : CInv fp h0 h vs s L) :
    ∀ (o : Option Expr) (r : Res (Option Value)), optOf ev o = some r → OptOK h r (evalOpt env n L h o)
  | none, r, hd => by
    simp [optOf, DM.ok] at hd; subst hd
    rw [evalOpt]; exact ⟨Ext_refl h, rfl, by simp⟩
  | some e, r, hd => by
    simp only [optOf] at hd
    rw [evalOpt]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE h hI e _ he)
      simp [hi, hne, OptOK]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE h hI e _ he)
      simp only [hi, Except.bind_ok']
      cases rv with
      | tree _ => simp at hd2
      | place _ _ => simp at hd2
      | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp [DM.ok] at hd2; subst hd2
        exact ⟨hx1, rfl, by simp [hv]⟩

theorem getSlice_bytes (bn : Name) (h : Heap) (c : Name) (bs : List UInt8) (lo hi : Option Value) :
    getSlice bn h (.bytes c bs) lo hi = (fun x => (x.1, h)) <$> getSlice bn Heap.empty (.bytes c bs) lo hi := by
  simp only [getSlice]
  cases sliceRange bs.length lo hi <;> rfl

/-- One fuel step of the expressions. -/
theorem exprStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    {fp : Footprint} {h0 : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (ih : EvF env fp h0 vs s L n ((den env fps n).expr fp s))
    (hF : FnOK env fps n) {h : Heap} (hI : CInv fp h0 h vs s L) :
    EvOK env h0.next h vs L (n + 1) (exprStep env fps n (den env fps n) fp s) := by
  have hr := hI.i.r
  intro e r hd
  cases e with
  | name l x =>
    have := name_sound hr x (l := l) hd
    rw [evalExpr]
    refine gok_of this fun rr w h' hrr hres => ?_
    cases rr with
    | tree d =>
      simp only [exprStep] at hd
      cases hx : s.loc x with
      | none =>
        rw [hx] at hd
        simp only [dGlobal] at hd
        split at hd <;> (try split at hd) <;> simp_all [DM.ok]
      | some r0 =>
        rw [hx] at hd
        simp [DM.ok] at hd; subst hd; cases hrr
        have hl := hr.loc x
        rw [hx] at hl
        cases hLx : L x with
        | none => rw [hLx] at hl; exact hl.elim
        | some w0 =>
          have hlk : lookupName env L x = .ok w0 := by simp [lookupName, hLx]
          rw [hlk] at hres
          simp at hres; obtain ⟨rfl, rfl⟩ := hres
          exact hI.tlo x _ _ hx hLx
    | _ => trivial
  | int l k =>
    simp [exprStep, DM.ok] at hd; subst hd
    rw [evalExpr]; exact ⟨Ext_refl h, trivial, rfl, rfl⟩
  | bool l b =>
    simp [exprStep, DM.ok] at hd; subst hd
    rw [evalExpr]; exact ⟨Ext_refl h, trivial, rfl, rfl⟩
  | noneLit l =>
    simp [exprStep, DM.ok] at hd; subst hd
    rw [evalExpr]; exact ⟨Ext_refl h, trivial, rfl, rfl⟩
  | attr l o f =>
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (ih h hI o _ he)
      simp [hi, gok_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI o _ he)
      have hI1 := hI.ext hx1
      simp only [hi, Except.bind_ok']
      refine gok_ext hx1 ?_
      cases ro with
      | tree _ => simp [dAttr] at hd2
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
            obtain ⟨nn, hn⟩ := deref_dec hI1.i.r hat hdr
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
                exact ⟨Ext_refl _, tlo_ofChild _ _ _ _, child_rel hat (by simp [okids, ho]) hx hdx⟩
  | index l o ie =>
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (ih h hI o _ he)
      simp [hi, gok_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI o _ he)
      have hI1 := hI.ext hx1
      simp only [hi, Except.bind_ok']
      refine gok_ext hx1 ?_
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ri, he2, hd3⟩
      · obtain ⟨hi2, hne⟩ := gok_error (ih h1 hI1 ie _ he2)
        simp [hi2, gok_err hne]
      · obtain ⟨wi, h2, hi2, hx2, hrel2⟩ := gok_ok (ih h1 hI1 ie _ he2)
        have hI2 := hI1.ext hx2
        simp only [hi2, Except.bind_ok']
        refine gok_ext hx2 ?_
        cases ro with
        | tree _ => simp [dIndex] at hd3
        | val _ => simp [dIndex] at hd3
        | place k p =>
        cases ri with
        | tree _ => simp [dIndex] at hd3
        | place _ _ => simp [dIndex] at hd3
        | val iv =>
        obtain ⟨a, rfl, hat⟩ := ERel_ext hI1.wf hI1.below hx2 hrel
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
            obtain ⟨nn, hn⟩ := deref_dec hI2.i.r hat hdr
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
                simp [← htr, gok_err (hne err htr.symm)]
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
                    exact ⟨Ext_refl _, tlo_ofChild _ _ _ _, child_rel hat (by simp [okids, ho]) hx hdx⟩
  | binop l op a b =>
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (ih h hI a _ he)
      simp [hi, gok_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI a _ he)
      have hI1 := hI.ext hx1
      simp only [hi, Except.bind_ok']
      refine gok_ext hx1 ?_
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨rb, he2, hd3⟩
      · obtain ⟨hi2, hne⟩ := gok_error (ih h1 hI1 b _ he2)
        simp [hi2, gok_err hne]
      · obtain ⟨wb, h2, hi2, hx2, hrel2⟩ := gok_ok (ih h1 hI1 b _ he2)
        simp only [hi2, Except.bind_ok']
        refine gok_ext hx2 ?_
        cases ra with
        | tree _ => simp [dBinop] at hd3
        | place _ _ => simp [dBinop] at hd3
        | val x =>
        cases rb with
        | tree _ => simp [dBinop] at hd3
        | place _ _ => simp [dBinop] at hd3
        | val y =>
        obtain ⟨rfl, hx⟩ := hrel
        obtain ⟨rfl, hy⟩ := hrel2
        simp only [dBinop] at hd3
        rw [seqBinop_flat (flat_nonref hx) (flat_nonref hy)]
        rcases bind_case hd3 with ⟨err, ht, rfl⟩ | ⟨v, ht, hd4⟩
        · obtain ⟨htr, hne⟩ := lift_some ht
          simp [← htr, gok_err (hne err htr.symm)]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [← htr, Except.bind_ok']
          by_cases hv : Flat v = true
          · simp [hv, DM.ok] at hd4; subst hd4; exact ⟨Ext_refl _, trivial, rfl, hv⟩
          · simp [hv] at hd4
  | compare l a rest =>
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (ih h hI a _ he)
      simp [hi, gok_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI a _ he)
      simp only [hi, Except.bind_ok']
      refine gok_ext hx1 ?_
      cases ra with
      | tree _ => simp at hd2
      | place _ _ => simp at hd2
      | val x =>
        obtain ⟨rfl, hx⟩ := hrel
        exact cmpOf_sound ih rest h1 _ r (hI.ext hx1) hx hd2
  | boolop l op es =>
    simp only [exprStep] at hd
    rw [evalExpr]
    exact boolOf_sound ih es h op r hI hd
  | ifExp l c a b =>
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rc, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (ih h hI c _ he)
      simp [hi, gok_err hne]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI c _ he)
      have hI1 := hI.ext hx1
      simp only [hi, Except.bind_ok']
      refine gok_ext hx1 ?_
      cases rc with
      | tree _ => simp at hd2
      | place _ _ => simp at hd2
      | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp only at hd2
        rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨t, ht, hd3⟩
        · obtain ⟨htr, hne⟩ := lift_some ht
          simp [truthyH_flat h1 hv, ← htr, gok_err (hne err htr.symm)]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [truthyH_flat h1 hv, ← htr, Except.bind_ok']
          cases t with
          | true => simp only [↓reduceIte] at hd3 ⊢; exact ih h1 hI1 a _ hd3
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hd3 ⊢; exact ih h1 hI1 b _ hd3
  | call l fn args =>
    simp only [exprStep] at hd
    cases n with
    | zero => simp at hd
    | succ m =>
      cases hch : callHead env s (.call l fn args) with
      | none => simp [hch] at hd
      | some ga =>
        obtain ⟨g, args'⟩ := ga
        obtain ⟨l1, l', he, hloc, hc⟩ := callHead_spec hch
        cases he
        simp only [hch] at hd
        exact roCall_sound hlf hI ih hF hloc hc hd
  | unop l op a =>
    cases op with
    | not =>
      simp only [exprStep] at hd
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
      · obtain ⟨hi, hne⟩ := gok_error (ih h hI a _ he)
        simp [hi, gok_err hne]
      · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI a _ he)
        simp only [hi, Except.bind_ok']
        refine gok_ext hx1 ?_
        cases ra with
        | tree _ => simp at hd2
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          simp only at hd2
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [truthyH_flat h1 hv, ← htr, gok_err (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp [DM.ok] at hd3; subst hd3
            simp [truthyH_flat h1 hv, ← htr]
            exact ⟨Ext_refl _, trivial, rfl, rfl⟩
    | neg =>
      simp (disch := decide) only [exprStep] at hd
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
      · obtain ⟨hi, hne⟩ := gok_error (ih h hI a _ he)
        simp [hi, gok_err hne]
      · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI a _ he)
        simp only [hi, Except.bind_ok']
        refine gok_ext hx1 ?_
        cases ra with
        | tree _ => simp at hd2
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          simp only at hd2
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨x, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [← htr, gok_err (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp only [← htr, Except.bind_ok']
            by_cases hx : Flat x = true
            · simp [hx, DM.ok] at hd3; subst hd3; exact ⟨Ext_refl _, trivial, rfl, hx⟩
            · simp [hx] at hd3
      all_goals (intro hx; cases hx)
    | invert =>
      simp (disch := decide) only [exprStep] at hd
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
      · obtain ⟨hi, hne⟩ := gok_error (ih h hI a _ he)
        simp [hi, gok_err hne]
      · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI a _ he)
        simp only [hi, Except.bind_ok']
        refine gok_ext hx1 ?_
        cases ra with
        | tree _ => simp at hd2
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          simp only at hd2
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨x, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [← htr, gok_err (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp only [← htr, Except.bind_ok']
            by_cases hx : Flat x = true
            · simp [hx, DM.ok] at hd3; subst hd3; exact ⟨Ext_refl _, trivial, rfl, hx⟩
            · simp [hx] at hd3
      all_goals (intro hx; cases hx)
  | slice l o lo up st =>
    cases st with
    | some _ => simp [exprStep] at hd
    | none =>
      simp only [exprStep] at hd
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
      · obtain ⟨hi, hne⟩ := gok_error (ih h hI o _ he)
        simp [hi, gok_err hne]
      · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (ih h hI o _ he)
        have hI1 := hI.ext hx1
        simp only [hi, Except.bind_ok']
        refine gok_ext hx1 ?_
        cases ro with
        | tree _ => simp at hd2
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          cases w with
          | bytes c bs =>
            simp only at hd2
            rcases bind_case hd2 with ⟨err, h1e, rfl⟩ | ⟨lov, h1e, hd3⟩
            · have := optOf_sound ih hI1 lo _ h1e
              revert this
              cases evalOpt env n L h1 lo with
              | error e' => rintro ⟨rfl, hne⟩; simp [gok_err hne]
              | ok q => intro hx; cases hx
            · have := optOf_sound ih hI1 lo _ h1e
              revert this
              cases evalOpt env n L h1 lo with
              | error e' => intro hx; cases hx
              | ok q =>
                obtain ⟨lov', h2⟩ := q
                rintro ⟨hx2, rfl, -⟩
                have hI2 := hI1.ext hx2
                simp only [Except.bind_ok']
                refine gok_ext hx2 ?_
                rcases bind_case hd3 with ⟨err, h3, rfl⟩ | ⟨hiv, h3, hd4⟩
                · have := optOf_sound ih hI2 up _ h3
                  revert this
                  cases evalOpt env n L h2 up with
                  | error e' => rintro ⟨rfl, hne⟩; simp [gok_err hne]
                  | ok q => intro hx; cases hx
                · have := optOf_sound ih hI2 up _ h3
                  revert this
                  cases evalOpt env n L h2 up with
                  | error e' => intro hx; cases hx
                  | ok q =>
                    obtain ⟨hiv', h4⟩ := q
                    rintro ⟨hx4, rfl, -⟩
                    simp only [Except.bind_ok']
                    refine gok_ext hx4 ?_
                    rw [getSlice_bytes]
                    cases hk : getSlice env.bytesName Heap.empty (.bytes c bs) lov' hiv' with
                    | error e' =>
                      rw [hk] at hd4
                      by_cases ho : e' = .outOfFuel
                      · subst ho; simp [lift, DM.bind] at hd4
                      · rw [lift_err e' ho] at hd4
                        simp [DM.bind] at hd4; subst hd4; exact ⟨rfl, ho⟩
                    | ok q =>
                      rw [hk, lift_ok] at hd4
                      simp only [DM.bind] at hd4
                      by_cases hx : Flat q.1 = true
                      · simp [hx, DM.ok] at hd4; subst hd4; exact ⟨Ext_refl _, trivial, rfl, hx⟩
                      · simp [hx] at hd4
          | _ => simp at hd2
  | _ => simp [exprStep] at hd

end SpecLean.Layer4
