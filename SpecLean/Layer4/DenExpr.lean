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

/-- The expressions at fuel `n` agree with the interpreter. -/
def EvOK (env : Env) (h : Heap) (vs : List Value) (L : Locals) (n : Nat)
    (ev : Expr → DM DRes) : Prop :=
  ∀ e r, ev e = some r → ExprOK h vs r (evalExpr env n L h e)

/-- The function bodies at fuel `n` agree with `callFn n`. -/
def FnOK (env : Env) (fps : Name → Footprint) (n : Nat) : Prop :=
  ∀ (fp : Footprint) (d : FunctionDef) (roots : List DV) (vs : List Value) (h : Heap)
    (r : Res (Value × List DV)), DecArgs h vs roots → WTree h vs fp →
    (den env fps n).fn fp d roots = some r →
    FnRel fp h vs r (callFn env n d.params (.stmts d.body) Locals.empty vs [] h)

def ArgsOK (h : Heap) (vs : List Value) :
    Res (List DRes) → Res (List Value × List (Name × Value) × Heap) → Prop
  | .ok rs, .ok (ws, kws, h') => h' = h ∧ kws = [] ∧ ERels h vs rs ws
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem cmpOf_sound {env : Env} {h : Heap} {vs : List Value} {L : Locals} {n : Nat}
    {ev : Expr → DM DRes} (hE : EvOK env h vs L n ev) :
    ∀ (rest : List (CmpOp × Expr)) (x : Value) (r : Res DRes), Flat x = true →
      cmpOf ev x rest = some r → ExprOK h vs r (evalCmp env n L h x rest)
  | [], x, r, _, hd => by
    simp [cmpOf, DM.ok] at hd; subst hd
    rw [evalCmp]; exact ⟨rfl, rfl, rfl⟩
  | (op, e) :: rest, x, r, hx, hd => by
    simp only [cmpOf] at hd
    rw [evalCmp]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ry, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he)
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he)
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
          | true => simp only [↓reduceIte] at hd3 ⊢; exact cmpOf_sound hE rest _ r hy hd3
          | false =>
            simp [DM.ok] at hd3; subst hd3
            exact ⟨rfl, rfl, rfl⟩

theorem boolOf_sound {env : Env} {h : Heap} {vs : List Value} {L : Locals} {n : Nat}
    {ev : Expr → DM DRes} (hE : EvOK env h vs L n ev) :
    ∀ (es : List Expr) (op : BoolOp) (r : Res DRes),
      boolOf ev op es = some r → ExprOK h vs r (evalBoolOp env n L h op es)
  | [], _, _, hd => by simp [boolOf] at hd
  | e :: es, op, r, hd => by
    simp only [boolOf] at hd
    rw [evalBoolOp]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he)
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he)
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
              | exact boolOf_sound hE es _ r hd3
              | (subst hd3; exact ⟨rfl, rfl, hv⟩)

theorem argsOf_sound {env : Env} {h : Heap} {vs : List Value} {L : Locals} {n : Nat}
    {ev : Expr → DM DRes} (hE : EvOK env h vs L n ev) :
    ∀ (args : List Arg) (r : Res (List DRes)), argsOf ev args = some r →
      ArgsOK h vs r (evalArgs env n L h args)
  | [], r, hd => by
    simp [argsOf, DM.ok] at hd; subst hd
    rw [evalArgs]; exact ⟨rfl, rfl, trivial⟩
  | .pos e :: as, r, hd => by
    simp only [argsOf] at hd
    rw [evalArgs]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he)
      simp [hi, hne, ArgsOK]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he)
      simp only [hi, Except.bind_ok']
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨rs, he2, hd3⟩
      · have := argsOf_sound hE as _ he2
        revert this
        cases evalArgs env n L h as with
        | error e' => rintro ⟨rfl, hne⟩; simp [hne, ArgsOK]
        | ok q => intro hx; cases hx
      · simp [DM.ok] at hd3; subst hd3
        have := argsOf_sound hE as _ he2
        revert this
        cases evalArgs env n L h as with
        | error e' => intro hx; cases hx
        | ok q =>
          obtain ⟨ws, kws, h2⟩ := q
          rintro ⟨rfl, rfl, hr⟩
          simp only [Except.bind_ok', Except.pure_ok']
          exact ⟨rfl, rfl, And.intro hrel hr⟩
  | .starred _ :: _, r, hd => by simp [argsOf] at hd
  | .kw _ _ :: _, r, hd => by simp [argsOf] at hd

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
    (hI : CInv fp h0 h vs s L) (ih : EvOK env h vs L (m + 1) ((den env fps (m + 1)).expr fp s))
    (hF : FnOK env fps (m + 1)) {g : Name} {l l' : Line} {args : List Arg}
    (hloc : s.loc g = none) (hc : callable env g = true) {r : Res DRes}
    (hd : DM.bind (argsOf ((den env fps (m + 1)).expr fp s) args)
      (fun rs => dCallRO env fps (den env fps (m + 1)).fn s g rs) = some r) :
    ExprOK h vs r (evalExpr env (m + 2) L h (.call l (.name l' g) args)) := by
  have hL : L g = none := by
    have := hI.i.r.loc g; rw [hloc] at this
    revert this; cases L g <;> simp [LRel]
  obtain ⟨hlk, hany⟩ := callable_lookup hc hL
  rw [evalExpr]
  have hname : evalExpr env (m + 1) L h (.name l' g) = .ok (.glob g, h) := by
    rw [evalExpr]; simp [hlk]
  simp only [hname, Except.bind_ok', hany]
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rs, he, hd2⟩
  · have := argsOf_sound ih args _ he
    revert this
    cases evalArgs env (m + 1) L h args with
    | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
    | ok q => intro hx; cases hx
  · have := argsOf_sound ih args _ he
    revert this
    cases hea : evalArgs env (m + 1) L h args with
    | error e' => intro hx; cases hx
    | ok q =>
      obtain ⟨ws, kws, h2⟩ := q
      rintro ⟨hh, rfl, hrel⟩
      subst h2
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
              · have := hF [] d rg ws h _ (argRoots_dec hI.i.r hrel hm) (fun _ _ hp => by simp at hp) hf
                revert this
                cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty ws [] h with
                | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
                | ok q => intro hx; cases hx
              · have := hF [] d rg ws h _ (argRoots_dec hI.i.r hrel hm) (fun _ _ hp => by simp at hp) hf
                revert this
                cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty ws [] h with
                | error e' => intro hx; cases hx
                | ok q =>
                  obtain ⟨w, h'⟩ := q
                  rintro ⟨rfl, -, -, -, hro⟩
                  cases hro rfl
                  by_cases hv : Flat w = true
                  · simp [hv, DM.ok] at hd3; subst hd3; exact ⟨rfl, rfl, hv⟩
                  · simp [hv] at hd3
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
              rw [hlf.ctor h t ws hct hfl]
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
                  · simp [hv, DM.ok] at hd3; subst hd3; exact ⟨rfl, rfl, hv⟩
                  · simp [hv] at hd3
          · cases hd2
        | builtin b =>
          simp only at hd2
          have hnf : b ≠ .filter := by rintro rfl; simp [dBuiltin] at hd2
          have hns : b ≠ .sorted := by rintro rfl; simp [dBuiltin] at hd2
          rw [callValue_builtin _ _ _ hg hnf hns]
          have minmax : ∀ (isMin : Bool), dBuiltin s (if isMin then .min else .max) rs = some r →
              ExprOK h vs r (applyBuiltin env h (if isMin then .min else .max) ws []) := by
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
                  · simp [hv, DM.ok] at hd4; subst hd4; exact ⟨rfl, rfl, hv⟩
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
                  obtain ⟨nn, hn⟩ := deref_dec hI.i.r hat hdr
                  obtain ⟨a', mm, xs, ha, -, ho, hm⟩ := dec_list hn
                  cases ha
                  have hlen := ((mapM_some_iff xs ds).mp hm).1
                  simp [applyBuiltin, hlf.builtin h .len _ [] (by simp), ho, hlen]
                  exact ⟨rfl, rfl, rfl⟩
            | [.val _], _, _, hd2 => simp at hd2
            | [], _, _, hd2 => simp at hd2
            | _ :: _ :: _, _, _, hd2 => simp at hd2
          all_goals simp [dBuiltin] at hd2
        | _ => simp at hd2

def OptOK (h : Heap) : Res (Option Value) → Res (Option Value × Heap) → Prop
  | .ok ov, .ok (ov', h') => h' = h ∧ ov' = ov ∧ ∀ v, ov = some v → Flat v = true
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem optOf_sound {env : Env} {h : Heap} {vs : List Value} {L : Locals} {n : Nat}
    {ev : Expr → DM DRes} (hE : EvOK env h vs L n ev) :
    ∀ (o : Option Expr) (r : Res (Option Value)), optOf ev o = some r → OptOK h r (evalOpt env n L h o)
  | none, r, hd => by
    simp [optOf, DM.ok] at hd; subst hd
    rw [evalOpt]; exact ⟨rfl, rfl, by simp⟩
  | some e, r, hd => by
    simp only [optOf] at hd
    rw [evalOpt]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (hE e _ he)
      simp [hi, hne, OptOK]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (hE e _ he)
      simp only [hi, Except.bind_ok']
      cases rv with
      | place _ _ => simp at hd2
      | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp [DM.ok] at hd2; subst hd2
        exact ⟨rfl, rfl, by simp [hv]⟩

theorem getSlice_bytes (bn : Name) (h : Heap) (c : Name) (bs : List UInt8) (lo hi : Option Value) :
    getSlice bn h (.bytes c bs) lo hi = (fun x => (x.1, h)) <$> getSlice bn Heap.empty (.bytes c bs) lo hi := by
  simp only [getSlice]
  cases sliceRange bs.length lo hi <;> rfl

/-- One fuel step of the expressions. -/
theorem exprStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (ih : EvOK env h vs L n ((den env fps n).expr fp s))
    (hF : FnOK env fps n) :
    EvOK env h vs L (n + 1) (exprStep env fps n (den env fps n) fp s) := by
  have hr := hI.i.r
  intro e r hd
  cases e with
  | name l x =>
    have := name_sound hr x (l := l) hd
    rw [evalExpr]; exact this
  | int l k =>
    simp [exprStep, DM.ok] at hd; subst hd
    rw [evalExpr]; exact ⟨rfl, rfl, rfl⟩
  | bool l b =>
    simp [exprStep, DM.ok] at hd; subst hd
    rw [evalExpr]; exact ⟨rfl, rfl, rfl⟩
  | noneLit l =>
    simp [exprStep, DM.ok] at hd; subst hd
    rw [evalExpr]; exact ⟨rfl, rfl, rfl⟩
  | attr l o f =>
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (ih o _ he)
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih o _ he)
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
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (ih o _ he)
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih o _ he)
      simp only [hi, Except.bind_ok']
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨ri, he2, hd3⟩
      · obtain ⟨hi2, hne⟩ := exprOK_error (ih ie _ he2)
        simp [hi2, error_ok hne]
      · obtain ⟨wi, hi2, hrel2⟩ := exprOK_ok (ih ie _ he2)
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
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (ih a _ he)
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih a _ he)
      simp only [hi, Except.bind_ok']
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨rb, he2, hd3⟩
      · obtain ⟨hi2, hne⟩ := exprOK_error (ih b _ he2)
        simp [hi2, error_ok hne]
      · obtain ⟨wb, hi2, hrel2⟩ := exprOK_ok (ih b _ he2)
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
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (ih a _ he)
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih a _ he)
      simp only [hi, Except.bind_ok']
      cases ra with
      | place _ _ => simp at hd2
      | val x =>
        obtain ⟨rfl, hx⟩ := hrel
        exact cmpOf_sound ih rest _ r hx hd2
  | boolop l op es =>
    simp only [exprStep] at hd
    rw [evalExpr]
    exact boolOf_sound ih es op r hd
  | ifExp l c a b =>
    simp only [exprStep] at hd
    rw [evalExpr]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rc, he, hd2⟩
    · obtain ⟨hi, hne⟩ := exprOK_error (ih c _ he)
      simp [hi, error_ok hne]
    · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih c _ he)
      simp only [hi, Except.bind_ok']
      cases rc with
      | place _ _ => simp at hd2
      | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp only at hd2
        rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨t, ht, hd3⟩
        · obtain ⟨htr, hne⟩ := lift_some ht
          simp [truthyH_flat h hv, ← htr, error_ok (hne err htr.symm)]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [truthyH_flat h hv, ← htr, Except.bind_ok']
          cases t with
          | true => simp only [↓reduceIte] at hd3 ⊢; exact ih a _ hd3
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hd3 ⊢; exact ih b _ hd3
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
      · obtain ⟨hi, hne⟩ := exprOK_error (ih a _ he)
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih a _ he)
        simp only [hi, Except.bind_ok']
        cases ra with
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          simp only at hd2
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [truthyH_flat h hv, ← htr, error_ok (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp [DM.ok] at hd3; subst hd3
            simp [truthyH_flat h hv, ← htr]
            exact ⟨rfl, rfl, rfl⟩
    | neg =>
      simp (disch := decide) only [exprStep] at hd
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (ih a _ he)
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih a _ he)
        simp only [hi, Except.bind_ok']
        cases ra with
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          simp only at hd2
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨x, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [← htr, error_ok (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp only [← htr, Except.bind_ok']
            by_cases hx : Flat x = true
            · simp [hx, DM.ok] at hd3; subst hd3; exact ⟨rfl, rfl, hx⟩
            · simp [hx] at hd3
      all_goals (intro hx; cases hx)
    | invert =>
      simp (disch := decide) only [exprStep] at hd
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ra, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (ih a _ he)
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih a _ he)
        simp only [hi, Except.bind_ok']
        cases ra with
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          simp only at hd2
          rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨x, ht, hd3⟩
          · obtain ⟨htr, hne⟩ := lift_some ht
            simp [← htr, error_ok (hne err htr.symm)]
          · obtain ⟨htr, -⟩ := lift_some ht
            simp only [← htr, Except.bind_ok']
            by_cases hx : Flat x = true
            · simp [hx, DM.ok] at hd3; subst hd3; exact ⟨rfl, rfl, hx⟩
            · simp [hx] at hd3
      all_goals (intro hx; cases hx)
  | slice l o lo up st =>
    cases st with
    | some _ => simp [exprStep] at hd
    | none =>
      simp only [exprStep] at hd
      rw [evalExpr]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ro, he, hd2⟩
      · obtain ⟨hi, hne⟩ := exprOK_error (ih o _ he)
        simp [hi, error_ok hne]
      · obtain ⟨w, hi, hrel⟩ := exprOK_ok (ih o _ he)
        simp only [hi, Except.bind_ok']
        cases ro with
        | place _ _ => simp at hd2
        | val v =>
          obtain ⟨rfl, hv⟩ := hrel
          cases w with
          | bytes c bs =>
            simp only at hd2
            rcases bind_case hd2 with ⟨err, h1, rfl⟩ | ⟨lov, h1, hd3⟩
            · have := optOf_sound ih lo _ h1
              revert this
              cases evalOpt env n L h lo with
              | error e' => rintro ⟨rfl, hne⟩; simp [error_ok hne]
              | ok q => intro hx; cases hx
            · have := optOf_sound ih lo _ h1
              revert this
              cases evalOpt env n L h lo with
              | error e' => intro hx; cases hx
              | ok q =>
                obtain ⟨lov', h2⟩ := q
                rintro ⟨hh, rfl, -⟩
                subst h2
                simp only [Except.bind_ok']
                rcases bind_case hd3 with ⟨err, h3, rfl⟩ | ⟨hiv, h3, hd4⟩
                · have := optOf_sound ih up _ h3
                  revert this
                  cases evalOpt env n L h up with
                  | error e' => rintro ⟨rfl, hne⟩; simp [error_ok hne]
                  | ok q => intro hx; cases hx
                · have := optOf_sound ih up _ h3
                  revert this
                  cases evalOpt env n L h up with
                  | error e' => intro hx; cases hx
                  | ok q =>
                    obtain ⟨hiv', h4⟩ := q
                    rintro ⟨hh, rfl, -⟩
                    subst h4
                    simp only [Except.bind_ok']
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
                      · simp [hx, DM.ok] at hd4; subst hd4; exact ⟨rfl, rfl, hx⟩
                      · simp [hx] at hd4
          | _ => simp at hd2
  | _ => simp [exprStep] at hd

end SpecLean.Layer4
