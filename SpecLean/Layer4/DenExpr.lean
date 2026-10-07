import SpecLean.Layer4.EncDV
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
  /-- The library leaves `len`, `min`, `max`, `enumerate` and `sum` to the core. -/
  builtin : ∀ h b args kws, (b = .len ∨ b = .min ∨ b = .max ∨ b = .enumerate ∨ b = .sum) →
    LibModel.builtin env h b args kws = none
  /-- A container from keyword arguments, all fields given and flat: a new object. -/
  kwctor : ∀ h ty fs kvs (r : Res (List Value)), env.containers.lookup ty = some fs →
    kvs.all (fun kv => (fs.map (·.1)).contains kv.1) = true → kwFields kvs fs = some r →
    LibModel.construct env h (.container ty) [] kvs =
      (fun ws => (Value.ref (h.alloc (.container ty ws)).1, (h.alloc (.container ty ws)).2)) <$> r
  /-- `o.append(v)` on a list that `appendable` admits: coerce `v` as an item, check the limit,
  add it at the end. -/
  append : ∀ h a k e l xs v, h.objs a = some (.list k e l xs) → appendable k e = true →
    applyMethod env h (.ref a) env.nm.append [v] =
      (coerceWith env false h e v).bind fun x =>
        (Ssz.checkLength k l (xs.length + 1)).bind fun _ =>
          .ok (.none, x.2.set a (.list k e l (xs ++ [x.1])))
  /-- The library leaves `int.from_bytes` to the core. -/
  fromBytesM : ∀ h g args, env.globals.lookup g = some (.builtin .int) →
    LibModel.method env h (.glob g) env.nm.fromBytes args = none
  /-- The library leaves `bls.f` to the core. -/
  blsM : ∀ h g f args, env.globals.lookup g = some (.module .bls) →
    LibModel.method env h (.glob g) f args = none
  /-- The BLS oracle on flat values does not read the heap. -/
  blsFlat : ∀ h f vs, (∀ v ∈ vs, Flat v = true) → env.bls f h vs = env.bls f Heap.empty vs
  /-- `hash_tree_root` is the oracle of the environment. -/
  htr : ∀ h v, LibModel.builtin env h .hashTreeRoot [v] [] =
    some (do pure (.bytes env.nm.root (← env.hashTreeRoot h v), h))
  /-- The oracle reads only the decoded content of a value. -/
  htrDec : ∀ h v h' v' n n' d, dec h n v = some d → dec h' n' v' = some d →
    env.hashTreeRoot h v = env.hashTreeRoot h' v'
  /-- A container of class `ty` is an item of type `container ty` as it is. -/
  coerceCont : ∀ h b ty fs, h.objs b = some (.container ty fs) →
    coerceWith env false h (.container ty) (.ref b) = .ok (.ref b, h)

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
theorem callValue_type_kw {env : Env} (n : Nat) {g : Name} {t : SszTy} (vs : List Value)
    (kws : List (Name × Value)) (h : Heap) (hg : env.globals.lookup g = some (.type t)) :
    callValue env n (.glob g) vs kws h = LibModel.construct env h t vs kws := by
  rw [callValue.eq_def]; simp only [hg]

theorem kwFields_noOof {kvs : List (Name × Value)} :
    ∀ (fs : List (Name × SszTy)) (e : SpecError), kwFields kvs fs = some (.error e) → e ≠ .outOfFuel
  | [], e, hk => by simp [kwFields, DM.ok] at hk
  | (f, ft) :: fs, e, hk => by
    simp only [kwFields] at hk
    split at hk
    · split at hk
      · rcases bind_case hk with ⟨err, hl, he⟩ | ⟨w, hl, hk2⟩
        · cases he; exact (lift_some hl).2 e (lift_some hl).1.symm
        · split at hk2
          · rcases bind_case hk2 with ⟨err, hl2, he⟩ | ⟨ws, hl2, hk3⟩
            · cases he; exact kwFields_noOof fs e hl2
            · simp [DM.ok] at hk3
          · cases hk2
      · cases hk
    · cases hk

theorem kwFields_flat {kvs : List (Name × Value)} :
    ∀ (fs : List (Name × SszTy)) (ws : List Value), kwFields kvs fs = some (.ok ws) → ∀ w ∈ ws, Flat w = true
  | [], ws, hk => by simp [kwFields, DM.ok] at hk; subst hk; simp
  | (f, ft) :: fs, ws, hk => by
    simp only [kwFields] at hk
    split at hk
    · split at hk
      · rcases bind_case hk with ⟨err, hl, he⟩ | ⟨w, hl, hk2⟩
        · cases he
        · split at hk2
          · next hw =>
            rcases bind_case hk2 with ⟨err, hl2, he⟩ | ⟨ws', hl2, hk3⟩
            · cases he
            · simp [DM.ok] at hk3; subst hk3
              intro x hx
              simp at hx
              rcases hx with rfl | hx
              · exact hw
              · exact kwFields_flat fs ws' hl2 x hx
          · cases hk2
      · cases hk
    · cases hk

/-- A new container of flat fields: a new tree, related to the new reference. -/
theorem alloc_cont {lo : Nat} {h : Heap} {vs : List Value} (hb : BelowArgs h vs) (hlo : lo ≤ h.next)
    {ty : Name} {xs : List Value} (hf : ∀ v ∈ xs, Flat v = true) :
    GOK lo h vs (.ok (.tree (.cont ty (xs.map DV.leaf))))
      (.ok (.ref (h.alloc (.container ty xs)).1, (h.alloc (.container ty xs)).2)) := by
  have he := Ext_alloc h (.container ty xs)
  have hobj : (h.alloc (.container ty xs)).2.objs h.next = some (.container ty xs) := by
    simp [Heap.alloc]
  have hpath : ∀ q b, follow (h.alloc (.container ty xs)).2 (.ref h.next) q = some (.ref b) →
      b = h.next := by
    intro q b e
    cases q with
    | nil => simp [follow] at e; exact e.symm
    | cons j q =>
      rw [follow_ref_cons, hobj] at e
      simp only [okids, Option.bind_some] at e
      cases hx : xs[j]? with
      | none => simp [hx] at e
      | some x =>
        simp only [hx, Option.bind_some] at e
        have hfx : Flat x = true := hf x (List.mem_of_getElem? hx)
        exact absurd e (fun e' => follow_nonref_ref (flat_nonref hfx) e')
  have ha : (h.alloc (.container ty xs)).1 = h.next := rfl
  rw [ha]
  simp only [GOK]
  refine ⟨he, fun q b e => (hpath q b e) ▸ hlo, ⟨2, ?_⟩, fun q b e k p ep => ?_⟩
  · rw [dec_ref_succ, hobj]
    have : xs.mapM (dec (h.alloc (.container ty xs)).2 1) = some (xs.map DV.leaf) := by
      rw [mapM_some_iff]
      refine ⟨by simp, fun i x hx => ?_⟩
      have hfx : Flat x = true := hf x (List.mem_of_getElem? hx)
      simp [dec_flat hfx, hx]
    simp [this]
  · have hb' := hpath q b e
    subst hb'
    have hlt := at?_below hb ((at?_Ext he hb k p h.next).mp ep)
    omega

def KwsOK : Res (List (Name × Value)) → Res (List Value × List (Name × Value) × Heap) → Heap → Prop
  | .ok kvs, .ok (ws, kws, h'), h => Ext h h' ∧ ws = [] ∧ kws = kvs
  | .error e, .error e', _ => e' = e ∧ e ≠ .outOfFuel
  | _, _, _ => False

theorem kwsOf_sound {env : Env} {fp : Footprint} {h0 : Heap} {vs : List Value} {s : DSt} {L : Locals}
    {n : Nat} {ev : Expr → DM DRes} (hE : EvF env fp h0 vs s L n ev) :
    ∀ (args : List Arg) (h : Heap) (r : Res (List (Name × Value))), CInv fp h0 h vs s L →
      kwsOf ev args = some r → KwsOK r (evalArgs env n L h args) h
  | [], h, r, _, hd => by
    simp [kwsOf, DM.ok] at hd; subst hd
    rw [evalArgs]; exact ⟨Ext_refl h, rfl, rfl⟩
  | .kw k e :: as, h, r, hI, hd => by
    simp only [kwsOf] at hd
    rw [evalArgs]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE h hI e _ he)
      simp [hi, hne, KwsOK]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE h hI e _ he)
      have hI1 := hI.ext hx1
      simp only [hi, Except.bind_ok']
      cases rv with
      | place _ _ => cases hd2
      | tree _ => cases hd2
      | val v =>
      obtain ⟨rfl, -⟩ := hrel
      simp only at hd2
      rcases bind_case hd2 with ⟨err, he2, rfl⟩ | ⟨rest, he2, hd3⟩
      · have := kwsOf_sound hE as h1 _ hI1 he2
        revert this
        cases evalArgs env n L h1 as with
        | error e' => rintro ⟨rfl, hne⟩; simp [hne, KwsOK]
        | ok q => intro hx; cases hx
      · simp [DM.ok] at hd3; subst hd3
        have := kwsOf_sound hE as h1 _ hI1 he2
        revert this
        cases evalArgs env n L h1 as with
        | error e' => intro hx; cases hx
        | ok q =>
          obtain ⟨ws, kws, h2⟩ := q
          rintro ⟨hx2, rfl, rfl⟩
          simp only [Except.bind_ok', Except.pure_ok']
          exact ⟨Ext_trans hx1 hx2, rfl, rfl⟩
  | .pos _ :: _, _, r, _, hd => by simp [kwsOf] at hd
  | .starred _ :: _, _, r, _, hd => by simp [kwsOf] at hd

theorem kwCall_sound {env : Env} (hlf : LibFlat env) {m : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals} {ev : Expr → DM DRes}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L (m + 1) ev)
    {g : Name} {l l' : Line} {args : List Arg}
    (hloc : s.loc g = none) (hc : callable env g = true) {r : Res DRes}
    (hd : DM.bind (kwsOf ev args) (fun kvs => kwCtor env g kvs) = some r) :
    GOK h0.next h vs r (evalExpr env (m + 2) L h (.call l (.name l' g) args)) := by
  have hL : L g = none := by
    have := hI.i.r.loc g; rw [hloc] at this
    revert this; cases L g <;> simp [LRel]
  obtain ⟨hlk, hany⟩ := callable_lookup hc hL
  rw [evalExpr]
  have hname : evalExpr env (m + 1) L h (.name l' g) = .ok (.glob g, h) := by
    rw [evalExpr]; simp [hlk]
  simp only [hname, Except.bind_ok', hany]
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨kvs, he, hd2⟩
  · have := kwsOf_sound ih args h _ hI he
    revert this
    cases evalArgs env (m + 1) L h args with
    | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
    | ok q => intro hx; cases hx
  · have := kwsOf_sound ih args h _ hI he
    revert this
    cases hea : evalArgs env (m + 1) L h args with
    | error e' => intro hx; cases hx
    | ok q =>
      obtain ⟨ws, kws, h2⟩ := q
      rintro ⟨hx2, rfl, rfl⟩
      have hI2 := hI.ext hx2
      refine gok_ext hx2 ?_
      simp only [Except.bind_ok']
      unfold kwCtor at hd2
      cases hg : env.globals.lookup g with
      | none => simp [hg] at hd2
      | some gl =>
      rw [hg] at hd2
      cases gl with
      | type t =>
        cases t with
        | container ty =>
          simp only at hd2
          rw [callValue_type_kw _ _ _ _ hg]
          cases hfs : env.containers.lookup ty with
          | none => simp [hfs] at hd2
          | some fs =>
          rw [hfs] at hd2
          simp only at hd2
          split at hd2
          · next hall =>
            rcases bind_case hd2 with ⟨err, hk, rfl⟩ | ⟨ws, hk, hd3⟩
            · rw [hlf.kwctor h2 ty fs kws _ hfs hall hk]
              exact ⟨rfl, kwFields_noOof fs err hk⟩
            · rw [hlf.kwctor h2 ty fs kws _ hfs hall hk]
              simp [DM.ok] at hd3; subst hd3
              exact alloc_cont hI2.below hI2.i.fresh.1 (kwFields_flat fs ws hk)
          · cases hd2
        | _ => simp at hd2
      | _ => simp at hd2

theorem mapM_leafVals {h : Heap} {m : Nat} :
    ∀ (xs : List Value) (ds : List DV) (vs : List Value), xs.mapM (dec h m) = some ds →
      leafVals ds = some vs → xs = vs
  | [], ds, vs, hm, hl => by simp at hm; subst hm; simp [leafVals] at hl; exact hl.symm
  | x :: xs, ds, vs, hm, hl => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hm
    obtain ⟨d, hd, ds', hds', e⟩ := hm
    simp at e; subst e
    cases d with
    | leaf u =>
      simp only [leafVals, Option.map_eq_some_iff] at hl
      obtain ⟨vs', hl', rfl⟩ := hl
      obtain ⟨rfl, -⟩ := dec_leaf hd
      rw [mapM_leafVals xs ds' vs' hds' hl']
    | cont _ _ => simp [leafVals] at hl
    | list _ _ _ _ => simp [leafVals] at hl

/-- `sum` of a list object whose items decode to `ds`. -/
theorem dSum_sound {env : Env} (hlf : LibFlat env) {lo : Nat} {h : Heap} {vs : List Value}
    {a : Nat} {kd : ListKind} {el : SszTy} {ll : Option Nat} {xs : List Value} {m : Nat}
    {ds : List DV} (ho : h.objs a = some (.list kd el ll xs)) (hm : xs.mapM (dec h m) = some ds)
    {r : Res DRes} (hd : dSum kd el ds = some r) :
    GOK lo h vs r (applyBuiltin env h .sum [.ref a] []) := by
  unfold dSum at hd
  cases hb : isByteList kd el with
  | true => simp [hb] at hd
  | false =>
  simp only [hb, Bool.false_eq_true, ↓reduceIte] at hd
  cases hl : leafVals ds with
  | none => simp [hl] at hd
  | some ys =>
  simp only [hl] at hd
  have hxy := mapM_leafVals xs ds ys hm hl
  subst hxy
  have hnb : ¬(kd = .list ∧ el = .uint (.width 8)) := by simpa [isByteList] using hb
  have hit : iterElems h (.ref a) = .ok xs := by
    simp only [iterElems, iterBase, ho]
    split
    · next heq => simp at heq; exact absurd ⟨heq.1, heq.2.1⟩ hnb
    · next heq => simp at heq; obtain ⟨-, -, -, rfl⟩ := heq; rfl
    all_goals (simp_all <;> (exfalso; rename_i hx; exact hx _ _ _ _ rfl rfl rfl rfl))
  simp only [applyBuiltin, hlf.builtin h .sum _ [] (by simp), hit, Except.bind_ok', List.headD_nil]
  rcases bind_case hd with ⟨err, hl2, rfl⟩ | ⟨w, hl2, hd2⟩
  · obtain ⟨hr, hne⟩ := lift_some hl2
    rw [← hr]; exact ⟨rfl, hne err hr.symm⟩
  · obtain ⟨hr, -⟩ := lift_some hl2
    rw [← hr]
    by_cases hv : Flat w = true
    · simp [hv, DM.ok] at hd2; subst hd2; exact ⟨Ext_refl _, trivial, rfl, hv⟩
    · simp [hv] at hd2

/-- `hash_tree_root` of a value that decodes to `d`. -/
theorem dHtr_sound {env : Env} (hlf : LibFlat env) {lo : Nat} {h : Heap} {vs : List Value}
    {w : Value} {n : Nat} {d : DV} (hn : dec h n w = some d) {r : Res DRes} (hd : dHtr env d = some r) :
    GOK lo h vs r (applyBuiltin env h .hashTreeRoot [w] []) := by
  obtain ⟨-, -, n', hd'⟩ := encDV_spec d Heap.empty (dec_leafFlat n w d hn)
  have he := hlf.htrDec h w _ _ n n' d hn hd'
  unfold dHtr at hd
  simp only [applyBuiltin, hlf.htr h w, he]
  rcases bind_case hd with ⟨err, hl, rfl⟩ | ⟨b, hl, hd2⟩
  · obtain ⟨hr, hne⟩ := lift_some hl
    rw [← hr]; exact ⟨rfl, hne err hr.symm⟩
  · obtain ⟨hr, -⟩ := lift_some hl
    rw [← hr]
    simp [DM.ok] at hd2; subst hd2
    exact ⟨Ext_refl _, trivial, rfl, rfl⟩

theorem fromBytesOf_spec {env : Env} {s : DSt} {e : Expr} {args' : List Arg}
    (h : fromBytesOf env s e = some args') :
    ∃ l la ln g, e = .call l (.attr la (.name ln g) env.nm.fromBytes) args' ∧ s.loc g = none ∧
      env.globals.lookup g = some (.builtin .int) := by
  cases e with
  | call l fn args =>
    cases fn with
    | attr la o f =>
      cases o with
      | name ln g =>
        simp only [fromBytesOf] at h
        cases hg : env.globals.lookup g with
        | none => simp [hg] at h
        | some gl =>
          rw [hg] at h
          cases gl with
          | builtin b =>
            cases b <;> simp only [reduceCtorEq] at h
            case int =>
              split at h
              · next hc =>
                simp only [Option.some.injEq] at h; subst h
                simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hc
                obtain ⟨hloc, rfl⟩ := hc
                exact ⟨l, la, ln, g, rfl, hloc, hg⟩
              · cases h
          | _ => simp at h
      | _ => simp [fromBytesOf] at h
    | _ => simp [fromBytesOf] at h
  | _ => simp [fromBytesOf] at h

/-- `int.from_bytes(args)`. -/
theorem fromBytes_sound {env : Env} (hlf : LibFlat env) {k : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals} {ev : Expr → DM DRes}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L (k + 2) ev)
    {e : Expr} {args : List Arg} (hfb : fromBytesOf env s e = some args)
    {r : Res DRes} (hd : DM.bind (argsOf ev args) (fun rs => dFromBytes env rs) = some r) :
    GOK h0.next h vs r (evalExpr env (k + 3) L h e) := by
  obtain ⟨l, l', l'', g, rfl, hloc, hg⟩ := fromBytesOf_spec hfb
  have hL : L g = none := by
    have := hI.i.r.loc g; rw [hloc] at this
    revert this; cases L g <;> simp [LRel]
  have hattr : evalExpr env (k + 2) L h (.attr l' (.name l'' g) env.nm.fromBytes) =
      .ok (.member (.glob g) env.nm.fromBytes, h) := by
    rw [evalExpr, evalExpr]; simp [lookupName, hL, hg, getAttr]
  rw [evalExpr]
  simp only [hattr, Except.bind_ok', anyAll]
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rs, he, hd2⟩
  · have := argsOf_sound ih args h _ hI he
    revert this
    cases evalArgs env (k + 2) L h args with
    | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
    | ok q => intro hx; cases hx
  · have := argsOf_sound ih args h _ hI he
    revert this
    cases evalArgs env (k + 2) L h args with
    | error e' => intro hx; cases hx
    | ok q =>
      obtain ⟨ws, kws, h2⟩ := q
      rintro ⟨hx2, rfl, hrel⟩
      simp only [Except.bind_ok']
      refine gok_ext hx2 ?_
      rw [callValue.eq_def]
      simp only [List.isEmpty_nil, if_true, applyMethod, hlf.fromBytesM h2 g ws hg, hg]
      unfold dFromBytes at hd2
      cases hav : allVals rs with
      | none => simp [hav] at hd2
      | some vals =>
        rw [hav] at hd2
        obtain ⟨rfl, -⟩ := allVals_spec hrel hav
        rcases bind_case hd2 with ⟨err, hl, rfl⟩ | ⟨v, hl, hd3⟩
        · obtain ⟨hr, hne⟩ := lift_some hl
          cases hf : fromBytes env ws with
          | ok q => rw [hf] at hr; cases hr
          | error e' => rw [hf] at hr; cases hr; exact ⟨rfl, hne _ (by rw [hf])⟩
        · obtain ⟨hr, -⟩ := lift_some hl
          cases hf : fromBytes env ws with
          | error e' => rw [hf] at hr; cases hr
          | ok q =>
            rw [hf] at hr; simp only [Except.ok.injEq] at hr; subst hr
            simp only [Except.bind_ok', Except.pure_ok']
            by_cases hv : Flat v = true
            · simp [hv, DM.ok] at hd3; subst hd3; exact ⟨Ext_refl _, trivial, rfl, hv⟩
            · simp [hv] at hd3

/-! ## Missing arguments with a `None` default -/

theorem evalList_noneLit {env : Env} {n : Nat} {L : Locals} :
    ∀ (es : List Expr) (h : Heap) (ds : List Value) (h' : Heap), es.all isNoneLit = true →
      evalList env n L h es = .ok (ds, h') → ds = es.map (fun _ => Value.none)
  | [], h, ds, h', _, e => by simp [evalList] at e; obtain ⟨rfl, -⟩ := e; rfl
  | e :: es, h, ds, h', hall, he => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨he1, hes⟩ := hall
    cases e <;> simp [isNoneLit] at he1
    rw [evalList] at he
    cases n with
    | zero => simp [evalExpr] at he
    | succ n =>
      rw [evalExpr] at he
      simp only [pure, Except.pure, Except.bind_ok'] at he
      cases hr : evalList env (n + 1) L h es with
      | error e => rw [hr] at he; cases he
      | ok q =>
        obtain ⟨ds', h2⟩ := q
        rw [hr] at he
        simp at he
        obtain ⟨rfl, rfl⟩ := he
        simp [evalList_noneLit es h ds' h2 hes hr]

theorem go_pad {ds ws : List Value} {k fd : Nat}
    (hd : ∀ i, ws.length ≤ i → i < ws.length + k → fd ≤ i ∧ ds[i - fd]? = some .none) :
    ∀ (xs : List (Name × Nat)) (L : Locals), (∀ q ∈ xs, q.2 < ws.length + k) →
      bindArgs.go ds ws [] fd L xs = bindArgs.go ds (ws ++ List.replicate k .none) [] fd L xs
  | [], L, _ => by simp [bindArgs.go]
  | (x, i) :: rest, L, hxs => by
    have hi : i < ws.length + k := hxs (x, i) (by simp)
    have ih := go_pad hd rest
    rw [bindArgs.go, bindArgs.go]
    by_cases hlt : i < ws.length
    · have h1 : ws[i]? = some ws[i] := List.getElem?_eq_getElem hlt
      have h2 : (ws ++ List.replicate k Value.none)[i]? = some ws[i] := by
        rw [List.getElem?_append_left hlt, h1]
      simp only [h1, h2, pure, Except.pure, Except.bind_ok']
      exact ih _ (fun q hq => hxs q (by simp [hq]))
    · have h1 : ws[i]? = none := List.getElem?_eq_none (by omega)
      have h2 : (ws ++ List.replicate k Value.none)[i]? = some .none := by
        rw [List.getElem?_append_right (by omega), List.getElem?_replicate, if_pos (by omega)]
      obtain ⟨hf, hdi⟩ := hd i (by omega) hi
      simp only [h1, h2, List.lookup_nil, hdi, if_pos hf, pure, Except.pure, Except.bind_ok']
      exact ih _ (fun q hq => hxs q (by simp [hq]))

/-- A call that leaves out trailing arguments with a `None` default: as with `None` given. -/
theorem callFn_pad {env : Env} (n : Nat) (ps : Params) (body : ClosureBody) (ws : List Value)
    (h : Heap) (k : Nat) (hall : ps.defaults.all isNoneLit = true) (hva : ps.vararg = none)
    (hk : ws.length + k = ps.names.length) (hkd : k ≤ ps.defaults.length) :
    callFn env n ps body Locals.empty ws [] h =
      callFn env n ps body Locals.empty (ws ++ List.replicate k .none) [] h := by
  cases n with
  | zero => rw [callFn, callFn]
  | succ n =>
    rw [callFn, callFn]
    cases he : evalList env n Locals.empty h ps.defaults with
    | error e => rfl
    | ok q =>
      obtain ⟨ds, h0⟩ := q
      have hds := evalList_noneLit ps.defaults h ds h0 hall he
      simp only [Except.bind_ok']
      have hb : bindArgs ps ds ws [] Locals.empty = bindArgs ps ds (ws ++ List.replicate k .none) [] Locals.empty := by
        unfold bindArgs
        have hl1 : ¬ (ws.length > ps.names.length ∧ ps.vararg.isNone = true) := by omega
        have hl2 : ¬ ((ws ++ List.replicate k Value.none).length > ps.names.length ∧ ps.vararg.isNone = true) := by
          simp; omega
        simp only [hl1, hl2, if_false, List.any_nil, Bool.false_eq_true]
        rw [go_pad (k := k) (fun i h1 h2 => ⟨by omega, by
          rw [hds, List.getElem?_map, List.getElem?_eq_getElem (by omega)]; rfl⟩) _ _
          (fun q hq => by have := (List.mem_zipIdx hq).2.1; simp at this; omega)]
        simp only [hva]
      rw [hb]

theorem padNone_spec {d : FunctionDef} {rg rg' : List DV} (h : padNone d rg = some rg') :
    (rg.length ≤ d.params.names.length ∧ d.params.names.length ≤ rg.length + d.params.defaults.length) ∧
      rg' = rg ++ List.replicate (d.params.names.length - rg.length) (.leaf .none) := by
  unfold padNone at h
  split at h
  · next hc => simp at h; exact ⟨hc, h.symm⟩
  · cases h

theorem blsOf_spec {env : Env} {s : DSt} {e : Expr} {f : Name} {args' : List Arg}
    (h : blsOf env s e = some (f, args')) :
    ∃ l la ln g, e = .call l (.attr la (.name ln g) f) args' ∧ s.loc g = none ∧
      env.globals.lookup g = some (.module .bls) := by
  cases e with
  | call l fn args =>
    cases fn with
    | attr la o f' =>
      cases o with
      | name ln g =>
        simp only [blsOf] at h
        cases hg : env.globals.lookup g with
        | none => simp [hg] at h
        | some gl =>
          rw [hg] at h
          cases gl with
          | module k =>
            cases k <;> simp only [reduceCtorEq] at h
            case bls =>
              split at h
              · next hc =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                simp only [Option.isNone_iff_eq_none] at hc
                exact ⟨l, la, ln, g, rfl, hc, hg⟩
              · cases h
          | _ => simp at h
      | _ => simp [blsOf] at h
    | _ => simp [blsOf] at h
  | _ => simp [blsOf] at h

/-- `bls.f(args)`. -/
theorem bls_sound {env : Env} (hlf : LibFlat env) {k : Nat}
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals} {ev : Expr → DM DRes}
    (hI : CInv fp h0 h vs s L) (ih : EvF env fp h0 vs s L (k + 2) ev)
    {e : Expr} {f : Name} {args : List Arg} (hfb : blsOf env s e = some (f, args))
    {r : Res DRes} (hd : DM.bind (argsOf ev args) (fun rs => dBls env f rs) = some r) :
    GOK h0.next h vs r (evalExpr env (k + 3) L h e) := by
  obtain ⟨l, l', l'', g, rfl, hloc, hg⟩ := blsOf_spec hfb
  have hL : L g = none := by
    have := hI.i.r.loc g; rw [hloc] at this
    revert this; cases L g <;> simp [LRel]
  have hattr : evalExpr env (k + 2) L h (.attr l' (.name l'' g) f) =
      .ok (.member (.glob g) f, h) := by
    rw [evalExpr, evalExpr]; simp [lookupName, hL, hg, getAttr]
  rw [evalExpr]
  simp only [hattr, Except.bind_ok', anyAll]
  rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rs, he, hd2⟩
  · have := argsOf_sound ih args h _ hI he
    revert this
    cases evalArgs env (k + 2) L h args with
    | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
    | ok q => intro hx; cases hx
  · have := argsOf_sound ih args h _ hI he
    revert this
    cases evalArgs env (k + 2) L h args with
    | error e' => intro hx; cases hx
    | ok q =>
      obtain ⟨ws, kws, h2⟩ := q
      rintro ⟨hx2, rfl, hrel⟩
      simp only [Except.bind_ok']
      refine gok_ext hx2 ?_
      rw [callValue.eq_def]
      simp only [List.isEmpty_nil, if_true, applyMethod, hlf.blsM h2 g f ws hg, hg]
      unfold dBls at hd2
      cases hav : allVals rs with
      | none => simp [hav] at hd2
      | some vals =>
        rw [hav] at hd2
        obtain ⟨rfl, hflv⟩ := allVals_spec hrel hav
        rw [hlf.blsFlat h2 f _ hflv]
        rcases bind_case hd2 with ⟨err, hl, rfl⟩ | ⟨v, hl, hd3⟩
        · obtain ⟨hr, hne⟩ := lift_some hl
          cases hf : env.bls f Heap.empty ws with
          | ok q => rw [hf] at hr; cases hr
          | error e' => rw [hf] at hr; cases hr; exact ⟨rfl, hne _ (by rw [hf])⟩
        · obtain ⟨hr, -⟩ := lift_some hl
          cases hf : env.bls f Heap.empty ws with
          | error e' => rw [hf] at hr; cases hr
          | ok q =>
            rw [hf] at hr; simp only [Except.ok.injEq] at hr; subst hr
            simp only [Except.bind_ok', Except.pure_ok']
            by_cases hv : Flat v = true
            · simp [hv, DM.ok] at hd3; subst hd3; exact ⟨Ext_refl _, trivial, rfl, hv⟩
            · simp [hv] at hd3

theorem decArgs_pad {h : Heap} {vs : List Value} {roots : List DV} (hd : DecArgs h vs roots) (k : Nat) :
    DecArgs h (vs ++ List.replicate k .none) (roots ++ List.replicate k (.leaf .none)) := by
  refine ⟨by simp [hd.1], fun i v d hv hdd => ?_⟩
  by_cases hi : i < vs.length
  · rw [List.getElem?_append_left hi] at hv
    rw [List.getElem?_append_left (by rw [hd.1]; exact hi)] at hdd
    exact hd.2 i v d hv hdd
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate] at hv
    rw [List.getElem?_append_right (by rw [hd.1]; omega), List.getElem?_replicate] at hdd
    split at hv
    · simp at hv hdd; subst hv; rw [hd.1] at hdd; simp [show i - vs.length < k by omega] at hdd
      subst hdd; exact ⟨0, dec_flat rfl 0⟩
    · cases hv

/-- A callee at fuel `n + 1` that gives a result: its defaults are `None`, and the tree of each
parameter is given. -/
theorem fn_shape {env : Env} {fps : Name → Footprint} {n : Nat} {fp : Footprint} {d : FunctionDef}
    {roots : List DV} {r : Res (DRes × List DV)} (hf : (den env fps (n + 1)).fn fp d roots = some r) :
    d.params.defaults.all isNoneLit = true ∧ d.params.vararg = none ∧ d.params.names.length = roots.length := by
  rw [den_fn] at hf
  unfold fnStep at hf
  split at hf
  · next hc =>
    obtain ⟨hnd, hva, hnl⟩ := hc
    refine ⟨?_, hva, hnl⟩
    unfold noneDefaults at hnd
    cases hdd : d.params.defaults with
    | nil => rfl
    | cons e es => rw [hdd] at hnd; simp at hnd; rw [← hdd]; simpa [hdd] using hnd.1
  · cases hf

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
              have hda := argRoots_dec hI2.i.r hrel hm
              cases hp : padNone d rg with
              | none => simp [hp] at hd2
              | some rgp =>
              simp only [hp] at hd2
              obtain ⟨⟨hl1, hl2⟩, rfl⟩ := padNone_spec hp
              have hpad := decArgs_pad hda (d.params.names.length - rg.length)
              rw [hda.1] at hpad
              rcases bind_case hd2 with ⟨err, hf, rfl⟩ | ⟨⟨v, rg'⟩, hf, hd3⟩
              · obtain ⟨hall, hva, -⟩ := fn_shape hf
                rw [callFn_pad (m + 1) d.params _ ws h2 (d.params.names.length - ws.length) hall hva
                  (by rw [← hda.1]; omega) (by rw [← hda.1]; omega)]
                have := hF [] d _ _ h2 _ hpad (fun _ _ hp => by simp at hp) hI2.wf (by rw [hda.1] at hf; exact hf)
                revert this
                cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty
                    (ws ++ List.replicate (d.params.names.length - ws.length) .none) [] h2 with
                | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
                | ok q => intro hx; cases hx
              · obtain ⟨hall, hva, -⟩ := fn_shape hf
                rw [callFn_pad (m + 1) d.params _ ws h2 (d.params.names.length - ws.length) hall hva
                  (by rw [← hda.1]; omega) (by rw [← hda.1]; omega)]
                have := hF [] d _ _ h2 _ hpad (fun _ _ hp => by simp at hp) hI2.wf (by rw [hda.1] at hf; exact hf)
                revert this
                cases callFn env (m + 1) d.params (.stmts d.body) Locals.empty
                    (ws ++ List.replicate (d.params.names.length - ws.length) .none) [] h2 with
                | error e' => intro hx; cases hx
                | ok q =>
                  obtain ⟨w, h'⟩ := q
                  rintro ⟨hrr, hlo, -, -, -, hro, -⟩
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
                    have hlt := at?_below hI2.below ((at?_Ext hx' hI2.below k p a).mp ep)
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
          have minmax : ∀ (isMin : Bool), dBuiltin env s (if isMin then .min else .max) rs = some r →
              GOK h0.next h2 vs r (applyBuiltin env h2 (if isMin then .min else .max) ws []) := by
            intro isMin hd3
            have hb : dBuiltin env s (if isMin then .min else .max) rs = (match allVals rs with
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
            | [.tree d], [w], ⟨⟨⟨nn, hn⟩, _⟩, _⟩, hd2 =>
              cases d with
              | leaf _ => simp at hd2
              | cont _ _ => simp at hd2
              | list kd el ll ds =>
                simp [DM.ok] at hd2; subst hd2
                obtain ⟨a', mm, xs, ha, -, ho, hm⟩ := dec_list hn
                subst ha
                have hlen := ((mapM_some_iff xs ds).mp hm).1
                simp [applyBuiltin, hlf.builtin h2 .len _ [] (by simp), ho, hlen]
                exact ⟨Ext_refl _, trivial, rfl, rfl⟩
            | [.val _], _, _, hd2 => simp at hd2
            | [], _, _, hd2 => simp at hd2
            | _ :: _ :: _, _, _, hd2 => simp at hd2
          case hashTreeRoot =>
            simp only [dBuiltin] at hd2
            match rs, ws, hrel, hd2 with
            | [.place k p], [w], ⟨⟨a, hw, hat⟩, _⟩, hd2 =>
              subst hw
              simp only at hd2
              cases hdr : s.deref k p with
              | none => simp [hdr] at hd2
              | some dd =>
                rw [hdr] at hd2
                obtain ⟨nn, hn⟩ := deref_dec hI2.i.r hat hdr
                exact dHtr_sound hlf hn hd2
            | [.tree d], [w], ⟨⟨⟨nn, hn⟩, _⟩, _⟩, hd2 => exact dHtr_sound hlf hn hd2
            | [.val _], _, _, hd2 => simp at hd2
            | [], _, _, hd2 => simp at hd2
            | _ :: _ :: _, _, _, hd2 => simp at hd2
          case sum =>
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
                  obtain ⟨nn, hn⟩ := deref_dec hI2.i.r hat hdr
                  obtain ⟨a', mm, xs, ha, -, ho, hm⟩ := dec_list hn
                  cases ha
                  exact dSum_sound hlf ho hm hd2
            | [.tree d], [w], ⟨⟨⟨nn, hn⟩, _⟩, _⟩, hd2 =>
              cases d with
              | leaf _ => simp at hd2
              | cont _ _ => simp at hd2
              | list kd el ll ds =>
                obtain ⟨a', mm, xs, ha, -, ho, hm⟩ := dec_list hn
                subst ha
                exact dSum_sound hlf ho hm hd2
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

theorem CInv.setLoc {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) (x : Name) {r : DRes} {w : Value} (hr : ERel h vs r w)
    (hlo : TLo h0.next h r w) : CInv fp h0 h vs { s with loc := setLoc s.loc x r } (L.set x w) := by
  refine ⟨setLoc_inv hI.i x hr, hI.skel, hI.ro, hI.wf0, fun y r' w' hy hw => ?_⟩
  simp only [SpecLean.Layer4.setLoc, Locals.set_apply] at hy hw
  by_cases hyx : y = x
  · subst hyx; simp at hy hw; subst hy; subst hw; exact hlo
  · simp only [hyx, if_false] at hy hw; exact hI.tlo y r' w' hy hw


/-- The interpreter's loop source for a loop over the list object `a`. -/
def LSrc.src (ls : LSrc) (a : Nat) : IterSrc := if ls.enum then .enum (.live a) else .seq (.live a)

/-- The iterable of a loop agrees with the interpreter's value and source. -/
def IterRel (h : Heap) (vs : List Value) : Res LSrc → Res (Value × Heap) → Prop
  | .ok ls, .ok (iv, h') =>
    Ext h h' ∧ ∃ a, at? h' vs ls.k ls.p = some (.ref a) ∧ iterSource h' iv = .ok (ls.src a)
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False


theorem toSeq_live {h : Heap} {a : Nat} {kd : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} (ho : h.objs a = some (.list kd e l xs)) (hb : isByteList kd e = false) :
    toSeq h (.ref a) = .ok (.live a) := by
  simp only [isByteList, decide_eq_false_iff_not] at hb
  simp only [toSeq, ho]
  split
  · next heq => cases heq; exact absurd ⟨rfl, rfl⟩ hb
  · rfl
  · next hne => exact absurd rfl (hne kd e l xs)

theorem seqItem_live {h : Heap} {a : Nat} {kd : ListKind} {e : SszTy} {l : Option Nat}
    {xs : List Value} (ho : h.objs a = some (.list kd e l xs)) (hb : isByteList kd e = false)
    (i : Nat) : seqItem h (.live a) i = .ok xs[i]? := by
  simp only [isByteList, decide_eq_false_iff_not] at hb
  simp only [seqItem, ho]
  split
  · next heq => cases heq; exact absurd ⟨rfl, rfl⟩ hb
  · next heq => cases heq; rfl
  · next hne => exact absurd rfl (hne kd e l xs)

theorem listPlace_spec {s : DSt} {k : Nat} {p : List Nat} (h : listPlace s k p = true) :
    ∃ kd e l ds, s.deref k p = some (.list kd e l ds) ∧ isByteList kd e = false := by
  unfold listPlace at h
  split at h
  · next kd e l ds hd => exact ⟨kd, e, l, ds, hd, by simpa using h⟩
  · cases h

/-- The object of a list place, and its items. -/
theorem listPlace_obj {h : Heap} {vs : List Value} {s : DSt} {L : Locals} (hr : RInv h vs s L)
    {k : Nat} {p : List Nat} {a : Nat} (hat : at? h vs k p = some (.ref a))
    {kd : ListKind} {e : SszTy} {l : Option Nat} {ds : List DV}
    (hdr : s.deref k p = some (.list kd e l ds)) :
    ∃ m xs, h.objs a = some (.list kd e l xs) ∧ xs.mapM (dec h m) = some ds := by
  obtain ⟨nn, hn⟩ := deref_dec hr hat hdr
  obtain ⟨a', m, xs, ha, -, ho, hm⟩ := dec_list hn
  cases ha
  exact ⟨m, xs, ho, hm⟩


/-- Bind the loop target, as `assignTarget n` does. -/
theorem bindLoop_sound {env : Env} {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt}
    {L : Locals} (hI : CInv fp h0 h vs s L) {n : Nat} {enum : Bool} {t : Target} {i : Nat}
    {xr : DRes} {x : Value} (hx : ERel h vs xr x) (hxlo : TLo h0.next h xr x) {s1 : DSt}
    (hb : bindLoop n enum s t i xr = some s1) :
    ∃ L1, assignTarget env n L h t (if enum then enumItem i x else x) = .ok (L1, h) ∧
      CInv fp h0 h vs s1 L1 := by
  unfold bindLoop at hb
  split at hb
  · next a m =>
    simp at hb; subst hb
    refine ⟨L.set a x, ?_, hI.setLoc a hx hxlo⟩
    simp [assignTarget]
  · next l a l' b m =>
    simp at hb; subst hb
    refine ⟨(L.set a (.int i)).set b x, ?_, ?_⟩
    · simp [assignTarget, assignTargets, enumItem]
    · have h1 : CInv fp h0 h vs { s with loc := setLoc s.loc a (.val (.int i)) } (L.set a (.int i)) :=
        hI.setLoc a (r := .val (.int i)) (w := .int i) ⟨rfl, rfl⟩ trivial
      exact h1.setLoc b hx hxlo
  · cases hb


/-! ## List comprehensions -/

theorem dbind_ok {α β : Type} (a : α) (f : α → DM β) : DM.bind (some (.ok a)) f = f a := rfl

def IfsOK (h : Heap) : Res Bool → Res (Bool × Heap) → Prop
  | .ok b, .ok (b', h') => Ext h h' ∧ b' = b
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

theorem ifsOf_sound {env : Env} {fp : Footprint} {h0 : Heap} {vs : List Value} {s : DSt} {L : Locals}
    {n : Nat} {ev : Expr → DM DRes} (hE : EvF env fp h0 vs s L n ev) :
    ∀ (cs : List Expr) (h : Heap) (r : Res Bool), CInv fp h0 h vs s L →
      ifsOf ev cs = some r → IfsOK h r (evalIfs env n L h cs)
  | [], h, r, _, hd => by
    simp [ifsOf, DM.ok] at hd; subst hd
    rw [evalIfs]; exact ⟨Ext_refl h, rfl⟩
  | c :: cs, h, r, hI, hd => by
    simp only [ifsOf] at hd
    rw [evalIfs]
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨rv, he, hd2⟩
    · obtain ⟨hi, hne⟩ := gok_error (hE h hI c _ he)
      simp [hi, hne, IfsOK]
    · obtain ⟨w, h1, hi, hx1, hrel⟩ := gok_ok (hE h hI c _ he)
      simp only [hi, Except.bind_ok']
      cases rv with
      | place _ _ => simp at hd2
      | tree _ => simp at hd2
      | val v =>
        obtain ⟨rfl, hv⟩ := hrel
        simp only at hd2
        rcases bind_case hd2 with ⟨err, ht, rfl⟩ | ⟨b, ht, hd3⟩
        · obtain ⟨htr, hne⟩ := lift_some ht
          simp [truthyH_flat h1 hv, ← htr, hne err htr.symm, IfsOK]
        · obtain ⟨htr, -⟩ := lift_some ht
          simp only [truthyH_flat h1 hv, ← htr, Except.bind_ok']
          cases b with
          | true =>
            simp only [↓reduceIte] at hd3 ⊢
            have := ifsOf_sound hE cs h1 r (hI.ext hx1) hd3
            revert this
            cases evalIfs env n L h1 cs with
            | error e' => cases r <;> simp [IfsOK]
            | ok q =>
              obtain ⟨b', h2⟩ := q
              cases r with
              | error _ => simp [IfsOK]
              | ok b => rintro ⟨hx2, rfl⟩; exact ⟨Ext_trans hx1 hx2, rfl⟩
          | false =>
            simp [DM.ok] at hd3; subst hd3
            exact ⟨hx1, rfl⟩

/-- The items of a list comprehension and the interpreter's: flat values. -/
def ItemsOK (h : Heap) : Res (List DV) → Res (List Value × Bool × Heap) → Prop
  | .ok ds, .ok (xs, st, h') =>
    Ext h h' ∧ st = false ∧ ds = xs.map DV.leaf ∧ ∀ v ∈ xs, Flat v = true
  | .error e, .error e' => e' = e ∧ e ≠ .outOfFuel
  | _, _ => False

/-- One fuel step of the items, from the expressions and the items one fuel below. -/
theorem itemsStep_sound {env : Env} {fps : Name → Footprint} {n : Nat}
    (hEx : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → EvOK env h0.next h vs L n ((den env fps n).expr fp s))
    (hIt : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ t ifs elt ls i r a,
      at? h vs ls.k ls.p = some (.ref a) → (den env fps n).items fp s t ifs elt ls i = some r →
      ItemsOK h r (compItems env n L h t ifs [] elt none (ls.src a) i))
    {fp : Footprint} {h0 h : Heap} {vs : List Value} {s : DSt} {L : Locals}
    (hI : CInv fp h0 h vs s L) {t : Target} {ifs : List Expr} {elt : Expr} {ls : LSrc} {i : Nat}
    {r : Res (List DV)} {a : Nat} (hat : at? h vs ls.k ls.p = some (.ref a))
    (hd : itemsStep n (den env fps n) fp s t ifs elt ls i = some r) :
    ItemsOK h r (compItems env (n + 1) L h t ifs [] elt none (ls.src a) i) := by
  unfold itemsStep at hd
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
  rw [compItems]
  simp only [hitem, Except.bind_ok']
  cases hc : ds[i]? with
  | none =>
    have : xs[i]? = none := by rw [List.getElem?_eq_none_iff] at hc ⊢; omega
    simp [hc, DM.ok] at hd; subst hd
    simp [this]; exact ⟨Ext_refl h, rfl, rfl, by simp⟩
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
    have hE1 : EvF env fp h0 vs s1 L1 n ((den env fps n).expr fp s1) :=
      fun h' hI' => hEx fp h0 h' vs s1 L1 hI'
    rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨keep, he, hd2⟩
    · have := ifsOf_sound hE1 ifs h _ hI1 he
      revert this
      cases evalIfs env n L1 h ifs with
      | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
      | ok q => intro hx; cases hx
    · have := ifsOf_sound hE1 ifs h _ hI1 he
      revert this
      cases evalIfs env n L1 h ifs with
      | error e' => intro hx; cases hx
      | ok q =>
        obtain ⟨keep', h2⟩ := q
        rintro ⟨hx2, hkk⟩
        subst keep'
        have hI2 := hI1.ext hx2
        simp only [Except.bind_ok']
        -- The items after this one.
        have rest : ∀ (xs1 : List Value) (h3 : Heap), Ext h2 h3 → (∀ v ∈ xs1, Flat v = true) →
            DM.bind ((den env fps n).items fp s1 t ifs elt ls (i + 1))
              (fun vs2 => DM.ok (xs1.map DV.leaf ++ vs2)) = some r →
            ItemsOK h r (do
              let __discr ← compItems env n L1 h3 t ifs [] elt none (ls.src a) (i + 1)
              pure (xs1 ++ __discr.fst, __discr.2.fst, __discr.2.snd)) := by
          intro xs1 h3 hx3 hf1 hd3
          have hI3 := hI2.ext hx3
          have hat3 : at? h3 vs ls.k ls.p = some (.ref a) := by
            have e13 : Ext h h3 := Ext_trans hx2 hx3
            exact (at?_Ext e13 hI.below _ _ a).mpr hat
          rcases bind_case hd3 with ⟨err, he4, rfl⟩ | ⟨vs2, he4, hd4⟩
          · have := hIt fp h0 h3 vs s1 L1 hI3 t ifs elt ls (i + 1) _ a hat3 he4
            revert this
            cases compItems env n L1 h3 t ifs [] elt none (ls.src a) (i + 1) with
            | error e' => rintro ⟨rfl, hne⟩; exact ⟨rfl, hne⟩
            | ok q => intro hx; cases hx
          · have := hIt fp h0 h3 vs s1 L1 hI3 t ifs elt ls (i + 1) _ a hat3 he4
            revert this
            cases compItems env n L1 h3 t ifs [] elt none (ls.src a) (i + 1) with
            | error e' => intro hx; cases hx
            | ok q =>
              obtain ⟨xs2, st2, h4⟩ := q
              rintro ⟨hx4, rfl, rfl, hf2⟩
              simp [DM.ok] at hd4; subst hd4
              refine ⟨Ext_trans hx2 (Ext_trans hx3 hx4), rfl, by simp, fun v hv => ?_⟩
              rcases List.mem_append.mp hv with hv | hv
              · exact hf1 v hv
              · exact hf2 v hv
        cases keep with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hd2 ⊢
          simp only [DM.ok, dbind_ok, pure, Except.pure, Except.bind_ok', Bool.false_eq_true,
            ↓reduceIte, List.nil_append] at hd2 ⊢
          exact rest [] h2 (Ext_refl h2) (by simp) (by simpa [DM.ok] using hd2)
        | true =>
          simp only [↓reduceIte] at hd2 ⊢
          rw [compLoop]
          rcases bind_case hd2 with ⟨err, he3, rfl⟩ | ⟨vs1, he3, hd3⟩
          · rcases bind_case he3 with ⟨err', he5, he6⟩ | ⟨re, he5, he6⟩
            · cases he6
              obtain ⟨hi3, hne⟩ := gok_error (hE1 h2 hI2 elt _ he5)
              simp [hi3]; exact ⟨rfl, hne⟩
            · cases re with
              | place _ _ => simp at he6
              | tree _ => simp at he6
              | val v => by_cases hv : Flat v = true <;> simp [hv, DM.ok] at he6
          · rcases bind_case he3 with ⟨err', he5, he6⟩ | ⟨re, he5, he6⟩
            · cases he6
            · obtain ⟨we, h3, hi3, hx3, hrel3⟩ := gok_ok (hE1 h2 hI2 elt _ he5)
              simp only [hi3, Except.bind_ok']
              cases re with
              | place _ _ => simp at he6
              | tree _ => simp at he6
              | val v =>
                obtain ⟨rfl, hv⟩ := hrel3
                simp [hv, DM.ok] at he6; subst he6
                simp only [Except.pure, pure, Except.bind_ok', Bool.false_eq_true, ↓reduceIte]
                exact rest [we] h3 hx3 (by simp [hv]) (by simpa [DM.ok] using hd3)

/-- A new Python list of flat values: a new tree, related to the new reference. -/
theorem alloc_tree {lo : Nat} {h : Heap} {vs : List Value} (hb : BelowArgs h vs) (hlo : lo ≤ h.next)
    {xs : List Value} (hf : ∀ v ∈ xs, Flat v = true) :
    GOK lo h vs (.ok (.tree (.list .pyList .any none (xs.map DV.leaf)))) (.ok (allocPyList h xs)) := by
  have he := Ext_alloc h (.list .pyList .any none xs)
  have hobj : (h.alloc (.list .pyList .any none xs)).2.objs h.next = some (.list .pyList .any none xs) := by
    simp [Heap.alloc]
  have hpath : ∀ q b, follow (h.alloc (.list .pyList .any none xs)).2 (.ref h.next) q = some (.ref b) →
      b = h.next := by
    intro q b e
    cases q with
    | nil => simp [follow] at e; exact e.symm
    | cons j q =>
      rw [follow_ref_cons, hobj] at e
      simp only [okids, Option.bind_some] at e
      cases hx : xs[j]? with
      | none => simp [hx] at e
      | some x =>
        simp only [hx, Option.bind_some] at e
        have hfx : Flat x = true := hf x (List.mem_of_getElem? hx)
        exact absurd e (fun e' => follow_nonref_ref (flat_nonref hfx) e')
  have hal : allocPyList h xs = (.ref h.next, (h.alloc (.list .pyList .any none xs)).2) := rfl
  rw [hal]
  simp only [GOK]
  refine ⟨he, fun q b e => (hpath q b e) ▸ hlo, ⟨2, ?_⟩, fun q b e k p ep => ?_⟩
  · rw [dec_ref_succ, hobj]
    have : xs.mapM (dec (h.alloc (.list .pyList .any none xs)).2 1) = some (xs.map DV.leaf) := by
      rw [mapM_some_iff]
      refine ⟨by simp, fun i x hx => ?_⟩
      have hfx : Flat x = true := hf x (List.mem_of_getElem? hx)
      simp [dec_flat hfx, hx]
    simp [this]
  · have hb' := hpath q b e
    subst hb'
    have hlt := at?_below hb ((at?_Ext he hb k p h.next).mp ep)
    omega

/-- One fuel step of the expressions. -/
theorem exprStep_sound (env : Env) (fps : Name → Footprint) (hlf : LibFlat env) {n : Nat}
    (hEx : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → EvOK env h0.next h vs L n ((den env fps n).expr fp s))
    (hF : FnOK env fps n)
    (hIter : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ it r, (den env fps n).iter fp s it = some r →
      IterRel h vs r (evalExpr env n L h it))
    (hItems : ∀ fp h0 h vs s L, CInv fp h0 h vs s L → ∀ t ifs elt ls i r a,
      at? h vs ls.k ls.p = some (.ref a) → (den env fps n).items fp s t ifs elt ls i = some r →
      ItemsOK h r (compItems env n L h t ifs [] elt none (ls.src a) i))
    {fp : Footprint} {h0 : Heap} {vs : List Value} {s : DSt} {L : Locals}
    {h : Heap} (hI : CInv fp h0 h vs s L) :
    EvOK env h0.next h vs L (n + 1) (exprStep env fps n (den env fps n) fp s) := by
  have ih : EvF env fp h0 vs s L n ((den env fps n).expr fp s) := fun h1 hI1 => hEx fp h0 h1 vs s L hI1
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
      | none =>
        cases m with
        | zero => simp [hch] at hd
        | succ k =>
        simp only [hch] at hd
        cases hfb : fromBytesOf env s (.call l fn args) with
        | none =>
          simp only [hfb] at hd
          cases hbl : blsOf env s (.call l fn args) with
          | none => simp [hbl] at hd
          | some fa =>
            obtain ⟨f, args'⟩ := fa
            simp only [hbl] at hd
            exact bls_sound hlf hI ih hbl hd
        | some args' =>
          simp only [hfb] at hd
          exact fromBytes_sound hlf hI ih hfb hd
      | some ga =>
        obtain ⟨g, args'⟩ := ga
        obtain ⟨l1, l', he, hloc, hc⟩ := callHead_spec hch
        cases he
        simp only [hch] at hd
        split at hd
        · exact kwCall_sound hlf hI ih hloc hc hd
        · exact roCall_sound hlf hI ih hF hloc hc hd
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
  | comp l kind elt gens =>
    cases kind with
    | set => simp [exprStep] at hd
    | gen => simp [exprStep] at hd
    | list =>
    rcases gens with _ | ⟨⟨t, it, ifs⟩, _ | ⟨g2, gs⟩⟩
    · simp [exprStep] at hd
    · simp only [exprStep] at hd
      rw [evalExpr, compLoop]
      rcases bind_case hd with ⟨err, he, rfl⟩ | ⟨ls, he, hd2⟩
      · have := hIter fp h0 h vs s L hI it _ he
        revert this
        cases hev : evalExpr env n L h it with
        | error e' =>
          rintro ⟨rfl, hne⟩
          simp; exact ⟨rfl, hne⟩
        | ok q => intro hx; cases hx
      · have := hIter fp h0 h vs s L hI it _ he
        revert this
        cases hev : evalExpr env n L h it with
        | error e' => intro hx; cases hx
        | ok q =>
          obtain ⟨iv, h1⟩ := q
          rintro ⟨hx1, a, hat, hsrc⟩
          have hI1 := hI.ext hx1
          simp only [Except.bind_ok', hsrc]
          rcases bind_case hd2 with ⟨err, hi, rfl⟩ | ⟨ds, hi, hd3⟩
          · have := hItems fp h0 h1 vs s L hI1 t ifs elt ls 0 _ a hat hi
            revert this
            cases compItems env n L h1 t ifs [] elt none (ls.src a) 0 with
            | error e' => rintro ⟨rfl, hne⟩; simp; exact ⟨rfl, hne⟩
            | ok q => intro hx; cases hx
          · have := hItems fp h0 h1 vs s L hI1 t ifs elt ls 0 _ a hat hi
            revert this
            cases compItems env n L h1 t ifs [] elt none (ls.src a) 0 with
            | error e' => intro hx; cases hx
            | ok q =>
              obtain ⟨xs, st, h2⟩ := q
              rintro ⟨hx2, rfl, rfl, hf⟩
              simp [DM.ok] at hd3; subst hd3
              simp only [Except.bind_ok']
              have hI2 := hI1.ext hx2
              exact gok_ext (Ext_trans hx1 hx2) (alloc_tree hI2.below hI2.i.fresh.1 hf)
    · simp [exprStep] at hd
  | _ => simp [exprStep] at hd

end SpecLean.Layer4
