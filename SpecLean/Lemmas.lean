import SpecLean.Interp
import SpecLean.Ssz

/-!
# Generic lemmas about the interpreter

Proved once and used by every validation theorem (SPEC 9.3).
-/

namespace SpecLean

/-! ## The `Except` monad

These lemmas are proved by `simp`, not by `rfl`. A `rfl` proof makes `simp` treat a lemma as a
definitional rewrite. The kernel then checks the whole goal before and after by defeq, and that
is very slow on unfolded interpreter terms. -/

@[simp] theorem Except.bind_ok' {ε α β} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := by simp only [bind, Except.bind]

@[simp] theorem Except.bind_error' {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = .error e := by simp only [bind, Except.bind]

@[simp] theorem Except.pure_ok' {ε α} (a : α) : (pure a : Except ε α) = .ok a := by
  simp only [pure, Except.pure]

@[simp] theorem Except.map_ok' {ε α β} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := by
  simp only [Functor.map, Except.map]

@[simp] theorem Except.map_error' {ε α β} (f : α → β) (e : ε) :
    (f <$> (Except.error e : Except ε α)) = .error e := by
  simp only [Functor.map, Except.map]

@[simp] theorem Except.throw_error' {ε α} (e : ε) : (throw e : Except ε α) = .error e := by
  simp only [throw, throwThe, MonadExceptOf.throw]

@[simp] theorem Locals.empty_apply (x : Name) : Locals.empty x = none := by
  simp only [Locals.empty]

/-! ## Statement sequences (`interp_seq`) -/

/-- A statement list runs its first statement, then the rest when the first ends normally. -/
theorem interp_seq (env : Env) (n : Nat) (L : Locals) (h : Heap) (s : Stmt) (ss : List Stmt) :
    execBlock env n L h (s :: ss) = (do
      let (o, L1, h1) ← execStmt env n L h s
      match o with
      | .normal => execBlock env n L1 h1 ss
      | _ => pure (o, L1, h1)) := by
  rw [execBlock]; rfl

theorem interp_seq_nil (env : Env) (n : Nat) (L : Locals) (h : Heap) :
    execBlock env n L h [] = .ok (.normal, L, h) := by
  rw [execBlock]; rfl

/-- A statement that ends normally passes its locals and heap to the rest. -/
theorem interp_seq_normal (env : Env) (n : Nat) (L L' : Locals) (h h' : Heap) (s : Stmt)
    (ss : List Stmt) (hs : execStmt env n L h s = .ok (.normal, L', h')) :
    execBlock env n L h (s :: ss) = execBlock env n L' h' ss := by
  rw [interp_seq, hs]; rfl

/-! ## Calls (`call_through`) -/

/-- A call: the callee, then the arguments left to right, then the call. A validation theorem
about the callee then replaces `callValue`. A call of `any` or `all` on a generator is the
exception. -/
theorem call_through (env : Env) (n : Nat) (L : Locals) (h : Heap) (line : Line) (fn : Expr)
    (args : List Arg) (hargs : ∀ l elt gens, args ≠ [.pos (.comp l .gen elt gens)]) :
    evalExpr env (n + 1) L h (.call line fn args) = (do
      let (fv, h1) ← evalExpr env n L h fn
      let (vs, kws, h2) ← evalArgs env n L h1 args
      callValue env n fv vs kws h2) := by
  rw [evalExpr]
  congr 1
  funext p
  obtain ⟨fv, h1⟩ := p
  dsimp only
  split
  · exact absurd rfl (hargs _ _ _)
  · rfl

/-- `callName` on a spec function `g`. -/
theorem callName_fn (env : Env) (n : Nat) (g : Name) (d : FunctionDef) (vs : List Value)
    (h : Heap) (hg : env.globals.lookup g = some (.fn d)) :
    callName env n g vs h = callFn env n d.params (.stmts d.body) Locals.empty vs [] h := by
  rw [callName, callValue.eq_def]
  simp only [hg, frame_eq]

/-! ## Loops (`interp_for`, `interp_while`) -/

/-- A statement run related to one readable step: an error of the same class on both sides
(never `outOfFuel`), or a normal end in a state that `R` relates to the readable result. -/
def StepRel (R : σ → Locals → Heap → Prop) :
    Res (Outcome × Locals × Heap) → Except Fail σ → Prop
  | .ok (.normal, L', h'), .ok s' => R s' L' h'
  | .error e, .error f => e ≠ .outOfFuel ∧ e.fail = f
  | _, _ => False

/-- A `for` loop simulates a readable index loop. `P i` is the invariant before item `i`.
At the end of the items the readable loop also ends. Each iteration (target assignment, then
body) ends normally or with an error, as the readable step does. Each iteration costs one unit
of fuel, so fuel `n + K + 1` with `len s - i ≤ n` is enough. -/
theorem interp_for {σ : Type} (env : Env) (t : Target) (body : List Stmt) (src : IterSrc)
    (K : Nat) (len : σ → Nat) (step : σ → Nat → Except Fail σ)
    (loop : σ → Nat → Except Fail σ)
    (hloop : ∀ s i, loop s i =
      if i < len s then step s i >>= fun s' => loop s' (i + 1) else pure s)
    (hlen : ∀ s i s', step s i = .ok s' → len s' = len s)
    (P : Nat → σ → Locals → Heap → Prop)
    (hend : ∀ i s L h, P i s L h → ¬ i < len s → iterItem h src i = .ok none)
    (hstep : ∀ n i s L h, P i s L h → i < len s → ∃ x, iterItem h src i = .ok (some x) ∧
      StepRel (P (i + 1)) (do
        let (L1, h1) ← assignTarget env (n + K) L h t x
        execBlock env (n + K) L1 h1 body) (step s i)) :
    ∀ n i s L h, P i s L h → len s - i ≤ n →
      StepRel (fun s L h => ∃ i, P i s L h ∧ ¬ i < len s)
        (execFor env (n + K + 1) L h t src i body) (loop s i) := by
  intro n
  induction n with
  | zero =>
    intro i s L h hp hn
    have hi : ¬ i < len s := by omega
    rw [execFor, hend i s L h hp hi, hloop, if_neg hi]
    exact ⟨i, hp, hi⟩
  | succ n ih =>
    intro i s L h hp hn
    rw [hloop]
    by_cases hi : i < len s
    · rw [if_pos hi]
      obtain ⟨x, hx, hs⟩ := hstep (n + 1) i s L h hp hi
      rw [execFor, hx]
      simp only [Except.bind_ok']
      revert hs
      cases assignTarget env (n + 1 + K) L h t x with
      | error e => cases step s i <;> simp [StepRel]
      | ok r =>
        obtain ⟨L1, h1⟩ := r
        simp only [Except.bind_ok']
        cases execBlock env (n + 1 + K) L1 h1 body with
        | error e => cases step s i <;> simp [StepRel]
        | ok r =>
          obtain ⟨o, L2, h2⟩ := r
          cases hst : step s i with
          | error => cases o <;> simp [StepRel]
          | ok s' =>
            cases o <;> simp only [StepRel, Except.bind_ok', false_implies]
            intro hp'
            rw [show n + 1 + K = n + K + 1 by omega]
            exact ih (i + 1) s' L2 h2 hp' (by have := hlen s i s' hst; omega)
    · rw [if_neg hi, execFor, hend i s L h hp hi]
      exact ⟨i, hp, hi⟩

/-- A `while` loop simulates a readable loop `loop` that runs `step` while `cond` holds and
returns `fin` of the last state. Each iteration costs one unit of fuel, and `μ` bounds the
number of iterations. So fuel `n + K + 1` with `μ s ≤ n` is enough. -/
theorem interp_while {σ σ' : Type} (env : Env) (c : Expr) (body : List Stmt) (K : Nat)
    (R : σ → Locals → Heap → Prop) (μ : σ → Nat) (cond : σ → Bool)
    (step : σ → Except Fail σ) (fin : σ → σ') (loop : σ → Except Fail σ')
    (hloop : ∀ s, loop s = if cond s then step s >>= loop else pure (fin s))
    (hcond : ∀ n s L h, R s L h → evalExpr env (n + K) L h c = .ok (.bool (cond s), h))
    (hbody : ∀ n s L h, R s L h → cond s = true →
      StepRel R (execBlock env (n + K) L h body) (step s))
    (hdec : ∀ s s', cond s = true → step s = .ok s' → μ s' < μ s) :
    ∀ n s L h, R s L h → μ s ≤ n →
      StepRel (fun s' L' h' => ∃ s, R s L' h' ∧ cond s = false ∧ fin s = s')
        (execWhile env (n + K + 1) L h c body) (loop s) := by
  intro n
  induction n with
  | zero =>
    intro s L h hR hμ
    rw [execWhile, hcond 0 s L h hR, hloop]
    cases hc : cond s
    · simp [truthy, LibValues.truthy, Ssz.truthy, pyTruthy, StepRel]; exact ⟨s, hR, hc, rfl⟩
    · obtain hb := hbody 0 s L h hR hc
      rw [Nat.zero_add] at hb
      simp only [Except.bind_ok', truthy, LibValues.truthy, Ssz.truthy, pyTruthy, ↓reduceIte, Nat.zero_add]
      cases hs : step s with
      | error e =>
        rw [hs] at hb
        revert hb; cases execBlock env K L h body with
        | error e' => intro hb; simp [StepRel] at hb ⊢; exact hb
        | ok r => obtain ⟨o, L1, h1⟩ := r; cases o <;> simp [StepRel]
      | ok s' => exact absurd (hdec s s' hc hs) (by omega)
  | succ n ih =>
    intro s L h hR hμ
    rw [execWhile, hcond (n + 1) s L h hR, hloop]
    cases hc : cond s
    · simp [truthy, LibValues.truthy, Ssz.truthy, pyTruthy, StepRel]; exact ⟨s, hR, hc, rfl⟩
    · obtain hb := hbody (n + 1) s L h hR hc
      simp only [Except.bind_ok', truthy, LibValues.truthy, Ssz.truthy, pyTruthy, ↓reduceIte]
      revert hb
      cases hs : step s with
      | error e =>
        cases execBlock env (n + 1 + K) L h body with
        | error e' => intro hb; simp [StepRel] at hb ⊢; exact hb
        | ok r => obtain ⟨o, L1, h1⟩ := r; cases o <;> simp [StepRel]
      | ok s' =>
        cases execBlock env (n + 1 + K) L h body with
        | error e' => simp [StepRel]
        | ok r =>
          obtain ⟨o, L1, h1⟩ := r
          cases o <;> simp only [StepRel, Except.bind_ok', false_implies]
          intro hR'
          rw [show n + 1 + K = n + K + 1 by omega]
          exact ih s' L1 h1 hR' (by have := hdec s s' hc hs; omega)

/-! ## Equality of values that are not heap objects -/

theorem deepEq_uint (h : Heap) (t t' : UintTy) (a b : Nat) :
    deepEq depthBound h (.uint t a) (.uint t' b) = cmpVal .eq (.uint t a) (.uint t' b) := by
  simp only [depthBound]; rw [deepEq.eq_def]

theorem deepEq_bytes (h : Heap) (c c' : Name) (a b : List UInt8) :
    deepEq depthBound h (.bytes c a) (.bytes c' b) = cmpVal .eq (.bytes c a) (.bytes c' b) := by
  simp only [depthBound]; rw [deepEq.eq_def]

/-! ## Heap access -/

theorem normIndex_nat (len i : Nat) :
    normIndex len (i : Int) = if i < len then some i else none := by
  unfold normIndex
  rw [if_neg (by omega)]
  by_cases hi : i < len
  · rw [if_pos (by omega), if_pos hi]; rfl
  · rw [if_neg (by omega), if_neg hi]

theorem getItem_list {h : Heap} {a : Nat} {k e l xs} (ho : h.objs a = some (.list k e l xs))
    (t : UintTy) (i : Nat) :
    getItem h (.ref a) (.uint t i) =
      match xs[i]? with
      | some v => .ok v
      | none => .error .indexError := by
  simp only [getItem, Ssz.toIndex_uint, Ssz.toIndex_int, Except.bind_ok', ho, normIndex_nat]
  by_cases hi : i < xs.length
  · simp [hi]
  · simp [hi]

theorem getItem_list_int {h : Heap} {a : Nat} {k e l xs} (ho : h.objs a = some (.list k e l xs))
    (i : Nat) :
    getItem h (.ref a) (.int (i : Int)) =
      match xs[i]? with
      | some v => .ok v
      | none => .error .indexError := by
  simp only [getItem, Ssz.toIndex_uint, Ssz.toIndex_int, Except.bind_ok', ho, normIndex_nat]
  by_cases hi : i < xs.length <;> simp [hi]

/-- `coerceH` on a value that is not a heap object, into a type that is not a heap type. -/
theorem coerceH_plain (env : Env) (b : Bool) (d : Nat) (h : Heap) (u : UintTy) (v : Value)
    (hv : ∀ a, v ≠ .ref a) :
    Ssz.coerceH env b (d + 1) h (.uint u) v =
      (fun x => (x, h)) <$> (if b then coerceField (.uint u) v else coerceElem (.uint u) v) := by
  rw [Ssz.coerceH.eq_def]
  cases v <;> first | (exact absurd rfl (hv _)) | (cases b <;> simp <;> rfl)

/-- The coercion of a value that is not a heap object, into a uint type. -/
theorem coerceWith_uint (env : Env) (b : Bool) (h : Heap) (u : UintTy) (v : Value)
    (hv : ∀ a, v ≠ .ref a) :
    coerceWith env b h (.uint u) v =
      (fun x => (x, h)) <$> (if b then coerceField (.uint u) v else coerceElem (.uint u) v) := by
  simp only [coerceWith, LibModel.coerce, Ssz.coerce, depthBound, coerceH_plain env b 63 h u v hv]

theorem setItem_list {env : Env} {h : Heap} {a : Nat} {k u l xs}
    (ho : h.objs a = some (.list k (.uint u) l xs)) (t : UintTy) (i : Nat) (v : Value)
    (hv : ∀ b, v ≠ .ref b) :
    setItem env h (.ref a) (.uint t i) v = (do
      let v' ← coerceElem (.uint u) v
      if i < xs.length then .ok (h.set a (.list k (.uint u) l (xs.set i v')))
      else .error .indexError) := by
  simp only [setItem, ho, Ssz.toIndex_uint, Except.bind_ok', coerceWith_uint env false h u v hv,
    normIndex_nat]
  cases coerceElem (.uint u) v with
  | error => rfl
  | ok v' => by_cases hi : i < xs.length <;> simp [hi]

theorem getAttr_container (env : Env) {h : Heap} {a : Nat} {ty fs} {f i : Nat} {t : SszTy}
    (ho : h.objs a = some (.container ty fs)) (hf : fieldIndex env ty f = some (i, t)) :
    getAttr env h (.ref a) f =
      match fs[i]? with
      | some v => .ok v
      | none => .error .unsupported := by
  simp only [getAttr, ho, hf]; rfl

theorem setAttr_container (env : Env) {h : Heap} {a : Nat} {ty fs} {f i : Nat} {u : UintTy}
    (ho : h.objs a = some (.container ty fs)) (hf : fieldIndex env ty f = some (i, .uint u))
    (v : Value) (hv : ∀ b, v ≠ .ref b) :
    setAttr env h (.ref a) f v = (do
      let v' ← coerceField (.uint u) v
      .ok (h.set a (.container ty (fs.set i v')))) := by
  simp only [setAttr, ho, hf, coerceWith_uint env true h u v hv]
  cases coerceField (.uint u) v <;> rfl

/-- A binary operator on values outside the heap does not go through `seqBinop`. -/
theorem seqBinop_none {env : Env} {h : Heap} {op : BinOp} {x y : Value}
    (hx : ∀ a, x ≠ .ref a) (hy : ∀ a, y ≠ .ref a) : seqBinop env h op x y = none := by
  unfold seqBinop
  split
  · exact absurd rfl (hx _)
  · exact absurd rfl (hy _)
  · rfl

@[simp] theorem seqBinop_uu {env : Env} {h : Heap} {op : BinOp} {t t' : UintTy} {a b : Nat} :
    seqBinop env h op (.uint t a) (.uint t' b) = none :=
  seqBinop_none (fun _ e => nomatch e) (fun _ e => nomatch e)

@[simp] theorem seqBinop_ui {env : Env} {h : Heap} {op : BinOp} {t : UintTy} {a : Nat} {b : Int} :
    seqBinop env h op (.uint t a) (.int b) = none :=
  seqBinop_none (fun _ e => nomatch e) (fun _ e => nomatch e)

@[simp] theorem seqBinop_iu {env : Env} {h : Heap} {op : BinOp} {t : UintTy} {a : Int} {b : Nat} :
    seqBinop env h op (.int a) (.uint t b) = none :=
  seqBinop_none (fun _ e => nomatch e) (fun _ e => nomatch e)

@[simp] theorem seqBinop_ii {env : Env} {h : Heap} {op : BinOp} {a b : Int} :
    seqBinop env h op (.int a) (.int b) = none :=
  seqBinop_none (fun _ e => nomatch e) (fun _ e => nomatch e)

end SpecLean
