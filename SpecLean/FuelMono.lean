import SpecLean.Lemmas

/-!
# Fuel monotonicity (`interp_fuel_mono`)

`Agree r r'` says that `r'` equals `r` unless `r` ran out of fuel. Each interpreter function
at fuel `n` agrees with fuel `n + 1`. The proof goes level by level: the functions that lower
the fuel use the level below, and the functions that recurse on a list at the same fuel use
the functions of the same level. It needs no premise beyond the interpreter itself, because
no construct catches an error.
-/

namespace SpecLean.Mono

open SpecLean

/-- `r'` equals `r` unless `r` ran out of fuel. -/
def Agree (r r' : Res α) : Prop := r ≠ .error .outOfFuel → r' = r

theorem agree_refl (r : Res α) : Agree r r := fun _ => rfl

theorem agree_oof (r : Res α) : Agree (.error .outOfFuel) r := fun h => absurd rfl h

theorem agree_bind {a a' : Res α} {f f' : α → Res β} (ha : Agree a a')
    (hf : ∀ x, Agree (f x) (f' x)) : Agree (a >>= f) (a' >>= f') := by
  intro hne
  cases a with
  | error e =>
    have : e ≠ .outOfFuel := fun he => hne (by subst he; rfl)
    rw [ha (fun h => this (by cases h; rfl))]; rfl
  | ok x =>
    rw [ha (by simp)]
    simp only [Except.bind_ok'] at hne ⊢
    exact hf x hne

variable (env : Env)

/-- Every interpreter function at fuel `n` agrees with fuel `n + 1`. -/
structure Level (n : Nat) : Prop where
  expr : ∀ L h e, Agree (evalExpr env n L h e) (evalExpr env (n + 1) L h e)
  opt : ∀ L h o, Agree (evalOpt env n L h o) (evalOpt env (n + 1) L h o)
  list : ∀ L h es, Agree (evalList env n L h es) (evalList env (n + 1) L h es)
  args : ∀ L h as, Agree (evalArgs env n L h as) (evalArgs env (n + 1) L h as)
  cmp : ∀ L h x rest, Agree (evalCmp env n L h x rest) (evalCmp env (n + 1) L h x rest)
  boolop : ∀ L h op es, Agree (evalBoolOp env n L h op es) (evalBoolOp env (n + 1) L h op es)
  comp : ∀ L h gs elt, Agree (compLoop env n L h gs elt) (compLoop env (n + 1) L h gs elt)
  items : ∀ L h t ifs rest elt xs,
    Agree (compItems env n L h t ifs rest elt xs) (compItems env (n + 1) L h t ifs rest elt xs)
  ifs : ∀ L h cs, Agree (evalIfs env n L h cs) (evalIfs env (n + 1) L h cs)
  call : ∀ f vs kws h, Agree (callValue env n f vs kws h) (callValue env (n + 1) f vs kws h)
  fn : ∀ ps body base vs kws h,
    Agree (callFn env n ps body base vs kws h) (callFn env (n + 1) ps body base vs kws h)
  filter : ∀ f xs h, Agree (filterItems env n f xs h) (filterItems env (n + 1) f xs h)
  map : ∀ f xs h, Agree (mapItems env n f xs h) (mapItems env (n + 1) f xs h)
  target : ∀ L h t v, Agree (assignTarget env n L h t v) (assignTarget env (n + 1) L h t v)
  targets : ∀ L h ts vs,
    Agree (assignTargets env n L h ts vs) (assignTargets env (n + 1) L h ts vs)
  all : ∀ L h ts v, Agree (assignAll env n L h ts v) (assignAll env (n + 1) L h ts v)
  stmt : ∀ L h s, Agree (execStmt env n L h s) (execStmt env (n + 1) L h s)
  block : ∀ L h ss, Agree (execBlock env n L h ss) (execBlock env (n + 1) L h ss)
  forLoop : ∀ L h t src i body,
    Agree (execFor env n L h t src i body) (execFor env (n + 1) L h t src i body)
  whileLoop : ∀ L h c body,
    Agree (execWhile env n L h c body) (execWhile env (n + 1) L h c body)

/-! ## Functions that recurse at the same fuel -/

section same

variable (n : Nat)
  (hE : ∀ L h e, Agree (evalExpr env n L h e) (evalExpr env (n + 1) L h e))

include hE

theorem opt_of : ∀ L h o, Agree (evalOpt env n L h o) (evalOpt env (n + 1) L h o) := by
  intro L h o
  cases o with
  | none => simp only [evalOpt]; exact agree_refl _
  | some e => simp only [evalOpt]; exact agree_bind (hE _ _ _) fun _ => agree_refl _

theorem list_of : ∀ L h es, Agree (evalList env n L h es) (evalList env (n + 1) L h es) := by
  intro L h es
  induction es generalizing L h with
  | nil => simp only [evalList]; exact agree_refl _
  | cons e es ih =>
    simp only [evalList]
    exact agree_bind (hE _ _ _) fun _ => agree_bind (ih _ _) fun _ => agree_refl _

theorem args_of : ∀ L h as, Agree (evalArgs env n L h as) (evalArgs env (n + 1) L h as) := by
  intro L h as
  induction as generalizing L h with
  | nil => simp only [evalArgs]; exact agree_refl _
  | cons a as ih =>
    cases a with
    | pos e =>
      simp only [evalArgs]
      exact agree_bind (hE _ _ _) fun _ => agree_bind (ih _ _) fun _ => agree_refl _
    | starred e =>
      simp only [evalArgs]
      exact agree_bind (hE _ _ _) fun _ => agree_bind (agree_refl _) fun _ =>
        agree_bind (ih _ _) fun _ => agree_refl _
    | kw k e =>
      simp only [evalArgs]
      exact agree_bind (hE _ _ _) fun _ => agree_bind (ih _ _) fun _ => agree_refl _

theorem cmp_of : ∀ L h x rest,
    Agree (evalCmp env n L h x rest) (evalCmp env (n + 1) L h x rest) := by
  intro L h x rest
  induction rest generalizing L h x with
  | nil => simp only [evalCmp]; exact agree_refl _
  | cons p rest ih =>
    obtain ⟨op, e⟩ := p
    simp only [evalCmp]
    refine agree_bind (hE _ _ _) fun y => agree_bind (agree_refl _) fun b => ?_
    cases b
    · exact agree_refl _
    · exact ih _ _ _

theorem boolop_of : ∀ L h op es,
    Agree (evalBoolOp env n L h op es) (evalBoolOp env (n + 1) L h op es) := by
  intro L h op es
  induction es generalizing L h with
  | nil => simp only [evalBoolOp]; exact agree_refl _
  | cons e es ih =>
    simp only [evalBoolOp]
    refine agree_bind (hE _ _ _) fun y => ?_
    split
    · exact agree_refl _
    · refine agree_bind (agree_refl _) fun b => ?_
      cases op <;> cases b <;> first | exact agree_refl _ | exact ih _ _

theorem ifs_of : ∀ L h cs, Agree (evalIfs env n L h cs) (evalIfs env (n + 1) L h cs) := by
  intro L h cs
  induction cs generalizing L h with
  | nil => simp only [evalIfs]; exact agree_refl _
  | cons c cs ih =>
    simp only [evalIfs]
    refine agree_bind (hE _ _ _) fun _ => agree_bind (agree_refl _) fun b => ?_
    cases b
    · exact agree_refl _
    · exact ih _ _

theorem comp_of
    (hI : ∀ L h t ifs rest elt xs,
      Agree (compItems env n L h t ifs rest elt xs) (compItems env (n + 1) L h t ifs rest elt xs)) :
    ∀ L h gs elt, Agree (compLoop env n L h gs elt) (compLoop env (n + 1) L h gs elt) := by
  intro L h gs elt
  cases gs with
  | nil => simp only [compLoop]; exact agree_bind (hE _ _ _) fun _ => agree_refl _
  | cons g gs =>
    obtain ⟨t, it, ifs⟩ := g
    simp only [compLoop]
    exact agree_bind (hE _ _ _) fun _ => agree_bind (agree_refl _) fun _ => hI _ _ _ _ _ _ _

end same

theorem call_of (n : Nat)
    (hF : ∀ ps body base vs kws h,
      Agree (callFn env n ps body base vs kws h) (callFn env (n + 1) ps body base vs kws h))
    (hFi : ∀ f xs h, Agree (filterItems env n f xs h) (filterItems env (n + 1) f xs h))
    (hM : ∀ f xs h, Agree (mapItems env n f xs h) (mapItems env (n + 1) f xs h)) :
    ∀ f vs kws h, Agree (callValue env n f vs kws h) (callValue env (n + 1) f vs kws h) := by
  intro f vs kws h
  rw [callValue.eq_def, callValue.eq_def]
  repeat' split
  all_goals first
    | exact hF _ _ _ _ _ _
    | exact agree_refl _
    | exact agree_bind (agree_refl _) fun _ => agree_bind (hFi _ _ _) fun _ => agree_refl _
    | exact agree_bind (agree_refl _) fun _ => agree_bind (hM _ _ _) fun _ =>
        agree_bind (agree_refl _) fun _ => agree_refl _

theorem targets_of (n : Nat)
    (hT : ∀ L h t v, Agree (assignTarget env n L h t v) (assignTarget env (n + 1) L h t v)) :
    ∀ L h ts vs, Agree (assignTargets env n L h ts vs) (assignTargets env (n + 1) L h ts vs) := by
  intro L h ts
  induction ts generalizing L h with
  | nil => intro vs; simp only [assignTargets]; exact agree_refl _
  | cons t ts ih =>
    intro vs
    cases vs with
    | nil => simp only [assignTargets]; exact agree_refl _
    | cons v vs =>
      simp only [assignTargets]
      exact agree_bind (hT _ _ _ _) fun _ => ih _ _ _

theorem all_of (n : Nat)
    (hT : ∀ L h t v, Agree (assignTarget env n L h t v) (assignTarget env (n + 1) L h t v)) :
    ∀ L h ts v, Agree (assignAll env n L h ts v) (assignAll env (n + 1) L h ts v) := by
  intro L h ts v
  induction ts generalizing L h with
  | nil => simp only [assignAll]; exact agree_refl _
  | cons t ts ih =>
    simp only [assignAll]
    exact agree_bind (hT _ _ _ _) fun _ => ih _ _

theorem block_of (n : Nat)
    (hS : ∀ L h s, Agree (execStmt env n L h s) (execStmt env (n + 1) L h s)) :
    ∀ L h ss, Agree (execBlock env n L h ss) (execBlock env (n + 1) L h ss) := by
  intro L h ss
  induction ss generalizing L h with
  | nil => simp only [execBlock]; exact agree_refl _
  | cons s ss ih =>
    simp only [execBlock]
    refine agree_bind (hS _ _ _) fun x => ?_
    obtain ⟨o, L1, h1⟩ := x
    cases o
    · exact ih _ _
    all_goals exact agree_refl _

/-! ## Functions that lower the fuel -/

section succ

variable (n : Nat) (ih : Level env n)
include ih

theorem expr_succ : ∀ L h e, Agree (evalExpr env (n + 1) L h e) (evalExpr env (n + 2) L h e) := by
  intro L h e
  rw [evalExpr.eq_def env (n + 1) L h e, evalExpr.eq_def env (n + 2) L h e]
  cases e with
  | attr l o f => exact agree_bind (ih.expr _ _ _) fun _ => agree_refl _
  | index l o i =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.expr _ _ _) fun _ => agree_refl _
  | slice l o lo hi st =>
    cases st with
    | none =>
      exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.opt _ _ _) fun _ =>
        agree_bind (ih.opt _ _ _) fun _ => agree_refl _
    | some => exact agree_refl _
  | binop l op a b =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.expr _ _ _) fun _ => agree_refl _
  | unop l op a =>
    cases op <;> exact agree_bind (ih.expr _ _ _) fun _ => agree_refl _
  | compare l a rest => exact agree_bind (ih.expr _ _ _) fun _ => ih.cmp _ _ _ _
  | boolop l op args => exact ih.boolop _ _ _ _
  | call l fn args =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.args _ _ _) fun _ => ih.call _ _ _ _
  | ifExp l c a b =>
    refine agree_bind (ih.expr _ _ _) fun _ => agree_bind (agree_refl _) fun b => ?_
    cases b <;> exact ih.expr _ _ _
  | comp l kind elt gens => exact agree_bind (ih.comp _ _ _ _) fun _ => agree_refl _
  | list l es => exact agree_bind (ih.list _ _ _) fun _ => agree_refl _
  | tuple l es => exact agree_bind (ih.list _ _ _) fun _ => agree_refl _
  | dict l kvs =>
    exact agree_bind (ih.list _ _ _) fun _ => agree_bind (ih.list _ _ _) fun _ => agree_refl _
  | _ => exact agree_refl _

theorem items_succ : ∀ L h t ifs rest elt xs,
    Agree (compItems env (n + 1) L h t ifs rest elt xs)
      (compItems env (n + 2) L h t ifs rest elt xs) := by
  intro L h t ifs rest elt xs
  induction xs generalizing L h with
  | nil => simp only [compItems]; exact agree_refl _
  | cons x xs ihx =>
    rw [compItems.eq_3 env L h t ifs rest elt n x xs,
      compItems.eq_3 env L h t ifs rest elt (n + 1) x xs]
    refine agree_bind (ih.target _ _ _ _) fun _ => agree_bind (ih.ifs _ _ _) fun p => ?_
    obtain ⟨keep, h2⟩ := p
    dsimp only
    cases keep
    · simp only [Bool.false_eq_true, ↓reduceIte, Except.pure_ok', Except.bind_ok']
      exact agree_bind (ihx _ _) fun _ => agree_refl _
    · simp only [↓reduceIte]
      exact agree_bind (ih.comp _ _ _ _) fun _ => agree_bind (ihx _ _) fun _ => agree_refl _

theorem fn_succ : ∀ ps body base vs kws h,
    Agree (callFn env (n + 1) ps body base vs kws h) (callFn env (n + 2) ps body base vs kws h) := by
  intro ps body base vs kws h
  simp only [callFn]
  refine agree_bind (ih.list _ _ _) fun _ => agree_bind (agree_refl _) fun _ => ?_
  cases body with
  | expr e => exact ih.expr _ _ _
  | stmts ss => exact agree_bind (ih.block _ _ _) fun _ => agree_refl _

theorem filter_succ : ∀ f xs h,
    Agree (filterItems env (n + 1) f xs h) (filterItems env (n + 2) f xs h) := by
  intro f xs
  induction xs with
  | nil => intro h; simp only [filterItems]; exact agree_refl _
  | cons x xs ihx =>
    intro h
    rw [filterItems.eq_3 env f h n x xs, filterItems.eq_3 env f h (n + 1) x xs]
    exact agree_bind (ih.call _ _ _ _) fun _ => agree_bind (agree_refl _) fun _ =>
      agree_bind (ihx _) fun _ => agree_refl _

theorem map_succ : ∀ f xs h, Agree (mapItems env (n + 1) f xs h) (mapItems env (n + 2) f xs h) := by
  intro f xs
  induction xs with
  | nil => intro h; simp only [mapItems]; exact agree_refl _
  | cons x xs ihx =>
    intro h
    rw [mapItems.eq_3 env f h n x xs, mapItems.eq_3 env f h (n + 1) x xs]
    exact agree_bind (ih.call _ _ _ _) fun _ => agree_bind (ihx _) fun _ => agree_refl _

theorem target_succ : ∀ L h t v,
    Agree (assignTarget env (n + 1) L h t v) (assignTarget env (n + 2) L h t v) := by
  intro L h t v
  rw [assignTarget.eq_def env (n + 1) L h t v, assignTarget.eq_def env (n + 2) L h t v]
  dsimp only
  cases t with
  | name => exact agree_refl _
  | attr l o f =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (agree_refl _) fun _ => agree_refl _
  | index l o i =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.expr _ _ _) fun _ =>
      agree_bind (agree_refl _) fun _ => agree_refl _
  | slice l o lo hi =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.opt _ _ _) fun _ =>
      agree_bind (ih.opt _ _ _) fun _ => agree_bind (agree_refl _) fun _ => agree_refl _
  | tuple l ts =>
    dsimp only
    split <;> refine agree_bind (agree_refl _) fun vs => ?_ <;> split
    all_goals first | exact ih.targets _ _ _ _ | exact agree_refl _

theorem stmt_succ : ∀ L h s, Agree (execStmt env (n + 1) L h s) (execStmt env (n + 2) L h s) := by
  intro L h s
  rw [execStmt.eq_def env (n + 1) L h s, execStmt.eq_def env (n + 2) L h s]
  cases s with
  | assign l ts e =>
    rcases ts with _ | ⟨t, _ | ⟨t2, ts⟩⟩
    · exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.all _ _ _ _) fun _ => agree_refl _
    · exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.target _ _ _ _) fun _ =>
        agree_refl _
    · exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.all _ _ _ _) fun _ => agree_refl _
  | annAssign l t e =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.target _ _ _ _) fun _ => agree_refl _
  | augAssign l t op e =>
    cases t with
    | name =>
      exact agree_bind (agree_refl _) fun _ => agree_bind (ih.expr _ _ _) fun _ =>
        agree_bind (agree_refl _) fun _ => agree_refl _
    | attr =>
      exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (agree_refl _) fun _ =>
        agree_bind (ih.expr _ _ _) fun _ => agree_bind (agree_refl _) fun _ =>
          agree_bind (agree_refl _) fun _ => agree_refl _
    | index =>
      exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (ih.expr _ _ _) fun _ =>
        agree_bind (agree_refl _) fun _ => agree_bind (ih.expr _ _ _) fun _ =>
          agree_bind (agree_refl _) fun _ => agree_bind (agree_refl _) fun _ => agree_refl _
    | _ => exact agree_refl _
  | exprStmt l e => exact agree_bind (ih.expr _ _ _) fun _ => agree_refl _
  | ifStmt l c thn els =>
    refine agree_bind (ih.expr _ _ _) fun _ => agree_bind (agree_refl _) fun b => ?_
    cases b <;> exact ih.block _ _ _
  | forStmt l t it body =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (agree_refl _) fun _ =>
      ih.forLoop _ _ _ _ _ _
  | whileStmt l c body => exact ih.whileLoop _ _ _ _
  | ret l e =>
    cases e with
    | none => exact agree_refl _
    | some e => exact agree_bind (ih.expr _ _ _) fun _ => agree_refl _
  | assert l e =>
    exact agree_bind (ih.expr _ _ _) fun _ => agree_bind (agree_refl _) fun _ => agree_refl _
  | _ => exact agree_refl _

theorem for_succ : ∀ L h t src i body,
    Agree (execFor env (n + 1) L h t src i body) (execFor env (n + 2) L h t src i body) := by
  intro L h t src i body
  rw [execFor.eq_2 env L h t src i body n, execFor.eq_2 env L h t src i body (n + 1)]
  refine agree_bind (agree_refl _) fun x => ?_
  cases x with
  | none => exact agree_refl _
  | some x =>
    refine agree_bind (ih.target _ _ _ _) fun y => agree_bind (ih.block _ _ _) fun z => ?_
    obtain ⟨o, L2, h2⟩ := z
    cases o <;> first | exact ih.forLoop _ _ _ _ _ _ | exact agree_refl _

theorem while_succ : ∀ L h c body,
    Agree (execWhile env (n + 1) L h c body) (execWhile env (n + 2) L h c body) := by
  intro L h c body
  rw [execWhile.eq_2 env L h c body n, execWhile.eq_2 env L h c body (n + 1)]
  refine agree_bind (ih.expr _ _ _) fun y => agree_bind (agree_refl _) fun b => ?_
  cases b
  · exact agree_refl _
  · refine agree_bind (ih.block _ _ _) fun z => ?_
    obtain ⟨o, L1, h1⟩ := z
    cases o <;> first | exact ih.whileLoop _ _ _ _ | exact agree_refl _

end succ

/-! ## Levels -/

/-- A level from the functions that lower the fuel. -/
theorem level_of (n : Nat)
    (hE : ∀ L h e, Agree (evalExpr env n L h e) (evalExpr env (n + 1) L h e))
    (hI : ∀ L h t ifs rest elt xs,
      Agree (compItems env n L h t ifs rest elt xs) (compItems env (n + 1) L h t ifs rest elt xs))
    (hF : ∀ ps body base vs kws h,
      Agree (callFn env n ps body base vs kws h) (callFn env (n + 1) ps body base vs kws h))
    (hFi : ∀ f xs h, Agree (filterItems env n f xs h) (filterItems env (n + 1) f xs h))
    (hM : ∀ f xs h, Agree (mapItems env n f xs h) (mapItems env (n + 1) f xs h))
    (hT : ∀ L h t v, Agree (assignTarget env n L h t v) (assignTarget env (n + 1) L h t v))
    (hS : ∀ L h s, Agree (execStmt env n L h s) (execStmt env (n + 1) L h s))
    (hFor : ∀ L h t src i body,
      Agree (execFor env n L h t src i body) (execFor env (n + 1) L h t src i body))
    (hW : ∀ L h c body, Agree (execWhile env n L h c body) (execWhile env (n + 1) L h c body)) :
    Level env n :=
  { expr := hE, opt := opt_of env n hE, list := list_of env n hE, args := args_of env n hE,
    cmp := cmp_of env n hE, boolop := boolop_of env n hE, comp := comp_of env n hE hI,
    items := hI, ifs := ifs_of env n hE, call := call_of env n hF hFi hM, fn := hF,
    filter := hFi, map := hM, target := hT, targets := targets_of env n hT,
    all := all_of env n hT, stmt := hS, block := block_of env n hS, forLoop := hFor,
    whileLoop := hW }

theorem level_zero : Level env 0 := by
  apply level_of
  · intro L h e; simp only [evalExpr]; exact agree_oof _
  · intro L h t ifs rest elt xs; simp only [compItems]; exact agree_oof _
  · intro ps body base vs kws h; simp only [callFn]; exact agree_oof _
  · intro f xs h; simp only [filterItems]; exact agree_oof _
  · intro f xs h; simp only [mapItems]; exact agree_oof _
  · intro L h t v; simp only [assignTarget]; exact agree_oof _
  · intro L h s; simp only [execStmt]; exact agree_oof _
  · intro L h t src i body; simp only [execFor]; exact agree_oof _
  · intro L h c body; simp only [execWhile]; exact agree_oof _

theorem level_succ (n : Nat) (ih : Level env n) : Level env (n + 1) :=
  level_of env (n + 1) (expr_succ env n ih) (items_succ env n ih) (fn_succ env n ih)
    (filter_succ env n ih) (map_succ env n ih) (target_succ env n ih) (stmt_succ env n ih)
    (for_succ env n ih) (while_succ env n ih)

theorem level (n : Nat) : Level env n := by
  induction n with
  | zero => exact level_zero env
  | succ n ih => exact level_succ env n ih

/-- `interp_fuel_mono` (SPEC 9.2): more fuel does not change a result that did not run out of
fuel. -/
theorem interp_fuel_mono (n m : Nat) (hnm : n ≤ m) (f : Name) (vs : List Value) (h : Heap)
    (hne : interp env n f vs h ≠ .error .outOfFuel) :
    interp env m f vs h = interp env n f vs h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => rfl
  | succ d ih =>
    have e := ih (Nat.le_add_right n d)
    rw [← Nat.add_assoc, interp, callName, (level env (n + d)).call _ vs [] h
      (by rw [← callName, ← interp, e]; exact hne)]
    exact e

end SpecLean.Mono
