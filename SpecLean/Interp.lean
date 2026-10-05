import SpecLean.Builtins

/-!
# Interpreter

Python reference semantics with a heap. Each expression or statement step, each call, each
`for` iteration, each comprehension item and each `while` iteration costs one unit of fuel.
Sequencing of statements and of arguments costs nothing. Running out of fuel is the error
`outOfFuel`. No construct catches an error, so an error ends the run (SPEC 9.2).
-/

namespace SpecLean

def Locals.empty : Locals := fun _ => none

def Locals.set (L : Locals) (x : Name) (v : Value) : Locals :=
  fun y => if y = x then some v else L y

@[simp] theorem Locals.set_apply (L : Locals) (x : Name) (v : Value) (y : Name) :
    L.set x v y = if y = x then some v else L y := by
  simp only [Locals.set]

/-- How a statement ends. -/
inductive Outcome where
  | normal | brk | cont
  | ret (v : Value)
  deriving Repr

/-- A local, then a global. A global that is not a constant is a `Value.glob`. -/
def lookupName (env : Env) (L : Locals) (x : Name) : Res Value :=
  match L x with
  | some v => .ok v
  | none =>
    match env.globals.lookup x with
    | some (.const v) => .ok v
    | some .configVar =>
      match env.config.lookup x with
      | some v => .ok v
      | none => .error .nameError
    | some _ => .ok (.glob x)
    | none => .error .nameError

/-- Bind call arguments to parameters: positional values, then `*args`, then keywords, then
defaults. A missing or doubled argument raises `TypeError`. -/
def bindArgs (ps : Params) (defaults : List Value) (vs : List Value) (kws : List (Name × Value))
    (base : Locals) : Res Locals := do
  let n := ps.names.length
  if vs.length > n ∧ ps.vararg.isNone then .error .typeError else
  if kws.any (fun (k, _) => !ps.names.contains k || (ps.names.idxOf k) < vs.length) then
    .error .typeError else
  let firstDefault := n - ps.defaults.length
  let rec go (L : Locals) : List (Name × Nat) → Res Locals
    | [] => .ok L
    | (x, i) :: rest => do
      let v ← match vs[i]? with
        | some v => pure v
        | none =>
          match kws.lookup x with
          | some v => pure v
          | none =>
            match defaults[i - firstDefault]? with
            | some d => if firstDefault ≤ i then pure d else .error .typeError
            | none => .error .typeError
      go (L.set x v) rest
  let L ← go base (ps.names.zipIdx)
  match ps.vararg with
  | some a => pure (L.set a (.tuple (vs.drop n)))
  | none => pure L

mutual

def evalExpr (env : Env) : Nat → Locals → Heap → Expr → Res (Value × Heap)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, L, h, e =>
    match e with
    | .name _ x => do
      let v ← lookupName env L x
      pure (v, h)
    | .int _ k => pure (.int k, h)
    | .bool _ b => pure (.bool b, h)
    | .str _ s => pure (.str s, h)
    | .bytes _ b => pure (.bytes env.bytesName b, h)
    | .noneLit _ => pure (.none, h)
    | .attr _ o f => do
      let (ov, h1) ← evalExpr env n L h o
      let v ← getAttr env h1 ov f
      pure (v, h1)
    | .index _ o i => do
      let (ov, h1) ← evalExpr env n L h o
      let (iv, h2) ← evalExpr env n L h1 i
      let v ← getItem h2 ov iv
      pure (v, h2)
    | .slice _ o lo hi none => do
      let (ov, h1) ← evalExpr env n L h o
      let (lov, h2) ← evalOpt env n L h1 lo
      let (hiv, h3) ← evalOpt env n L h2 hi
      getSlice env.bytesName h3 ov lov hiv
    | .slice _ _ _ _ (some _) => .error .unsupported
    | .binop _ op a b => do
      let (x, h1) ← evalExpr env n L h a
      let (y, h2) ← evalExpr env n L h1 b
      let v ← binopVal op x y
      pure (v, h2)
    | .unop _ .not a => do
      let (x, h1) ← evalExpr env n L h a
      pure (.bool !(← truthyH h1 x), h1)
    | .unop _ op a => do
      let (x, h1) ← evalExpr env n L h a
      let v ← unopVal op x
      pure (v, h1)
    | .compare _ a rest => do
      let (x, h1) ← evalExpr env n L h a
      evalCmp env n L h1 x rest
    | .boolop _ op args => evalBoolOp env n L h op args
    | .call _ fn args => do
      let (fv, h1) ← evalExpr env n L h fn
      let (vs, kws, h2) ← evalArgs env n L h1 args
      callValue env n fv vs kws h2
    | .ifExp _ c a b => do
      let (cv, h1) ← evalExpr env n L h c
      if ← truthyH h1 cv then evalExpr env n L h1 a else evalExpr env n L h1 b
    | .comp _ kind elt gens => do
      let (vs, h1) ← compLoop env n L h gens elt
      match kind with
      | .list => pure (allocPyList h1 vs)
      | .gen => pure (.tuple vs, h1)
      | .set => do
        let xs ← dedupe h1 [] vs
        let (a, h2) := h1.alloc (.set xs)
        pure (.ref a, h2)
    | .lambda _ ps body =>
      let (a, h1) := h.alloc (.closure ⟨ps, [], none⟩ (.expr body) L)
      pure (.ref a, h1)
    | .list _ es => do
      let (vs, h1) ← evalList env n L h es
      pure (allocPyList h1 vs)
    | .tuple _ es => do
      let (vs, h1) ← evalList env n L h es
      pure (.tuple vs, h1)
    | .dict _ kvs => do
      let (ks, h1) ← evalList env n L h (kvs.map (·.1))
      let (vs, h2) ← evalList env n L h1 (kvs.map (·.2))
      let (a, h3) := h2.alloc (.dict [])
      let h4 ← (ks.zip vs).foldlM (fun h (k, v) => setItem env h (.ref a) k v) h3
      pure (.ref a, h4)
termination_by n _ _ _ => (n, 0, 0)

def evalOpt (env : Env) : Nat → Locals → Heap → Option Expr → Res (Option Value × Heap)
  | _, _, h, none => pure (none, h)
  | n, L, h, some e => do
    let (v, h1) ← evalExpr env n L h e
    pure (some v, h1)
termination_by n _ _ _ => (n, 1, 0)

def evalList (env : Env) : Nat → Locals → Heap → List Expr → Res (List Value × Heap)
  | _, _, h, [] => pure ([], h)
  | n, L, h, e :: es => do
    let (v, h1) ← evalExpr env n L h e
    let (vs, h2) ← evalList env n L h1 es
    pure (v :: vs, h2)
termination_by n _ _ es => (n, 1, es.length)

/-- Call arguments, left to right. `*xs` adds the items of `xs`. -/
def evalArgs (env : Env) : Nat → Locals → Heap → List Arg →
    Res (List Value × List (Name × Value) × Heap)
  | _, _, h, [] => pure ([], [], h)
  | n, L, h, a :: as => do
    match a with
    | .pos e => do
      let (v, h1) ← evalExpr env n L h e
      let (vs, kws, h2) ← evalArgs env n L h1 as
      pure (v :: vs, kws, h2)
    | .starred e => do
      let (v, h1) ← evalExpr env n L h e
      let xs ← iterElems h1 v
      let (vs, kws, h2) ← evalArgs env n L h1 as
      pure (xs ++ vs, kws, h2)
    | .kw k e => do
      let (v, h1) ← evalExpr env n L h e
      let (vs, kws, h2) ← evalArgs env n L h1 as
      pure (vs, (k, v) :: kws, h2)
termination_by n _ _ as => (n, 1, as.length)

/-- A comparison: `is`, `in`, `==` (by contents for heap objects), or an order. -/
def evalCmp (env : Env) : Nat → Locals → Heap → Value → List (CmpOp × Expr) →
    Res (Value × Heap)
  | _, _, h, _, [] => pure (.bool true, h)
  | n, L, h, x, (op, e) :: rest => do
    let (y, h1) ← evalExpr env n L h e
    if ← compareOp h1 op x y then evalCmp env n L h1 y rest else pure (.bool false, h1)
termination_by n _ _ _ rest => (n, 1, rest.length)

/-- `and` and `or` short-circuit and return an operand, not a `bool`. -/
def evalBoolOp (env : Env) : Nat → Locals → Heap → BoolOp → List Expr → Res (Value × Heap)
  | _, _, _, _, [] => .error .unsupported
  | n, L, h, op, e :: es => do
    let (v, h1) ← evalExpr env n L h e
    -- The last operand is the result, with no truth test.
    if es.isEmpty then pure (v, h1) else
    let b ← truthyH h1 v
    match op, b with
    | .or, true => pure (v, h1)
    | .and, false => pure (v, h1)
    | _, _ => evalBoolOp env n L h1 op es
termination_by n _ _ _ es => (n, 1, es.length)

/-- The items of a comprehension. Its names do not leak into the enclosing frame. -/
def compLoop (env : Env) : Nat → Locals → Heap → List Comprehension → Expr →
    Res (List Value × Heap)
  | n, L, h, [], elt => do
    let (v, h1) ← evalExpr env n L h elt
    pure ([v], h1)
  | n, L, h, .mk t it ifs :: rest, elt => do
    let (iv, h1) ← evalExpr env n L h it
    let xs ← iterElems h1 iv
    compItems env n L h1 t ifs rest elt xs
termination_by n _ _ gens _ => (n, 3, gens.length)

/-- One comprehension item costs one unit of fuel. -/
def compItems (env : Env) : Nat → Locals → Heap → Target → List Expr → List Comprehension →
    Expr → List Value → Res (List Value × Heap)
  | 0, _, _, _, _, _, _, _ => .error .outOfFuel
  | _ + 1, _, h, _, _, _, _, [] => pure ([], h)
  | n + 1, L, h, t, ifs, rest, elt, x :: xs => do
    let (L1, h1) ← assignTarget env n L h t x
    let (keep, h2) ← evalIfs env n L1 h1 ifs
    let (vs1, h3) ← if keep then compLoop env n L1 h2 rest elt else pure ([], h2)
    let (vs2, h4) ← compItems env (n + 1) L1 h3 t ifs rest elt xs
    pure (vs1 ++ vs2, h4)
termination_by n _ _ _ _ _ _ xs => (n, 2, xs.length)

def evalIfs (env : Env) : Nat → Locals → Heap → List Expr → Res (Bool × Heap)
  | _, _, h, [] => pure (true, h)
  | n, L, h, c :: cs => do
    let (v, h1) ← evalExpr env n L h c
    if ← truthyH h1 v then evalIfs env n L h1 cs else pure (false, h1)
termination_by n _ _ cs => (n, 1, cs.length)

/-- Call a value: a spec function, a builtin, a type, a closure or a method. -/
def callValue (env : Env) : Nat → Value → List Value → List (Name × Value) → Heap →
    Res (Value × Heap)
  | n, f, vs, kws, h =>
    match f with
    | .glob g =>
      match env.globals.lookup g with
      | some (.fn d) => callFn env n d.params (.stmts d.body) Locals.empty vs kws h
      | some (.builtin .filter) =>
        match vs with
        | [fn, it] => do
          let xs ← iterElems h it
          let (ys, h1) ← filterItems env n fn xs h
          pure (.tuple ys, h1)
        | _ => .error .typeError
      | some (.builtin .sorted) =>
        match vs, kws.lookup env.nm.key with
        | [it], some key => do
          let xs ← iterElems h it
          let (ks, h1) ← mapItems env n key xs h
          let rev := match kws.lookup env.nm.reverse with | some (.bool true) => true | _ => false
          let ys ← stableSort rev (ks.zip xs)
          pure (allocPyList h1 ys)
        | _, _ => applyBuiltin env h .sorted vs kws
      | some (.builtin b) => applyBuiltin env h b vs kws
      | some (.type t) => applyType env h t vs kws
      | some (.dataclass ty) => applyDataclass env h ty vs kws
      | _ => .error .typeError
    | .ref a =>
      match h.objs a with
      | some (.closure ps body captured) => callFn env n ps body captured vs kws h
      | _ => .error .typeError
    | .member base m =>
      if kws.isEmpty then applyMethod env h base m vs else .error .unsupported
    | _ => .error .typeError
termination_by n _ _ _ _ => (n, 3, 0)

/-- Run a function body in a new frame on top of `base`: empty for a spec function, the
captured frame for a closure. A body that ends without `return` gives `None`. -/
def callFn (env : Env) : Nat → Params → ClosureBody → Locals → List Value →
    List (Name × Value) → Heap → Res (Value × Heap)
  | 0, _, _, _, _, _, _ => .error .outOfFuel
  | n + 1, ps, body, base, vs, kws, h => do
    -- Python evaluates defaults once, at `def` time. Spec defaults are constants, so evaluating
    -- them at each call gives the same values.
    let (ds, h0) ← evalList env n Locals.empty h ps.defaults
    let L0 ← bindArgs ps ds vs kws base
    let h := h0
    match body with
    | .expr e => evalExpr env n L0 h e
    | .stmts ss => do
      let (o, _, h1) ← execBlock env n L0 h ss
      match o with
      | .ret v => pure (v, h1)
      | _ => pure (.none, h1)
termination_by n _ _ _ _ _ _ => (n, 0, 0)

/-- `filter(fn, xs)`: each item costs one unit of fuel. -/
def filterItems (env : Env) : Nat → Value → List Value → Heap → Res (List Value × Heap)
  | 0, _, _, _ => .error .outOfFuel
  | _ + 1, _, [], h => pure ([], h)
  | n + 1, fn, x :: xs, h => do
    let (v, h1) ← callValue env n fn [x] [] h
    let keep ← truthyH h1 v
    let (ys, h2) ← filterItems env (n + 1) fn xs h1
    pure (if keep then x :: ys else ys, h2)
termination_by n _ xs _ => (n, 2, xs.length)

/-- `[fn(x) for x in xs]`, for `sorted(..., key=fn)`. -/
def mapItems (env : Env) : Nat → Value → List Value → Heap → Res (List Value × Heap)
  | 0, _, _, _ => .error .outOfFuel
  | _ + 1, _, [], h => pure ([], h)
  | n + 1, fn, x :: xs, h => do
    let (v, h1) ← callValue env n fn [x] [] h
    let (ys, h2) ← mapItems env (n + 1) fn xs h1
    pure (v :: ys, h2)
termination_by n _ xs _ => (n, 2, xs.length)

def assignTarget (env : Env) : Nat → Locals → Heap → Target → Value → Res (Locals × Heap)
  | 0, _, _, _, _ => .error .outOfFuel
  | n + 1, L, h, t, v =>
    match t with
    | .name _ x => pure (L.set x v, h)
    | .attr _ o f => do
      let (ov, h1) ← evalExpr env n L h o
      let h2 ← setAttr env h1 ov f v
      pure (L, h2)
    | .index _ o i => do
      let (ov, h1) ← evalExpr env n L h o
      let (iv, h2) ← evalExpr env n L h1 i
      let h3 ← setItem env h2 ov iv v
      pure (L, h3)
    | .slice _ o lo hi => do
      let (ov, h1) ← evalExpr env n L h o
      let (lov, h2) ← evalOpt env n L h1 lo
      let (hiv, h3) ← evalOpt env n L h2 hi
      let h4 ← setSlice env h3 ov lov hiv v
      pure (L, h4)
    | .tuple _ ts => do
      let vs ← match v with
        | .tuple vs => pure vs
        | _ => iterElems h v
      if ts.length = vs.length then assignTargets env n L h ts vs
      else .error .valueError
termination_by n _ _ _ _ => (n, 0, 0)

def assignTargets (env : Env) : Nat → Locals → Heap → List Target → List Value →
    Res (Locals × Heap)
  | n, L, h, t :: ts, v :: vs => do
    let (L1, h1) ← assignTarget env n L h t v
    assignTargets env n L1 h1 ts vs
  | _, L, h, [], _ => pure (L, h)
  | _, L, h, _ :: _, [] => pure (L, h)
termination_by n _ _ ts _ => (n, 1, ts.length)

/-- `t1 = t2 = v`: each target gets the same value, left to right. -/
def assignAll (env : Env) : Nat → Locals → Heap → List Target → Value → Res (Locals × Heap)
  | _, L, h, [], _ => pure (L, h)
  | n, L, h, t :: ts, v => do
    let (L1, h1) ← assignTarget env n L h t v
    assignAll env n L1 h1 ts v
termination_by n _ _ ts _ => (n, 1, ts.length)

def execStmt (env : Env) : Nat → Locals → Heap → Stmt → Res (Outcome × Locals × Heap)
  | 0, _, _, _ => .error .outOfFuel
  | n + 1, L, h, s =>
    match s with
    | .assign _ [t] e => do
      -- `obj[i] = rhs` evaluates `rhs` first, then `obj`, then `i`.
      let (v, h1) ← evalExpr env n L h e
      let (L1, h2) ← assignTarget env n L h1 t v
      pure (.normal, L1, h2)
    | .assign _ ts e => do
      let (v, h1) ← evalExpr env n L h e
      let (L1, h2) ← assignAll env n L h1 ts v
      pure (.normal, L1, h2)
    | .annAssign _ t e => do
      let (v, h1) ← evalExpr env n L h e
      let (L1, h2) ← assignTarget env n L h1 t v
      pure (.normal, L1, h2)
    | .augAssign _ t op e =>
      -- `obj[i] op= rhs` evaluates `obj`, then `i`, then reads `obj[i]`, then `rhs`.
      match t with
      | .name _ x => do
        let cur ← lookupName env L x
        let (r, h1) ← evalExpr env n L h e
        let v ← binopVal op cur r
        pure (.normal, L.set x v, h1)
      | .attr _ o f => do
        let (ov, h1) ← evalExpr env n L h o
        let cur ← getAttr env h1 ov f
        let (r, h2) ← evalExpr env n L h1 e
        let v ← binopVal op cur r
        let h3 ← setAttr env h2 ov f v
        pure (.normal, L, h3)
      | .index _ o i => do
        let (ov, h1) ← evalExpr env n L h o
        let (iv, h2) ← evalExpr env n L h1 i
        let cur ← getItem h2 ov iv
        let (r, h3) ← evalExpr env n L h2 e
        let v ← binopVal op cur r
        let h4 ← setItem env h3 ov iv v
        pure (.normal, L, h4)
      | _ => .error .unsupported
    | .exprStmt _ e => do
      let (_, h1) ← evalExpr env n L h e
      pure (.normal, L, h1)
    | .ifStmt _ c thn els => do
      let (cv, h1) ← evalExpr env n L h c
      if ← truthyH h1 cv then execBlock env n L h1 thn else execBlock env n L h1 els
    | .forStmt _ t it body => do
      let (iv, h1) ← evalExpr env n L h it
      let src ← iterSource h1 iv
      execFor env n L h1 t src 0 body
    | .whileStmt _ c body => execWhile env n L h c body
    | .ret _ (some e) => do
      let (v, h1) ← evalExpr env n L h e
      pure (.ret v, L, h1)
    | .ret _ none => pure (.ret .none, L, h)
    | .assert _ e => do
      let (v, h1) ← evalExpr env n L h e
      if ← truthyH h1 v then pure (.normal, L, h1) else .error .assertionFailed
    | .raise _ => .error .raised
    | .brk _ => pure (.brk, L, h)
    | .cont _ => pure (.cont, L, h)
    | .pass _ => pure (.normal, L, h)
    | .funDef _ x ps body =>
      let (a, h1) := h.alloc (.closure ps (.stmts body) L)
      pure (.normal, L.set x (.ref a), h1)
termination_by n _ _ _ => (n, 0, 0)

def execBlock (env : Env) : Nat → Locals → Heap → List Stmt → Res (Outcome × Locals × Heap)
  | _, L, h, [] => pure (.normal, L, h)
  | n, L, h, s :: ss => do
    let (o, L1, h1) ← execStmt env n L h s
    match o with
    | .normal => execBlock env n L1 h1 ss
    | _ => pure (o, L1, h1)
termination_by n _ _ ss => (n, 1, ss.length)

/-- A `for` loop by index. Each iteration costs one unit of fuel, because an append inside
the loop extends it. -/
def execFor (env : Env) : Nat → Locals → Heap → Target → IterSrc → Nat → List Stmt →
    Res (Outcome × Locals × Heap)
  | 0, _, _, _, _, _, _ => .error .outOfFuel
  | n + 1, L, h, t, src, i, body => do
    match ← iterItem h src i with
    | none => pure (.normal, L, h)
    | some x =>
      let (L1, h1) ← assignTarget env n L h t x
      let (o, L2, h2) ← execBlock env n L1 h1 body
      match o with
      | .brk => pure (.normal, L2, h2)
      | .ret v => pure (.ret v, L2, h2)
      | _ => execFor env n L2 h2 t src (i + 1) body
termination_by n _ _ _ _ _ _ => (n, 0, 0)

/-- A `while` loop. Each iteration costs one unit of fuel. -/
def execWhile (env : Env) : Nat → Locals → Heap → Expr → List Stmt →
    Res (Outcome × Locals × Heap)
  | 0, _, _, _, _ => .error .outOfFuel
  | n + 1, L, h, c, body => do
    let (cv, h1) ← evalExpr env n L h c
    if ← truthyH h1 cv then
      let (o, L1, h2) ← execBlock env n L h1 body
      match o with
      | .brk => pure (.normal, L1, h2)
      | .ret v => pure (.ret v, L1, h2)
      | _ => execWhile env n L1 h2 c body
    else pure (.normal, L, h1)
termination_by n _ _ _ _ => (n, 0, 0)

end

/-- Call a spec function by name with positional arguments. -/
def callName (env : Env) (n : Nat) (f : Name) (vs : List Value) (h : Heap) :
    Res (Value × Heap) :=
  callValue env n (.glob f) vs [] h

def interp (env : Env) (fuel : Nat) (f : Name) (args : List Value) (h : Heap) :
    Res (Value × Heap) :=
  callName env fuel f args h

end SpecLean
