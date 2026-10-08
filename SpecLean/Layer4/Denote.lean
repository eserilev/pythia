import SpecLean.Validation.Where

/-!
# Layer 4 spike: a denotation of a fragment (SPEC 10)

The fragment: names, `int`, `bool` and `None` literals, attribute and index reads, binary
operators, comparisons, `and` and `or`; assignment to a local, attribute write, index write,
`obj[i] op= e`, `if`, `return`, `assert`, `pass` and sequencing. No loops and no calls.

`denoteFn` runs a function body on decoded values (`DV`): trees with no heap and no sharing.
A local holds a flat value or a place: an argument number and a path in that argument. A write
through a place changes the tree of that argument. This is the path model of SPEC 7.3 (V1).
The proof in `SpecLean/Layer4/Sound.lean` shows that it agrees with the heap interpreter under
`WTree`.

The denotation gives `none` outside the fragment, and in the cases that the proof does not
cover: a value that is not flat where the proof needs one, a write of a heap object, a write
outside the footprint `fp`. The checks on `fp` hold for a whole function when its footprint is
right, so `simp` removes them on a real function.

Scalar operations are the interpreter's own value rules (`binopVal`, `cmpVal`, `truthy`). The
typed readable Lean is a separate refinement of this denotation (`SpecLean/Layer4/Examples.lean`).
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

/-- A value that needs no heap. -/
def Flat : Value → Bool
  | .int _ | .bool _ | .lib _ | .str _ | .none | .bytes _ _ => true
  | _ => false

/-- A decoded value: a tree of heap objects with flat leaves. -/
inductive DV where
  | leaf (v : Value)
  | cont (ty : Name) (fs : List DV)
  | list (k : ListKind) (e : SszTy) (l : Option Nat) (xs : List DV)
  deriving Inhabited

/-- Decode a value to depth `n`. A heap object decodes to a node, a flat value to a leaf. Two
references to one object decode to two equal trees. -/
def dec (h : Heap) : Nat → Value → Option DV
  | m + 1, .ref a =>
    match h.objs a with
    | some (.container ty fs) => (DV.cont ty) <$> fs.mapM (dec h m)
    | some (.list k e l xs) => (DV.list k e l) <$> xs.mapM (dec h m)
    | _ => none
  | _, v => if Flat v then some (.leaf v) else none

def DV.kids : DV → List DV
  | .leaf _ => []
  | .cont _ ds => ds
  | .list _ _ _ ds => ds

/-- The subtree at a path. -/
def subAt : List Nat → DV → Option DV
  | [], d => some d
  | i :: p, d => match d.kids[i]? with
    | some c => subAt p c
    | none => none

/-- Set child `i` of the node at path `p` to `x`. -/
def updAt : List Nat → DV → Nat → DV → DV
  | [], .cont ty ds, i, x => .cont ty (ds.set i x)
  | [], .list k e l ds, i, x => .list k e l (ds.set i x)
  | [], d, _, _ => d
  | j :: p, .cont ty ds, i, x =>
    .cont ty (match ds[j]? with
      | some c => ds.set j (updAt p c i x)
      | none => ds)
  | j :: p, .list k e l ds, i, x =>
    .list k e l (match ds[j]? with
      | some c => ds.set j (updAt p c i x)
      | none => ds)
  | _ :: _, d, _, _ => d

/-- The result of an expression: a flat value, or a place (argument `k`, path `p`) that holds a
heap object. -/
inductive DRes where
  | val (v : Value)
  | place (k : Nat) (p : List Nat)
  /-- A new object that this run made and never changes: its whole tree. -/
  | tree (d : DV)

/-- A child of the node at place `(k, p)`. -/
def ofChild (k : Nat) (p : List Nat) : DV → DRes
  | .leaf v => .val v
  | _ => .place k p

/-- The state of the denotation: the trees of the arguments and the locals. -/
structure DSt where
  roots : List DV
  loc : Name → Option DRes

def DSt.deref (s : DSt) (k : Nat) (p : List Nat) : Option DV := s.roots[k]?.bind (subAt p)

def setLoc (dl : Name → Option DRes) (x : Name) (r : DRes) : Name → Option DRes :=
  fun y => if y = x then some r else dl y

/-! ## The monad: `none` is "not covered", `some (.error e)` a Python error -/

abbrev DM (α : Type) := Option (Res α)

def DM.ok (a : α) : DM α := some (.ok a)

def DM.bind (x : DM α) (f : α → DM β) : DM β :=
  match x with
  | some (.ok a) => f a
  | some (.error e) => some (.error e)
  | none => none

/-- A value rule. Running out of fuel is not a Python error, so it is not covered. -/
def lift : Res α → DM α
  | .error .outOfFuel => none
  | r => some r

/-- An error of each class (`SpecError.fail`): the proofs compare errors by class, since a
callee taken from a statement (`ResultMatches`) fixes only the class of its error. -/
def SpecError.rep : Fail → SpecError
  | .invalid => .assertionFailed
  | .bug => .typeError

/-- The error of the class of `e`. Running out of fuel stays as it is. -/
def normE : SpecError → SpecError
  | .outOfFuel => .outOfFuel
  | e => SpecError.rep e.fail

theorem normE_ne {e : SpecError} (h : e ≠ .outOfFuel) : normE e ≠ .outOfFuel := by
  cases e <;> simp_all [normE, SpecError.rep, SpecError.fail] <;> split <;> simp

theorem normE_ne' {e : SpecError} (h : normE e ≠ .outOfFuel) : e ≠ .outOfFuel := by
  rintro rfl; exact h rfl

theorem normE_eq_oof {e : SpecError} (h : normE e = .outOfFuel) : e = .outOfFuel := by
  cases e <;> simp_all [normE, SpecError.rep, SpecError.fail] <;> split at h <;> simp_all

theorem normE_fail (e : SpecError) : (normE e).fail = e.fail := by
  cases e <;> simp [normE, SpecError.rep, SpecError.fail] <;> split <;> simp_all [SpecError.fail]

/-! ## Footprint check -/

def matchesB : List PStep → List Nat → Bool
  | [], [] => true
  | .exact i :: ps, j :: qs => i == j && matchesB ps qs
  | .any :: ps, _ :: qs => matchesB ps qs
  | _, _ => false

def rootIs (ty : Name) : Option DV → Bool
  | some (.cont ty' _) => ty' == ty
  | _ => false

/-- The node at place `(k, p)` is at a footprint path. -/
def fpOk (fp : Footprint) (roots : List DV) (k : Nat) (p : List Nat) : Bool :=
  fp.any fun pat => rootIs pat.ty roots[k]? && matchesB pat.steps p

/-- Child `i` of the node at path `p` is a leaf. -/
def leafAt (d : DV) (p : List Nat) (i : Nat) : Bool :=
  match subAt p d with
  | some n => match n.kids[i]? with
    | some (.leaf _) => true
    | _ => false
  | none => false

/-! ## Expressions -/

variable [LibModel]

-- The SSZ instance of `LibValues` is global. The interpreter takes its value rules from the
-- `LibModel` argument, so the denotation must use the same instance.
attribute [local instance high] LibModel.toLibValues

def dGlobal (env : Env) (x : Name) : DM DRes :=
  match env.globals.lookup x with
  | some (.const v) => if Flat v then .ok (.val v) else none
  | some .configVar =>
    match env.config.lookup x with
    | some v => if Flat v then .ok (.val v) else none
    | none => some (.error .nameError)
  | some _ => none
  | none => some (.error .nameError)

def dAttr (env : Env) (s : DSt) : DRes → Name → DM DRes
  | .place k p, f =>
    match s.deref k p with
    | some (.cont ty ds) =>
      match fieldIndex env ty f with
      | some (i, _) =>
        match ds[i]? with
        | some c => .ok (ofChild k (p ++ [i]) c)
        | none => none
      | none => none
    | _ => none
  | _, _ => none

def isByteList (k : ListKind) (e : SszTy) : Bool := decide (k = .list ∧ e = .uint (.width 8))

def dIndex (s : DSt) : DRes → DRes → DM DRes
  | .place k p, .val iv =>
    match s.deref k p with
    | some (.list kd e _ ds) =>
      if isByteList kd e then none else
      DM.bind (lift (toIndex iv)) fun j =>
        match normIndex ds.length j with
        | some m =>
          match ds[m]? with
          | some c => .ok (ofChild k (p ++ [m]) c)
          | none => none
        | none => some (.error .indexError)
    | _ => none
  | _, _ => none

def dBinop (op : BinOp) : DRes → DRes → DM DRes
  | .val x, .val y => DM.bind (lift (binopVal op x y)) fun v => if Flat v then .ok (.val v) else none
  | _, _ => none

def cmpF (op : CmpOp) (x y : Value) : DM Bool :=
  match op with
  | .is => .ok (isVal x y)
  | .isNot => .ok !(isVal x y)
  | .isIn | .notIn => none
  | .eq => lift (cmpVal .eq x y)
  | .notEq => DM.bind (lift (cmpVal .eq x y)) fun b => .ok !b
  | op => lift (cmpVal op x y)

mutual

def dExpr (env : Env) (s : DSt) : Expr → DM DRes
  | .name _ x =>
    match s.loc x with
    | some r => .ok r
    | none => dGlobal env x
  | .int _ k => .ok (.val (.int k))
  | .bool _ b => .ok (.val (.bool b))
  | .noneLit _ => .ok (.val .none)
  | .attr _ o f => DM.bind (dExpr env s o) fun ro => dAttr env s ro f
  | .index _ o i =>
    DM.bind (dExpr env s o) fun ro => DM.bind (dExpr env s i) fun ri => dIndex s ro ri
  | .binop _ op a b =>
    DM.bind (dExpr env s a) fun ra => DM.bind (dExpr env s b) fun rb => dBinop op ra rb
  | .compare _ a rest =>
    DM.bind (dExpr env s a) fun ra =>
      match ra with
      | .val x => dCmp env s x rest
      | _ => none
  | .boolop _ op es => dBool env s op es
  | _ => none

def dCmp (env : Env) (s : DSt) (x : Value) : List (CmpOp × Expr) → DM DRes
  | [] => .ok (.val (.bool true))
  | (op, e) :: rest =>
    DM.bind (dExpr env s e) fun ry =>
      match ry with
      | .val y => DM.bind (cmpF op x y) fun b => if b then dCmp env s y rest else .ok (.val (.bool false))
      | _ => none

def dBool (env : Env) (s : DSt) (op : BoolOp) : List Expr → DM DRes
  | [] => none
  | e :: es =>
    DM.bind (dExpr env s e) fun r =>
      match r with
      | .val v =>
        if es.isEmpty then .ok (.val v) else
        DM.bind (lift (truthy v)) fun b =>
          match op, b with
          | .or, true => .ok (.val v)
          | .and, false => .ok (.val v)
          | _, _ => dBool env s op es
      | _ => none

end

/-! ## Statements -/

/-- Write the flat value `v` as child `i` of the node at place `(k, p)`. -/
def dWrite (fp : Footprint) (s : DSt) (k : Nat) (p : List Nat) (i : Nat) (v : Value) :
    DM (Outcome × DSt) :=
  match s.roots[k]? with
  | some d =>
    if Flat v && fpOk fp s.roots k p && leafAt d p i then
      .ok (.normal, { s with roots := s.roots.set k (updAt p d i (.leaf v)) })
    else none
  | none => none

/-- The coercion of a written flat value. -/
def dCoerce (env : Env) (field : Bool) (t : SszTy) (v : Value) : DM Value :=
  lift (Prod.fst <$> coerceWith env field Heap.empty t v)

def dAssign (env : Env) (fp : Footprint) (s : DSt) : Target → DRes → DM (Outcome × DSt)
  | .name _ x, r => .ok (.normal, { s with loc := setLoc s.loc x r })
  | .attr _ o f, .val v =>
    DM.bind (dExpr env s o) fun ro =>
      match ro with
      | .place k p =>
        match s.deref k p with
        | some (.cont ty _) =>
          match fieldIndex env ty f with
          | some (i, t) => DM.bind (dCoerce env true t v) fun v' => dWrite fp s k p i v'
          | none => none
        | _ => none
      | _ => none
  | .index _ o ie, .val v =>
    DM.bind (dExpr env s o) fun ro => DM.bind (dExpr env s ie) fun ri =>
      match ro, ri with
      | .place k p, .val iv =>
        match s.deref k p with
        | some (.list kd e _ ds) =>
          if isByteList kd e then none else
          DM.bind (lift (toIndex iv)) fun j =>
          DM.bind (dCoerce env false e v) fun v' =>
            match normIndex ds.length j with
            | some m => dWrite fp s k p m v'
            | none => some (.error .indexError)
        | _ => none
      | _, _ => none
  | _, _ => none

/-- `obj[i] op= e`. -/
def dAugIndex (env : Env) (fp : Footprint) (s : DSt) (o ie : Expr) (op : BinOp) (e : Expr) :
    DM (Outcome × DSt) :=
  DM.bind (dExpr env s o) fun ro => DM.bind (dExpr env s ie) fun ri =>
    match ro, ri with
    | .place k p, .val iv =>
      match s.deref k p with
      | some (.list kd el _ ds) =>
        if isByteList kd el then none else
        DM.bind (lift (toIndex iv)) fun j =>
          match normIndex ds.length j with
          | some m =>
            match ds[m]? with
            | some (.leaf cur) =>
              DM.bind (dExpr env s e) fun re =>
                match re with
                | .val r =>
                  DM.bind (lift (binopVal op cur r)) fun v =>
                    if Flat v then DM.bind (dCoerce env false el v) fun v' => dWrite fp s k p m v'
                    else none
                | _ => none
            | _ => none
          | none => some (.error .indexError)
      | _ => none
    | _, _ => none

mutual

def dStmt (env : Env) (fp : Footprint) (s : DSt) : Stmt → DM (Outcome × DSt)
  | .assign _ [t] e => DM.bind (dExpr env s e) fun r => dAssign env fp s t r
  | .annAssign _ t e => DM.bind (dExpr env s e) fun r => dAssign env fp s t r
  | .augAssign _ (.index _ o ie) op e => dAugIndex env fp s o ie op e
  | .ifStmt _ c thn els =>
    DM.bind (dExpr env s c) fun r =>
      match r with
      | .val v =>
        DM.bind (lift (truthy v)) fun b => if b then dBlock env fp s thn else dBlock env fp s els
      | _ => none
  | .ret _ (some e) =>
    DM.bind (dExpr env s e) fun r =>
      match r with
      | .val v => .ok (.ret v, s)
      | _ => none
  | .ret _ none => .ok (.ret .none, s)
  | .assert _ e =>
    DM.bind (dExpr env s e) fun r =>
      match r with
      | .val v =>
        DM.bind (lift (truthy v)) fun b => if b then .ok (.normal, s) else some (.error .assertionFailed)
      | _ => none
  | .pass _ => .ok (.normal, s)
  | _ => none

def dBlock (env : Env) (fp : Footprint) (s : DSt) : List Stmt → DM (Outcome × DSt)
  | [] => .ok (.normal, s)
  | st :: ss =>
    DM.bind (dStmt env fp s st) fun (o, s1) =>
      match o with
      | .normal => dBlock env fp s1 ss
      | _ => .ok (o, s1)

end

/-! ## Functions -/

/-- The local for argument `i`: its leaf, or the place of its root. -/
def slot (roots : List DV) (i : Nat) : DRes :=
  match roots[i]? with
  | some (.leaf v) => .val v
  | _ => .place i []

/-- The locals after binding the parameters, as `bindArgs.go` binds them. -/
def initLoc (roots : List DV) : (Name → Option DRes) → List (Name × Nat) → (Name → Option DRes)
  | dl, [] => dl
  | dl, (x, i) :: rest => initLoc roots (setLoc dl x (slot roots i)) rest

/-- The denotation of a spec function on the decoded arguments: the return value and the
decoded arguments after the call. -/
def denoteFn (env : Env) (fp : Footprint) (d : FunctionDef) (roots : List DV) :
    DM (Value × List DV) :=
  if d.params.defaults = [] ∧ d.params.vararg = none ∧ d.params.names.length = roots.length then
    let s0 : DSt := { roots, loc := initLoc roots (fun _ => none) d.params.names.zipIdx }
    DM.bind (dBlock env fp s0 d.body) fun (o, s1) =>
      match o with
      | .ret v => .ok (v, s1.roots)
      | _ => .ok (.none, s1.roots)
  else none

/-! ## Fuel bounds -/

mutual

def eDep : Expr → Nat
  | .attr _ o _ => eDep o + 1
  | .index _ o i => max (eDep o) (eDep i) + 1
  | .binop _ _ a b => max (eDep a) (eDep b) + 1
  | .compare _ a rest => max (eDep a) (cDep rest) + 1
  | .boolop _ _ es => lDep es + 1
  | _ => 1

def cDep : List (CmpOp × Expr) → Nat
  | [] => 0
  | (_, e) :: rest => max (eDep e) (cDep rest)

def lDep : List Expr → Nat
  | [] => 0
  | e :: rest => max (eDep e) (lDep rest)

end

def tDep : Target → Nat
  | .attr _ o _ => eDep o + 1
  | .index _ o i => max (eDep o) (eDep i) + 1
  | _ => 1

mutual

def sDep : Stmt → Nat
  | .assign _ [t] e => max (eDep e) (tDep t) + 1
  | .annAssign _ t e => max (eDep e) (tDep t) + 1
  | .augAssign _ t _ e => max (tDep t) (eDep e) + 1
  | .ifStmt _ c thn els => max (eDep c) (max (bDep thn) (bDep els)) + 1
  | .ret _ (some e) => eDep e + 1
  | .assert _ e => eDep e + 1
  | _ => 1

def bDep : List Stmt → Nat
  | [] => 0
  | s :: ss => max (sDep s) (bDep ss)

end

end SpecLean.Layer4
