import SpecLean.Layer4.Denote
import SpecLean.RootKey

/-!
# Layer 4: the denotation with calls, by fuel

`den env fps n` is the denotation at fuel `n`. Each part uses the same fuel as the interpreter
part it stands for: `expr` is `evalExpr n`, `target` is `assignTarget n`, `stmt` is
`execStmt n`, `fn` is `callFn n`. So the proof is one induction on the fuel, and a call is one
more step of it.

A call `g(args)` to a spec function runs the denotation of `g` on the decoded arguments: a
place argument gives its subtree, a value its leaf. `fps g` is the footprint of `g`.

- A call that writes nothing (`fps g = []`) can be anywhere in an expression. The heap does not
  change.
- A call that writes is a statement, or the right side of an assignment. It takes exactly one
  place argument. Its footprint, seen from that place, must lie in the caller's footprint
  (`coversAll`). After the call, the callee's tree of that argument replaces the subtree at the
  place in the caller's tree (a backward function, as in Aeneas).

A call of an SSZ uint or `Boolean` class, such as `Epoch(x)`, on flat values is a value rule.
-/

namespace SpecLean.Layer4

open SpecLean SpecLean.Encode

/-! ## Footprints of a callee, seen from a place of the caller -/

/-- Pattern `ps` is more general than pattern `ps'`, step by step. -/
def genB : List PStep → List PStep → Bool
  | [], [] => true
  | .any :: ps, _ :: ps' => genB ps ps'
  | .exact i :: ps, .exact j :: ps' => i == j && genB ps ps'
  | _, _ => false

/-- Pattern `ps` matches every path `p ++ q` where `q` matches `ps'`. -/
def coversB : List PStep → List Nat → List PStep → Bool
  | ps, [], ps' => genB ps ps'
  | .exact i :: ps, j :: p, ps' => i == j && coversB ps p ps'
  | .any :: ps, _ :: p, ps' => coversB ps p ps'
  | [], _ :: _, _ => false

/-- Every pattern of the callee footprint `fpG` that applies to the argument tree `dk` at place
`(k, p)` lies in the caller footprint `fp`. -/
def coversAll (fp : Footprint) (roots : List DV) (k : Nat) (p : List Nat) (dk : DV)
    (fpG : Footprint) : Bool :=
  fpG.all fun pg => Nat.blt pg.ty listRootBase && (!(rootIs pg.ty (some dk)) ||
    fp.any fun pat => rootIs pat.ty roots[k]? && coversB pat.steps p pg.steps)

/-- Replace the subtree at a path. -/
def setAt : List Nat → DV → DV → DV
  | [], _, x => x
  | j :: p, .cont ty ds, x =>
    .cont ty (match ds[j]? with
      | some c => ds.set j (setAt p c x)
      | none => ds)
  | j :: p, .list k e l ds, x =>
    .list k e l (match ds[j]? with
      | some c => ds.set j (setAt p c x)
      | none => ds)
  | _ :: _, d, _ => d

/-- The argument tree of a call argument. -/
def argRoot (s : DSt) : DRes → Option DV
  | .val v => some (.leaf v)
  | .place k p => s.deref k p
  | .tree d => some d

/-- The one place among the arguments: its position and the place. -/
def onePlace : List DRes → Option (Nat × Nat × List Nat)
  | [] => none
  | .val _ :: rs => (onePlace rs).map fun (i, kp) => (i + 1, kp)
  | .place k p :: rs => if rs.all (fun r => match r with | .val _ => true | _ => false)
      then some (0, k, p) else none
  | .tree _ :: _ => none

/-- An SSZ class whose constructor on flat values needs no heap. -/
def ctorFlat : SszTy → Bool
  | .uint _ | .boolean | .bytes _ _ => true
  | _ => false

def allVals : List DRes → Option (List Value)
  | [] => some []
  | .val v :: rs => (allVals rs).map (v :: ·)
  | _ => none

/-! ## A decoded tree as a heap value -/

mutual
/-- A new heap object for each node of a tree, children first. -/
def encDV : DV → Heap → Value × Heap
  | .leaf v, h => (v, h)
  | .cont ty ds, h =>
    let r := encDVs ds h
    (.ref r.2.next, (r.2.alloc (.container ty r.1)).2)
  | .list k e l ds, h =>
    let r := encDVs ds h
    (.ref r.2.next, (r.2.alloc (.list k e l r.1)).2)
def encDVs : List DV → Heap → List Value × Heap
  | [], h => ([], h)
  | d :: ds, h =>
    let r := encDV d h
    let rs := encDVs ds r.2
    (r.1 :: rs.1, rs.2)
end

/-! ## The parts at one fuel -/

/-- A loop over the list at place `(k, p)`, read live at each item; `enum` for `enumerate`. -/
structure LSrc where
  k : Nat
  p : List Nat
  enum : Bool

/-- How a statement ends. A `return` gives a flat value or the tree of a new object. -/
inductive DOut where
  | normal | brk | cont
  | ret (r : DRes)

/-- `dWrite`, which always ends normally. -/
def dWriteD (fp : Footprint) (s : DSt) (k : Nat) (p : List Nat) (i : Nat) (v : Value) :
    DM (DOut × DSt) :=
  (dWrite fp s k p i v).map (Except.map fun x => (.normal, x.2))

/-- The denotation at one fuel. `fp` is the footprint of the running function. -/
structure Sem where
  expr : Footprint → DSt → Expr → DM DRes
  /-- An expression at statement level: a call may write. The new trees of the arguments. -/
  call : Footprint → DSt → Expr → DM (DRes × List DV)
  target : Footprint → DSt → Target → DRes → DM (DOut × DSt)
  stmt : Footprint → DSt → Stmt → DM (DOut × DSt)
  /-- The body of a spec function, on the decoded arguments. -/
  fn : Footprint → FunctionDef → List DV → DM (DRes × List DV)
  /-- The iterable of a `for` loop: `evalExpr` then `iterSource`. -/
  iter : Footprint → DSt → Expr → DM LSrc
  /-- `execFor`: a loop from item `i`, one fuel unit per item. -/
  loop : Footprint → DSt → Target → LSrc → Nat → List Stmt → DM (DOut × DSt)
  /-- `compItems`: the items of a list comprehension from item `i`, one fuel unit per item. -/
  items : Footprint → DSt → Target → List Expr → Expr → LSrc → Nat → DM (List DV)
  /-- `expr` at the fuel below: the receiver `o` of a method call `o.m(args)`. -/
  sub : Footprint → DSt → Expr → DM DRes
  /-- `execWhile`: a `while` loop, one fuel unit per test. -/
  whl : Footprint → DSt → Expr → List Stmt → DM (DOut × DSt)

def blockOf (stmt : DSt → Stmt → DM (DOut × DSt)) : DSt → List Stmt → DM (DOut × DSt)
  | s, [] => .ok (.normal, s)
  | s, st :: ss =>
    DM.bind (stmt s st) fun (o, s1) =>
      match o with
      | .normal => blockOf stmt s1 ss
      | _ => .ok (o, s1)

def Sem.block (S : Sem) (fp : Footprint) : DSt → List Stmt → DM (DOut × DSt) :=
  blockOf (S.stmt fp)

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

def cmpOf (ev : Expr → DM DRes) (x : Value) : List (CmpOp × Expr) → DM DRes
  | [] => .ok (.val (.bool true))
  | (op, e) :: rest =>
    DM.bind (ev e) fun ry =>
      match ry with
      | .val y => DM.bind (cmpF op x y) fun b => if b then cmpOf ev y rest else .ok (.val (.bool false))
      | _ => none

def boolOf (ev : Expr → DM DRes) (op : BoolOp) : List Expr → DM DRes
  | [] => none
  | e :: es =>
    DM.bind (ev e) fun r =>
      match r with
      | .val v =>
        if es.isEmpty then .ok (.val v) else
        DM.bind (lift (truthy v)) fun b =>
          match op, b with
          | .or, true => .ok (.val v)
          | .and, false => .ok (.val v)
          | _, _ => boolOf ev op es
      | _ => none

/-- An optional slice bound. -/
def optOf (ev : Expr → DM DRes) : Option Expr → DM (Option Value)
  | none => .ok none
  | some e => DM.bind (ev e) fun r =>
    match r with
    | .val v => .ok (some v)
    | _ => none

def argsOf (ev : Expr → DM DRes) : List Arg → DM (List DRes)
  | [] => .ok []
  | .pos e :: as => DM.bind (ev e) fun r => DM.bind (argsOf ev as) fun rs => .ok (r :: rs)
  | _ => none

/-- A call of an SSZ class on flat values. -/
def dCtor (env : Env) (t : SszTy) (rs : List DRes) : DM DRes :=
  if ctorFlat t then
    match allVals rs with
    | some vs =>
      DM.bind (lift (Prod.fst <$> LibModel.construct env Heap.empty t vs [])) fun v =>
        if Flat v then .ok (.val v) else none
    | none => none
  else none

/-- The values of a list of leaves. -/
def leafVals : List DV → Option (List Value)
  | [] => some []
  | .leaf v :: ds => (leafVals ds).map (v :: ·)
  | _ :: _ => none

/-- `sum(xs)` of a list of flat values that is not a byte list. -/
def dSum (kd : ListKind) (el : SszTy) (ds : List DV) : DM DRes :=
  if isByteList kd el then none else
  match leafVals ds with
  | some xs => DM.bind (lift (xs.foldlM (binopVal .add) (.int 0))) fun w => if Flat w then .ok (.val w) else none
  | none => none

/-- `hash_tree_root` of a tree: the oracle on the tree as a new heap value. -/
def dHtr (env : Env) (d : DV) : DM DRes :=
  DM.bind (lift (env.hashTreeRoot (encDV d Heap.empty).2 (encDV d Heap.empty).1)) fun r =>
    .ok (.val (.bytes env.nm.root r))

/-- `min`, `max` of two or more flat values, `len` of a list, `sum` of a list of flat
values, and `hash_tree_root` of an object. -/
def dBuiltin (env : Env) (s : DSt) (b : Builtin) (rs : List DRes) : DM DRes :=
  match b with
  | .min | .max =>
    match allVals rs with
    | some (x :: y :: ys) =>
      DM.bind (lift (pickBest (b == .max) x (y :: ys))) fun w => if Flat w then .ok (.val w) else none
    | _ => none
  | .len =>
    match rs with
    | [.place k p] =>
      match s.deref k p with
      | some (.list _ _ _ ds) => .ok (.val (.int ds.length))
      | _ => none
    | [.tree (.list _ _ _ ds)] => .ok (.val (.int ds.length))
    | _ => none
  | .sum =>
    match rs with
    | [.place k p] =>
      match s.deref k p with
      | some (.list kd el _ ds) => dSum kd el ds
      | _ => none
    | [.tree (.list kd el _ ds)] => dSum kd el ds
    | _ => none
  | .sha256 =>
    match rs with
    | [.val (.bytes _ bs)] => .ok (.val (.bytes env.nm.bytes32 (env.sha256 bs)))
    | _ => none
  | .sszSerialize =>
    match rs with
    | [.val (.uint t n)] => .ok (.val (.bytes env.bytesName (Prim.serializeUint n (t.bits / 8))))
    | _ => none
  | .hashTreeRoot =>
    match rs with
    | [.place k p] =>
      match s.deref k p with
      | some d => dHtr env d
      | none => none
    | [.tree d] => dHtr env d
    | _ => none
  | _ => none

/-- The trees of the arguments of a call that leaves out trailing arguments: `None` for each.
The callee checks that their defaults are `None`. -/
def padNone (d : FunctionDef) (rg : List DV) : Option (List DV) :=
  if rg.length ≤ d.params.names.length ∧ d.params.names.length ≤ rg.length + d.params.defaults.length then
    some (rg ++ List.replicate (d.params.names.length - rg.length) (.leaf .none))
  else none

theorem padNone_full {d : FunctionDef} {rg : List DV} (h : rg.length = d.params.names.length) :
    padNone d rg = some rg := by
  unfold padNone; rw [if_pos (by omega)]; simp [h]

/-- A call that writes nothing. `fn` is the callee body at the fuel of the call. -/
def dCallRO (env : Env) (fps : Name → Footprint)
    (fn : Footprint → FunctionDef → List DV → DM (DRes × List DV)) (s : DSt) (g : Name)
    (rs : List DRes) : DM DRes :=
  match env.globals.lookup g with
  | some (.fn d) =>
    if (fps g).isEmpty then
      match rs.mapM (argRoot s) with
      | some rg =>
        match padNone d rg with
        | some rg' => DM.bind (fn [] d rg') fun (r, _) =>
            match r with
            | .val v => if Flat v then .ok (.val v) else none
            | .tree t => .ok (.tree t)
            | .place _ _ => none
        | none => none
      | none => none
    else none
  | some (.type t) => dCtor env t rs
  | some (.builtin b) => dBuiltin env s b rs
  | _ => none

/-- A call at statement level: it may write through its one place argument. -/
def dCallW (env : Env) (fps : Name → Footprint)
    (fn : Footprint → FunctionDef → List DV → DM (DRes × List DV)) (fp : Footprint) (s : DSt)
    (g : Name) (rs : List DRes) : DM (DRes × List DV) :=
  match env.globals.lookup g with
  | some (.fn d) =>
    if (fps g).isEmpty then
      DM.bind (dCallRO env fps fn s g rs) fun r => .ok (r, s.roots)
    else
      match onePlace rs, rs.mapM (argRoot s) with
      | some (i, k, p), some rg =>
        match s.deref k p, s.roots[k]? with
        | some dk, some dr =>
          if !fp.isEmpty && coversAll fp s.roots k p dk (fps g) then
            DM.bind (fn (fps g) d rg) fun (r, rg') =>
              match r, rg'[i]? with
              | .val v, some di =>
                if Flat v then .ok (.val v, s.roots.set k (setAt p dr di)) else none
              | _, _ => none
          else none
        | _, _ => none
      | _, _ => none
  | _ => dCallRO env fps fn s g rs |>.map (·.map (·, s.roots))

/-- A global that a call can name: a spec function or an SSZ class. -/
def callable (env : Env) (g : Name) : Bool :=
  match env.globals.lookup g with
  | some (.fn _) | some (.type _) => true
  | some (.builtin .min) | some (.builtin .max) | some (.builtin .len) => true
  | some (.builtin .sum) | some (.builtin .hashTreeRoot) | some (.builtin .sha256)
  | some (.builtin .sszSerialize) => true
  | _ => false

/-- Bind the loop target at fuel `n`, as `assignTarget n`. -/
def bindLoop (n : Nat) (enum : Bool) (s : DSt) (t : Target) (i : Nat) (x : DRes) : Option DSt :=
  match enum, t, n with
  | false, .name _ a, _ + 1 => some { s with loc := setLoc s.loc a x }
  | true, .tuple _ [.name _ a, .name _ b], _ + 2 =>
    some { s with loc := setLoc (setLoc s.loc a (.val (.int i))) b x }
  | _, _, _ => none

/-- The conditions of a comprehension item, as `evalIfs`. -/
def ifsOf (ev : Expr → DM DRes) : List Expr → DM Bool
  | [] => .ok true
  | c :: cs =>
    DM.bind (ev c) fun r =>
      match r with
      | .val v => DM.bind (lift (truthy v)) fun b => if b then ifsOf ev cs else .ok false
      | _ => none

/-- `compItems (n + 1)` of a list comprehension with one generator over a list place: item
`i`, its conditions and its flat element at fuel `n`, then the rest at fuel `n`. -/
def itemsStep (n : Nat) (P : Sem) (fp : Footprint) (s : DSt) (t : Target) (ifs : List Expr)
    (elt : Expr) (ls : LSrc) (i : Nat) : DM (List DV) :=
  match s.deref ls.k ls.p with
  | some (.list kd e _ ds) =>
    if isByteList kd e then none else
    match ds[i]? with
    | none => .ok []
    | some c =>
      match bindLoop n ls.enum s t i (ofChild ls.k (ls.p ++ [i]) c) with
      | some s1 =>
        DM.bind (ifsOf (P.expr fp s1) ifs) fun keep =>
          DM.bind (if keep then
              DM.bind (P.expr fp s1 elt) fun r =>
                match r with
                | .val v => if Flat v then .ok [DV.leaf v] else none
                | _ => none
            else .ok []) fun vs1 =>
            DM.bind (P.items fp s1 t ifs elt ls (i + 1)) fun vs2 => .ok (vs1 ++ vs2)
      | none => none
  | _ => none

/-- Every argument is a keyword argument, and there is at least one. -/
def allKw : List Arg → Bool
  | [] => false
  | as => as.all fun a => match a with | .kw _ _ => true | _ => false

@[simp] theorem allKw_nil : allKw [] = false := Eq.trans rfl rfl
@[simp] theorem allKw_pos (e : Expr) (as : List Arg) : allKw (.pos e :: as) = false := Eq.trans rfl rfl
@[simp] theorem allKw_starred (e : Expr) (as : List Arg) : allKw (.starred e :: as) = false :=
  Eq.trans rfl rfl

/-- The keyword arguments, each a flat value, in order. -/
def kwsOf (ev : Expr → DM DRes) : List Arg → DM (List (Name × Value))
  | [] => .ok []
  | .kw k e :: as =>
    DM.bind (ev e) fun r =>
      match r with
      | .val v => DM.bind (kwsOf ev as) fun rest => .ok ((k, v) :: rest)
      | _ => none
  | _ => none

/-- A field type whose values are flat. -/
def flatTy : SszTy → Bool
  | .uint _ | .boolean | .bytes _ _ => true
  | _ => false

/-- The field values of a container from its keyword arguments: every field given, of a flat
type, with a flat value, coerced as a field. -/
def kwFields (kvs : List (Name × Value)) : List (Name × SszTy) → DM (List Value)
  | [] => .ok []
  | (f, ft) :: fs =>
    match kvs.lookup f with
    | some v =>
      if flatTy ft && Flat v then
        DM.bind (lift (coerceField ft v)) fun w =>
          if Flat w then DM.bind (kwFields kvs fs) fun ws => .ok (w :: ws) else none
      else none
    | none => none

/-- `T(f=v, ...)` for a container class `T`: a new container of flat fields. -/
def kwCtor (env : Env) (g : Name) (kvs : List (Name × Value)) : DM DRes :=
  match env.globals.lookup g with
  | some (.type (.container ty)) =>
    match env.containers.lookup ty with
    | some fs =>
      if kvs.all (fun kv => (fs.map (·.1)).contains kv.1) then
        DM.bind (kwFields kvs fs) fun ws => .ok (.tree (.cont ty (ws.map .leaf)))
      else none
    | none => none
  | _ => none

/-- A call expression `g(args)` to a callable global that no local hides. The interpreter looks
the name up before it evaluates the arguments. -/
def callHead (env : Env) (s : DSt) : Expr → Option (Name × List Arg)
  | .call _ (.name _ g) args =>
    if (s.loc g).isNone && callable env g then some (g, args) else none
  | _ => none

/-- `int.from_bytes(args)`: the arguments, when no local hides `int`. -/
def fromBytesOf (env : Env) (s : DSt) : Expr → Option (List Arg)
  | .call _ (.attr _ (.name _ g) f) args =>
    match env.globals.lookup g with
    | some (.builtin .int) => if (s.loc g).isNone && f == env.nm.fromBytes then some args else none
    | _ => none
  | _ => none

/-- `bls.f(args)`: the method and the arguments, when no local hides `bls`. -/
def blsOf (env : Env) (s : DSt) : Expr → Option (Name × List Arg)
  | .call _ (.attr _ (.name _ g) f) args =>
    match env.globals.lookup g with
    | some (.module .bls) => if (s.loc g).isNone then some (f, args) else none
    | _ => none
  | _ => none

/-- A BLS oracle call on flat values. -/
def dBls (env : Env) (f : Name) (rs : List DRes) : DM DRes :=
  match allVals rs with
  | some vs => DM.bind (lift (env.bls f Heap.empty vs)) fun v => if Flat v then .ok (.val v) else none
  | none => none

/-- `int.from_bytes` of flat values. -/
def dFromBytes (env : Env) (rs : List DRes) : DM DRes :=
  match allVals rs with
  | some vs => DM.bind (lift (fromBytes env vs)) fun v => if Flat v then .ok (.val v) else none
  | none => none

def exprStep (env : Env) (fps : Name → Footprint) (n : Nat) (P : Sem) (fp : Footprint)
    (s : DSt) : Expr → DM DRes
  | .name _ x =>
    match s.loc x with
    | some r => .ok r
    | none => dGlobal env x
  | .int _ k => .ok (.val (.int k))
  | .bool _ b => .ok (.val (.bool b))
  | .noneLit _ => .ok (.val .none)
  | .attr _ o f => DM.bind (P.expr fp s o) fun ro => dAttr env s ro f
  | .index _ o i =>
    DM.bind (P.expr fp s o) fun ro => DM.bind (P.expr fp s i) fun ri => dIndex s ro ri
  | .binop _ op a b =>
    DM.bind (P.expr fp s a) fun ra => DM.bind (P.expr fp s b) fun rb => dBinop op ra rb
  | .compare _ a rest =>
    DM.bind (P.expr fp s a) fun ra =>
      match ra with
      | .val x => cmpOf (P.expr fp s) x rest
      | _ => none
  | .boolop _ op es => boolOf (P.expr fp s) op es
  | .unop _ .not a =>
    DM.bind (P.expr fp s a) fun r =>
      match r with
      | .val v => DM.bind (lift (truthy v)) fun b => .ok (.val (.bool !b))
      | _ => none
  | .unop _ op a =>
    DM.bind (P.expr fp s a) fun r =>
      match r with
      | .val v => DM.bind (lift (unopVal op v)) fun w => if Flat w then .ok (.val w) else none
      | _ => none
  | .slice _ o lo hi none =>
    DM.bind (P.expr fp s o) fun ro =>
      match ro with
      | .val (.bytes c bs) =>
        DM.bind (optOf (P.expr fp s) lo) fun lov => DM.bind (optOf (P.expr fp s) hi) fun hiv =>
          DM.bind (lift (getSlice env.bytesName Heap.empty (.bytes c bs) lov hiv)) fun x =>
            if Flat x.1 then .ok (.val x.1) else none
      | _ => none
  | .ifExp _ c a b =>
    DM.bind (P.expr fp s c) fun rc =>
      match rc with
      | .val v => DM.bind (lift (truthy v)) fun t => if t then P.expr fp s a else P.expr fp s b
      | _ => none
  | .comp _ .list elt [.mk t it ifs] =>
    DM.bind (P.iter fp s it) fun ls =>
      DM.bind (P.items fp s t ifs elt ls 0) fun ds => .ok (.tree (.list .pyList .any none ds))
  | e@(.call _ _ _) =>
    match n, callHead env s e with
    | _ + 1, some (g, args) =>
      if allKw args then DM.bind (kwsOf (P.expr fp s) args) fun kvs => kwCtor env g kvs
      else DM.bind (argsOf (P.expr fp s) args) fun rs => dCallRO env fps P.fn s g rs
    | _ + 2, none =>
      match fromBytesOf env s e with
      | some args => DM.bind (argsOf (P.expr fp s) args) fun rs => dFromBytes env rs
      | none =>
        match blsOf env s e with
        | some (f, args) => DM.bind (argsOf (P.expr fp s) args) fun rs => dBls env f rs
        | none => none
    | _, _ => none
  | _ => none

/-- `o.append(a)`: the receiver and the argument. -/
def appendOf (env : Env) : Expr → Option (Expr × Expr)
  | .call _ (.attr _ o m) [.pos a] => if m = env.nm.append then some (o, a) else none
  | _ => none

/-- An SSZ list that takes `append` with the item rules of the core: a `List` or a
`ProgressiveList`, not a byte list. -/
def appendable (k : ListKind) (e : SszTy) : Bool :=
  decide ((k = .list ∨ k = .progressiveList) ∧ e ≠ .any ∧ ¬ (k = .list ∧ e = .uint (.width 8)))

/-- The tree of an appended item: a flat value, coerced as an item, or a new container from
keyword arguments. -/
def appendItemD (env : Env) (s : DSt) (el : SszTy) (a : Expr) : DRes → DM DV
  | .val v => DM.bind (dCoerce env false el v) fun v' => if Flat v' then .ok (.leaf v') else none
  | .tree (.cont ty ds) =>
    match callHead env s a, el with
    | some (_, cargs), .container ty' => if allKw cargs && ty' == ty then .ok (.cont ty ds) else none
    | _, _ => none
  | _ => none

/-- `o.append(a)` at fuel `n + 1`: the list at a place in the footprint gains an item at its end. -/
def appendStep (env : Env) (n : Nat) (P : Sem) (fp : Footprint) (s : DSt) (o a : Expr) :
    DM (DRes × List DV) :=
  match n with
  | 0 => none
  | _ + 1 =>
    DM.bind (P.sub fp s o) fun ro =>
      match ro with
      | .place k p =>
        match s.deref k p, s.roots[k]? with
        | some (.list kd el l ds), some dk =>
          if appendable kd el && fpOk fp s.roots k p then
            DM.bind (P.expr fp s a) fun ra =>
              DM.bind (appendItemD env s el a ra) fun d =>
                DM.bind (lift (Ssz.checkLength kd l (ds.length + 1))) fun _ =>
                  .ok (.val .none, s.roots.set k (setAt p dk (.list kd el l (ds ++ [d]))))
          else none
        | _, _ => none
      | _ => none

def callStep (env : Env) (fps : Name → Footprint) (n : Nat) (P : Sem) (fp : Footprint)
    (s : DSt) (e : Expr) : DM (DRes × List DV) :=
  match appendOf env e with
  | some (o, a) => appendStep env n P fp s o a
  | none =>
  match n, callHead env s e with
  | _ + 1, some (g, args) =>
    if allKw args then
      DM.bind (DM.bind (kwsOf (P.expr fp s) args) fun kvs => kwCtor env g kvs) fun r => .ok (r, s.roots)
    else DM.bind (argsOf (P.expr fp s) args) fun rs => dCallW env fps P.fn fp s g rs
  | _, _ => (exprStep env fps n P fp s e).map (·.map (·, s.roots))

def targetStep (env : Env) (P : Sem) (fp : Footprint) (s : DSt) :
    Target → DRes → DM (DOut × DSt)
  | .name _ x, r => .ok (.normal, { s with loc := setLoc s.loc x r })
  | .attr _ o f, .val v =>
    DM.bind (P.expr fp s o) fun ro =>
      match ro with
      | .place k p =>
        match s.deref k p with
        | some (.cont ty _) =>
          match fieldIndex env ty f with
          | some (i, t) => DM.bind (dCoerce env true t v) fun v' => dWriteD fp s k p i v'
          | none => none
        | _ => none
      | _ => none
  | .index _ o ie, .val v =>
    DM.bind (P.expr fp s o) fun ro => DM.bind (P.expr fp s ie) fun ri =>
      match ro, ri with
      | .place k p, .val iv =>
        match s.deref k p with
        | some (.list kd e _ ds) =>
          if isByteList kd e then none else
          DM.bind (lift (toIndex iv)) fun j =>
          DM.bind (dCoerce env false e v) fun v' =>
            match normIndex ds.length j with
            | some m => dWriteD fp s k p m v'
            | none => some (.error .indexError)
        | _ => none
      | _, _ => none
  | _, _ => none

/-- The list at a place, with items that are not bytes. -/
def listPlace (s : DSt) (k : Nat) (p : List Nat) : Bool :=
  match s.deref k p with
  | some (.list kd e _ _) => !isByteList kd e
  | _ => false

def isEnumerate (env : Env) (g : Name) : Bool :=
  match env.globals.lookup g with
  | some (.builtin .enumerate) => true
  | _ => false

/-- The iterable of a loop at fuel `n + 1`: a list at a place, or `enumerate` of one. -/
def iterStep (env : Env) (fps : Name → Footprint) (n : Nat) (P : Sem) (fp : Footprint)
    (s : DSt) : Expr → DM LSrc
  | .call _ (.name _ g) [.pos e] =>
    match n with
    | 0 => none
    | _ + 1 =>
      if (s.loc g).isNone && isEnumerate env g then
        DM.bind (P.expr fp s e) fun r =>
          match r with
          | .place k p => if listPlace s k p then .ok ⟨k, p, true⟩ else none
          | _ => none
      else none
  | e =>
    DM.bind (exprStep env fps n P fp s e) fun r =>
      match r with
      | .place k p => if listPlace s k p then .ok ⟨k, p, false⟩ else none
      | _ => none

/-- `execFor (n + 1)`: item `i`, the body at fuel `n`, then the rest at fuel `n`. -/
def loopStep (n : Nat) (P : Sem) (fp : Footprint) (s : DSt) (t : Target) (ls : LSrc) (i : Nat)
    (body : List Stmt) : DM (DOut × DSt) :=
  match s.deref ls.k ls.p with
  | some (.list kd e _ ds) =>
    if isByteList kd e then none else
    match ds[i]? with
    | none => .ok (.normal, s)
    | some c =>
      match bindLoop n ls.enum s t i (ofChild ls.k (ls.p ++ [i]) c) with
      | some s1 =>
        DM.bind (P.block fp s1 body) fun (o, s2) =>
          match o with
          | .brk => .ok (.normal, s2)
          | .ret v => .ok (.ret v, s2)
          | _ => P.loop fp s2 t ls (i + 1) body
      | none => none
  | _ => none

/-- `execWhile (n + 1)`: the test and the body at fuel `n`, then the loop again at fuel `n`. -/
def whileStep (P : Sem) (fp : Footprint) (s : DSt) (c : Expr) (body : List Stmt) : DM (DOut × DSt) :=
  DM.bind (P.expr fp s c) fun r =>
    match r with
    | .val v =>
      DM.bind (lift (truthy v)) fun b =>
        if b then
          DM.bind (P.block fp s body) fun (o, s1) =>
            match o with
            | .brk => .ok (.normal, s1)
            | .ret v => .ok (.ret v, s1)
            | _ => P.whl fp s1 c body
        else .ok (.normal, s)
    | _ => none

/-- `x op= e` for a local `x` that holds a flat value: `x = x op e`. -/
def augName (P : Sem) (fp : Footprint) (s : DSt) (x : Name) (op : BinOp) (e : Expr) :
    DM (DOut × DSt) :=
  match s.loc x with
  | some (.val cur) =>
    DM.bind (P.expr fp s e) fun r =>
      match r with
      | .val rv =>
        DM.bind (lift (binopVal op cur rv)) fun v =>
          if Flat v then .ok (.normal, { s with loc := setLoc s.loc x (.val v) }) else none
      | _ => none
  | _ => none

/-- `obj[i] op= e`, with the parts at the fuel below. -/
def augStep (env : Env) (P : Sem) (fp : Footprint) (s : DSt) (o ie : Expr) (op : BinOp)
    (e : Expr) : DM (DOut × DSt) :=
  DM.bind (P.expr fp s o) fun ro => DM.bind (P.expr fp s ie) fun ri =>
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
              DM.bind (P.expr fp s e) fun re =>
                match re with
                | .val r =>
                  DM.bind (lift (binopVal op cur r)) fun v =>
                    if Flat v then DM.bind (dCoerce env false el v) fun v' => dWriteD fp s k p m v'
                    else none
                | _ => none
            | _ => none
          | none => some (.error .indexError)
      | _ => none
    | _, _ => none

def stmtStep (env : Env) (P : Sem) (fp : Footprint) (s : DSt) : Stmt → DM (DOut × DSt)
  | .assign _ [t] e =>
    DM.bind (P.call fp s e) fun (r, rs) => P.target fp { s with roots := rs } t r
  | .annAssign _ t e =>
    DM.bind (P.call fp s e) fun (r, rs) => P.target fp { s with roots := rs } t r
  | .augAssign _ (.name _ x) op e => augName P fp s x op e
  | .augAssign _ (.index _ o ie) op e => augStep env P fp s o ie op e
  | .exprStmt _ e => DM.bind (P.call fp s e) fun (_, rs) => .ok (.normal, { s with roots := rs })
  | .ifStmt _ c thn els =>
    DM.bind (P.expr fp s c) fun r =>
      match r with
      | .val v =>
        DM.bind (lift (truthy v)) fun b => if b then P.block fp s thn else P.block fp s els
      | _ => none
  | .ret _ (some e) =>
    DM.bind (P.expr fp s e) fun r =>
      match r with
      | .val v => .ok (.ret (.val v), s)
      | .tree d => .ok (.ret (.tree d), s)
      | .place _ _ => none
  | .ret _ none => .ok (.ret (.val .none), s)
  | .assert _ e =>
    DM.bind (P.expr fp s e) fun r =>
      match r with
      | .val v =>
        DM.bind (lift (truthy v)) fun b => if b then .ok (.normal, s) else some (.error .assertionFailed)
      | _ => none
  | .pass _ => .ok (.normal, s)
  | .forStmt _ t it body => DM.bind (P.iter fp s it) fun ls => P.loop fp s t ls 0 body
  | .whileStmt _ c body => P.whl fp s c body
  | _ => none

def isNoneLit : Expr → Bool
  | .noneLit _ => true
  | _ => false

/-- Defaults that are all `None`, in a function with a body: given every argument, a call does
not use them. -/
def noneDefaults (d : FunctionDef) : Bool :=
  d.params.defaults.isEmpty || (d.params.defaults.all isNoneLit && !d.body.isEmpty)

/-- `callFn (n + 1)`: bind the parameters, run the body at fuel `n`. -/
def fnStep (P : Sem) (fp : Footprint) (d : FunctionDef) (roots : List DV) :
    DM (DRes × List DV) :=
  if noneDefaults d = true ∧ d.params.vararg = none ∧ d.params.names.length = roots.length then
    let s0 : DSt := { roots, loc := initLoc roots (fun _ => none) d.params.names.zipIdx }
    DM.bind (P.block fp s0 d.body) fun (o, s1) =>
      match o with
      | .ret r => .ok (r, s1.roots)
      | _ => .ok (.val .none, s1.roots)
  else none

/-- The denotation at fuel `n`. -/
def den (env : Env) (fps : Name → Footprint) : Nat → Sem
  | 0 => { expr := fun _ _ _ => none, call := fun _ _ _ => none, target := fun _ _ _ _ => none,
           stmt := fun _ _ _ => none, fn := fun _ _ _ => none, iter := fun _ _ _ => none,
           items := fun _ _ _ _ _ _ _ => none,
           loop := fun _ _ _ _ _ _ => none, sub := fun _ _ _ => none, whl := fun _ _ _ _ => none }
  | n + 1 =>
    let P := den env fps n
    { expr := exprStep env fps n P
      call := callStep env fps n P
      target := targetStep env P
      stmt := stmtStep env P
      fn := fnStep P
      iter := iterStep env fps n P
      loop := loopStep n P
      items := itemsStep n P
      sub := P.expr
      whl := whileStep P }

/-! Each part one fuel up, without unfolding the others. -/

@[simp] theorem den_expr (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).expr = exprStep env fps n (den env fps n) := rfl
@[simp] theorem den_call (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).call = callStep env fps n (den env fps n) := rfl
@[simp] theorem den_target (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).target = targetStep env (den env fps n) := rfl
@[simp] theorem den_stmt (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).stmt = stmtStep env (den env fps n) := rfl
@[simp] theorem den_fn (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).fn = fnStep (den env fps n) := rfl
@[simp] theorem den_iter (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).iter = iterStep env fps n (den env fps n) := rfl
@[simp] theorem den_loop (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).loop = loopStep n (den env fps n) := rfl
@[simp] theorem den_items (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).items = itemsStep n (den env fps n) := rfl
@[simp] theorem den_sub (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).sub = (den env fps n).expr := rfl
@[simp] theorem den_whl (env : Env) (fps : Name → Footprint) (n : Nat) :
    (den env fps (n + 1)).whl = whileStep (den env fps n) := rfl

end SpecLean.Layer4
