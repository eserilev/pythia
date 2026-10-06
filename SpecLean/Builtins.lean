import SpecLean.Lib
import SpecLean.Prim

/-!
# Heap access, coercion, builtins and methods

Everything the interpreter does on values and the heap that does not run spec code. The
functions that call back into spec code (`filter`, `sorted` with `key`, closures) are in
`Interp.lean`.

Deep operations (equality, copy, defaults) recurse on the heap structure. `depthBound` bounds
the depth. SSZ types nest only a few levels.
-/

namespace SpecLean

variable [LibModel]

def depthBound : Nat := 64

def fieldIndex (env : Env) (ty : Name) (f : Name) : Option (Nat × SszTy) :=
  match env.containers.lookup ty with
  | some fs =>
    let i := fs.findIdx (fun p => p.1 == f)
    match fs[i]? with
    | some (_, t) => some (i, t)
    | none => none
  | none => none

def enumerateValues (xs : List Value) : List Value :=
  (xs.zipIdx).map fun (x, i) => .tuple [.int (i : Int), x]

/-! ## Byte lists

A `ByteList` is a heap list of kind `list` with `Uint8` elements, so `hash_tree_root` and the
readable Lean see a `List[uint8, N]`. In Python it holds a `bytearray`: an element read gives an
`int`, and a slice gives `bytes` (probed). The serializer allows no other list of `Uint8`. -/

/-- A byte list element as Python reads it. -/
def byteInt : Value → Value
  | .lib (.uint _ n) => .int n
  | v => v

def byteU8 : Value → UInt8
  | .lib (.uint _ n) => UInt8.ofNat n
  | _ => 0

/-- A byte written into a byte list: a value with `__index__` in `range(256)`, else
`ValueError`. A value with no `__index__` raises `TypeError` (probed). -/
def coerceByte : Value → Res Value
  | .int n => if 0 ≤ n ∧ n < 256 then .ok (.lib (.uint (.width 8) n.toNat)) else .error .valueError
  | .lib (.uint _ n) => if n < 256 then .ok (.lib (.uint (.width 8) n)) else .error .valueError
  | .bool b | .lib (.boolean b) => .ok (.lib (.uint (.width 8) (if b then 1 else 0)))
  | _ => .error .typeError

/-! ## Iteration -/

/-- The elements of an iterable that is not a lazy view, as a snapshot. -/
def iterBase (h : Heap) : Value → Res (List Value)
  | .ref a =>
    match h.objs a with
    | some (.list .list (.uint (.width 8)) _ xs) => .ok (xs.map byteInt)
    | some (.list _ _ _ xs) => .ok xs
    | some (.set xs) => .ok xs
    | some (.dict es) => .ok (es.map (·.1))
    | _ => .error .typeError
  | .tuple xs => .ok xs
  | .bytes _ b => .ok (b.map fun x => .int x.toNat)
  | .frozenDict kvs => .ok (kvs.map (·.1))
  | _ => .error .typeError

/-- `zip` of snapshots. `strict` raises `ValueError` on different lengths. -/
def zipLists (strict : Bool) : List (List Value) → Res (List Value)
  | [] => .ok []
  | ls =>
    let n := (ls.map List.length).foldl min (ls.headD []).length
    if strict && ls.any (·.length != n) then .error .valueError
    else .ok ((List.range n).map fun i => .tuple (ls.map fun l => l.getD i .none))

/-- The elements of any iterable, as a snapshot. -/
def iterElems (h : Heap) : Value → Res (List Value)
  | .enumView v => enumerateValues <$> iterBase h v
  | .zipView vs strict => do zipLists strict (← vs.mapM (iterBase h))
  | v => iterBase h v

/-- What a `for` loop iterates over. A list is read live through its address. -/
inductive Seq where
  | live (a : Nat)
  | snap (xs : List Value)

/-- A `for` loop source. The loop evaluates the iterable once, keeps this, and reads the length
of each live list again at each step (SPEC 7.4). -/
inductive IterSrc where
  | seq (s : Seq)
  | enum (s : Seq)
  | zip (ss : List Seq) (strict : Bool)

def toSeq (h : Heap) : Value → Res Seq
  | .ref a =>
    match h.objs a with
    -- A byte list iterates over a snapshot of its data (probed).
    | some (.list .list (.uint (.width 8)) _ xs) => .ok (.snap (xs.map byteInt))
    | some (.list _ _ _ _) => .ok (.live a)
    | _ => .snap <$> iterBase h (.ref a)
  | v => .snap <$> iterBase h v

def iterSource (h : Heap) : Value → Res IterSrc
  | .enumView v => .enum <$> toSeq h v
  | .zipView vs strict => do pure (.zip (← vs.mapM (toSeq h)) strict)
  | v => .seq <$> toSeq h v

def seqItem (h : Heap) : Seq → Nat → Res (Option Value)
  | .live a, i =>
    match h.objs a with
    | some (.list .list (.uint (.width 8)) _ xs) => .ok (xs[i]?.map byteInt)
    | some (.list _ _ _ xs) => .ok xs[i]?
    | _ => .error .typeError
  | .snap xs, i => .ok xs[i]?

def enumItem (i : Nat) (x : Value) : Value := .tuple [.int (i : Int), x]

/-- Item `i` of a loop, or `none` at the end. -/
def iterItem (h : Heap) : IterSrc → Nat → Res (Option Value)
  | .seq s, i => seqItem h s i
  | .enum s, i => do pure ((← seqItem h s i).map (enumItem i))
  | .zip ss strict, i => do
    let items ← ss.mapM (seqItem h · i)
    if items.all Option.isSome then pure (some (.tuple (items.map (·.getD .none))))
    else if strict && items.any Option.isSome then .error .valueError
    else pure none

/-! ## Equality, membership and truth -/

/-- The number in an `int`, a uint or a `bool`. -/
def numOf (v : Value) : Option Int :=
  match LibValues.index v with
  | some (.ok n) => some n
  | _ =>
    match v with
    | .int n => some n
    | .bool b => some (if b then 1 else 0)
    | _ => none

mutual

/-- Python `==`. Two heap objects compare by contents. A byte list equals only a byte list of
a related class. Against anything else it raises `TypeError`, except on the right of an SSZ
object, whose `==` gives `False` first (probed). -/
def deepEq : Nat → Heap → Value → Value → Res Bool
  | 0, _, _, _ => .error .unsupported
  | d + 1, h, .ref a, .ref b =>
    if a = b then .ok true else
    match h.objs a, h.objs b with
    | some (.list .list (.uint (.width 8)) l xs), some (.list .list (.uint (.width 8)) l' ys) =>
      if l = l' then eqLists d h xs ys else .error .typeError
    | some (.list .list (.uint (.width 8)) _ _), _ => .error .typeError
    | some (.container _ _), some (.list .list (.uint (.width 8)) _ _) => .ok false
    | some (.list .pyList _ _ _), some (.list .list (.uint (.width 8)) _ _) => .error .typeError
    | some (.list _ _ _ _), some (.list .list (.uint (.width 8)) _ _) => .ok false
    | _, some (.list .list (.uint (.width 8)) _ _) => .error .typeError
    | some (.container t fs), some (.container t' gs) =>
      if t = t' then eqLists d h fs gs else .ok false
    | some (.list _ _ _ xs), some (.list _ _ _ ys) => eqLists d h xs ys
    | _, _ => .ok false
  | d + 1, h, .tuple xs, .tuple ys => eqLists d h xs ys
  | _ + 1, h, .ref a, _ | _ + 1, h, _, .ref a =>
    match h.objs a with
    | some (.list .list (.uint (.width 8)) _ _) => .error .typeError
    | _ => .ok false
  | _ + 1, _, a, b => cmpVal .eq a b

def eqLists : Nat → Heap → List Value → List Value → Res Bool
  | _, _, [], [] => .ok true
  | d, h, x :: xs, y :: ys => do
    if ← deepEq d h x y then eqLists d h xs ys else pure false
  | _, _, _, _ => .ok false

end

/-- Dict and set lookup: Python compares only values with equal hashes. For numbers, equal
hashes mean equal numbers, and then `==` can raise `TypeError` for sibling uint classes. -/
def keyMatch (h : Heap) (a b : Value) : Res Bool :=
  match numOf a, numOf b with
  | some x, some y => if x = y then deepEq depthBound h a b else .ok false
  | _, _ => deepEq depthBound h a b

def findKey (h : Heap) (k : Value) : List Value → Res (Option Nat)
  | [] => .ok none
  | x :: xs => do
    if ← keyMatch h k x then pure (some 0) else
    pure ((← findKey h k xs).map (· + 1))

/-- `x in c`. A list and a tuple use `==`. A set and a dict use the hash rule. -/
def memberOf (h : Heap) (x c : Value) : Res Bool := do
  match c with
  | .ref a =>
    match h.objs a with
    | some (.set xs) => pure (← findKey h x xs).isSome
    | some (.dict es) => pure (← findKey h x (es.map (·.1))).isSome
    | _ => listIn (← iterBase h c)
  | .frozenDict kvs => pure (← findKey h x (kvs.map (·.1))).isSome
  | .bytes _ _ => .error .unsupported
  | _ => listIn (← iterBase h c)
where
  listIn : List Value → Res Bool
    | [] => .ok false
    | y :: ys => do if ← deepEq depthBound h x y then pure true else listIn ys

/-- A comparison: `is`, `in`, `==` by contents, or an order (`cmpVal`). -/
def compareOp (h : Heap) (op : CmpOp) (x y : Value) : Res Bool :=
  match op with
  | .is => .ok (isVal x y)
  | .isNot => .ok !(isVal x y)
  | .isIn => memberOf h x y
  | .notIn => (!·) <$> memberOf h x y
  | .eq => deepEq depthBound h x y
  | .notEq => (!·) <$> deepEq depthBound h x y
  | _ => cmpVal op x y

/-- Python truth value. -/
def truthyH (h : Heap) : Value → Res Bool
  | .ref a =>
    match h.objs a with
    | some (.list _ _ _ xs) => .ok !xs.isEmpty
    | some (.set xs) => .ok !xs.isEmpty
    | some (.dict es) => .ok !es.isEmpty
    | some _ => .ok true
    | none => .error .unsupported
  | .frozenDict kvs => .ok !kvs.isEmpty
  | v => truthy v

/-! ## Copy, defaults and coercion -/

mutual

/-- `.copy()`: a deep copy. The copy shares no object with the original. -/
def deepCopy : Nat → Heap → Value → Res (Value × Heap)
  | 0, _, _ => .error .unsupported
  | d + 1, h, .ref a =>
    match h.objs a with
    | some (.container t fs) => do
      let (fs', h1) ← copyList d h fs
      let (b, h2) := h1.alloc (.container t fs')
      pure (.ref b, h2)
    | some (.list k e l xs) => do
      let (xs', h1) ← copyList d h xs
      let (b, h2) := h1.alloc (.list k e l xs')
      pure (.ref b, h2)
    | _ => .error .unsupported
  | _ + 1, h, v => .ok (v, h)

def copyList : Nat → Heap → List Value → Res (List Value × Heap)
  | _, h, [] => .ok ([], h)
  | d, h, x :: xs => do
    let (y, h1) ← deepCopy d h x
    let (ys, h2) ← copyList d h1 xs
    pure (y :: ys, h2)

end

/-! ## Reads and writes -/

/-- `x.bit_length` of a number, bound to it as an `int`. Any other attribute of a number
raises `AttributeError` (probed). -/
def bitLengthAttr (env : Env) (n : Int) (f : Name) : Res Value :=
  if f = env.nm.bitLength then .ok (.member (.int n) f) else .error (.other "AttributeError")

/-- `obj.f`. A container field, a `config` value, a member of a fork module, or else a method
or member, bound for a later call. -/
def getAttr (env : Env) (h : Heap) : Value → Name → Res Value
  | .ref a, f =>
    match h.objs a with
    | some (.container ty fs) =>
      match fieldIndex env ty f with
      | some (i, _) =>
        match fs[i]? with
        | some v => .ok v
        | none => .error .unsupported
      | none => .ok (.member (.ref a) f)
    | some _ => .ok (.member (.ref a) f)
    | none => .error .unsupported
  | .glob g, f =>
    match env.globals.lookup g with
    | some (.module .config) =>
      match env.config.lookup f with
      | some v => .ok v
      | none => .error .nameError
    | some (.module .fork) => .ok (.glob f)
    | _ => .ok (.member (.glob g) f)
  -- A number has one attribute that spec code reads, `bit_length` (probed).
  | .int n, f => bitLengthAttr env n f
  | .bool b, f => bitLengthAttr env (if b then 1 else 0) f
  | .lib (.uint _ n), f => bitLengthAttr env n f
  | .lib (.boolean b), f => bitLengthAttr env (if b then 1 else 0) f
  -- A byte string has no attribute that spec code writes. Its methods stay readable.
  | .bytes ty b, f =>
    if f = env.nm.copy ∨ f = env.nm.hashTreeRoot then .ok (.member (.bytes ty b) f)
    else .error (.other "AttributeError")
  | v, f => .ok (.member v f)

def lookupPairs (h : Heap) (k : Value) (kvs : List (Value × Value)) : Res Value := do
  match ← findKey h k (kvs.map (·.1)) with
  | some i =>
    match kvs[i]? with
    | some (_, v) => pure v
    | none => .error .keyError
  | none => .error .keyError

def getItem (h : Heap) : Value → Value → Res Value
  | .ref a, iv =>
    match h.objs a with
    | some (.list .list (.uint (.width 8)) _ xs) => do
      let i ← toIndex iv
      match normIndex xs.length i with
      | some k =>
        match xs[k]? with
        | some v => .ok (byteInt v)
        | none => .error .indexError
      | none => .error .indexError
    | some (.list _ _ _ xs) => do
      let i ← toIndex iv
      match normIndex xs.length i with
      | some k =>
        match xs[k]? with
        | some v => .ok v
        | none => .error .indexError
      | none => .error .indexError
    | some (.dict es) => lookupPairs h iv es
    | _ => .error .typeError
  | .bytes _ bs, iv => do
    let i ← toIndex iv
    match normIndex bs.length i with
    | some k =>
      match bs[k]? with
      | some b => .ok (.int b.toNat)
      | none => .error .indexError
    | none => .error .indexError
  | .tuple xs, iv => do
    let i ← toIndex iv
    match normIndex xs.length i with
    | some k =>
      match xs[k]? with
      | some v => .ok v
      | none => .error .indexError
    | none => .error .indexError
  | .frozenDict kvs, k => lookupPairs h k kvs
  | _, _ => .error .typeError

def sliceRange (len : Nat) (lo hi : Option Value) : Res (Nat × Nat) := do
  let lo' ← match lo with
    | some v => (sliceBound len ·) <$> toIndex v
    | none => pure 0
  let hi' ← match hi with
    | some v => (sliceBound len ·) <$> toIndex v
    | none => pure len
  pure (lo', hi')

/-- `obj[lo:hi]`. A byte string and a byte list give Python `bytes`. A `List` gives the same SSZ
type. A `Vector`, a `Bitvector` or a Python list gives a Python list (probed). -/
def getSlice (bytesName : Name) (h : Heap) : Value → Option Value → Option Value →
    Res (Value × Heap)
  | .bytes _ bs, lo, hi => do
    let (a, b) ← sliceRange bs.length lo hi
    pure (.bytes bytesName (bs.extract a b), h)
  | .tuple xs, lo, hi => do
    let (a, b) ← sliceRange xs.length lo hi
    pure (.tuple (xs.extract a b), h)
  | .ref r, lo, hi =>
    match h.objs r with
    | some (.list .list (.uint (.width 8)) _ xs) => do
      let (a, b) ← sliceRange xs.length lo hi
      pure (.bytes bytesName ((xs.extract a b).map byteU8), h)
    | some (.list k e l xs) => do
      let (a, b) ← sliceRange xs.length lo hi
      let ys := xs.extract a b
      match k with
      | .list | .progressiveList | .bitlist | .progressiveBitlist =>
        let (c, h1) := h.alloc (.list k e l ys)
        pure (.ref c, h1)
      | _ =>
        let (c, h1) := h.alloc (.list .pyList .any none ys)
        pure (.ref c, h1)
    | _ => .error .typeError
  | _, _, _ => .error .typeError

/-- `obj[i] = v`. The element is coerced before the index is checked, as in
`_SSZSequence.__setitem__` and `bytearray`. -/
def setItem (env : Env) (h : Heap) : Value → Value → Value → Res Heap
  | .ref a, iv, v =>
    match h.objs a with
    | some (.list kind elem limit xs) => do
      let i ← toIndex iv
      let (v', h1) ← if kind = .list ∧ elem = .uint (.width 8) then (·, h) <$> coerceByte v
        else coerceWith env false h elem v
      match normIndex xs.length i with
      | some k => .ok (h1.set a (.list kind elem limit (xs.set k v')))
      | none => .error .indexError
    | some (.dict es) => do
      match ← findKey h iv (es.map (·.1)) with
      | some k => .ok (h.set a (.dict (es.set k (iv, v))))
      | none => .ok (h.set a (.dict (es ++ [(iv, v)])))
    | _ => .error .typeError
  | _, _, _ => .error .typeError

/-- `obj[lo:hi] = values`, step 1. The library handles its own lists. -/
def setSlice (env : Env) (h : Heap) (obj : Value) (lo hi : Option Value) (vals : Value) :
    Res Heap :=
  match obj with
  | .ref a =>
    match h.objs a with
    | some (.list kind elem limit xs) => do
      let (lo', hi') ← sliceRange xs.length lo hi
      let ins ← iterElems h vals
      match LibModel.setSlice env h a lo' hi' ins with
      | some r => r
      | none => .ok (h.set a (.list kind elem limit (xs.take lo' ++ ins ++ xs.drop (max lo' hi'))))
    | _ => .error .typeError
  | _ => .error .typeError

/-- `obj.f = v`. -/
def setAttr (env : Env) (h : Heap) : Value → Name → Value → Res Heap
  | .ref a, f, v =>
    match h.objs a with
    | some (.container ty fs) =>
      match fieldIndex env ty f with
      | some (i, t) => do
        let (v', h1) ← coerceWith env true h t v
        .ok (h1.set a (.container ty (fs.set i v')))
      | none => .error .unsupported
    | _ => .error .unsupported
  | _, _, _ => .error .unsupported

/-! ## Builtins that do not call spec code -/

/-- Stable sort of `(key, item)` pairs by key: the primitive with Python's `<`. -/
def stableSort (rev : Bool) (ps : List (Value × Value)) : Res (List Value) :=
  Prim.sortBy (cmpVal .lt) rev ps

/-- `min` and `max` keep the first of equal items. This is `Prim.pick` with Python's order
(`pickBest_eq_prim`), written out because the proofs unfold it. -/
def pickBest (isMax : Bool) : Value → List Value → Res Value
  | best, [] => .ok best
  | best, x :: xs => do
    let better ← if isMax then cmpVal .gt x best else cmpVal .lt x best
    pickBest isMax (if better then x else best) xs

theorem pickBest_eq_prim (isMax : Bool) : ∀ (best : Value) (xs : List Value),
    pickBest isMax best xs =
      Prim.pick (fun x b => if isMax then cmpVal .gt x b else cmpVal .lt x b) best xs
  | _, [] => rfl
  | best, x :: xs => by
    have ih := fun b => pickBest_eq_prim isMax b xs
    cases isMax
    · simp only [pickBest, Prim.pick, Bool.false_eq_true, ↓reduceIte]
      cases cmpVal .lt x best with
      | error => rfl
      | ok b => exact ih _
    · simp only [pickBest, Prim.pick, ↓reduceIte]
      cases cmpVal .gt x best with
      | error => rfl
      | ok b => exact ih _

def leBytes (n width : Nat) : List UInt8 := Prim.serializeUint n width

def kwArg (kws : List (Name × Value)) (k : Name) : Option Value := kws.lookup k

def isPyList (h : Heap) (a : Nat) : Bool :=
  match h.objs a with
  | some (.list .pyList _ _ _) => true
  | _ => false

def allocPyList (h : Heap) (xs : List Value) : Value × Heap :=
  let (a, h1) := h.alloc (.list .pyList .any none xs)
  (.ref a, h1)

/-- `x + y` and `x * n` where an operand is a heap object. `none` when neither operand is. The
library handles its own lists. A Python list concatenates with a Python list, and repeats.
Every other pair raises `TypeError`. -/
def seqBinop (env : Env) (h : Heap) (op : BinOp) (x y : Value) : Option (Res (Value × Heap)) :=
  let list := fun (v : Value) => match v with
    | .ref a => match h.objs a with
      | some (.list k _ _ xs) => some (k, xs)
      | _ => none
    | _ => none
  match x, y with
  | .ref _, _ | _, .ref _ => some <|
    match LibModel.binopH env h op x y with
    | some r => r
    | none =>
      match op, list x, list y, y, x with
      | .add, some (.pyList, xs), some (.pyList, ys), _, _ => .ok (allocPyList h (xs ++ ys))
      | .mul, some (.pyList, xs), none, .int n, _ | .mul, none, some (.pyList, xs), _, .int n =>
        .ok (allocPyList h (List.replicate n.toNat xs).flatten)
      | _, _, _, _, _ => .error .typeError
  | _, _ => none

/-- `x += y` where `x` is a Python list: it extends `x` in place, from any iterable. `none`
otherwise: then `x += y` is `x = x + y`. -/
def seqAugAdd (h : Heap) (op : BinOp) (x y : Value) : Option (Res (Value × Heap)) :=
  match op, x with
  | .add, .ref a =>
    match h.objs a with
    | some (.list .pyList e l xs) => some do
      let ys ← iterElems h y
      pure (x, h.set a (.list .pyList e l (xs ++ ys)))
    | _ => none
  | _, _ => none

/-- `set(xs)` from `acc`: the primitive with Python's `in` for sets (`findKey`). -/
def dedupe (h : Heap) (acc xs : List Value) : Res (List Value) :=
  Prim.dedupBy (fun x acc => do pure (← findKey h x acc).isSome) acc xs

def applyBuiltin (env : Env) (h : Heap) (b : Builtin) (args : List Value)
    (kws : List (Name × Value)) : Res (Value × Heap) :=
  match LibModel.builtin env h b args kws with
  | some r => r
  | none =>
  match b, args with
  | .len, [v] =>
    match v with
    | .ref a =>
      match h.objs a with
      | some (.list _ _ _ xs) => .ok (.int (Prim.len xs), h)
      | some (.set xs) => .ok (.int (Prim.len xs), h)
      | some (.dict es) => .ok (.int (Prim.len es), h)
      | _ => .error .typeError
    | .bytes _ bs => .ok (.int (Prim.len bs), h)
    | .tuple xs => .ok (.int (Prim.len xs), h)
    | .frozenDict kvs => .ok (.int (Prim.len kvs), h)
    | _ => .error .typeError
  | .range, rargs => do
    let ns ← rargs.mapM toIndex
    let (lo, hi, step) ← match ns with
      | [n] => pure (0, n, 1)
      | [a, b] => pure (a, b, 1)
      | [a, b, c] => pure (a, b, c)
      | _ => .error .typeError
    if step = 0 then .error .valueError
    else
      let count := if step > 0 then ((hi - lo + step - 1) / step).toNat
        else ((lo - hi - step - 1) / (-step)).toNat
      pure (.tuple ((List.range count).map fun (i : Nat) => Value.int (lo + step * (i : Int))), h)
  | .enumerate, [v] =>
    match v with
    | .ref _ | .tuple _ | .bytes _ _ => .ok (.enumView v, h)
    | _ => .error .typeError
  | .zip, vs =>
    let strict := match kwArg kws env.nm.strict with | some (.bool true) => true | _ => false
    .ok (.zipView vs strict, h)
  | .sorted, [v] => do
    let xs ← iterElems h v
    let rev := match kwArg kws env.nm.reverse with | some (.bool true) => true | _ => false
    let ys ← stableSort rev (xs.map fun x => (x, x))
    pure (allocPyList h ys)
  | .min, [v] => do
    match ← iterElems h v with
    | x :: xs => pure (← pickBest false x xs, h)
    | [] => .error .valueError
  | .max, [v] => do
    match ← iterElems h v with
    | x :: xs => pure (← pickBest true x xs, h)
    | [] => .error .valueError
  | .min, x :: xs => do pure (← pickBest false x xs, h)
  | .max, x :: xs => do pure (← pickBest true x xs, h)
  | .sum, v :: rest => do
    let xs ← iterElems h v
    let start := rest.headD (.int 0)
    -- `Prim.sum (binopVal .add) start xs`, written out: the tactic matches `List.foldlM`.
    pure (← xs.foldlM (binopVal .add) start, h)
  | .any, [v] => do
    let xs ← iterElems h v
    pure (.bool (← Prim.any (truthyH h) xs), h)
  | .all, [v] => do
    let xs ← iterElems h v
    pure (.bool (← Prim.all (truthyH h) xs), h)
  | .list, [] => .ok (allocPyList h [])
  | .list, [v] => do pure (allocPyList h (← iterElems h v))
  | .tuple, [v] => do pure (.tuple (← iterElems h v), h)
  | .set, [] =>
    let (a, h1) := h.alloc (.set [])
    .ok (.ref a, h1)
  | .set, [v] => do
    let xs ← dedupe h [] (← iterElems h v)
    let (a, h1) := h.alloc (.set xs)
    pure (.ref a, h1)
  | .dict, [] =>
    let (a, h1) := h.alloc (.dict [])
    .ok (.ref a, h1)
  | .bytes, [.bytes _ bs] => .ok (.bytes env.bytesName bs, h)
  | .bytes, [v] => do
    let xs ← iterElems h v
    let bs ← xs.mapM fun x => match x with
      | .int n => if 0 ≤ n ∧ n < 256 then pure (UInt8.ofNat n.toNat) else .error .valueError
      | _ => .error .typeError
    pure (.bytes env.bytesName bs, h)
  | .int, [v] => do
    match numOf v with
    | some n => pure (.int n, h)
    | none => .error .typeError
  | .bool, [v] => do pure (.bool (← truthyH h v), h)
  | .sha256, [.bytes _ bs] => .ok (.bytes env.nm.bytes32 (env.sha256 bs), h)
  | _, _ => .error .unsupported

/-! ## Constructors -/

/-- Bind constructor arguments to fields: positional first, then keywords, then defaults. -/
def ctorFields (fields : List Name) (args : List Value) (kws : List (Name × Value)) :
    Res (List (Option Value)) :=
  if args.length > fields.length then .error .typeError
  else if kws.any (fun (k, _) => !fields.contains k) then .error .typeError
  else .ok ((fields.zipIdx).map fun (f, i) =>
    match args[i]? with
    | some v => some v
    | none => kwArg kws f)

/-- `D(args)` for a Python dataclass `D`. Every field is required. -/
def applyDataclass (env : Env) (h : Heap) (ty : Name) (args : List Value)
    (kws : List (Name × Value)) : Res (Value × Heap) :=
  match env.containers.lookup ty with
  | some fs => do
    let given ← ctorFields (fs.map (·.1)) args kws
    let vs ← given.mapM fun g => match g with
      | some v => pure v
      | none => .error .typeError
    let (a, h1) := h.alloc (.container ty vs)
    pure (.ref a, h1)
  | none => .error .unsupported

/-! ## Methods that do not call spec code -/

/-- `self.append(v)`: coerced, then the limit is checked. -/
def appendItem (env : Env) (h : Heap) (a : Nat) (v : Value) : Res Heap :=
  match LibModel.append env h a v with
  | some r => r
  | none =>
    match h.objs a with
    | some (.list k e l xs) => .ok (h.set a (.list k e l (xs ++ [v])))
    | _ => .error .typeError

def indexOf (h : Heap) (x : Value) : List Value → Nat → Res (Option Nat)
  | [], _ => .ok none
  | y :: ys, i => do if ← deepEq depthBound h x y then pure (some i) else indexOf h x ys (i + 1)

def countOf (h : Heap) (x : Value) : List Value → Res Nat
  | [] => .ok 0
  | y :: ys => do
    let c ← countOf h x ys
    if ← deepEq depthBound h x y then pure (c + 1) else pure c

/-- `int.from_bytes(data, endianness)`. -/
def fromBytes (env : Env) : List Value → Res Value
  | [.bytes _ bs, .str e] =>
    if e = env.nm.little then .ok (.int (Prim.fromBytesLE bs))
    else .ok (.int (Prim.fromBytesBE bs))
  | _ => .error .typeError

def applyMethod (env : Env) (h : Heap) (self : Value) (m : Name) (args : List Value) :
    Res (Value × Heap) :=
  match LibModel.method env h self m args with
  | some r => r
  | none =>
  match self with
  | .ref a =>
    match h.objs a with
    -- A byte list reads its elements as `int`. The library handles its `copy` and `extend`.
    | some (.list .list (.uint (.width 8)) _ xs) =>
      if m = env.nm.append then
        match args with
        | [v] => do pure (.none, ← appendItem env h a v)
        | _ => .error .typeError
      else if m = env.nm.index then
        match args with
        | [v] => do
          match ← indexOf h v (xs.map byteInt) 0 with
          | some i => pure (.int i, h)
          | none => .error .valueError
        | _ => .error .typeError
      else if m = env.nm.count then
        match args with
        | [v] => do pure (.int (← countOf h v (xs.map byteInt)), h)
        | _ => .error .typeError
      else .error .unsupported
    | some (.list _ _ _ xs) =>
      if m = env.nm.append then
        match args with
        | [v] => do pure (.none, ← appendItem env h a v)
        | _ => .error .typeError
      else if m = env.nm.extend then
        match args with
        | [v] => do
          let ys ← iterElems h v
          let h' ← ys.foldlM (fun h y => appendItem env h a y) h
          pure (.none, h')
        | _ => .error .typeError
      else if m = env.nm.index then
        match args with
        | [v] => do
          match ← indexOf h v xs 0 with
          | some i => pure (.int i, h)
          | none => .error .valueError
        | _ => .error .typeError
      else if m = env.nm.count then
        match args with
        | [v] => do pure (.int (← countOf h v xs), h)
        | _ => .error .typeError
      -- `.copy()` of a Python list is shallow (probed).
      else if m = env.nm.copy then .ok (allocPyList h xs)
      else .error .unsupported
    | some (.set xs) =>
      if m = env.nm.union then
        match args with
        | [v] => do
          let ys ← dedupe h xs (← iterElems h v)
          let (b, h1) := h.alloc (.set ys)
          pure (.ref b, h1)
        | _ => .error .typeError
      else if m = env.nm.intersection then
        match args with
        | [v] => do
          let other ← iterElems h v
          let ys ← xs.filterM fun x => do pure (← findKey h x other).isSome
          let (b, h1) := h.alloc (.set ys)
          pure (.ref b, h1)
        | _ => .error .typeError
      else if m = env.nm.difference then
        match args with
        | [v] => do
          let other ← iterElems h v
          let ys ← xs.filterM fun x => do pure (← findKey h x other).isNone
          let (b, h1) := h.alloc (.set ys)
          pure (.ref b, h1)
        | _ => .error .typeError
      else if m = env.nm.add then
        match args with
        | [v] => do
          if (← findKey h v xs).isSome then pure (.none, h)
          else pure (.none, h.set a (.set (xs ++ [v])))
        | _ => .error .typeError
      else .error .unsupported
    | some (.dict es) =>
      if m = env.nm.get then
        match args with
        | [k] => do
          match ← findKey h k (es.map (·.1)) with
          | some i => pure ((es[i]?.map (·.2)).getD .none, h)
          | none => pure (.none, h)
        | [k, d] => do
          match ← findKey h k (es.map (·.1)) with
          | some i => pure ((es[i]?.map (·.2)).getD d, h)
          | none => pure (d, h)
        | _ => .error .typeError
      -- A dict view is a snapshot here. Spec code does not change a dict while it iterates
      -- a view of it (CPython raises `RuntimeError` then).
      else if m = env.nm.items ∧ args.isEmpty then .ok (.tuple (es.map fun (k, v) => .tuple [k, v]), h)
      else if m = env.nm.values ∧ args.isEmpty then .ok (.tuple (es.map (·.2)), h)
      else if m = env.nm.keys ∧ args.isEmpty then .ok (.tuple (es.map (·.1)), h)
      else .error .unsupported
    | _ => .error .unsupported
  | .int n =>
    -- `x.bit_length()`: `getAttr` binds it to the number as an `int`.
    if m = env.nm.bitLength ∧ args.isEmpty then .ok (.int (Prim.bitLength n), h)
    else .error .unsupported
  | .glob g =>
    match env.globals.lookup g with
    | some (.module .bls) => do pure (← env.bls m h args, h)
    | some (.builtin .int) => if m = env.nm.fromBytes then do pure (← fromBytes env args, h)
                              else .error .unsupported
    | _ => .error .unsupported
  | _ => .error .unsupported

end SpecLean
