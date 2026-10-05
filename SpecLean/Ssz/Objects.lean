import SpecLean.Builtins
import SpecLean.Ssz.Values

/-!
# eth-ssz-specs: objects

The library model for SSZ objects: containers and lists with their element types, limits and
default values, the coercion of written values, constructors, methods and builtins.
-/

namespace SpecLean.Ssz

mutual

/-- The default value of an SSZ type. Each element of a vector is a separate object. -/
def defaultOf (env : Env) : Nat → Heap → SszTy → Res (Value × Heap)
  | 0, _, _ => .error .unsupported
  | d + 1, h, t =>
    match t with
    | .uint u => .ok (.uint u 0, h)
    | .boolean => .ok (.boolean false, h)
    | .bytes ty len => .ok (.bytes ty (List.replicate len 0), h)
    | .any => .ok (.none, h)
    | .container ty =>
      match env.containers.lookup ty with
      | some fs => do
        let (vs, h1) ← defaultList env d h (fs.map (·.2))
        let (a, h2) := h1.alloc (.container ty vs)
        pure (.ref a, h2)
      | none => .error .unsupported
    | .list k e l =>
      match k, l with
      | .vector, some n | .bitvector, some n => do
        let (vs, h1) ← defaultList env d h (List.replicate n e)
        let (a, h2) := h1.alloc (.list k e l vs)
        pure (.ref a, h2)
      | _, _ =>
        let (a, h1) := h.alloc (.list k e l [])
        .ok (.ref a, h1)

def defaultList (env : Env) : Nat → Heap → List SszTy → Res (List Value × Heap)
  | _, h, [] => .ok ([], h)
  | d, h, t :: ts => do
    let (v, h1) ← defaultOf env d h t
    let (vs, h2) ← defaultList env d h1 ts
    pure (v :: vs, h2)

end

/-- The length rule of an SSZ list kind. -/
def checkLength (k : ListKind) (l : Option Nat) (n : Nat) : Res Unit :=
  match k, l with
  | .vector, some m | .bitvector, some m => if n = m then .ok () else .error .sszValue
  | .list, some m | .bitlist, some m => if n ≤ m then .ok () else .error .sszValue
  | _, _ => .ok ()

mutual

/-- Coerce a value into an SSZ type, for a list element (`fieldErr = false`) or a container
field (`fieldErr = true`). A heap object passes when its type matches, and then it is shared,
as in Python. A Python list or a tuple for an SSZ list type becomes a new SSZ list in a list
element, and raises `ValidationError` in a field. -/
def coerceH (env : Env) (fieldErr : Bool) : Nat → Heap → SszTy → Value → Res (Value × Heap)
  | 0, _, _, _ => .error .unsupported
  | d + 1, h, t, v =>
    let bad : SpecError := if fieldErr then .validation else .typeError
    match t, v with
    | .container ty, .ref a =>
      match h.objs a with
      | some (.container ty' _) => if ty' = ty then .ok (v, h) else .error bad
      | _ => .error bad
    | .list k e l, .ref a =>
      match h.objs a with
      | some (.list k' e' l' xs) =>
        if k' = k ∧ e' = e ∧ l' = l then .ok (v, h)
        -- pydantic rejects a Python list for an SSZ list field (probed). A list element
        -- takes it.
        else if k' = .pyList then
          if fieldErr then .error .validation else newList env d h k e l xs
        else .error bad
      | _ => .error bad
    | .list k e l, .tuple xs =>
      if fieldErr then .error .validation else newList env d h k e l xs
    | .any, _ => .ok (v, h)
    | _, .ref _ => .error bad
    | _, _ => do
      let v' ← if fieldErr then coerceField t v else coerceElem t v
      pure (v', h)
termination_by d => (d, 0, 0)

/-- A new SSZ list of kind `k` from values. -/
def newList (env : Env) : Nat → Heap → ListKind → SszTy → Option Nat → List Value →
    Res (Value × Heap)
  | d, h, k, e, l, xs => do
    checkLength k l xs.length
    let (ys, h1) ← match k, e with
      | .list, .uint (.width 8) => (·, h) <$> xs.mapM coerceByte
      | _, _ => coerceAll env d h e xs
    let (a, h2) := h1.alloc (.list k e l ys)
    pure (.ref a, h2)
termination_by d => (d, 2, 0)

def coerceAll (env : Env) : Nat → Heap → SszTy → List Value → Res (List Value × Heap)
  | _, h, _, [] => .ok ([], h)
  | d, h, e, x :: xs => do
    let (y, h1) ← coerceH env false d h e x
    let (ys, h2) ← coerceAll env d h1 e xs
    pure (y :: ys, h2)
termination_by d _ _ xs => (d, 1, xs.length)

end

/-- `T(args)` for an SSZ type `T`. -/
def construct (env : Env) (h : Heap) (t : SszTy) (args : List Value)
    (kws : List (Name × Value)) : Res (Value × Heap) :=
  match t, args with
  | .uint u, [.int n] => do pure (← wrapUint u n, h)
  | .uint u, [.uint _ n] => do pure (← wrapUint u n, h)
  -- An SSZ `Boolean` converts. A Python `bool` raises `SSZTypeError` (probed).
  | .uint u, [.boolean b] => .ok (.uint u (if b then 1 else 0), h)
  | .uint _, _ => .error .typeError
  | .boolean, [v] => do pure (← coerceElem .boolean v, h)
  | .boolean, [] => .ok (.boolean false, h)
  | .bytes ty len, [] => .ok (.bytes ty (List.replicate len 0), h)
  | .bytes ty len, [.bytes _ bs] =>
    if bs.length = len then .ok (.bytes ty bs, h) else .error .sszValue
  | .bytes ty len, [v] => do
    let xs ← iterElems h v
    let bs ← xs.mapM fun x => match x with
      | .int n => if 0 ≤ n ∧ n < 256 then pure (UInt8.ofNat n.toNat) else .error .valueError
      | _ => .error .typeError
    if bs.length = len then pure (.bytes ty bs, h) else .error .sszValue
  -- A pydantic model takes keyword arguments only (probed).
  | .container _, _ :: _ => .error .typeError
  | .container ty, [] =>
    match env.containers.lookup ty with
    | some fs => do
      let given ← ctorFields (fs.map (·.1)) args kws
      let rec build (h : Heap) : List ((Name × SszTy) × Option Value) → Res (List Value × Heap)
        | [] => .ok ([], h)
        | ((_, ft), gv) :: rest => do
          let (v, h1) ← match gv with
            | some v => coerceH env true depthBound h ft v
            | none => defaultOf env depthBound h ft
          let (vs, h2) ← build h1 rest
          pure (v :: vs, h2)
      let (vs, h1) ← build h (fs.zip given)
      let (a, h2) := h1.alloc (.container ty vs)
      pure (.ref a, h2)
    | none => .error .unsupported
  | .list k e l, [] =>
    match kwArg kws env.nm.data with
    | some v => do
      -- pydantic checks `data`: a wrong length, or a byte out of range, raises
      -- `ValidationError` (probed).
      match newList env depthBound h k e l (← iterElems h v) with
      | .error .sszValue | .error .valueError => .error .validation
      | r => r
    | none => defaultOf env depthBound h t
  | .list _ _ _, _ :: _ => .error .typeError
  | _, _ => .error .unsupported


def isBitlist : ListKind → Bool
  | .bitlist | .progressiveBitlist => true
  | _ => false

/-- `bytes(v)`: a count of zero bytes for a number, else the bytes of an iterable of numbers in
`range(256)`. A count over the `Py_ssize_t` range raises `OverflowError` (probed). -/
def bytesOfValue (h : Heap) (v : Value) : Res (List UInt8) :=
  let count : Int → Res (List UInt8) := fun n =>
    if n < 0 then .error .valueError
    else if 2 ^ 63 ≤ n then .error (.other "OverflowError")
    -- A large count needs a large allocation. Generated programs do not make one.
    else if 2 ^ 20 ≤ n then .error .unsupported
    else .ok (List.replicate n.toNat 0)
  match v with
  | .bytes _ bs => .ok bs
  | .int n => count n
  | .uint _ n => count n
  | .bool b | .boolean b => count (if b then 1 else 0)
  | v => do
    (← iterElems h v).mapM fun x => byteU8 <$> coerceByte x

/-- A byte list `b`: `b + x` is `b.data + bytes(x)`, and `x + b` is `bytes(x) + b.data`.
Either gives Python `bytes` (probed). -/
def byteListAdd (env : Env) (h : Heap) (op : BinOp) (x y : Value) :
    Option (Res (Value × Heap)) :=
  let data := fun (v : Value) => match v with
    | .ref a => match h.objs a with
      | some (.list .list (.uint (.width 8)) _ xs) => some (xs.map byteU8)
      | _ => none
    | _ => none
  match op, data x, data y with
  | .add, some xs, _ => some do pure (.bytes env.bytesName (xs ++ (← bytesOfValue h y)), h)
  | .add, none, some ys => some do pure (.bytes env.bytesName ((← bytesOfValue h x) ++ ys), h)
  | _, _, _ => none

/-- `x + y` with an SSZ list on the left. It concatenates with a list or a tuple into a new
list of its own type, through the constructor (probed). `none` for two Python lists, and for
an operator other than `+`. -/
def binopH (env : Env) (h : Heap) (op : BinOp) (x y : Value) : Option (Res (Value × Heap)) :=
  (byteListAdd env h op x y).or <|
  let list := fun (v : Value) => match v with
    | .ref a => match h.objs a with
      | some (.list k _ _ xs) => some (k, xs)
      | _ => none
    | _ => none
  match op, list x, list y, y, x with
  | .add, some (.pyList, _), some (.pyList, _), _, _ => none
  | .add, some (k, xs), some (k', ys), _, .ref a =>
    some <| match h.objs a with
      | some (.list _ e l _) =>
        if (k = .list ∨ k = .progressiveList) ∧ (k' = .list ∨ k' = .progressiveList ∨ k' = .pyList)
          ∨ isBitlist k ∧ isBitlist k' then newList env depthBound h k e l (xs ++ ys)
        else .error .typeError
      | _ => .error .typeError
  | .add, some (k, xs), none, .tuple ys, .ref a =>
    some <| match h.objs a with
      | some (.list _ e l _) =>
        if k = .list ∨ k = .progressiveList then newList env depthBound h k e l (xs ++ ys)
        else .error .typeError
      | _ => .error .typeError
  | _, _, _, _, _ => none

/-- Methods of SSZ objects: a deep `.copy()`, `.hash_tree_root()`, `T.empty()`. An SSZ list has
no `extend` (probed). -/
def method (env : Env) (h : Heap) (self : Value) (m : Name) (_args : List Value) :
    Option (Res (Value × Heap)) :=
  match self with
  | .ref a =>
    match h.objs a with
    | some (.list k _ _ _) =>
      if m = env.nm.extend ∧ k ≠ .pyList then some (.error (.other "AttributeError"))
      else if m = env.nm.copy ∧ k ≠ .pyList then some (deepCopy depthBound h self)
      else if m = env.nm.hashTreeRoot then
        some do pure (.bytes env.nm.root (← env.hashTreeRoot h self), h)
      else none
    | some (.container _ _) =>
      if m = env.nm.copy then some (deepCopy depthBound h self)
      else if m = env.nm.hashTreeRoot then
        some do pure (.bytes env.nm.root (← env.hashTreeRoot h self), h)
      else none
    | _ => none
  | .bytes _ _ => if m = env.nm.copy then some (.ok (self, h)) else none
  | .glob g =>
    match env.globals.lookup g with
    | some (.type t) => if m = env.nm.empty then some (defaultOf env depthBound h t) else none
    | _ => none
  | _ => none

/-- `obj.append(v)` on an SSZ list: coerce, then check the limit. A vector has no `append`. -/
def append (env : Env) (h : Heap) (a : Nat) (v : Value) : Option (Res Heap) :=
  match h.objs a with
  | some (.list .pyList _ _ _) => none
  | some (.list k e l xs) => some do
    match k with
    | .vector | .bitvector => .error .unsupported
    | _ =>
      let (v', h1) ← match k, e with
        | .list, .uint (.width 8) => (·, h) <$> coerceByte v
        | _, _ => coerceH env false depthBound h e v
      checkLength k l (xs.length + 1)
      .ok (h1.set a (.list k e l (xs ++ [v'])))
  | _ => none

/-- `obj[lo:hi] = vals` on an SSZ list. A `Vector` keeps its length or raises. -/
def setSlice (env : Env) (h : Heap) (a lo hi : Nat) (ins : List Value) : Option (Res Heap) :=
  match h.objs a with
  | some (.list .pyList _ _ _) => none
  | some (.list kind elem limit xs) => some do
    let (ins', h1) ← match kind, elem with
      | .list, .uint (.width 8) => (·, h) <$> ins.mapM coerceByte
      | _, _ => coerceAll env depthBound h elem ins
    let ys := xs.take lo ++ ins' ++ xs.drop (max lo hi)
    checkLength kind limit ys.length
    .ok (h1.set a (.list kind elem limit ys))
  | _ => none

/-- `ssz_serialize` of a uint or a `Boolean`, and `hash_tree_root` through the oracle. -/
def builtin (env : Env) (h : Heap) (b : Builtin) (args : List Value) (_kws : List (Name × Value)) :
    Option (Res (Value × Heap)) :=
  match b, args with
  | .sszSerialize, [.uint t n] => some (.ok (.bytes env.bytesName (leBytes n (t.bits / 8)), h))
  | .sszSerialize, [.boolean b] => some (.ok (.bytes env.bytesName [if b then 1 else 0], h))
  -- A Python `int`, `bool` or `bytes` has no `encode_bytes` (probed).
  | .sszSerialize, [.int _] | .sszSerialize, [.bool _] | .sszSerialize, [.bytes _ _] =>
    some (.error (.other "AttributeError"))
  | .hashTreeRoot, [v] => some do pure (.bytes env.nm.root (← env.hashTreeRoot h v), h)
  | _, _ => none

/-- The coercion of a written value. A Python list element or a dataclass field (`any`) takes
the value as it is. -/
def coerce (env : Env) (field : Bool) (h : Heap) (t : SszTy) (v : Value) :
    Option (Res (Value × Heap)) :=
  match t with
  | .any => none
  | _ => some (coerceH env field depthBound h t v)

instance model : LibModel where
  toLibValues := values
  coerce := coerce
  binopH := binopH
  construct := construct
  method := method
  append := append
  setSlice := setSlice
  builtin := builtin

end SpecLean.Ssz
