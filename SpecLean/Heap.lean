import SpecLean.Value

/-!
# Heap

Lists, containers, dicts, sets and closures live in the heap, as in Python. A `Value.ref`
points at them.
-/

namespace SpecLean

inductive ListKind where
  | list | vector | progressiveList | bitlist | bitvector | progressiveBitlist
  /-- A plain Python `list`: no element type and no limit. -/
  | pyList
  deriving DecidableEq, Repr

/-- The SSZ type of a list element or a container field. `any` is a field of a Python
dataclass, or an element of a Python list: no coercion. -/
inductive SszTy where
  | uint (t : UintTy)
  | boolean
  /-- A fixed-size byte vector class, for example `Bytes32`. -/
  | bytes (ty : Name) (len : Nat)
  | container (ty : Name)
  | list (kind : ListKind) (elem : SszTy) (limit : Option Nat)
  | any
  deriving Repr, DecidableEq

/-- A persistent map from `Nat` keys, as a binary trie. Key `0` is at the root. Key `n + 1`
is under the left child for an even `n`, else under the right child, at `n / 2`. The
executable heap and locals use it. -/
inductive Trie (α : Type) where
  | nil
  | node (v : Option α) (l r : Trie α)

def Trie.get {α : Type} : Trie α → Nat → Option α
  | .nil, _ => none
  | .node v _ _, 0 => v
  | .node _ l r, n + 1 => if n % 2 = 0 then l.get (n / 2) else r.get (n / 2)

/-- `fuel` bounds the depth. `n + 1` is enough for key `n`. -/
def Trie.insert {α : Type} : Nat → Trie α → Nat → α → Trie α
  | 0, s, _, _ => s
  | _ + 1, .nil, 0, o => .node (some o) .nil .nil
  | _ + 1, .node _ l r, 0, o => .node (some o) l r
  | f + 1, s, n + 1, o =>
    let (v, l, r) := match s with
      | .nil => (none, Trie.nil, Trie.nil)
      | .node v l r => (v, l, r)
    if n % 2 = 0 then .node v (insert f l (n / 2) o) r else .node v l (insert f r (n / 2) o)

/-- Local variables of one call frame. Read them as a function: `L x`. -/
structure Locals where
  get : Name → Option Value
  /-- The same bindings as `get`, for fast execution. `Locals.set` keeps the two equal. The
  semantics read `get` only. -/
  store : Trie Value := .nil

instance : CoeFun Locals (fun _ => Name → Option Value) := ⟨Locals.get⟩

/-- The body of a closure: a `lambda` expression or the statements of a nested `def`. -/
inductive ClosureBody where
  | expr (e : Expr)
  | stmts (ss : List Stmt)

inductive HeapObj where
  | list (kind : ListKind) (elem : SszTy) (limit : Option Nat) (xs : List Value)
  | container (ty : Name) (fields : List Value)
  /-- Insertion order, as Python keeps it. -/
  | dict (entries : List (Value × Value))
  /-- Insertion order. Spec code iterates a set only through `sorted` (SPEC 6.3). -/
  | set (elems : List Value)
  /-- A `lambda` or a nested `def`. `captured` is the frame where it was made. Spec code calls
  a closure before that frame changes the names it reads, so a snapshot is enough. -/
  | closure (params : Params) (body : ClosureBody) (captured : Locals)

abbrev Store := Trie HeapObj

structure Heap where
  objs : Nat → Option HeapObj
  next : Nat
  /-- The same objects as `objs`, for fast execution. `set` and `alloc` keep the two equal.
  The semantics read `objs` only. -/
  store : Store := .nil

/-- A watch on in-place writes, for the EF vector runner (SPEC 9.4). The semantics never read
it. The watch returns `0`. -/
initialize writeWatch : IO.Ref (Heap → Nat → HeapObj → BaseIO Nat) ← IO.mkRef fun _ _ _ => pure 0

namespace Heap

def empty : Heap := ⟨fun _ => none, 0, .nil⟩

/-- `set` for execution: it reads the store, and it calls the watch. The watch returns `0`.
`objs` equals `store.get`, so this is `set`. -/
@[noinline] unsafe def setFast (h : Heap) (a : Nat) (o : HeapObj) : Heap :=
  let z := unsafeBaseIO do (← writeWatch.get) h a o
  let s := h.store.insert (a + z + 1) a o
  { objs := s.get, next := h.next, store := s }

@[implemented_by setFast]
def set (h : Heap) (a : Nat) (o : HeapObj) : Heap :=
  { objs := fun b => if b = a then some o else h.objs b, next := h.next,
    store := h.store.insert (a + 1) a o }

/-- `alloc` for execution: it reads the store. `objs` equals `store.get`, so this is
`alloc`. -/
unsafe def allocFast (h : Heap) (o : HeapObj) : Nat × Heap :=
  let s := h.store.insert (h.next + 1) h.next o
  (h.next, { objs := s.get, next := h.next + 1, store := s })

@[implemented_by allocFast]
def alloc (h : Heap) (o : HeapObj) : Nat × Heap :=
  (h.next, { objs := fun b => if b = h.next then some o else h.objs b, next := h.next + 1,
             store := h.store.insert (h.next + 1) h.next o })

@[simp] theorem set_objs (h : Heap) (a : Nat) (o : HeapObj) (b : Nat) :
    (h.set a o).objs b = if b = a then some o else h.objs b := by
  simp only [Heap.set]

@[simp] theorem set_next (h : Heap) (a : Nat) (o : HeapObj) : (h.set a o).next = h.next := by
  simp only [Heap.set]

end Heap

end SpecLean
