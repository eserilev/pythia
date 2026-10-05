/-!
# Syntax tree of the spec subset

One constructor per CPython `ast` node that the version 1 scope uses (SPEC 5.1). Names are
interned to `Nat` indices by the serializer. Every node carries its source line in the spec
markdown.
-/

namespace SpecLean

/-- An interned identifier. The generated files list the strings. -/
abbrev Name := Nat

/-- A line in the source markdown file. -/
abbrev Line := Nat

inductive BinOp where
  | add | sub | mul | floorDiv | mod | pow | bitAnd | bitOr | bitXor | lShift | rShift
  deriving DecidableEq, Repr

inductive UnOp where
  | not | neg | invert
  deriving DecidableEq, Repr

inductive CmpOp where
  | eq | notEq | lt | ltE | gt | gtE | is | isNot | isIn | notIn
  deriving DecidableEq, Repr

inductive BoolOp where
  | and | or
  deriving DecidableEq, Repr

/-- The kind of a comprehension. A generator is evaluated at once, into a snapshot. -/
inductive CompKind where
  | list | set | gen
  deriving DecidableEq, Repr

mutual

inductive Expr where
  | name (line : Line) (id : Name)
  | int (line : Line) (n : Int)
  | bool (line : Line) (b : Bool)
  | str (line : Line) (s : String)
  | bytes (line : Line) (b : List UInt8)
  | noneLit (line : Line)
  | attr (line : Line) (e : Expr) (field : Name)
  | index (line : Line) (e i : Expr)
  | slice (line : Line) (e : Expr) (lo hi step : Option Expr)
  | binop (line : Line) (op : BinOp) (a b : Expr)
  | unop (line : Line) (op : UnOp) (e : Expr)
  /-- `a op1 b op2 c`: CPython `Compare(left, ops, comparators)`. -/
  | compare (line : Line) (left : Expr) (rest : List (CmpOp × Expr))
  | boolop (line : Line) (op : BoolOp) (args : List Expr)
  | call (line : Line) (fn : Expr) (args : List Arg)
  | ifExp (line : Line) (c a b : Expr)
  | comp (line : Line) (kind : CompKind) (elt : Expr) (gens : List Comprehension)
  | lambda (line : Line) (params : List Name) (body : Expr)
  | list (line : Line) (es : List Expr)
  | tuple (line : Line) (es : List Expr)
  | dict (line : Line) (kvs : List (Expr × Expr))

inductive Arg where
  | pos (e : Expr)
  | starred (e : Expr)
  | kw (name : Name) (e : Expr)

/-- `for t in iter if c1 if c2`. -/
inductive Comprehension where
  | mk (t : Target) (iter : Expr) (ifs : List Expr)

/-- An assignment target. CPython uses `Expr` with a `Store` context. -/
inductive Target where
  | name (line : Line) (id : Name)
  | attr (line : Line) (e : Expr) (field : Name)
  | index (line : Line) (e i : Expr)
  | slice (line : Line) (e : Expr) (lo hi : Option Expr)
  | tuple (line : Line) (ts : List Target)

end

instance : Inhabited Expr := ⟨.noneLit 0⟩

/-- A parameter list: plain names, default expressions for the last ones, and an optional
`*args` name. -/
structure Params where
  names : List Name
  defaults : List Expr
  vararg : Option Name

inductive Stmt where
  | assign (line : Line) (targets : List Target) (value : Expr)
  | annAssign (line : Line) (t : Target) (value : Expr)
  /-- `t op= v`. -/
  | augAssign (line : Line) (t : Target) (op : BinOp) (v : Expr)
  | exprStmt (line : Line) (e : Expr)
  | ifStmt (line : Line) (c : Expr) (thn els : List Stmt)
  | forStmt (line : Line) (t : Target) (iter : Expr) (body : List Stmt)
  | whileStmt (line : Line) (c : Expr) (body : List Stmt)
  | ret (line : Line) (e : Option Expr)
  | assert (line : Line) (e : Expr)
  | raise (line : Line)
  | brk (line : Line)
  | cont (line : Line)
  | pass (line : Line)
  /-- A nested `def`, as in `for_ops`. -/
  | funDef (line : Line) (name : Name) (params : Params) (body : List Stmt)

structure FunctionDef where
  name : Name
  params : Params
  body : List Stmt
  line : Line

end SpecLean
