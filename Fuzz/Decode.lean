import SpecLean.Interp
import SpecLean.Ssz
import Fuzz.Term

/-!
# Terms to interpreter data

Decoders for the syntax that `tools/serialize.py` writes, plus the heap objects and the
`(.fn ...)` global that `tools/fuzz/encode.py` adds.
-/

namespace SpecLean.Fuzz

abbrev D := Except String

def bad {α : Type} (what : String) (t : Term) : D α := .error s!"bad {what}: {reprStr t}"

def dNat : Term → D Nat
  | .int n => if 0 ≤ n then .ok n.toNat else bad "nat" (.int n)
  | t => bad "nat" t

def dInt : Term → D Int
  | .int n => .ok n
  | t => bad "int" t

def dStr : Term → D String
  | .str s => .ok s
  | t => bad "string" t

def dBool : Term → D Bool
  | .app "true" [] => .ok true
  | .app "false" [] => .ok false
  | t => bad "bool" t

def dList {α : Type} (f : Term → D α) : Term → D (List α)
  | .list xs => xs.mapM f
  | t => bad "list" t

def dPair {α β : Type} (f : Term → D α) (g : Term → D β) : Term → D (α × β)
  | .tuple [a, b] => do pure (← f a, ← g b)
  | t => bad "pair" t

def dOpt {α : Type} (f : Term → D α) : Term → D (Option α)
  | .app "none" [] => .ok none
  | .app "some" [x] => some <$> f x
  | t => bad "option" t

def dBinOp : Term → D BinOp
  | .app "add" [] => .ok .add | .app "sub" [] => .ok .sub | .app "mul" [] => .ok .mul
  | .app "floorDiv" [] => .ok .floorDiv | .app "mod" [] => .ok .mod | .app "pow" [] => .ok .pow
  | .app "bitAnd" [] => .ok .bitAnd | .app "bitOr" [] => .ok .bitOr
  | .app "bitXor" [] => .ok .bitXor | .app "lShift" [] => .ok .lShift
  | .app "rShift" [] => .ok .rShift
  | t => bad "binop" t

def dUnOp : Term → D UnOp
  | .app "not" [] => .ok .not | .app "neg" [] => .ok .neg | .app "invert" [] => .ok .invert
  | t => bad "unop" t

def dCmpOp : Term → D CmpOp
  | .app "eq" [] => .ok .eq | .app "notEq" [] => .ok .notEq | .app "lt" [] => .ok .lt
  | .app "ltE" [] => .ok .ltE | .app "gt" [] => .ok .gt | .app "gtE" [] => .ok .gtE
  | .app "is" [] => .ok .is | .app "isNot" [] => .ok .isNot | .app "isIn" [] => .ok .isIn
  | .app "notIn" [] => .ok .notIn
  | t => bad "cmpop" t

def dBoolOp : Term → D BoolOp
  | .app "and" [] => .ok .and | .app "or" [] => .ok .or
  | t => bad "boolop" t

def dCompKind : Term → D CompKind
  | .app "list" [] => .ok .list | .app "set" [] => .ok .set | .app "gen" [] => .ok .gen
  | t => bad "comp kind" t

def dBytes : Term → D (List UInt8) := dList fun t => do pure (UInt8.ofNat (← dNat t))

mutual

partial def dExpr : Term → D Expr
  | .app "name" [l, x] => do pure (.name (← dNat l) (← dNat x))
  | .app "int" [l, n] => do pure (.int (← dNat l) (← dInt n))
  | .app "bool" [l, b] => do pure (.bool (← dNat l) (← dBool b))
  | .app "str" [l, s] => do pure (.str (← dNat l) (← dStr s))
  | .app "bytes" [l, b] => do pure (.bytes (← dNat l) (← dBytes b))
  | .app "noneLit" [l] => do pure (.noneLit (← dNat l))
  | .app "attr" [l, e, f] => do pure (.attr (← dNat l) (← dExpr e) (← dNat f))
  | .app "index" [l, e, i] => do pure (.index (← dNat l) (← dExpr e) (← dExpr i))
  | .app "slice" [l, e, lo, hi, st] => do
    pure (.slice (← dNat l) (← dExpr e) (← dOpt dExpr lo) (← dOpt dExpr hi) (← dOpt dExpr st))
  | .app "binop" [l, op, a, b] => do
    pure (.binop (← dNat l) (← dBinOp op) (← dExpr a) (← dExpr b))
  | .app "unop" [l, op, a] => do pure (.unop (← dNat l) (← dUnOp op) (← dExpr a))
  | .app "compare" [l, a, rest] => do
    pure (.compare (← dNat l) (← dExpr a) (← dList (dPair dCmpOp dExpr) rest))
  | .app "boolop" [l, op, xs] => do
    pure (.boolop (← dNat l) (← dBoolOp op) (← dList dExpr xs))
  | .app "call" [l, f, as] => do pure (.call (← dNat l) (← dExpr f) (← dList dArg as))
  | .app "ifExp" [l, c, a, b] => do
    pure (.ifExp (← dNat l) (← dExpr c) (← dExpr a) (← dExpr b))
  | .app "comp" [l, k, elt, gens] => do
    pure (.comp (← dNat l) (← dCompKind k) (← dExpr elt) (← dList dComp gens))
  | .app "lambda" [l, ps, b] => do pure (.lambda (← dNat l) (← dList dNat ps) (← dExpr b))
  | .app "list" [l, xs] => do pure (.list (← dNat l) (← dList dExpr xs))
  | .app "tuple" [l, xs] => do pure (.tuple (← dNat l) (← dList dExpr xs))
  | .app "dict" [l, kvs] => do pure (.dict (← dNat l) (← dList (dPair dExpr dExpr) kvs))
  | t => bad "expr" t

partial def dArg : Term → D Arg
  | .app "pos" [e] => .pos <$> dExpr e
  | .app "starred" [e] => .starred <$> dExpr e
  | .app "kw" [k, e] => do pure (.kw (← dNat k) (← dExpr e))
  | t => bad "arg" t

partial def dComp : Term → D Comprehension
  | .app "mk" [t, it, ifs] => do pure (.mk (← dTarget t) (← dExpr it) (← dList dExpr ifs))
  | t => bad "comprehension" t

partial def dTarget : Term → D Target
  | .app "name" [l, x] => do pure (.name (← dNat l) (← dNat x))
  | .app "attr" [l, e, f] => do pure (.attr (← dNat l) (← dExpr e) (← dNat f))
  | .app "index" [l, e, i] => do pure (.index (← dNat l) (← dExpr e) (← dExpr i))
  | .app "slice" [l, e, lo, hi] => do
    pure (.slice (← dNat l) (← dExpr e) (← dOpt dExpr lo) (← dOpt dExpr hi))
  | .app "tuple" [l, ts] => do pure (.tuple (← dNat l) (← dList dTarget ts))
  | t => bad "target" t

end

def dParams : Term → D Params
  | .record fs => do
    let get (k : String) : D Term := match fs.lookup k with
      | some v => .ok v
      | none => .error s!"params: missing {k}"
    pure { names := ← dList dNat (← get "names"), defaults := ← dList dExpr (← get "defaults"),
           vararg := ← dOpt dNat (← get "vararg") }
  | t => bad "params" t

partial def dStmt : Term → D Stmt
  | .app "assign" [l, ts, e] => do pure (.assign (← dNat l) (← dList dTarget ts) (← dExpr e))
  | .app "annAssign" [l, t, e] => do pure (.annAssign (← dNat l) (← dTarget t) (← dExpr e))
  | .app "augAssign" [l, t, op, e] => do
    pure (.augAssign (← dNat l) (← dTarget t) (← dBinOp op) (← dExpr e))
  | .app "exprStmt" [l, e] => do pure (.exprStmt (← dNat l) (← dExpr e))
  | .app "ifStmt" [l, c, a, b] => do
    pure (.ifStmt (← dNat l) (← dExpr c) (← dList dStmt a) (← dList dStmt b))
  | .app "forStmt" [l, t, it, b] => do
    pure (.forStmt (← dNat l) (← dTarget t) (← dExpr it) (← dList dStmt b))
  | .app "whileStmt" [l, c, b] => do
    pure (.whileStmt (← dNat l) (← dExpr c) (← dList dStmt b))
  | .app "ret" [l, e] => do pure (.ret (← dNat l) (← dOpt dExpr e))
  | .app "assert" [l, e] => do pure (.assert (← dNat l) (← dExpr e))
  | .app "raise" [l] => .raise <$> dNat l
  | .app "brk" [l] => .brk <$> dNat l
  | .app "cont" [l] => .cont <$> dNat l
  | .app "pass" [l] => .pass <$> dNat l
  | .app "funDef" [l, x, ps, b] => do
    pure (.funDef (← dNat l) (← dNat x) (← dParams ps) (← dList dStmt b))
  | t => bad "stmt" t

def dUintTy : Term → D UintTy
  | .app "width" [b] => .width <$> dNat b
  | .app "nominal" [n, b] => do pure (.nominal (← dNat n) (← dNat b))
  | t => bad "uint type" t

def dListKind : Term → D ListKind
  | .app "list" [] => .ok .list | .app "vector" [] => .ok .vector
  | .app "progressiveList" [] => .ok .progressiveList | .app "bitlist" [] => .ok .bitlist
  | .app "bitvector" [] => .ok .bitvector
  | .app "progressiveBitlist" [] => .ok .progressiveBitlist
  | .app "pyList" [] => .ok .pyList
  | t => bad "list kind" t

partial def dSszTy : Term → D SszTy
  | .app "uint" [u] => .uint <$> dUintTy u
  | .app "boolean" [] => .ok .boolean
  | .app "bytes" [n, len] => do pure (.bytes (← dNat n) (← dNat len))
  | .app "container" [n] => .container <$> dNat n
  | .app "list" [k, e, l] => do pure (.list (← dListKind k) (← dSszTy e) (← dOpt dNat l))
  | .app "any" [] => .ok .any
  | t => bad "ssz type" t

partial def dValue : Term → D Value
  | .app "int" [n] => .int <$> dInt n
  | .app "uint" [u, n] => do pure (.uint (← dUintTy u) (← dNat n))
  | .app "bool" [b] => .bool <$> dBool b
  | .app "boolean" [b] => .boolean <$> dBool b
  | .app "str" [s] => .str <$> dStr s
  | .app "none" [] => .ok .none
  | .app "bytes" [n, b] => do pure (.bytes (← dNat n) (← dBytes b))
  | .app "ref" [a] => .ref <$> dNat a
  | .app "tuple" [xs] => .tuple <$> dList dValue xs
  | .app "frozenDict" [kvs] => .frozenDict <$> dList (dPair dValue dValue) kvs
  | t => bad "value" t

def dHeapObj : Term → D HeapObj
  | .app "list" [k, e, l, xs] => do
    pure (.list (← dListKind k) (← dSszTy e) (← dOpt dNat l) (← dList dValue xs))
  | .app "container" [n, fs] => do pure (.container (← dNat n) (← dList dValue fs))
  | .app "dict" [kvs] => .dict <$> dList (dPair dValue dValue) kvs
  | .app "set" [xs] => .set <$> dList dValue xs
  | t => bad "heap object" t

def dBuiltin : Term → D Builtin
  | .app "len" [] => .ok .len | .app "range" [] => .ok .range
  | .app "enumerate" [] => .ok .enumerate | .app "zip" [] => .ok .zip
  | .app "sorted" [] => .ok .sorted | .app "min" [] => .ok .min | .app "max" [] => .ok .max
  | .app "sum" [] => .ok .sum | .app "any" [] => .ok .any | .app "all" [] => .ok .all
  | .app "filter" [] => .ok .filter | .app "list" [] => .ok .list
  | .app "tuple" [] => .ok .tuple | .app "set" [] => .ok .set | .app "dict" [] => .ok .dict
  | .app "bytes" [] => .ok .bytes | .app "int" [] => .ok .int | .app "bool" [] => .ok .bool
  | .app "sszSerialize" [] => .ok .sszSerialize | .app "sha256" [] => .ok .sha256
  | .app "hashTreeRoot" [] => .ok .hashTreeRoot
  | t => bad "builtin" t

def dModule : Term → D ModuleKind
  | .app "bls" [] => .ok .bls | .app "fork" [] => .ok .fork | .app "config" [] => .ok .config
  | t => bad "module" t

/-- `(.fn name params line [body])` is a spec function. -/
def dGlobal : Term → D Global
  | .app "fn" [n, ps, l, b] => do
    pure (.fn { name := ← dNat n, params := ← dParams ps, line := ← dNat l,
                body := ← dList dStmt b })
  | .app "builtin" [b] => .builtin <$> dBuiltin b
  | .app "type" [t] => .type <$> dSszTy t
  | .app "dataclass" [n] => .dataclass <$> dNat n
  | .app "const" [v] => .const <$> dValue v
  | .app "configVar" [] => .ok .configVar
  | .app "module" [k] => .module <$> dModule k
  | t => bad "global" t

end SpecLean.Fuzz
