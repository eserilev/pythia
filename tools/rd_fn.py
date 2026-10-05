"""Compile one spec function to readable Lean (SPEC 9.1, 4.2).

The output is a `do` block in the state-passing style:

- Each parameter that the function changes in place (`Footprint f`) is a `let mut` variable,
  and the function returns its final value after the result.
- A local name bound to a path from a variable is an alias: a read through it reads the path,
  and a write through it writes the path (SPEC 4.2).
- Each `for` and `while` loop becomes its own function: index loops recurse on `n - i`, while
  loops on a measure from `tools/while_measures.txt`, checked at each step.
"""

import ast
import dataclasses
import typing

import rd_types as T
import serialize as S


class Unsupported(Exception):
    pass


BUILTIN_FNS = {"len", "range", "enumerate", "zip", "sorted", "min", "max", "sum", "any", "all",
               "filter", "list", "tuple", "set", "dict", "bytes", "int", "bool"}

OPS = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul", ast.FloorDiv: "floorDiv",
       ast.Mod: "mod", ast.Pow: "pow", ast.BitAnd: "bitAnd", ast.BitOr: "bitOr",
       ast.BitXor: "bitXor", ast.LShift: "lShift", ast.RShift: "rShift"}
CMP = {ast.Lt: "<", ast.LtE: "≤", ast.Gt: ">", ast.GtE: "≥"}


def join(a, b):
    """The type of a variable that gets values of types `a` and `b`."""
    if a is None:
        return b
    if b is None or a == b:
        return a
    if a == T.INT and b[0] == "uint":
        return b
    if b == T.INT and a[0] == "uint":
        return a
    if a[0] == "uint" and b[0] == "uint":
        return T.derive(a, b)
    if a[0] == "list" and b[0] == "list":
        e = join(a[1], b[1])
        return ("list", e, a[2] or b[2])
    if a[0] == "set" and b[0] == "set":
        return ("set", join(a[1], b[1]))
    if a[0] == "option":
        return ("option", join(a[1], b[1] if b[0] == "option" else b))
    if b[0] == "option":
        return ("option", join(a, b[1]))
    if a == T.NONE:
        return ("option", b)
    if b == T.NONE:
        return ("option", a)
    return a


class Sig:
    """The Lean signature of a spec function."""

    def __init__(self, name, params, defaults, ret, mutated, generic):
        self.name = name
        self.params = params            # [(name, type)]
        self.defaults = defaults        # {name: ast default}
        self.ret = ret                  # type
        self.mutated = mutated          # sorted parameter indices
        self.generic = generic          # parameter names of a generic uint class


def out_types(sig):
    ts = ([sig.ret] if sig.ret != T.NONE else []) + [sig.params[j][1] for j in sig.mutated]
    return ts


class Fn:
    """The compiler state of one function."""

    def __init__(self, em, sig, tree):
        self.em, self.b, self.sig, self.tree = em, em.b, sig, tree
        self.names = self.b.names
        self.vars = {p: t for p, t in sig.params}
        self.aliases = {}
        self.lines = []
        self.ind = 1
        self.tmp = 0
        self.loops = []          # emitted loop functions
        self.base_ind = 1
        self.body_start = 0
        self.hoisted = {}
        self.loop_no = 0
        self.mutable = set()
        self.in_loop = None      # the loop context while compiling a loop body
        self.declared = set(p for p, _ in sig.params)

    # --- helpers -------------------------------------------------------------------------

    def fresh(self, base="t"):
        self.tmp += 1
        return f"{base}{self.tmp}"

    def line(self, s):
        self.lines.append("  " * self.ind + s)

    def lean(self, t):
        if t is None:
            raise Unsupported("unknown type")
        if t[0] == "list" and t[1] is None:
            raise Unsupported("list of unknown element type")
        if t == T.ANY:
            return "SszObj"
        if t[0] == "uint" and self.sig.generic and t[1] is None:
            return "α"
        return self.names.lean(t)

    # --- types ---------------------------------------------------------------------------

    def field_type(self, c, f):
        if T.is_container_cls(c):
            for name, ft in c._FIELD_TYPES:
                if name == f:
                    return T.of_class(ft)
        elif dataclasses.is_dataclass(c):
            hints = dict(self.b.dataclass_fields[c])
            if f in hints:
                from rd_emit import type_of_hint
                return type_of_hint(self.b, hints[f])
        raise Unsupported(f"field {f} of {c.__name__}")

    def ty(self, e):
        """The static type of an expression, or None when it is not known yet."""
        b = self.b
        match e:
            case ast.Constant(value=v):
                if v is None:
                    return T.NONE
                if type(v) is bool:
                    return T.BOOL
                if type(v) is int:
                    return T.INT
                if type(v) is bytes:
                    return T.BYTES
                if type(v) is str:
                    return T.STR
            case ast.Name(id=x):
                if x in self.aliases:
                    return self.aliases[x][1]
                if x in self.vars:
                    return self.vars[x]
                if x in b.const_types:
                    return b.const_types[x]
                if x in b.config_types:
                    return b.config_types[x]
                return None
            case ast.Attribute(value=ast.Name(id="config"), attr=f):
                return b.config_types[f]
            case ast.Attribute(value=ast.Name(id="bls"), attr=f):
                return T.BYTES
            case ast.Attribute(value=o, attr=f):
                ot = self.ty(o)
                if ot is None:
                    return None
                if ot[0] == "container":
                    return self.field_type(ot[1], f)
                return None
            case ast.Subscript(value=o, slice=ast.Slice()):
                ot = self.ty(o)
                if ot is None:
                    return None
                if ot[0] == "list":
                    li = T.list_info(ot[2]) if ot[2] else None
                    if li and li[0] == "vector":
                        return ("list", ot[1], None)
                    return ot
                if ot[0] in ("bytes", "bytesN"):
                    return T.BYTES
            case ast.Subscript(value=o, slice=i):
                ot = self.ty(o)
                if ot is None:
                    return None
                if ot[0] in ("list", "set"):
                    return ot[1]
                if ot[0] in ("bytes", "bytesN"):
                    return T.INT
                if ot[0] == "dict":
                    return ot[2]
                if ot[0] == "tuple" and isinstance(i, ast.Constant):
                    return ot[1][i.value]
                if ot[0] == "record" and isinstance(i, ast.Constant):
                    return dict(ot[2])[i.value]
            case ast.BinOp(left=l, op=op, right=r):
                lt, rt = self.ty(l), self.ty(r)
                if lt is None or rt is None:
                    return None
                if lt[0] == "uint" and rt[0] == "uint":
                    return T.derive(lt, rt)
                if lt[0] == "uint" and rt in (T.INT, T.BOOL):
                    return lt
                if rt[0] == "uint" and lt == T.INT:
                    return rt
                if lt == T.BOOL and rt[0] == "uint":
                    return T.INT
                if lt in (T.INT, T.BOOL) and rt in (T.INT, T.BOOL):
                    return T.INT
                if lt[0] in ("bytes", "bytesN") and rt[0] in ("bytes", "bytesN"):
                    return T.BYTES
                if lt[0] in ("bytes", "bytesN") and rt == T.INT:
                    return T.BYTES
                if lt[0] == "list" and rt[0] == "list":
                    return ("list", join(lt[1], rt[1]), lt[2])
                if lt[0] == "list" and rt == T.INT:
                    return ("list", lt[1], None)
                if lt[0] == "tuple" and rt[0] == "tuple":
                    return ("tuple", lt[1] + rt[1])
                return None
            case ast.UnaryOp(op=ast.Not()):
                return T.BOOL
            case ast.UnaryOp(operand=o):
                ot = self.ty(o)
                return T.INT if ot is not None else None
            case ast.Compare():
                return T.BOOL
            case ast.BoolOp(values=vs):
                ts = [self.ty(v) for v in vs]
                if all(t in (T.BOOL, T.BOOLEAN) for t in ts):
                    return T.BOOL
                out = None
                for t in ts:
                    out = join(out, t)
                return out
            case ast.IfExp(test=ast.Compare(left=ast.Name(id=x), ops=[ast.Is()],
                                            comparators=[ast.Constant(value=None)]),
                           body=a, orelse=ast.Name(id=y)) if x == y:
                return self.ty(a)
            case ast.IfExp(body=a, orelse=c):
                return join(self.ty(a), self.ty(c))
            case ast.ListComp(elt=elt, generators=gens) | ast.GeneratorExp(elt=elt, generators=gens):
                return ("list", self.comp_elt_ty(elt, gens), None)
            case ast.SetComp(elt=elt, generators=gens):
                return ("set", self.comp_elt_ty(elt, gens))
            case ast.List(elts=es):
                out = None
                for x in es:
                    out = join(out, self.ty(x))
                return ("list", out, None)
            case ast.Tuple(elts=es):
                return ("tuple", tuple(self.ty(x) for x in es))
            case ast.Dict(keys=ks, values=vs):
                return ("dict", self.ty(ks[0]) if ks else None, self.ty(vs[0]) if vs else None)
            case ast.Call():
                return self.call_ty(e)
        return None

    def comp_elt_ty(self, elt, gens):
        saved = dict(self.vars)
        try:
            for g in gens:
                self.bind_iter_types(g.target, g.iter)
            return self.ty(elt)
        finally:
            self.vars = saved

    def iter_elem_ty(self, it):
        """The element type of an iterable, and the element types of `enumerate` and `zip`."""
        match it:
            case ast.Call(func=ast.Name(id="enumerate"), args=[x]):
                t = self.ty(x)
                return ("tuple", (T.INT, t[1] if t else None))
            case ast.Call(func=ast.Name(id="zip"), args=xs):
                return ("tuple", tuple(self.iter_elem_ty(x) for x in xs))
            case ast.Call(func=ast.Name(id="range")):
                return T.INT
        t = self.ty(it)
        if t is None:
            return None
        if t[0] == "tuple":
            out = None
            for x in t[1]:
                out = join(out, x)
            return out
        if t[0] in ("list", "set"):
            return t[1]
        if t[0] == "dict":
            return t[1]
        if t[0] in ("bytes", "bytesN"):
            return T.INT
        return None

    def bind_iter_types(self, target, it):
        self.bind_target_type(target, self.iter_elem_ty(it))

    def bind_target_type(self, target, t):
        match target:
            case ast.Name(id=x):
                self.vars[x] = join(self.vars.get(x), t)
            case ast.Tuple(elts=es) | ast.List(elts=es):
                for i, x in enumerate(es):
                    sub = t[1][i] if t and t[0] == "tuple" and i < len(t[1]) else None
                    self.bind_target_type(x, sub)

    def call_ty(self, e):
        b = self.b
        f = e.func
        match f:
            case ast.Name(id=n) if n in self.em.sigs:
                sig = self.em.sigs[n]
                if n == "saturating_sub":
                    return self.ty(e.args[0])
                return sig.ret
            case ast.Name(id="ssz_serialize"):
                return T.BYTES
            case ast.Name(id=n) if n in S.ORACLE_FUNCTIONS:
                return ("bytesN", b.spec.Root) if n == "hash_tree_root" else ("bytesN", b.spec.Bytes32)
            case ast.Name(id=n) if n in S.BLS_FUNCTIONS:
                return ("bytesN", b.spec.BLSPubkey)
            case ast.Name(id=n) if n in BUILTIN_FNS:
                args = e.args
                if n in ("len", "int"):
                    return T.INT
                if n in ("any", "all", "bool"):
                    return T.BOOL
                if n == "bytes":
                    return T.BYTES
                if n == "range":
                    return ("list", T.INT, None)
                if n in ("list", "sorted", "filter"):
                    src = args[-1] if n == "filter" else args[0]
                    return ("list", self.iter_elem_ty(src), None)
                if n == "set":
                    return ("set", self.iter_elem_ty(args[0]) if args else None)
                if n == "tuple":
                    return ("list", self.iter_elem_ty(args[0]), None)
                if n in ("min", "max"):
                    if len(args) == 1:
                        return self.iter_elem_ty(args[0])
                    out = None
                    for a in args:
                        out = join(out, self.ty(a))
                    return out
                if n == "sum":
                    return self.iter_elem_ty(args[0]) if len(args) == 1 else self.ty(args[1])
                if n == "enumerate":
                    return ("list", self.iter_elem_ty(e), None)
                if n == "zip":
                    return ("list", self.iter_elem_ty(e), None)
                if n == "dict":
                    return ("dict", None, None)
            case ast.Name(id=n):
                c = getattr(b.spec, n, None)
                if isinstance(c, type) and T.of_class(c) is not None:
                    return T.of_class(c)
            case ast.Attribute(value=ast.Name(id="bls"), attr=m):
                if m in ("Verify", "FastAggregateVerify", "AggregateVerify", "KeyValidate"):
                    return T.BOOL
                return T.BYTES
            case ast.Attribute(value=ast.Name(id="int"), attr="from_bytes"):
                return T.INT
            case ast.Attribute(value=ast.Name(id=mod), attr=fn) if mod in S.FORK_MODULES:
                if fn in self.em.sigs:
                    return self.em.sigs[fn].ret
            case ast.Attribute(value=ast.Name(id=n), attr="empty"):
                c = getattr(b.spec, n, None)
                return T.of_class(c)
            case ast.Attribute(value=o, attr=m):
                ot = self.ty(o)
                if m == "copy":
                    return ot
                if m in ("index", "count"):
                    return T.INT
                if m == "hash_tree_root":
                    return ("bytesN", b.spec.Root)
                if m in ("union", "intersection"):
                    return ot
                if m in ("append", "extend", "add"):
                    return T.NONE
        return None

    # --- type inference over the body ---------------------------------------------------

    def infer(self, stmts):
        for _ in range(4):
            before = dict(self.vars)
            self.infer_block(stmts)
            if self.vars == before:
                return

    def infer_block(self, stmts):
        for s in stmts:
            self.infer_stmt(s)

    def infer_stmt(self, s):
        match s:
            case ast.Assign(targets=ts, value=v):
                t = self.ty(v)
                for x in ts:
                    self.bind_target_type(x, t)
            case ast.AnnAssign(target=x, annotation=a, value=v):
                from rd_emit import type_of_annotation
                t = type_of_annotation(self.b, a)
                if isinstance(x, ast.Name):
                    self.vars[x.id] = t
            case ast.AugAssign(target=ast.Name(id=x), op=op, value=v):
                t = self.ty(ast.BinOp(left=ast.Name(id=x), op=op, right=v))
                self.vars[x] = join(self.vars.get(x), t)
            case ast.For(target=x, iter=it, body=bd, orelse=o):
                self.bind_iter_types(x, it)
                self.infer_block(bd + o)
            case ast.While(body=bd, orelse=o) | ast.If(body=bd, orelse=o):
                self.infer_block(bd + o)
            case ast.Expr(value=ast.Call(func=ast.Attribute(value=ast.Name(id=x), attr="append"),
                                         args=[v])):
                if x in self.vars and self.vars[x] and self.vars[x][0] == "list":
                    lt = self.vars[x]
                    self.vars[x] = ("list", join(lt[1], self.ty(v)), lt[2])
            case ast.Expr(value=ast.Call(func=ast.Attribute(value=ast.Name(id=x), attr="add"),
                                         args=[v])):
                if x in self.vars and self.vars[x] and self.vars[x][0] == "set":
                    self.vars[x] = ("set", join(self.vars[x][1], self.ty(v)))

    # --- conversions -----------------------------------------------------------------------

    def conv(self, code, src, dst):
        """`code` of type `src` as a value of type `dst`, as Python passes it."""
        if dst is None or src is None or src == dst:
            return code
        if dst[0] in ("tvar", "utvar") or src[0] in ("tvar", "utvar"):
            return code
        if dst[0] == "list" and dst[1] and dst[1][0] == "tvar":
            return code
        if src[0] in ("list", "set") and (src[1] is None or len(dst) < 2 or dst[1] is None):
            return code
        if src[0] == "dict" and (None in src[1:] or None in dst[1:]):
            return code
        ks, kd = src[0], dst[0]
        L = self.lean
        if kd == "uint":
            if ks == "int":
                return f"(← uOf {L(dst)} {code})"
            if ks == "uint":
                if src[1].BITS == dst[1].BITS:
                    return f"(⟨({code}).val⟩ : {L(dst)})"
                return f"(← uCast {L(dst)} {code})"
            if ks == "boolean":
                return f"(⟨if ({code}).val then 1 else 0⟩ : {L(dst)})"
        if kd == "int":
            if ks == "uint":
                return f"(uv {code})"
            if ks == "bool":
                return f"(if {code} then (1 : Int) else 0)"
        if kd == "boolean" and ks == "bool":
            return f"(⟨{code}⟩ : Boolean)"
        if kd == "boolean" and ks == "int":
            return f"(← booleanOfInt {code})"
        if kd == "bool" and ks == "boolean":
            return f"({code}).val"
        if kd == "bytesN":
            if ks == "bytes":
                return f"(← bytesOf {L(dst)} {code})"
            if ks == "bytesN":
                if src[1].LENGTH == dst[1].LENGTH:
                    return f"(⟨bd {code}⟩ : {L(dst)})"
                return f"(← bytesOf {L(dst)} (bd {code}))"
        if kd == "bytes" and ks == "bytesN":
            return f"(bd {code})"
        if kd in ("list", "set") and ks in ("list", "set"):
            if src[1] is None or dst[1] is None or L(src[1]) == L(dst[1]):
                return code
            inner = self.conv("x", src[1], dst[1])
            if "(←" in inner:
                return f"(← ({code}).mapM fun x => do pure {inner})"
            return f"(({code}).map fun x => {inner})"
        if kd == "option":
            if ks == "none":
                return "none"
            if ks == "option":
                return code
            return f"(some {self.conv(code, src, dst[1])})"
        if kd == "any":
            return f"(⟨{self.enc_of(src)} {code}⟩ : SszObj)"
        if kd == "tuple" and ks == "tuple" and len(src[1]) == len(dst[1]):
            parts = [self.conv(self.proj(code, i, len(src[1])), a, b)
                     for i, (a, b) in enumerate(zip(src[1], dst[1]))]
            return "(" + ", ".join(parts) + ")"
        if L(src) == L(dst):
            return code
        raise Unsupported(f"conversion {src} -> {dst}")

    def proj(self, code, i, n):
        """Component `i` of an `n`-tuple."""
        out = code
        for _ in range(i):
            out = f"({out}).2"
        return out if i == n - 1 else f"({out}).1"

    def enc_of(self, t):
        from translate import enc_term
        if t[0] in ("uint", "bytesN", "container"):
            return enc_term(self.b, t[1])
        if t == T.BOOLEAN:
            return "encBoolean"
        if t[0] == "list" and t[2] is not None:
            return enc_term(self.b, t[2])
        raise Unsupported(f"no SSZ class for {t}")

    def truth(self, code, t):
        if t is None or t == T.BOOL:
            return code
        k = t[0]
        if k == "boolean":
            return f"({code}).val"
        if k == "int":
            return f"({code} != 0)"
        if k == "uint":
            return f"(({code}).val != 0)"
        if k in ("list", "set", "dict", "bytes"):
            return f"!({code}).isEmpty"
        if k == "bytesN":
            return f"!(bd {code}).isEmpty"
        if k == "option":
            return f"({code}).isSome"
        if k == "container":
            return "true"
        raise Unsupported(f"truth of {t}")

    def as_int(self, e):
        t = self.ty(e)
        return self.conv(self.ex(e), t, T.INT)

    def num(self, e, cls_t):
        """An operand of a uint operator in class `cls_t`, as an `Int`."""
        t = self.ty(e)
        code = self.ex(e)
        if t is None:
            raise Unsupported("operand of unknown type")
        if t[0] == "uint":
            return f"(uv {code})"
        if t == T.BOOL:
            return f"(if {code} then (1 : Int) else 0)"
        return code

    # --- expressions -----------------------------------------------------------------------

    def use(self, x):
        if self.in_loop is not None:
            self.in_loop.read(x)

    def ex(self, e, want=None):
        code = self.ex0(e)
        if want is not None:
            return self.conv(code, self.ty(e), want)
        return code

    def ex0(self, e):
        b = self.b
        match e:
            case ast.Constant(value=v):
                if v is None:
                    return "()"
                if type(v) is bool:
                    return "true" if v else "false"
                if type(v) is int:
                    return f"({v} : Int)"
                if type(v) is bytes:
                    return "[" + ", ".join(str(x) for x in v) + "]"
                if type(v) is str:
                    return S.lean_str(v)
            case ast.Name(id=x):
                if x in self.aliases:
                    return self.rd(*self.aliases[x])
                if x in self.vars:
                    self.use(x)
                    return T.ident(x)
                if x in b.const_types:
                    return T.ident(x)
                if x in b.config_types:
                    return f"Cfg.{T.ident(x)}"
                raise Unsupported(f"name {x}")
            case ast.Attribute(value=ast.Name(id="config"), attr=f):
                return f"Cfg.{T.ident(f)}"
            case ast.Attribute(value=ast.Name(id="bls"), attr=f):
                return self.em.value_term(getattr(b.spec.bls, f), T.BYTES)
            case ast.Attribute(value=o, attr=f):
                return f"({self.ex(o)}).{T.ident(f)}"
            case ast.Subscript(value=o, slice=ast.Slice(lower=lo, upper=hi, step=None)):
                ot = self.ty(o)
                base = self.ex(o)
                if ot[0] == "bytesN":
                    base = f"(bd {base})"
                lo_c = f"(some {self.as_int(lo)})" if lo is not None else "none"
                hi_c = f"(some {self.as_int(hi)})" if hi is not None else "none"
                return f"(lslice {base} {lo_c} {hi_c})"
            case ast.Subscript(value=o, slice=i):
                ot = self.ty(o)
                if ot is None:
                    raise Unsupported("subscript of unknown type")
                if ot[0] in ("list", "set"):
                    return f"(← lget {self.ex(o)} {self.as_int(i)})"
                if ot[0] == "bytes":
                    return f"(← bget {self.ex(o)} {self.as_int(i)})"
                if ot[0] == "bytesN":
                    return f"(← bget (bd {self.ex(o)}) {self.as_int(i)})"
                if ot[0] == "tuple" and isinstance(i, ast.Constant):
                    return self.proj(self.ex(o), i.value, len(ot[1]))
                if ot[0] == "dict":
                    return f"(← dget {self.ex(o)} {self.ex(i, ot[1])})"
                if ot[0] == "record":
                    return f"({self.ex(o)}).{T.ident(i.value)}"
            case ast.BinOp():
                return self.binop(e)
            case ast.UnaryOp(op=ast.Not(), operand=o):
                return f"(!{self.truth(self.ex(o), self.ty(o))})"
            case ast.UnaryOp(op=ast.USub(), operand=o):
                return f"(-{self.as_int(o)})"
            case ast.UnaryOp(op=ast.Invert(), operand=o):
                return f"(Int.not {self.as_int(o)})"
            case ast.Compare():
                return self.compare(e)
            case ast.BoolOp(op=op, values=vs):
                if self.ty(e) != T.BOOL:
                    raise Unsupported("and/or of values that are not bool")
                acc = self.truth(self.ex(vs[-1]), self.ty(vs[-1]))
                for v in reversed(vs[:-1]):
                    cur = self.truth(self.ex(v), self.ty(v))
                    if "(←" in acc:
                        if isinstance(op, ast.And):
                            acc = f"(← (if {cur} then (do pure {acc}) else pure false : SpecM Bool))"
                        else:
                            acc = f"(← (if {cur} then pure true else (do pure {acc}) : SpecM Bool))"
                    else:
                        acc = f"({cur} {'&&' if isinstance(op, ast.And) else '||'} {acc})"
                return acc
            case ast.IfExp(test=ast.Compare(left=ast.Name(id=x), ops=[ast.Is()],
                                            comparators=[ast.Constant(value=None)]),
                           body=a, orelse=ast.Name(id=y)) if x == y:
                t = self.ty(e)
                self.lazy = getattr(self, "lazy", 0) + 1
                try:
                    ca = self.ex(a, t)
                finally:
                    self.lazy -= 1
                return (f"(← (match {T.ident(x)} with | some v => pure v | none => "
                        f"(do pure {ca}) : SpecM {self.lean(t)}))")
            case ast.IfExp(test=c, body=a, orelse=d):
                t = self.ty(e)
                ca, cd = self.ex(a, t), self.ex(d, t)
                cc = self.truth(self.ex(c), self.ty(c))
                if "(←" in ca or "(←" in cd:
                    return (f"(← (if {cc} then (do pure {ca}) else (do pure {cd}) : "
                            f"SpecM {self.lean(t)}))")
                return f"(if {cc} then {ca} else {cd})"
            case ast.ListComp(elt=elt, generators=gens) | ast.GeneratorExp(elt=elt, generators=gens):
                return self.comp(elt, gens, self.ty(e)[1])
            case ast.SetComp(elt=elt, generators=gens):
                return f"(dedup {self.comp(elt, gens, self.ty(e)[1])})"
            case ast.List(elts=es):
                t = self.ty(e)
                return "[" + ", ".join(self.ex(x, t[1]) for x in es) + "]"
            case ast.Tuple(elts=es):
                return "(" + ", ".join(self.ex(x) for x in es) + ")"
            case ast.Dict(keys=ks, values=vs):
                if not ks:
                    return "[]"
                return "[" + ", ".join(f"({self.ex(k)}, {self.ex(v)})" for k, v in zip(ks, vs)) + "]"
            case ast.Call():
                return self.call(e)
        raise Unsupported(f"expression {ast.unparse(e)}")

    def binop(self, e):
        l, r, op = e.left, e.right, e.op
        lt, rt, t = self.ty(l), self.ty(r), self.ty(e)
        if t is None:
            raise Unsupported(f"binop of unknown type: {ast.unparse(e)}")
        name = OPS[type(op)]
        if t[0] == "uint":
            return f"(← (uOp .{name} {self.num(l, t)} {self.num(r, t)} : SpecM {self.lean(t)}))"
        if t == T.INT:
            a, c = self.as_int(l), self.as_int(r)
            if name in ("add", "sub", "mul"):
                sym = {"add": "+", "sub": "-", "mul": "*"}[name]
                return f"({a} {sym} {c})"
            return f"(← iOp .{name} {a} {c})"
        if t == T.BYTES:
            if name == "add":
                return f"({self.ex(l, T.BYTES)} ++ {self.ex(r, T.BYTES)})"
            if name == "mul":
                return f"(List.replicate ({self.as_int(r)}).toNat {self.ex(l, T.BYTES)}).flatten"
        if t[0] == "list":
            if name == "add":
                code = f"({self.ex(l, t)} ++ {self.ex(r, t)})"
                li = T.list_info(t[2]) if t[2] else None
                if li and li[2] is not None and li[0] == "list":
                    return f"(← lcheck {code} {li[2]})"
                return code
            if name == "mul":
                if isinstance(l, ast.List) and len(l.elts) == 1:
                    return f"(List.replicate ({self.as_int(r)}).toNat {self.ex(l.elts[0], t[1])})"
                return f"(List.replicate ({self.as_int(r)}).toNat {self.ex(l, t)}).flatten"
        if t[0] == "tuple" and name == "add":
            raise Unsupported("tuple +")
        raise Unsupported(f"binop {ast.unparse(e)} on {lt}, {rt}")

    def cmp1(self, a, op, c):
        at, ct = self.ty(a), self.ty(c)
        if isinstance(op, (ast.Is, ast.IsNot)):
            neg = isinstance(op, ast.IsNot)
            if isinstance(c, ast.Constant) and c.value is None:
                return f"({self.ex(a)}).{'isSome' if neg else 'isNone'}"
            raise Unsupported("is")
        if isinstance(op, (ast.In, ast.NotIn)):
            neg = "!" if isinstance(op, ast.NotIn) else ""
            if ct[0] == "dict":
                return f"{neg}(({self.ex(c)}).any fun p => p.1 == {self.ex(a, ct[1])})"
            if ct[0] in ("bytes", "bytesN"):
                raise Unsupported("in bytes")
            if ct[0] == "tuple":
                et = self.iter_elem_ty(c)
                items = ", ".join(self.ex(x, et) for x in c.elts)
                return f"{neg}([{items}].contains {self.ex(a, et)})"
            return f"{neg}(({self.ex(c)}).contains {self.ex(a, ct[1])})"
        num = lambda t: t is not None and t[0] in ("uint", "int", "bool")
        if num(at) and num(ct) and not (at == T.BOOL and ct == T.BOOL and
                                        isinstance(op, (ast.Eq, ast.NotEq))):
            x, y = self.as_int(a), self.as_int(c)
            if isinstance(op, ast.Eq):
                return f"({x} == {y})"
            if isinstance(op, ast.NotEq):
                return f"({x} != {y})"
            return f"(decide ({x} {CMP[type(op)]} {y}))"
        if at and ct and at[0] in ("bytes", "bytesN") and ct[0] in ("bytes", "bytesN"):
            x, y = self.ex(a, T.BYTES), self.ex(c, T.BYTES)
        else:
            x, y = self.ex(a), self.ex(c, at)
        if isinstance(op, ast.Eq):
            return f"({x} == {y})"
        if isinstance(op, ast.NotEq):
            return f"({x} != {y})"
        if at and at[0] in ("bytes", "bytesN"):
            o = CMP[type(op)]
            if o in ("<", ">"):
                return f"(PyOrd.lt {x if o == '<' else y} {y if o == '<' else x})"
        raise Unsupported(f"compare {ast.unparse(a)} {type(op).__name__}")

    def compare(self, e):
        parts = []
        left = e.left
        for op, right in zip(e.ops, e.comparators):
            parts.append(self.cmp1(left, op, right))
            left = right
        return parts[0] if len(parts) == 1 else "(" + " && ".join(parts) + ")"

    def comp(self, elt, gens, et):
        """A comprehension: `filterMapM` over each generator, live over the source."""
        saved = dict(self.vars)
        saved_al = dict(self.aliases)
        try:
            return self.comp_rec(elt, gens, et)
        finally:
            self.vars = saved
            self.aliases = saved_al

    def comp_rec(self, elt, gens, et):
        g = gens[0]
        it_code, pat = self.iter_value(g.target, g.iter)
        self.bind_iter_types(g.target, g.iter)
        for x in names_of(g.target):
            self.aliases.pop(x, None)
        conds = [self.truth(self.ex(c), self.ty(c)) for c in g.ifs]
        cond = " && ".join(conds) if conds else None
        if len(gens) == 1:
            body = self.ex(elt, et)
            if cond is None:
                if "(←" in body:
                    return f"(← ({it_code}).mapM fun {pat} => do pure {body})"
                return f"(({it_code}).map fun {pat} => {body})"
            if "(←" in body or "(←" in cond:
                return (f"(← ({it_code}).filterMapM fun {pat} => do "
                        f"if {cond} then (do pure (some {body})) else pure none)")
            return f"(({it_code}).filterMap fun {pat} => if {cond} then some {body} else none)"
        inner = self.comp_rec(elt, gens[1:], et)
        keep = f"if {cond} then (do pure {inner}) else pure []" if cond else f"pure {inner}"
        return f"(← ({it_code}).flatMapM fun {pat} => do {keep})"

    def iter_value(self, target, it):
        """The list to iterate over as a value, and the binder for each element."""
        pat = binder(target)
        match it:
            case ast.Call(func=ast.Name(id="enumerate"), args=[x]):
                return f"(({self.ex(x)}).zipIdx.map fun (v, i) => ((i : Int), v))", pat
            case ast.Call(func=ast.Name(id="zip"), args=xs):
                cs = [self.iter_value(ast.Name(id="_"), x)[0] for x in xs]
                if len(cs) != 2:
                    raise Unsupported("zip of more than 2")
                return f"(({cs[0]}).zip {cs[1]})", pat
            case ast.Call(func=ast.Name(id="range"), args=args):
                return self.range_code(args), pat
        if isinstance(it, ast.Tuple):
            et = self.iter_elem_ty(it)
            return "[" + ", ".join(self.ex(x, et) for x in it.elts) + "]", pat
        t = self.ty(it)
        code = self.ex(it)
        if t and t[0] == "bytesN":
            code = f"((bd {code}).map fun b => (b.toNat : Int))"
        elif t and t[0] == "bytes":
            code = f"(({code}).map fun b => (b.toNat : Int))"
        return code, pat

    def range_code(self, args):
        ints = [self.as_int(a) for a in args]
        if len(ints) == 1:
            ints = ["0", ints[0], "1"]
        elif len(ints) == 2:
            ints = ints + ["1"]
        return f"(← pyRange {ints[0]} {ints[1]} {ints[2]})"

    # --- calls -----------------------------------------------------------------------------

    def args_of(self, sig, e):
        """The argument expressions of a call of `sig`, in parameter order, with defaults."""
        pos = list(e.args)
        kws = {k.arg: k.value for k in e.keywords}
        out = []
        for j, (p, _) in enumerate(sig.params):
            if j < len(pos):
                out.append(pos[j])
            elif p in kws:
                out.append(kws[p])
            elif p in sig.defaults:
                out.append(sig.defaults[p])
            else:
                raise Unsupported(f"missing argument {p} of {sig.name}")
        return out

    def call_spec(self, n, e):
        sig = self.em.sigs[n]
        args = self.args_of(sig, e)
        codes = []
        for (p, pt), a in zip(sig.params, args):
            if p in sig.generic:
                codes.append(self.ex(a))
            elif pt == T.INT and sig.generic:
                codes.append(self.as_int(a))
            else:
                codes.append(self.ex(a, pt))
        call = f"{T.ident(n)} {' '.join(codes)}".strip()
        outs = out_types(sig)
        want = self.call_ty(e)
        if not sig.mutated:
            if sig.ret == T.NONE:
                if self.hoist_ok():
                    self.line(f"let _ ← {call}")
                    return "()"
                return f"(← {call})"
            return self.conv(f"(← {call})", sig.ret, want)
        if not self.hoist_ok():
            raise Unsupported(f"call of {n}, which writes, inside a lazy expression")
        tmp = self.fresh("r")
        self.line(f"let {tmp} ← {call}")
        k = 1 if sig.ret != T.NONE else 0
        for idx, j in enumerate(sig.mutated):
            comp = self.proj(tmp, k + idx, len(outs)) if len(outs) > 1 else tmp
            self.write_back(args[j], comp, sig.params[j][1])
        if sig.ret == T.NONE:
            return "()"
        return self.proj(tmp, 0, len(outs)) if len(outs) > 1 else tmp

    def hoist_ok(self):
        return getattr(self, "lazy", 0) == 0

    def write_back(self, arg, code, pt):
        """After a call, the new value of an argument that the callee changed."""
        path = self.path_of(arg)
        if path is None:
            return
        at = self.ty(arg)
        self.wr(path, self.conv(code, pt, at))

    def call(self, e):
        b = self.b
        f = e.func
        args = e.args
        kws = {k.arg: k.value for k in e.keywords}
        match f:
            case ast.Name(id=n) if n in self.em.sigs:
                return self.call_spec(n, e)
            case ast.Name(id="hash_tree_root"):
                return f"(← bytesOf Root (← {self.htr_of(args[0])}))"
            case ast.Name(id="sha256"):
                return f"(← bytesOf Bytes32 (Spec.sha256 {self.ex(args[0], T.BYTES)}))"
            case ast.Name(id="ssz_serialize"):
                t = self.ty(args[0])
                x = self.ex(args[0])
                if t == T.BOOLEAN:
                    return f"[if ({x}).val then 1 else 0]"
                if t[0] == "utvar":
                    return f"(toLE (UintC.val {x}) (UintC.bits {t[1]} / 8))"
                return f"(toLE ({x}).val {t[1].BITS // 8})"
            case ast.Name(id="eth_aggregate_pubkeys"):
                return (f"(← bytesOf BLSPubkey (Spec.blsAggregatePKs "
                        f"(({self.ex(args[0])}).map bd)))")
            case ast.Name(id=n) if n in BUILTIN_FNS:
                return self.builtin(n, e)
            case ast.Name(id=n):
                c = getattr(b.spec, n, None)
                if isinstance(c, type) and T.of_class(c) is not None:
                    return self.construct(c, args, kws)
            case ast.Attribute(value=ast.Name(id="bls"), attr=m):
                a = [self.ex(x) for x in args]
                ts = [self.ty(x) for x in args]
                bs = [self.conv(c, t, T.BYTES) if t and t[0] in ("bytesN", "bytes") else c
                      for c, t in zip(a, ts)]
                lst = lambda c: f"(({c}).map bd)"
                if m == "Verify":
                    return f"(Spec.blsVerify {bs[0]} {bs[1]} {bs[2]})"
                if m == "FastAggregateVerify":
                    return f"(Spec.blsFastAggregateVerify {lst(a[0])} {bs[1]} {bs[2]})"
                if m == "AggregateVerify":
                    return f"(Spec.blsAggregateVerify {lst(a[0])} {lst(a[1])} {bs[2]})"
                if m == "KeyValidate":
                    return f"(Spec.blsKeyValidate {bs[0]})"
                if m in ("bytes48_to_G1", "G1_to_bytes48"):
                    return bs[0]
                if m == "neg":
                    return f"(Spec.blsG1Neg {bs[0]})"
                if m == "add":
                    return f"(Spec.blsG1Add {bs[0]} {bs[1]})"
            case ast.Attribute(value=ast.Name(id="int"), attr="from_bytes"):
                return f"(fromLE {self.ex(args[0], T.BYTES)})"
            case ast.Attribute(value=ast.Name(id=mod), attr=fn) if mod in S.FORK_MODULES:
                return self.ex(self.inline(fn, args))
            case ast.Attribute(value=ast.Name(id=n), attr="empty"):
                c = getattr(b.spec, n)
                return f"(default : {self.lean(T.of_class(c))})"
            case ast.Attribute(value=o, attr=m):
                ot = self.ty(o)
                if m == "copy":
                    return self.ex(o)
                if m == "index":
                    return f"(← lindex {self.ex(o)} {self.ex(args[0], ot[1])})"
                if m == "count":
                    return f"(lcount {self.ex(o)} {self.ex(args[0], ot[1])})"
                if m == "hash_tree_root":
                    return f"(← bytesOf Root (← {self.htr_of(o)}))"
                if m == "union":
                    return f"(dedup ({self.ex(o)} ++ {self.ex(args[0], ot)}))"
                if m == "intersection":
                    other = self.ex(args[0], ot)
                    return f"(({self.ex(o)}).filter fun x => ({other}).contains x)"
        raise Unsupported(f"call {ast.unparse(e)[:60]}")

    def inline(self, fn, args):
        """The body of a one-line spec function, with the arguments in place of the
        parameters. A call through a fork module (`fulu.get_current_epoch(pre)`) needs it, since
        the argument has the older fork's class."""
        tree = self.b.fns[fn]
        body = S.strip_docstring(tree.body)
        if len(body) != 1 or not isinstance(body[0], ast.Return):
            raise Unsupported(f"inline of {fn}")
        sub = {a.arg: x for a, x in zip(tree.args.args, args)}

        class R(ast.NodeTransformer):
            def visit_Name(self, n):
                return sub.get(n.id, n)
        import copy
        return R().visit(copy.deepcopy(body[0].value))

    def htr_of(self, x):
        t = self.ty(x)
        if t == T.ANY:
            return f"htrObj {self.ex(x)}"
        return f"htr {self.enc_of(t)} {self.ex(x)}"

    def construct(self, c, args, kws):
        t = T.of_class(c)
        L = self.lean(t)
        k = t[0]
        if k == "uint":
            if not args:
                return f"(⟨0⟩ : {L})"
            at = self.ty(args[0])
            if at and at[0] == "uint":
                return f"(← uCast {L} {self.ex(args[0])})"
            if at == T.BOOLEAN:
                return self.conv(self.ex(args[0]), at, t)
            if at == T.BOOL:
                return f"(← (throw .bug : SpecM {L}))"
            return f"(← uOf {L} {self.as_int(args[0])})"
        if k == "boolean":
            if not args:
                return "(⟨false⟩ : Boolean)"
            at = self.ty(args[0])
            if at == T.BOOL:
                return f"(⟨{self.ex(args[0])}⟩ : Boolean)"
            if at == T.BOOLEAN:
                return self.ex(args[0])
            return f"(⟨{self.as_int(args[0])} != 0⟩ : Boolean)"
        if k == "bytesN":
            if not args:
                return f"(⟨List.replicate {c.LENGTH} 0⟩ : {L})"
            at = self.ty(args[0])
            if at and at[0] in ("bytes", "bytesN"):
                return self.conv(self.ex(args[0]), at, t) if at[0] == "bytesN" and \
                    at[1].LENGTH == c.LENGTH else f"(← bytesOf {L} {self.ex(args[0], T.BYTES)})"
            if at and at[0] == "list":
                return (f"(← bytesOf {L} (({self.ex(args[0])}).map fun (x : Int) => "
                        f"UInt8.ofNat x.toNat))")
        if k == "container":
            if dataclasses.is_dataclass(c):
                fields = self.b.dataclass_fields[c]
                from rd_emit import type_of_hint
                ftys = [(f, type_of_hint(self.b, h)) for f, h in fields]
                given = dict(zip([f for f, _ in ftys], args))
                given.update(kws)
            else:
                if args:
                    return f"(← (throw .bug : SpecM {L}))"
                ftys = [(f, T.of_class(ft)) for f, ft in c._FIELD_TYPES]
                given = kws
            parts = []
            for f, ft in ftys:
                if f in given:
                    parts.append(f"{T.ident(f)} := {self.field_value(given[f], ft)}")
            if not parts:
                return f"(default : {L})"
            return "{ (default : " + L + ") with " + ", ".join(parts) + " }"
        if k == "list":
            li = T.list_info(c)
            if args:
                return f"(← (throw .bug : SpecM {L}))"
            if "data" in kws:
                lim = "none" if li[2] is None else f"(some {li[2]})"
                return f"(← lfrom .{li[0]} {lim} {self.ex(kws['data'], ('list', t[1], None))})"
            from translate import default_term
            return f"({default_term(self.b, c)} : {L})"
        raise Unsupported(f"constructor {c.__name__}")

    def field_value(self, x, ft):
        """A value for a container field: pydantic coerces a uint, and rejects a Python
        list for an SSZ list field."""
        xt = self.ty(x)
        if ft[0] == "list" and xt and xt[0] == "list" and xt[2] is None and ft[2] is not None:
            return f"(← (throw .bug : SpecM {self.lean(ft)}))"
        return self.ex(x, ft)

    def builtin(self, n, e):
        args = e.args
        kws = {k.arg: k.value for k in e.keywords}
        if n == "len":
            t = self.ty(args[0])
            code = self.ex(args[0])
            if t[0] == "bytesN":
                code = f"(bd {code})"
            return f"(Int.ofNat ({code}).length)"
        if n == "range":
            return self.range_code(args)
        if n in ("enumerate", "zip"):
            return self.iter_value(ast.Name(id="_"), e)[0]
        if n in ("list", "tuple"):
            if not args:
                return "[]"
            return self.iter_value(ast.Name(id="_"), args[0])[0]
        if n == "set":
            if not args:
                return "[]"
            return f"(dedup {self.iter_value(ast.Name(id='_'), args[0])[0]})"
        if n == "dict":
            return "[]"
        if n == "bytes":
            return self.ex(args[0], T.BYTES)
        if n == "int":
            return self.as_int(args[0])
        if n == "bool":
            return self.truth(self.ex(args[0]), self.ty(args[0]))
        if n == "sorted":
            src, _ = self.iter_value(ast.Name(id="_"), args[0])
            rev = self.truth(self.ex(kws["reverse"]), T.BOOL) if "reverse" in kws else "false"
            if "key" in kws:
                key = self.lam_code(kws["key"], [self.iter_elem_ty(args[0])])
                if "(←" in key:
                    raise Unsupported("sort key that can fail")
            else:
                key = "id"
            return f"(pySort {key} {rev} {src})"
        if n in ("min", "max"):
            t = self.ty(e)
            fn = "pyMin" if n == "min" else "pyMax"
            if len(args) == 1:
                src, _ = self.iter_value(ast.Name(id="_"), args[0])
                return f"(← {fn} {src})"
            items = ", ".join(self.ex(a, t) for a in args)
            return f"(← {fn} [{items}])"
        if n == "sum":
            et = self.iter_elem_ty(args[0])
            src, _ = self.iter_value(ast.Name(id="_"), args[0])
            if et and et[0] == "uint":
                start = self.ex(args[1], et) if len(args) > 1 else f"(⟨0⟩ : {self.lean(et)})"
                return f"(← sumU {start} {src})"
            start = self.as_int(args[1]) if len(args) > 1 else "(0 : Int)"
            return f"(({src}).foldl (· + ·) {start})"
        if n in ("any", "all"):
            fn = "anyM" if n == "any" else "allM"
            a = args[0]
            if isinstance(a, ast.GeneratorExp) and len(a.generators) == 1:
                g = a.generators[0]
                saved, saved_al = dict(self.vars), dict(self.aliases)
                self.lazy = getattr(self, "lazy", 0) + 1
                try:
                    it_code, pat = self.iter_value(g.target, g.iter)
                    self.bind_iter_types(g.target, g.iter)
                    body = self.truth(self.ex(a.elt), self.ty(a.elt))
                    conds = [self.truth(self.ex(c), self.ty(c)) for c in g.ifs]
                finally:
                    self.lazy -= 1
                    self.vars, self.aliases = saved, saved_al
                if conds:
                    skip = "false" if n == "any" else "true"
                    body = f"(← (if {' && '.join(conds)} then (do pure {body}) else pure {skip} : SpecM Bool))"
                return f"(← ({it_code}).{fn} fun {pat} => do pure {body})"
            src, _ = self.iter_value(ast.Name(id="_"), a)
            et = self.iter_elem_ty(a)
            return f"(({src}).{'any' if n == 'any' else 'all'} fun x => {self.truth('x', et)})"
        if n == "filter":
            fn_e, src_e = args
            src, _ = self.iter_value(ast.Name(id="_"), src_e)
            ps, body = self.lam_parts(fn_e, [self.iter_elem_ty(src_e)], truth=True)
            return f"(← ({src}).filterM fun {ps} => do pure {body})"
        raise Unsupported(f"builtin {n}")

    def lam_parts(self, lam, arg_tys, truth=False):
        """The parameters and the body of a lambda."""
        saved, saved_al = dict(self.vars), dict(self.aliases)
        self.lazy = getattr(self, "lazy", 0) + 1
        try:
            ps = [a.arg for a in lam.args.args]
            for p, t in zip(ps, arg_tys):
                self.vars[p] = t
                self.aliases.pop(p, None)
            body = self.ex(lam.body)
            if truth:
                body = self.truth(body, self.ty(lam.body))
            return " ".join(T.ident(p) for p in ps), body
        finally:
            self.lazy -= 1
            self.vars, self.aliases = saved, saved_al

    def lam_code(self, lam, arg_tys, truth=False):
        if not isinstance(lam, ast.Lambda):
            raise Unsupported("function value that is not a lambda")
        saved, saved_al = dict(self.vars), dict(self.aliases)
        self.lazy = getattr(self, "lazy", 0) + 1
        try:
            ps = [a.arg for a in lam.args.args]
            for p, t in zip(ps, arg_tys):
                self.vars[p] = t
                self.aliases.pop(p, None)
            body = self.ex(lam.body)
            if truth:
                body = self.truth(body, self.ty(lam.body))
            if "(←" in body:
                return f"(fun {' '.join(ps)} => (do pure {body} : SpecM _))"
            return f"(fun {' '.join(ps)} => {body})"
        finally:
            self.lazy -= 1
            self.vars, self.aliases = saved, saved_al

    # --- paths (SPEC 4.2) ------------------------------------------------------------------

    def path_of(self, e):
        """The place of an expression, or None. A place is `("p", root, steps)`, or
        `("c", sel, place1, place2)` for a name that one of two branches bound (SPEC 4.2,
        pattern 2). A step is `("f", field)`, `("i", index variable)`, `("d", key variable)` or
        `("s", (lo, hi))`. Each index is evaluated once, into a variable."""
        match e:
            case ast.Name(id=x):
                if x in self.aliases:
                    return self.aliases[x][0]
                if x in self.vars:
                    return ("p", x, [])
            case ast.Attribute(value=o, attr=f):
                p = self.path_of(o)
                if p is not None:
                    return ext(p, ("f", f))
            case ast.Subscript(value=o, slice=ast.Slice(lower=lo, upper=hi, step=None)):
                p = self.path_of(o)
                if p is not None:
                    lo_c = f"(some {self.as_int(lo)})" if lo is not None else "none"
                    hi_c = f"(some {self.as_int(hi)})" if hi is not None else "none"
                    return ext(p, ("s", (lo_c, hi_c)))
            case ast.Subscript(value=o, slice=i) if not isinstance(i, ast.Slice):
                ot = self.ty(o)
                p = self.path_of(o)
                if p is not None and ot and ot[0] in ("list", "dict"):
                    tmp = self.fresh("i")
                    code = self.as_int(i) if ot[0] == "list" else self.ex(i, ot[1])
                    kt = T.INT if ot[0] == "list" else ot[1]
                    self.vars[tmp] = kt
                    if getattr(self, "aliasing", False) and self.ind > self.base_ind:
                        # The alias outlives this block: its index lives at the top.
                        self.lines.insert(self.body_start,
                                          "  " * self.base_ind + f"let mut {tmp} : {self.lean(kt)} := default")
                        self.line(f"{tmp} := {code}")
                        self.declared.add(tmp)
                        self.wrote(tmp)
                        self.hoisted[tmp] = kt
                    else:
                        self.line(f"let {tmp} := {code}")
                    return ext(p, ("i" if ot[0] == "list" else "d", tmp))
        return None

    def rd(self, p, t):
        """Read a place."""
        if p[0] == "c":
            a, b = self.rd(p[2], t), self.rd(p[3], t)
            self.use(p[1])
            return f"(← (if {p[1]} then (do pure {a}) else (do pure {b}) : SpecM {self.lean(t)}))"
        return self.read_path(p[1], p[2])

    def wr(self, p, value):
        """Write a place."""
        if p[0] == "c":
            tmp = self.fresh("w")
            self.line(f"let {tmp} := {value}")
            self.use(p[1])
            self.line(f"if {p[1]} then")
            self.ind += 1
            self.wr(p[2], tmp)
            self.ind -= 1
            self.line("else")
            self.ind += 1
            self.wr(p[3], tmp)
            self.ind -= 1
            return
        self.set_path(p[1], p[2], value)

    def ptype(self, p):
        if p[0] == "c":
            return self.ptype(p[2])
        return self.path_type(p[1], p[2])

    def materialize(self, p):
        """Python rebinds the object at `p`. A name that pointed into it keeps the old object:
        it becomes a value."""
        for x, (q, t) in list(self.aliases.items()):
            if overlaps(p, q):
                code = self.rd(q, t)
                del self.aliases[x]
                self.vars[x] = t
                self.declare(x, code)

    def read_path(self, root, steps):
        self.use(root)
        code = T.ident(root)
        for k, v in steps:
            if k == "f":
                code = f"({code}).{T.ident(v)}"
            elif k == "i":
                self.use(v)
                code = f"(← lget {code} {v})"
            elif k == "s":
                code = f"(lslice {code} {v[0]} {v[1]})"
            else:
                self.use(v)
                code = f"(← dget {code} {v})"
        return code

    def set_path(self, root, steps, value):
        """`root := ...`, with `value` at the end of the path."""
        def upd(base, st):
            if not st:
                return value
            (k, v), rest = st[0], st[1:]
            if k == "f":
                return f"{{ {base} with {T.ident(v)} := {upd(f'({base}).{T.ident(v)}', rest)} }}"
            if k == "s":
                lo, hi = v
                return f"(← lsetSlice' {base} {lo} {hi} {upd(f'(lslice {base} {lo} {hi})', rest)})"
            self.use(v)
            if k == "i":
                return f"(← lset {base} {v} {upd(f'(← lget {base} {v})', rest)})"
            return f"(dset {base} {v} {upd(f'(dgetD {base} {v})', rest)})"
        self.use(root)
        self.line(f"{T.ident(root)} := {upd(T.ident(root), steps)}")
        self.wrote(root)

    def wrote(self, x):
        self.mutable.add(x)
        if self.in_loop is not None:
            self.in_loop.write(x)

    def path_type(self, root, steps):
        t = self.vars[root]
        for k, v in steps:
            if k == "f":
                t = self.field_type(t[1], v)
            elif k == "i":
                t = t[1]
            elif k == "s":
                t = ("list", t[1], None)
            else:
                t = t[2]
        return t

    # --- statements --------------------------------------------------------------------------

    def declare(self, x, code):
        self.declared.add(x)
        self.line(f"let @M@{T.ident(x)} := {code}")

    def assign_var(self, x, code):
        if x in self.aliases:
            raise Unsupported(f"rebinding the alias {x}")
        if x in self.declared:
            self.line(f"{T.ident(x)} := {code}")
            self.wrote(x)
        else:
            self.declare(x, code)

    def alias_ok(self, x, v):
        """`x = <place>` makes `x` an alias, when the place holds a heap object."""
        if x in self.declared or x in self.sig_params:
            return False
        return self.alias_place_ok(v)

    def alias_place_ok(self, v):
        t = self.ty(v)
        if t is None or t[0] not in ("container", "list"):
            return False
        if not (isinstance(v, (ast.Attribute, ast.Subscript, ast.Name)) and
                not isinstance(getattr(v, "slice", None), ast.Slice)):
            return False
        # A later statement that rebinds the place, or a place that holds it, leaves the name
        # with the old object: then the name is a value.
        vp = self.syn(v)
        if vp is None:
            return False
        for n in ast.walk(self.tree):
            if isinstance(n, (ast.Assign, ast.AugAssign)) and n.lineno > v.lineno:
                for t in (n.targets if isinstance(n, ast.Assign) else [n.target]):
                    tp = self.syn(t)
                    if tp is not None and tp[1] and tp[0] == vp[0] and \
                            len(tp[1]) <= len(vp[1]) and \
                            all(a == b or "*" in (a, b) for a, b in zip(tp[1], vp[1])):
                        return False
        return True

    def syn(self, e):
        """The syntactic place of an expression: root name and steps, `*` for an index."""
        match e:
            case ast.Name(id=x):
                if x in self.aliases and self.aliases[x][0][0] == "p":
                    p = self.aliases[x][0]
                    return p[1], ["*" if k != "f" else v for k, v in p[2]]
                return x, []
            case ast.Attribute(value=o, attr=f):
                r = self.syn(o)
                return (r[0], r[1] + [f]) if r else None
            case ast.Subscript(value=o):
                r = self.syn(o)
                return (r[0], r[1] + ["*"]) if r else None
        return None

    def block(self, stmts):
        n0 = len(self.lines)
        for s in stmts:
            self.stmt(s)
        if len(self.lines) == n0:
            self.line("pure ()")

    def stmt(self, s):
        match s:
            case ast.If(test=ast.Compare(left=ast.Name(id=x), ops=[ast.Is()],
                                         comparators=[ast.Constant(value=None)]),
                        body=[ast.Assign(targets=[ast.Name(id=y)], value=v)], orelse=[]) \
                    if x == y and self.vars.get(x, (None,))[0] == "option":
                inner = self.vars[x][1]
                self.lazy = getattr(self, "lazy", 0) + 1
                try:
                    code = self.ex(v, inner)
                finally:
                    self.lazy -= 1
                self.line(f"let {T.ident(x)} ← (match {T.ident(x)} with | some v => pure v | "
                          f"none => (do pure {code}) : SpecM {self.lean(inner)})")
                self.vars[x] = inner
                return
            case ast.Expr(value=ast.Constant(value=str())):
                return
            case ast.Pass():
                return
            case ast.Assign(targets=[ast.Name(id=x)], value=v) | \
                    ast.AnnAssign(target=ast.Name(id=x), value=v) if v is not None:
                if self.alias_ok(x, v):
                    self.aliasing = True
                    try:
                        p = self.path_of(v)
                    finally:
                        self.aliasing = False
                    if p is not None:
                        self.aliases[x] = (p, self.ty(v))
                        return
                vt = self.ty(v)
                cur = self.vars.get(x)
                if cur and cur[0] == "option" and vt and vt[0] != "option" and vt != T.NONE:
                    # `epoch = ... if epoch is None else epoch`: a narrower variable.
                    self.line(f"let {T.ident(x)} := {self.ex(v)}")
                    self.vars[x] = vt
                    return
                self.assign_var(x, self.ex(v, self.vars.get(x)))
            case ast.Assign(targets=[ast.Tuple(elts=es) | ast.List(elts=es)], value=v):
                t = self.ty(v)
                tmp = self.fresh("p")
                self.line(f"let {tmp} := {self.ex(v)}")
                for i, x in enumerate(es):
                    comp = self.proj(tmp, i, len(es))
                    if isinstance(x, ast.Name):
                        self.assign_var(x.id, self.conv(comp, t[1][i], self.vars.get(x.id)))
                    else:
                        raise Unsupported("tuple target that is not a name")
            case ast.Assign(targets=[ast.Subscript(slice=ast.Slice()) as target], value=v):
                p = self.path_of(target)
                if p is None:
                    raise Unsupported(f"write to {ast.unparse(target)}")
                pt = self.ptype(parent(p))
                code = self.ex(v, ("list", pt[1], None))
                self.materialize(p)
                self.wr(p, code)
                li = T.list_info(pt[2]) if pt[0] == "list" and pt[2] else None
                if li and li[0] in ("vector", "bitvector"):
                    cur = self.rd(parent(p), pt)
                    self.line(f"assertBug (({cur}).length == {li[2]})")
            case ast.Assign(targets=[target], value=v):
                code = self.target_value(target, v)
                p = self.path_of(target)
                if p is None:
                    raise Unsupported(f"write to {ast.unparse(target)}")
                self.materialize(p)
                self.wr(p, code)
            case ast.AugAssign(target=target, op=op, value=v):
                expr = ast.BinOp(left=target, op=op, right=v)
                if isinstance(target, ast.Name) and target.id not in self.aliases:
                    self.assign_var(target.id, self.ex(expr, self.vars.get(target.id)))
                else:
                    p = self.path_of(target)
                    if p is None:
                        raise Unsupported(f"augmented write to {ast.unparse(target)}")
                    pt = self.ptype(p)
                    code = self.ex(expr, pt)
                    self.materialize(p)
                    self.wr(p, code)
            case ast.Expr(value=ast.Call(func=ast.Attribute(value=o, attr=m), args=args)) \
                    if m in ("append", "extend", "add"):
                ot = self.ty(o)
                p = self.path_of(o)
                if p is None:
                    raise Unsupported(f"{m} on {ast.unparse(o)}")
                cur = self.rd(p, ot)
                li = T.list_info(ot[2]) if ot[0] == "list" and ot[2] else None
                lim = "none" if li is None or li[2] is None or li[0] == "progressiveList" \
                    else f"(some {li[2]})"
                if m == "append":
                    self.wr(p, f"(← lappend {cur} {self.ex(args[0], ot[1])} {lim})")
                elif m == "add":
                    x = self.ex(args[0], ot[1])
                    self.wr(p, f"(if ({cur}).contains {x} then {cur} else {cur} ++ [{x}])")
                else:
                    src, _ = self.iter_value(ast.Name(id="_"), args[0])
                    self.wr(p, f"(← lextend {cur} {src} {lim})")
            case ast.Expr(value=v):
                code = self.ex(v)
                if code != "()":
                    self.line(f"let _ := {code}")
            case ast.If(test=c, body=bd, orelse=o):
                cond = self.truth(self.ex(c), self.ty(c))
                sel = None
                if self.binds_alias(bd) or self.binds_alias(o):
                    sel = self.fresh("c")
                    self.line(f"let {sel} := {cond}")
                    self.vars[sel] = T.BOOL
                    cond = sel
                self.line(f"if {cond} then")
                self.ind += 1
                saved = dict(self.aliases)
                saved_decl = set(self.declared)
                saved_vars = dict(self.vars)
                self.block(bd)
                al_then = dict(self.aliases)
                self.aliases = dict(saved)
                self.declared = set(saved_decl)
                self.vars = dict(saved_vars)
                self.ind -= 1
                al_else = dict(saved)
                if o:
                    self.line("else")
                    self.ind += 1
                    self.block(o)
                    al_else = dict(self.aliases)
                    self.aliases = dict(saved)
                    self.declared = saved_decl
                    self.vars = saved_vars
                    self.ind -= 1
                # A name that each branch binds to a place points to one of the two.
                if always_returns(bd):
                    al_then = al_else
                if o and always_returns(o):
                    al_else = al_then
                for x, t in self.hoisted.items():
                    self.vars.setdefault(x, t)
                    self.declared.add(x)
                for x in set(al_then) | set(al_else):
                    a, b = al_then.get(x), al_else.get(x)
                    if a is not None and b is not None:
                        if a == b:
                            self.aliases[x] = a
                        elif sel is not None:
                            self.aliases[x] = (("c", sel, a[0], b[0]), a[1])
            case ast.Return(value=v):
                code = self.ex(v, self.sig.ret) if v is not None else "()"
                self.ret_line(code)
            case ast.Assert(test=c):
                self.line(f"assert {self.truth(self.ex(c), self.ty(c))}")
            case ast.For():
                self.for_loop(s)
            case ast.While():
                self.while_loop(s)
            case ast.Break():
                self.line(f"return {self.in_loop.brk()}")
            case ast.Continue():
                self.line(f"return (← {self.in_loop.next()})")
            case _:
                raise Unsupported(f"statement {type(s).__name__}: {ast.unparse(s)[:60]}")

    def target_value(self, target, v):
        """The value that `target = v` writes, coerced to the type of the place."""
        if isinstance(target, ast.Attribute):
            ot = self.ty(target.value)
            ft = self.field_type(ot[1], target.attr)
            return self.field_value(v, ft)
        return self.ex(v, self.ty(target))

    def outputs(self, ret_code):
        parts = ([ret_code] if self.sig.ret != T.NONE else []) + \
            [T.ident(self.sig.params[j][0]) for j in self.sig.mutated]
        if not parts:
            return "()"
        return parts[0] if len(parts) == 1 else "(" + ", ".join(parts) + ")"

    def ret_line(self, code):
        out = self.outputs(code)
        if self.in_loop is not None:
            self.in_loop.has_return = True
            self.line(f"return {self.in_loop.ret(out)}")
        else:
            self.line(f"return {out}")

    # --- loops ---------------------------------------------------------------------------------

    def for_loop(self, s):
        target, it = s.target, s.iter
        if s.orelse:
            raise Unsupported("for ... else")
        self.loop_no += 1
        name = f"{self.sig.name}.loop{self.loop_no}"
        # The element: an alias into a place, or an item of a list value (a snapshot).
        elem_alias = None
        idx_name = None
        src = it
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and \
                it.func.id == "enumerate" and isinstance(target, ast.Tuple) and \
                len(target.elts) == 2 and isinstance(target.elts[0], ast.Name):
            src = it.args[0]
            idx_name = target.elts[0].id
            tgt = target.elts[1]
        else:
            tgt = target
        st = self.ty(src)
        place = self.path_of(src) if st and st[0] == "list" and isinstance(tgt, ast.Name) and \
            st[1] and st[1][0] in ("container", "list") else None
        n_var = self.fresh("n")
        if place is not None and (idx_name is not None or src is it):
            self.line(f"let {n_var} := ({self.rd(place, st)}).length")
            elem_alias = (tgt.id, place, st[1])
            xs_var = None
        else:
            idx_name = None
            tgt = target
            xs_var = self.fresh("xs")
            code, _ = self.iter_value(target, it)
            et = self.iter_elem_ty(it)
            self.line(f"let {xs_var} := {code}")
            self.vars[xs_var] = ("list", et, None)
            self.line(f"let {n_var} := {xs_var}.length")
        self.vars[n_var] = ("nat",)
        self.compile_loop(name, s.body, kind="for", n_var=n_var, xs_var=xs_var,
                          tgt=tgt, it=it, elem_alias=elem_alias, idx_name=idx_name)

    def while_loop(self, s):
        if s.orelse:
            raise Unsupported("while ... else")
        self.loop_no += 1
        name = f"{self.sig.name}.loop{self.loop_no}"
        measure = self.em.while_measures.get(self.sig.name)
        if measure is None:
            raise Unsupported(f"no measure for the while loop of {self.sig.name}")
        self.compile_loop(name, s.body, kind="while", test=s.test,
                          measure=ast.parse(measure, mode="eval").body)

    def compile_loop(self, name, body, kind, **kw):
        outer_vars = dict(self.vars)
        saved = (self.lines, self.ind, self.in_loop, dict(self.aliases), set(self.declared),
                 set(self.mutable))
        ctx = LoopCtx(name, kind, set(outer_vars) | set(self.aliases), self.in_loop)
        self.in_loop = ctx
        self.lines = []
        self.ind = 2
        saved_base = (self.base_ind, self.body_start)
        self.base_ind, self.body_start = 2, 0
        # The element.
        if kind == "for":
            if kw["elem_alias"] is not None:
                x, place, et = kw["elem_alias"]
                self.line("let i_' : Int := i_")
                self.vars["i_'"] = T.INT
                self.aliases[x] = (ext(place, ("i", "i_'")), et)
                self.declared.discard(x)
                if kw["idx_name"]:
                    self.line(f"let {T.ident(kw['idx_name'])} : Int := i_")
                    self.declared.add(kw["idx_name"])
            else:
                ctx.read(kw["xs_var"])
                pat = binder(kw["tgt"])
                self.line(f"let {pat} ← lget {kw['xs_var']} i_")
                for x in names_of(kw["tgt"]):
                    self.declared.add(x)
                    self.aliases.pop(x, None)
                self.bind_iter_types(kw["tgt"], kw["it"])
        else:
            cond = self.truth(self.ex(kw["test"]), self.ty(kw["test"]))
            self.line(f"if !({cond}) then return {ctx.done()}")
        self.block(body)
        self.line(ctx.tail())
        body_lines = self.lines
        self.base_ind, self.body_start = saved_base
        self.lines, self.ind, self.in_loop, aliases, self.declared, mutable = saved
        loop_vars = self.vars
        self.vars = {x: t for x, t in loop_vars.items() if x in outer_vars}
        self.aliases = aliases
        self.mutable = mutable | {x for x in ctx.writes if x in self.declared or x in self.vars}
        # The variables of the loop function. The loop target is bound by the loop.
        bound = {"i_'"}
        if kind == "for":
            if kw["elem_alias"] is not None:
                bound.add(kw["elem_alias"][0])
            else:
                bound |= set(names_of(kw["tgt"]))
            if kw["idx_name"]:
                bound.add(kw["idx_name"])
        carried = sorted(x for x in ctx.writes if x in outer_vars and x not in bound)
        captured = sorted(x for x in ctx.reads if x in outer_vars and x not in carried
                          and x not in bound)
        ctx.carried = carried
        if kind == "for":
            captured = [x for x in captured if x != kw["n_var"]]
        types = {x: outer_vars[x] for x in carried + captured}
        cap_params = " ".join(f"({T.ident(x)} : {self.lean_or_nat(types[x])})" for x in captured)
        carry_ty = self.tuple_ty([types[x] for x in carried])
        out_ty = f"(Option {self.out_ty()} × {carry_ty})" if ctx.has_return else carry_ty
        carry_in = " ".join(f"({T.ident(x)}_in : {self.lean(types[x])})" for x in carried)
        lets = "".join(f"\n    let mut {T.ident(x)} := {T.ident(x)}_in" for x in carried)
        cap_args = " ".join(T.ident(x) for x in captured)
        cargs = " ".join(T.ident(x) for x in carried)
        cargs_in = " ".join(f"{T.ident(x)}_in" for x in carried)
        tup = lambda xs: "()" if not xs else xs[0] if len(xs) == 1 else "(" + ", ".join(xs) + ")"
        ctup = tup([T.ident(x) for x in carried])
        ctup_in = tup([f"{T.ident(x)}_in" for x in carried])

        def subst(t):
            done = f"(none, {ctup})" if ctx.has_return else ctup
            wnext = (f"(if h : {name}.μ @CAP@ @CARGS@ < {name}.μ @CAP@ @CARGS_in@ then "
                     f"{name} @CAP@ @CARGS@ else throw .bug)")
            t = t.replace("@WNEXT@", wnext).replace("@DONE@", done)
            t = t.replace("@CARGS_in@", cargs_in).replace("@CARGS@", cargs)
            t = t.replace("@CTUP@", ctup).replace("@CAP@", cap_args)
            if kind == "for":
                t = t.replace("@N@", kw["n_var"])
            return t
        text = subst("\n".join(body_lines))
        text = finalize_lets(text, self.mutable | set(carried))
        if kind == "for":
            n = kw["n_var"]
            else_val = f"(none, {ctup_in})" if ctx.has_return else ctup_in
            header = (f"def {name} {cap_params} ({n} : Nat) (i_ : Nat) {carry_in} : "
                      f"SpecM {out_ty} :=\n  if h : i_ < {n} then do{lets}\n{text}\n"
                      f"  else pure {else_val}\n"
                      f"termination_by {n} - i_\n")
            call = f"{name} {cap_args} {n} 0 {cargs}"
        else:
            measure_code = self.measure_code(kw["measure"], outer_vars)
            mparams = cap_params + " " + " ".join(
                f"({T.ident(x)} : {self.lean(types[x])})" for x in carried)
            self.loops.append(f"def {name}.μ {mparams} : Nat := {measure_code}\n")
            header = (f"def {name} {cap_params} {carry_in} : SpecM {out_ty} := do{lets}\n{text}\n"
                      f"termination_by {name}.μ {cap_args} {cargs_in}\n"
                      f"decreasing_by all_goals (simp_wf; assumption)\n")
            call = f"{name} {cap_args} {cargs}"
        header = header.replace("@CAP@", cap_args)
        self.loops.append(header)
        for x in captured + carried:
            self.use(x)
        for x in carried:
            self.wrote(x)
        res = self.fresh("l")
        self.line(f"let {res} ← {call}")
        cs = carried
        carry_val = f"{res}.2" if ctx.has_return else res
        for k, x in enumerate(cs):
            self.line(f"{T.ident(x)} := {self.proj(carry_val, k, len(cs)) if len(cs) > 1 else carry_val}")
        if ctx.has_return:
            if self.in_loop is not None:
                self.in_loop.has_return = True
                self.line(f"if let some v := {res}.1 then return {self.in_loop.ret('v')}")
            else:
                self.line(f"if let some v := {res}.1 then return v")

    def measure_code(self, m, env):
        def pure_int(e):
            match e:
                case ast.Constant(value=v) if type(v) is int:
                    return f"({v} : Int)"
                case ast.BinOp(left=a, op=op, right=b) if type(op) in (ast.Add, ast.Sub,
                                                                          ast.Mult, ast.Pow):
                    sym = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Pow: "^"}[type(op)]
                    if sym == "^":
                        return f"({pure_int(a)} ^ ({pure_int(b)}).toNat)"
                    return f"({pure_int(a)} {sym} {pure_int(b)})"
            code = self.as_int(e)
            if "(←" in code:
                raise Unsupported("a measure that can fail")
            return code
        return f"({pure_int(m)}).toNat"

    def lean_or_nat(self, t):
        return "Nat" if t == ("nat",) else self.lean(t)

    def tuple_ty(self, ts):
        if not ts:
            return "Unit"
        if len(ts) == 1:
            return self.lean_or_nat(ts[0])
        return "(" + " × ".join(self.lean_or_nat(t) for t in ts) + ")"

    def out_ty(self):
        return self.tuple_ty(out_types(self.sig)) if out_types(self.sig) else "Unit"


    # --- the function -------------------------------------------------------------------------

    def compile(self):
        tree = expand_for_ops(self.tree)
        body = S.strip_docstring(tree.body)
        self.sig_params = {p for p, _ in self.sig.params}
        self.infer(body)
        # A variable that a nested block assigns and that code after the block, or a later
        # iteration, reads needs a declaration at the top.
        pre = {x for x in assigned_names(body) - self.sig_params
               if self.needs_predecl(x, body)}
        for x in sorted(pre):
            t = self.vars.get(x)
            if t is None:
                raise Unsupported(f"type of {x}")
            if t[0] in ("container", "list") and self.is_alias_candidate(x, body):
                continue
            self.line(f"let @M@{T.ident(x)} : {self.lean(t)} := default")
            self.declared.add(x)
            self.mutable.add(x)
        self.block(body)
        if not always_returns(body):
            self.ret_line("()")
        lines = [f"  let mut {T.ident(p)} := {T.ident(p)}" for p, _ in self.sig.params
                 if p in self.mutable]
        text = finalize_lets("\n".join(lines + self.lines), self.mutable)
        return text

    def binds_alias(self, stmts):
        for s in stmts:
            for n in ast.walk(s):
                if isinstance(n, ast.Assign) and len(n.targets) == 1 and \
                        isinstance(n.targets[0], ast.Name) and \
                        self.place_expr(n.value):
                    return True
        return False

    def place_expr(self, v):
        t = self.ty(v)
        if t is None or t[0] not in ("container", "list"):
            return False
        while isinstance(v, (ast.Attribute, ast.Subscript)):
            if isinstance(v, ast.Subscript) and isinstance(v.slice, ast.Slice):
                return False
            v = v.value
        return isinstance(v, ast.Name)

    def needs_predecl(self, x, body):
        """`x` is assigned inside a nested block, and read outside it, or assigned at the top
        after a nested assignment."""
        top_assigned = set()
        for s in body:
            if isinstance(s, (ast.Assign, ast.AnnAssign)):
                for t in (s.targets if isinstance(s, ast.Assign) else [s.target]):
                    if isinstance(t, ast.Name):
                        top_assigned.add(t.id)
            if isinstance(s, (ast.If, ast.For, ast.While)):
                if x in assigned_names(s.body + s.orelse) and x not in top_assigned:
                    rest = body[body.index(s):]
                    reads_after = read_names([y for y in body[body.index(s) + 1:]])
                    if x in reads_after:
                        return True
                    # Read in a later iteration of a loop, or in the test.
                    if isinstance(s, (ast.For, ast.While)) and x in read_names(s.body):
                        return True
                    if self.nested_needs(x, s):
                        return True
        return False

    def nested_needs(self, x, s):
        for b in [s.body, s.orelse]:
            if self.needs_predecl(x, b):
                return True
        return False

    def is_alias_candidate(self, x, body):
        """Every assignment to `x` binds it to a place."""
        found = False
        for n in ast.walk(ast.Module(body=body, type_ignores=[])):
            if isinstance(n, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                ts = n.targets if isinstance(n, ast.Assign) else [n.target]
                for t in ts:
                    if isinstance(t, ast.Name) and t.id == x:
                        if not isinstance(n, ast.Assign) or not self.alias_place_ok(n.value):
                            return False
                        found = True
            if isinstance(n, ast.For) and x in names_of(n.target):
                return False
        return found


class LoopCtx:
    """The variables that a loop body reads and writes from outside."""

    def __init__(self, name, kind, outer, parent):
        self.name, self.kind, self.outer, self.parent = name, kind, outer, parent
        self.reads, self.writes = set(), set()
        self.has_return = False
        self.carried = None

    def read(self, x):
        if x in self.outer:
            self.reads.add(x)
            if self.parent is not None:
                self.parent.read(x)

    def write(self, x):
        if x in self.outer:
            self.writes.add(x)
            if self.parent is not None:
                self.parent.write(x)

    # Placeholders: the carried variables are known only after the body.
    def carry_names(self, suffix=""):
        return f"@CARGS{suffix}@"

    def ret_shape(self, carry):
        return f"(none, {carry})" if self.has_return else carry

    def done(self):
        return "@DONE@"

    def brk(self):
        return "@DONE@"

    def ret(self, out):
        return f"(some {out}, @CTUP@)"

    def next(self):
        if self.kind == "for":
            return f"{self.name} @CAP@ @N@ (i_ + 1) @CARGS@"
        return "@WNEXT@"

    def tail(self):
        return self.next()


def ext(p, step):
    if p[0] == "c":
        return ("c", p[1], ext(p[2], step), ext(p[3], step))
    return ("p", p[1], p[2] + [step])


def parent(p):
    if p[0] == "c":
        return ("c", p[1], parent(p[2]), parent(p[3]))
    return ("p", p[1], p[2][:-1])


def overlaps(w, q):
    """A write to place `w` replaces the object at place `q`, or one that holds it. Two index
    steps may name the same element."""
    if w[0] == "c":
        return overlaps(w[2], q) or overlaps(w[3], q)
    if q[0] == "c":
        return overlaps(w, q[2]) or overlaps(w, q[3])
    if w[1] != q[1] or len(w[2]) > len(q[2]):
        return False
    for a, b in zip(w[2], q[2]):
        if a[0] != b[0]:
            return False
        if a[0] == "f" and a[1] != b[1]:
            return False
    return True


def always_returns(stmts):
    """Every path through the statements ends in `return`."""
    if not stmts:
        return False
    last = stmts[-1]
    if isinstance(last, ast.Return):
        return True
    if isinstance(last, ast.If):
        return always_returns(last.body) and always_returns(last.orelse)
    return False


def names_of(target):
    match target:
        case ast.Name(id=x):
            return [x]
        case ast.Tuple(elts=es) | ast.List(elts=es):
            return [n for e in es for n in names_of(e)]
    raise Unsupported(f"target {ast.unparse(target)}")


def binder(target):
    """A Lean pattern for a loop or comprehension target."""
    match target:
        case ast.Name(id=x):
            return T.ident(x)
        case ast.Tuple(elts=es) | ast.List(elts=es):
            return "(" + ", ".join(binder(e) for e in es) + ")"
    raise Unsupported(f"target {ast.unparse(target)}")


def finalize_lets(text, mutable):
    import re
    def rep(m):
        x = m.group(1)
        bare = x[1:-1] if x.startswith("«") else x
        return f"let mut {x} :=" if bare in mutable or x in mutable else f"let {x} :="
    def rep2(m):
        x = m.group(1)
        bare = x[1:-1] if x.startswith("«") else x
        kw = "let mut" if bare in mutable or x in mutable else "let"
        return f"{kw} {x}{m.group(2) or ''} :="
    return re.sub(r"let @M@(\S+)( : [^\n]*?)? :=", rep2, text)


def assigned_names(stmts):
    out = set()
    for s in stmts:
        for n in ast.walk(s):
            if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                ts = n.targets if isinstance(n, ast.Assign) else [n.target]
                for t in ts:
                    for x in ast.walk(t):
                        if isinstance(x, ast.Name) and isinstance(x.ctx, ast.Store):
                            out.add(x.id)
            if isinstance(n, ast.For):
                for x in ast.walk(n.target):
                    if isinstance(x, ast.Name):
                        out.add(x.id)
    return out


def read_names(nodes):
    out = set()
    for s in nodes:
        for n in ast.walk(s):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                out.add(n.id)
    return out


def expand_for_ops(tree):
    """Expand a nested `for_ops` helper into plain loops (SPEC 4.2, pattern 4)."""
    import copy
    tree = copy.deepcopy(tree)
    helpers = {}
    body = []
    for s in tree.body:
        if isinstance(s, ast.FunctionDef):
            inner = [x for x in s.body if not isinstance(x, ast.Expr) or
                     not isinstance(x.value, ast.Constant)]
            if len(inner) == 1 and isinstance(inner[0], ast.For):
                helpers[s.name] = s
                continue
            raise Unsupported(f"nested function {s.name}")
        body.append(s)
    if not helpers:
        return tree

    class R(ast.NodeTransformer):
        def visit_Expr(self, node):
            c = node.value
            if isinstance(c, ast.Call) and isinstance(c.func, ast.Name) and c.func.id in helpers:
                h = helpers[c.func.id]
                loop = copy.deepcopy([x for x in h.body if isinstance(x, ast.For)][0])
                params = [a.arg for a in h.args.args]
                sub = dict(zip(params, c.args))
                extra = c.args[len(params):]

                class P(ast.NodeTransformer):
                    def visit_Name(self, n):
                        return copy.deepcopy(sub[n.id]) if n.id in sub else n

                    def visit_Call(self, n):
                        self.generic_visit(n)
                        args = []
                        for a in n.args:
                            if isinstance(a, ast.Starred):
                                args += [copy.deepcopy(x) for x in extra]
                            else:
                                args.append(a)
                        n.args = args
                        return n
                return P().visit(loop)
            return node
    tree.body = [R().visit(s) for s in body]
    return tree
