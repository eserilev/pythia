"""The generic part of the serializer: Python `ast` to Lean syntax trees (SPEC 5.1).

It knows Python and the `SpecLean.Ast` syntax tree, and nothing of pyspec or SSZ. The front
end (`serialize.py`) feeds it the functions and builds the environment.
"""

import ast


class Unsupported(Exception):
    pass


class Interner:
    def __init__(self):
        self.names: list[str] = []
        self.ids: dict[str, int] = {}

    def __call__(self, s: str) -> int:
        if s not in self.ids:
            self.ids[s] = len(self.names)
            self.names.append(s)
        return self.ids[s]


BINOPS = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul", ast.FloorDiv: "floorDiv",
          ast.Mod: "mod", ast.Pow: "pow", ast.BitAnd: "bitAnd", ast.BitOr: "bitOr",
          ast.BitXor: "bitXor", ast.LShift: "lShift", ast.RShift: "rShift"}
UNOPS = {ast.Not: "not", ast.USub: "neg", ast.Invert: "invert"}
CMPOPS = {ast.Eq: "eq", ast.NotEq: "notEq", ast.Lt: "lt", ast.LtE: "ltE", ast.Gt: "gt",
          ast.GtE: "gtE", ast.Is: "is", ast.IsNot: "isNot", ast.In: "isIn", ast.NotIn: "notIn"}
BOOLOPS = {ast.And: "and", ast.Or: "or"}
COMPS = {ast.ListComp: "list", ast.SetComp: "set", ast.GeneratorExp: "gen"}


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


class Emitter:
    """Lean syntax trees from Python `ast` nodes. `constants` holds `(module, attr)` pairs: a
    data member of a module, such as `bls.G2_POINT_AT_INFINITY`, becomes the name
    `module.attr`."""

    def __init__(self, intern: Interner, base_line: int, constants=frozenset()):
        self.intern = intern
        self.base = base_line - 1
        self.constants = constants

    def line(self, node) -> int:
        return self.base + getattr(node, "lineno", 1)

    def fail(self, node, what):
        raise Unsupported(f"line {self.line(node)}: {what} {type(node).__name__}")

    def lst(self, xs) -> str:
        return "[" + ", ".join(xs) + "]"

    def opt(self, e) -> str:
        return "none" if e is None else f"(some {self.expr(e)})"

    def expr(self, e) -> str:
        ln = self.line(e)
        match e:
            case ast.Name(id=x):
                return f"(.name {ln} {self.intern(x)})"
            case ast.Constant(value=v) if type(v) is bool:
                return f"(.bool {ln} {'true' if v else 'false'})"
            case ast.Constant(value=v) if type(v) is int:
                return f"(.int {ln} ({v}))"
            case ast.Constant(value=v) if type(v) is str:
                return f"(.str {ln} {lean_str(v)})"
            case ast.Constant(value=v) if type(v) is bytes:
                return f"(.bytes {ln} [{', '.join(str(b) for b in v)}])"
            case ast.Constant(value=None):
                return f"(.noneLit {ln})"
            case ast.Attribute(value=ast.Name(id=m), attr=f) if (m, f) in self.constants:
                return f"(.name {ln} {self.intern(m + '.' + f)})"
            case ast.Attribute(value=o, attr=f):
                return f"(.attr {ln} {self.expr(o)} {self.intern(f)})"
            case ast.Subscript(value=o, slice=ast.Slice(lower=lo, upper=hi, step=st)):
                return f"(.slice {ln} {self.expr(o)} {self.opt(lo)} {self.opt(hi)} {self.opt(st)})"
            case ast.Subscript(value=o, slice=i):
                return f"(.index {ln} {self.expr(o)} {self.expr(i)})"
            case ast.BinOp(left=a, op=op, right=b) if type(op) in BINOPS:
                return f"(.binop {ln} .{BINOPS[type(op)]} {self.expr(a)} {self.expr(b)})"
            case ast.UnaryOp(op=op, operand=a) if type(op) in UNOPS:
                return f"(.unop {ln} .{UNOPS[type(op)]} {self.expr(a)})"
            case ast.Compare(left=a, ops=ops, comparators=cs):
                for op in ops:
                    if type(op) not in CMPOPS:
                        self.fail(op, "compare op")
                rest = [f"(.{CMPOPS[type(op)]}, {self.expr(c)})" for op, c in zip(ops, cs)]
                return f"(.compare {ln} {self.expr(a)} {self.lst(rest)})"
            case ast.BoolOp(op=op, values=vs):
                return f"(.boolop {ln} .{BOOLOPS[type(op)]} {self.lst(self.expr(v) for v in vs)})"
            case ast.Call(func=f, args=args, keywords=kws):
                out = []
                for a in args:
                    if isinstance(a, ast.Starred):
                        out.append(f"(.starred {self.expr(a.value)})")
                    else:
                        out.append(f"(.pos {self.expr(a)})")
                for k in kws:
                    if k.arg is None:
                        self.fail(k, "**kwargs")
                    out.append(f"(.kw {self.intern(k.arg)} {self.expr(k.value)})")
                return f"(.call {ln} {self.expr(f)} {self.lst(out)})"
            case ast.IfExp(test=c, body=a, orelse=b):
                return f"(.ifExp {ln} {self.expr(c)} {self.expr(a)} {self.expr(b)})"
            case ast.ListComp() | ast.SetComp() | ast.GeneratorExp():
                gens = []
                for g in e.generators:
                    if g.is_async:
                        self.fail(g, "async comprehension")
                    ifs = self.lst(self.expr(c) for c in g.ifs)
                    gens.append(f"(.mk {self.target(g.target)} {self.expr(g.iter)} {ifs})")
                return f"(.comp {ln} .{COMPS[type(e)]} {self.expr(e.elt)} {self.lst(gens)})"
            case ast.Lambda(args=a, body=b):
                if a.defaults or a.vararg or a.kwonlyargs or a.kwarg:
                    self.fail(e, "lambda parameter form")
                ps = self.lst(str(self.intern(p.arg)) for p in a.args)
                return f"(.lambda {ln} {ps} {self.expr(b)})"
            case ast.List(elts=es):
                return f"(.list {ln} {self.lst(self.expr(x) for x in es)})"
            case ast.Tuple(elts=es):
                return f"(.tuple {ln} {self.lst(self.expr(x) for x in es)})"
            case ast.Dict(keys=ks, values=vs):
                if any(k is None for k in ks):
                    self.fail(e, "dict unpacking")
                pairs = [f"({self.expr(k)}, {self.expr(v)})" for k, v in zip(ks, vs)]
                return f"(.dict {ln} {self.lst(pairs)})"
        self.fail(e, "expression")

    def target(self, t) -> str:
        ln = self.line(t)
        match t:
            case ast.Name(id=x):
                return f"(.name {ln} {self.intern(x)})"
            case ast.Attribute(value=ast.Name(id=m), attr=f) if (m, f) in self.constants:
                return f"(.name {ln} {self.intern(m + '.' + f)})"
            case ast.Attribute(value=o, attr=f):
                return f"(.attr {ln} {self.expr(o)} {self.intern(f)})"
            case ast.Subscript(value=o, slice=ast.Slice(lower=lo, upper=hi, step=None)):
                return f"(.slice {ln} {self.expr(o)} {self.opt(lo)} {self.opt(hi)})"
            case ast.Subscript(value=o, slice=i) if not isinstance(i, ast.Slice):
                return f"(.index {ln} {self.expr(o)} {self.expr(i)})"
            case ast.Tuple(elts=ts) | ast.List(elts=ts):
                return f"(.tuple {ln} {self.lst(self.target(x) for x in ts)})"
        self.fail(t, "target")

    def params(self, a: ast.arguments) -> str:
        if a.kwonlyargs or a.kwarg or a.posonlyargs:
            raise Unsupported("parameter form")
        names = self.lst(str(self.intern(p.arg)) for p in a.args)
        defaults = self.lst(self.expr(d) for d in a.defaults)
        va = "none" if a.vararg is None else f"(some {self.intern(a.vararg.arg)})"
        return f"{{ names := {names}, defaults := {defaults}, vararg := {va} }}"

    def block(self, stmts, indent) -> str:
        if not stmts:
            return "[]"
        pad = " " * indent
        inner = (",\n" + pad + "  ").join(self.stmt(s, indent + 2) for s in stmts)
        return f"[\n{pad}  {inner}]"

    def stmt(self, s, indent) -> str:
        ln = self.line(s)
        match s:
            case ast.Assign(targets=ts, value=v):
                return f"(.assign {ln} {self.lst(self.target(t) for t in ts)} {self.expr(v)})"
            case ast.AnnAssign(target=t, value=v) if v is not None:
                return f"(.annAssign {ln} {self.target(t)} {self.expr(v)})"
            case ast.AugAssign(target=t, op=op, value=v) if type(op) in BINOPS:
                return f"(.augAssign {ln} {self.target(t)} .{BINOPS[type(op)]} {self.expr(v)})"
            case ast.Expr(value=e):
                return f"(.exprStmt {ln} {self.expr(e)})"
            case ast.If(test=c, body=b, orelse=o):
                return f"(.ifStmt {ln} {self.expr(c)} {self.block(b, indent)} {self.block(o, indent)})"
            case ast.For(target=t, iter=it, body=b, orelse=[]):
                return f"(.forStmt {ln} {self.target(t)} {self.expr(it)} {self.block(b, indent)})"
            case ast.While(test=c, body=b, orelse=[]):
                return f"(.whileStmt {ln} {self.expr(c)} {self.block(b, indent)})"
            case ast.Return(value=v):
                return f"(.ret {ln} {self.opt(v)})"
            case ast.Assert(test=e):
                return f"(.assert {ln} {self.expr(e)})"
            case ast.Raise():
                return f"(.raise {ln})"
            case ast.Break():
                return f"(.brk {ln})"
            case ast.Continue():
                return f"(.cont {ln})"
            case ast.Pass():
                return f"(.pass {ln})"
            case ast.FunctionDef(name=n, args=a, body=b, decorator_list=[]):
                body = self.block(strip_docstring(b), indent)
                return f"(.funDef {ln} {self.intern(n)} {self.params(a)} {body})"
        self.fail(s, "statement")


def strip_docstring(body):
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
        if isinstance(body[0].value.value, str):
            return body[1:]
    return body


def code_nodes(fn: ast.FunctionDef):
    """The nodes of the body and of default values, without annotations."""
    out = []

    def visit(n):
        if isinstance(n, ast.arg):
            return
        if isinstance(n, ast.FunctionDef):
            for d in n.args.defaults:
                visit(d)
            for s in n.body:
                visit(s)
            return
        if isinstance(n, ast.Lambda):
            visit(n.body)
            return
        out.append(n)
        for c in ast.iter_child_nodes(n):
            visit(c)

    for d in fn.args.defaults:
        visit(d)
    for s in fn.body:
        visit(s)
    return out


def free_names(fn: ast.FunctionDef):
    nodes = code_nodes(fn)
    bound = set()
    for n in ast.walk(fn):
        if isinstance(n, ast.arg):
            bound.add(n.arg)
        if isinstance(n, ast.FunctionDef) and n is not fn:
            bound.add(n.name)
    bound |= {n.id for n in nodes if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
    return {n.id for n in nodes if isinstance(n, ast.Name) and n.id not in bound}


def config_names(fn: ast.FunctionDef):
    return {n.attr for n in ast.walk(fn) if isinstance(n, ast.Attribute)
            and isinstance(n.value, ast.Name) and n.value.id == "config"}
