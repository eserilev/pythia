"""Serialize spec functions from the pyspec SpecObject into Lean syntax trees.

Run from the consensus-specs checkout, in its uv environment:

    cd ../consensus-specs-safe
    uv run python ../consensus-specs-lean/tools/serialize.py --rev 889a389f9 \
        --roots decrease_balance,process_effective_balance_updates,integer_squareroot \
        --namespace Gen --out ../consensus-specs-lean/SpecLean/Gen/Ast.lean

`--rev` extracts that commit with `git archive`, so uncommitted edits do not leak in.
The SpecObject comes from `combine_spec_objects` over the fork's markdown files, as
`pysetup/generate_specs.py` builds it. The SpecObject has no source positions, so the
serializer finds each function's `def` line in the markdown by text search.

The output holds the syntax trees of the roots and their callees, and the environment: types,
dataclasses, constants, the referenced `config` values, modules, builtins and the known names.
`--extra FILE` adds the functions of a Python file (the construct tests), with the spec module
as their namespace.
"""

import argparse
import ast
import dataclasses
import importlib
import inspect
import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from footprint import footprint  # noqa: E402

TOOL_VERSION = "0.2.0"

BUILTINS = {
    "len": "len", "range": "range", "enumerate": "enumerate", "zip": "zip", "sorted": "sorted",
    "min": "min", "max": "max", "sum": "sum", "any": "any", "all": "all", "filter": "filter",
    "list": "list", "tuple": "tuple", "set": "set", "dict": "dict", "bytes": "bytes",
    "int": "int", "bool": "bool", "ssz_serialize": "sszSerialize",
}
# Spec functions whose bodies use library internals. The oracle gives them (SPEC 8).
ORACLE_FUNCTIONS = {"sha256": "sha256", "hash_tree_root": "hashTreeRoot"}
# Spec functions that pyspec replaces with a BLS call (`implement_optimizations`). The
# markdown text is for show only. They become `bls.<name>` (SPEC 8).
BLS_FUNCTIONS = {"eth_aggregate_pubkeys": "AggregatePKs"}
# Data members of the `bls` module. `bls.X` becomes the constant `bls.X`.
BLS_CONSTANTS = {"G2_POINT_AT_INFINITY"}
FORK_MODULES = {"phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas"}
KNOWN = ["append", "extend", "index", "count", "copy", "union", "intersection", "add",
         "from_bytes", "empty", "hash_tree_root", "data", "key", "reverse", "strict", "get",
         "Bytes32", "Root"]
ANNOTATION_ONLY = {"Any", "Callable", "Sequence", "SSZObject", "Uint", "List", "BitVector",
                   "ProgressiveList", "Optional", "Tuple", "Set", "Dict"}


class Unsupported(Exception):
    pass


def build_spec_object(spec_dir: Path, fork: str, preset_name: str):
    sys.path.insert(0, str(spec_dir))
    os.chdir(spec_dir)
    from pysetup.generate_specs import get_spec, load_config, load_preset
    from pysetup.helpers import combine_spec_objects, finalized_spec_object
    from pysetup.md_doc_paths import get_md_doc_paths

    sources = [Path(p) for p in get_md_doc_paths(fork).split()]
    preset = load_preset(tuple(sorted(Path(f"presets/{preset_name}").glob("*.yaml"))))
    config = load_config(Path(f"configs/{preset_name}.yaml"))
    specs = [get_spec(s, preset, config, preset_name) for s in sources]
    spec_object = specs[0]
    for other in specs[1:]:
        spec_object = combine_spec_objects(spec_object, other)
    return finalized_spec_object(spec_object), sources


def find_source_line(sources, name: str, text: str):
    """The markdown file and line of the `def` that produced `text`. The last match wins."""
    body = text.splitlines()
    found = None
    for src in sources:
        lines = src.read_text().splitlines()
        for i, line in enumerate(lines):
            if line == body[0] and lines[i : i + len(body)] == body:
                found = (str(src), i + 1)
    if found is None:
        raise Unsupported(f"no markdown source for {name}")
    return found


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
    def __init__(self, intern: Interner, base_line: int):
        self.intern = intern
        self.base = base_line - 1

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
            case ast.Attribute(value=ast.Name(id="bls"), attr=f) if f in BLS_CONSTANTS:
                return f"(.name {ln} {self.intern('bls.' + f)})"
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
            case ast.Attribute(value=ast.Name(id="bls"), attr=f) if f in BLS_CONSTANTS:
                return f"(.name {ln} {self.intern('bls.' + f)})"
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


class Types:
    """SSZ types and dataclasses that the code references, emitted as Lean data."""

    def __init__(self, intern, m, spec=None, prev=""):
        self.intern, self.m = intern, m
        # A class of an older fork that the build does not have gets the fork's prefix, as in
        # `fulu.BeaconState`.
        self.spec, self.prev = spec, prev
        self.containers: dict[str, str] = {}
        self.active: dict[str, str] = {}

    def cname(self, cls) -> str:
        name = cls.__name__
        if self.spec is None or getattr(self.spec, name, None) is cls:
            return name
        return f"{self.prev}.{name}"

    def uint_ty(self, cls) -> str:
        BaseUint = self.m["BaseUint"]
        parents = [b for b in cls.__bases__ if issubclass(b, BaseUint)]
        if parents == [BaseUint]:
            return f"(.width {cls.BITS})"
        if len(parents) == 1 and parents[0].__bases__ == (BaseUint,):
            return f"(.nominal {self.intern(self.cname(cls))} {cls.BITS})"
        raise Unsupported(f"uint class depth: {cls.__name__}")

    def ssz(self, t) -> str:
        m = self.m
        if issubclass(t, m["BaseUint"]):
            return f"(.uint {self.uint_ty(t)})"
        if issubclass(t, m["Boolean"]):
            return ".boolean"
        if issubclass(t, m["ByteVector"]):
            return f"(.bytes {self.intern(self.cname(t))} {t.LENGTH})"
        if issubclass(t, m["Container"]) or issubclass(t, m["ProgressiveContainer"]):
            self.container(t)
            return f"(.container {self.intern(self.cname(t))})"
        for kind, base in [("progressiveBitlist", "ProgressiveBitList"), ("bitlist", "BitList"),
                           ("bitvector", "BitVector")]:
            if issubclass(t, m[base]):
                limit = getattr(t, "LIMIT", None) if kind == "bitlist" else getattr(t, "LENGTH", None)
                lim = "none" if limit is None else f"(some {limit})"
                return f"(.list .{kind} .boolean {lim})"
        if issubclass(t, m["ByteList"]):
            return f"(.list .list (.uint (.width 8)) (some {t.LIMIT}))"
        for kind, base in [("progressiveList", "ProgressiveList"), ("list", "List"),
                           ("vector", "Vector")]:
            if issubclass(t, m[base]):
                limit = None if kind == "progressiveList" else (t.LIMIT if kind == "list" else t.LENGTH)
                lim = "none" if limit is None else f"(some {limit})"
                return f"(.list .{kind} {self.ssz(t.ELEMENT_TYPE)} {lim})"
        raise Unsupported(f"SSZ type {t}")

    def container(self, t):
        name = self.cname(t)
        if name in self.containers:
            return
        self.containers[name] = ""
        fields = [f"({self.intern(f)}, {self.ssz(ft)})" for f, ft in t._FIELD_TYPES]
        self.containers[name] = f"({self.intern(name)}, [{', '.join(fields)}])"
        if issubclass(t, self.m["ProgressiveContainer"]):
            bits = ", ".join(str(int(b)) for b in t.ACTIVE_FIELDS)
            self.active[name] = f"({self.intern(name)}, [{bits}])"

    def dataclass(self, t):
        name = t.__name__
        fields = [f"({self.intern(f.name)}, .any)" for f in dataclasses.fields(t)]
        self.containers[name] = f"({self.intern(name)}, [{', '.join(fields)}])"

    def is_ssz_class(self, obj) -> bool:
        return inspect.isclass(obj) and issubclass(obj, self.m["SSZType"])


def value_term(v, types: Types) -> str:
    m, intern = types.m, types.intern
    if isinstance(v, m["BaseUint"]):
        return f"(.uint {types.uint_ty(type(v))} {int(v)})"
    if isinstance(v, m["Boolean"]):
        return f"(.boolean {'true' if v else 'false'})"
    if isinstance(v, bytes):
        return f"(.bytes {intern(type(v).__name__)} [{', '.join(str(b) for b in v)}])"
    if type(v) is bool:
        return f"(.bool {'true' if v else 'false'})"
    if type(v) is int:
        return f"(.int ({v}))"
    if type(v) is str:
        return f"(.str {lean_str(v)})"
    if v is None:
        return ".none"
    if isinstance(v, (list, tuple)):
        return f"(.tuple [{', '.join(value_term(x, types) for x in v)}])"
    if isinstance(v, dict) or type(v).__name__ == "frozendict":
        kvs = [f"({value_term(k, types)}, {value_term(x, types)})" for k, x in v.items()]
        return f"(.frozenDict [{', '.join(kvs)}])"
    raise Unsupported(f"constant value {v!r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default="889a389f9")
    ap.add_argument("--fork", default="gloas")
    ap.add_argument("--preset", default="minimal")
    ap.add_argument("--roots",
                    default="decrease_balance,process_effective_balance_updates,integer_squareroot")
    ap.add_argument("--namespace", default="Gen")
    ap.add_argument("--extra", default=None)
    ap.add_argument("--containers", default="BeaconState",
                    help="container types to emit even if the code does not name them")
    ap.add_argument("--out", required=True)
    ap.add_argument("--fp-out", default=None, help="write FP and the write sites as text")
    ap.add_argument("--prev-fork", default=None,
                    help="also emit the BeaconState of this fork, for the upgrade function")
    args = ap.parse_args()

    repo = Path.cwd()
    out = Path(args.out).resolve()
    extra = Path(args.extra).resolve() if args.extra else None
    commit = subprocess.check_output(["git", "rev-parse", args.rev], text=True).strip()
    tmp = Path(tempfile.mkdtemp(prefix="spec-"))
    archive = subprocess.run(["git", "archive", commit], check=True, capture_output=True).stdout
    subprocess.run(["tar", "-x", "-C", str(tmp)], input=archive, check=True)

    spec_object, sources = build_spec_object(tmp, args.fork, args.preset)
    os.chdir(repo)
    spec = importlib.import_module(f"eth_consensus_specs.{args.fork}.{args.preset}")
    import ssz.bitfields, ssz.boolean, ssz.byte_arrays, ssz.collections, ssz.container
    import ssz.ssz_base, ssz.uint

    m = {
        "BaseUint": ssz.uint.BaseUint, "Boolean": ssz.boolean.Boolean,
        "ByteVector": ssz.byte_arrays.ByteVector, "ByteList": ssz.byte_arrays.ByteList,
        "Container": ssz.container.Container,
        "ProgressiveContainer": ssz.container.ProgressiveContainer,
        "BitList": ssz.bitfields.BitList, "BitVector": ssz.bitfields.BitVector,
        "ProgressiveBitList": ssz.bitfields.ProgressiveBitList, "List": ssz.collections.List,
        "ProgressiveList": ssz.collections.ProgressiveList, "Vector": ssz.collections.Vector,
        "SSZType": ssz.ssz_base.SSZType,
    }

    intern = Interner()
    intern("bytes")
    types = Types(intern, m)

    sources_text = dict(spec_object.functions)
    extra_names = []
    if extra is not None:
        extra_src = extra.read_text()
        for node in ast.parse(extra_src).body:
            if isinstance(node, ast.FunctionDef):
                sources_text[node.name] = ast.get_source_segment(extra_src, node)
                extra_names.append(node.name)

    roots = [r for r in args.roots.split(",") if r] + extra_names
    todo, fns = list(roots), {}
    while todo:
        name = todo.pop()
        if (name in fns or name in ORACLE_FUNCTIONS or name in BLS_FUNCTIONS
                or name not in sources_text):
            continue
        tree = ast.parse(sources_text[name]).body[0]
        fns[name] = tree
        todo += [c for c in free_names(tree) if c in sources_text]

    defs, globals_, configs, base_lines = [], {}, set(), {}
    for name in sorted(fns):
        tree = fns[name]
        text = sources_text[name]
        if name in extra_names:
            src = extra.name
            line = next(n.lineno for n in ast.parse(extra.read_text()).body
                        if isinstance(n, ast.FunctionDef) and n.name == name)
        else:
            src, line = find_source_line(sources, name, text)
        base_lines[name] = (src, line)
        em = Emitter(intern, line)
        params = em.params(tree.args)
        body = em.block(strip_docstring(tree.body), 2)
        quoted = text.rstrip().replace("-/", "- /").replace("/-", "/ -")
        defs.append(
            f"/-- `{src}:{line}`\n```python\n{quoted}\n``` -/\n"
            f"def fn_{name} : FunctionDef where\n"
            f"  name := {intern(name)}\n  params := {params}\n"
            f"  line := {line}\n  body := {body}\n"
        )
        globals_[name] = f"(.fn fn_{name})"
        configs |= config_names(tree)
    for name in sorted(fns):
        for free in sorted(free_names(fns[name])):
            if free in globals_:
                continue
            if free in ORACLE_FUNCTIONS:
                globals_[free] = f"(.builtin .{ORACLE_FUNCTIONS[free]})"
            elif free in BLS_FUNCTIONS:
                globals_[free] = (f"(.const (.member (.glob {intern('bls')}) "
                                  f"{intern(BLS_FUNCTIONS[free])}))")
                globals_.setdefault("bls", "(.module .bls)")
            elif free in BUILTINS:
                globals_[free] = f"(.builtin .{BUILTINS[free]})"
            elif free == "bls":
                globals_[free] = "(.module .bls)"
            elif free in FORK_MODULES:
                globals_[free] = "(.module .fork)"
            elif free == "config":
                globals_[free] = "(.module .config)"
            elif free in ANNOTATION_ONLY:
                continue
            elif free in spec_object.config_vars:
                # A runtime configuration value: looked up in `Env.config` at each read.
                globals_[free] = "(.configVar)"
                configs.add(free)
            else:
                obj = getattr(spec, free, None)
                if obj is None:
                    raise Unsupported(f"{name}: free name {free}")
                if types.is_ssz_class(obj):
                    globals_[free] = f"(.type {types.ssz(obj)})"
                elif inspect.isclass(obj) and dataclasses.is_dataclass(obj):
                    types.dataclass(obj)
                    globals_[free] = f"(.dataclass {intern(obj.__name__)})"
                elif not callable(obj) or isinstance(obj, (bytes, int)):
                    globals_[free] = f"(.const {value_term(obj, types)})"
                else:
                    raise Unsupported(f"{name}: free name {free}")

    for c in sorted(BLS_CONSTANTS):
        if f"bls.{c}" in intern.ids:
            globals_[f"bls.{c}"] = f"(.const {value_term(getattr(spec.bls, c), types)})"
    for c in [c for c in args.containers.split(",") if c]:
        types.ssz(getattr(spec, c))
    if args.prev_fork:
        prev = importlib.import_module(f"eth_consensus_specs.{args.prev_fork}.{args.preset}")
        types.spec, types.prev = spec, args.prev_fork
        types.ssz(prev.BeaconState)
    ssz_names = {n for n in dir(spec) if types.is_ssz_class(getattr(spec, n))}
    def is_heap(t, steps):
        cls = getattr(spec, t)
        for x in steps:
            if x == "*":
                cls = getattr(cls, "ELEMENT_TYPE", None)
            else:
                cls = dict(getattr(cls, "_FIELD_TYPES", [])).get(x)
            if cls is None:
                return False
        return not issubclass(cls, (m["BaseUint"], m["Boolean"], m["ByteVector"]))

    fp, sites, per_fn = footprint(fns, ssz_names, is_heap)
    fn_fp_terms = [
        f"({intern(n)}, [{', '.join(f'({j}, [{chr(44).join(str(intern(x)) for x in st)}])' for j, st in ps)}])"
        for n, ps in sorted(per_fn.items()) if ps]
    fp_terms = [f"({intern(t)}, [{', '.join(str(intern(x)) for x in steps)}])" for t, steps in fp]
    if args.fp_out:
        Path(args.fp_out).write_text(
            "".join(f"FP {t}{''.join('.' + x for x in steps)}\n" for t, steps in fp)
            + "".join(f"WRITE {n}:{base_lines[n][0]}:{base_lines[n][1] + line - 1} {t}{''.join('.' + x for x in steps)}\n"
                      for n, line, t, steps in sites))
    config_terms = [f"({intern(c)}, {value_term(getattr(spec.config, c), types)})"
                    for c in sorted(configs)]
    known = {k: intern(k) for k in KNOWN}
    ns = args.namespace
    gl = ",\n".join(f"  ({intern(k)}, {v})" for k, v in globals_.items())
    ids = "\n".join(f"abbrev «{s}» : Name := {i}" for i, s in enumerate(intern.names))
    name_table = ",\n  ".join(lean_str(s) for s in intern.names)
    containers = ",\n  ".join(v for v in types.containers.values() if v)
    known_fields = "\n".join(
        f"  {lean}  := {known[py]}" for lean, py in [
            ("append", "append"), ("extend", "extend"), ("index", "index"), ("count", "count"),
            ("copy", "copy"), ("union", "union"), ("intersection", "intersection"),
            ("add", "add"), ("fromBytes", "from_bytes"), ("empty", "empty"),
            ("hashTreeRoot", "hash_tree_root"), ("data", "data"), ("key", "key"),
            ("reverse", "reverse"), ("strict", "strict"), ("get", "get"),
            ("bytes32", "Bytes32"), ("root", "Root")])
    nl = "\n"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        f"""-- Generated by tools/serialize.py {TOOL_VERSION}. Do not edit.
-- Spec: consensus-specs {commit} ({args.fork}, {args.preset}).
import SpecLean.Interp

namespace SpecLean.{ns}

/-- Interned names. Index `i` is the name with id `i`. -/
def names : Array String := #[
  {name_table}]

namespace Id
{ids}
end Id

open SpecLean

{nl.join(defs)}
def containers : List (Name × List (Name × SszTy)) := [
  {containers}]

/-- The layout of each progressive container: one bit per position (EIP-7495). -/
def activeFields : List (Name × List Nat) := [
  {(','+nl+'  ').join(types.active.values())}]

/-- FP: the pattern of each object that a function of this build changes in place (SPEC 9.2).
A pattern is a root type and a list of steps. A step is a field name or `*`, any element. -/
def footprint : List (Name × List Name) := [
  {(','+nl+'  ').join(fp_terms)}]

/-- `Footprint f` of each function that writes in place: a parameter index and the steps from
it. A step is a field name or `*`. -/
def fnFootprint : List (Name × List (Nat × List Name)) := [
  {(','+nl+'  ').join(fn_fp_terms)}]

def globals : List (Name × Global) := [
{gl}]

def config : List (Name × Value) := [
  {(','+nl+'  ').join(config_terms)}]

def knownNames : KnownNames where
{known_fields}

/-- The environment of this build. The oracle gives `sha256`, `hash_tree_root` and BLS. -/
def env (o : Oracle) : Env :=
  {{ globals, containers, bytesName := 0, nm := knownNames, config,
     sha256 := o.sha256, hashTreeRoot := o.hashTreeRoot, bls := o.bls }}

end SpecLean.{ns}
"""
    )
    print(f"wrote {out}: {len(defs)} functions, {len(intern.names)} names, "
          f"{len([c for c in types.containers.values() if c])} containers")


if __name__ == "__main__":
    try:
        main()
    except Unsupported as e:
        sys.exit(f"serialize: unsupported: {e}")
