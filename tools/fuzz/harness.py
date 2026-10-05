"""Shared parts of the differential fuzzer: the type pool, the encoder to the Lean runner, the
CPython renderer and the client of the Lean runner.

A fuzz case is one Python source text. It defines `mk()`, which builds the arguments, the entry
function `f` and its helpers. `run_python` runs it in CPython. `encode` turns it into the input
of `pythiafuzz` (see `Fuzz/Main.lean`). Both sides print one canonical line, so the two results
compare as strings.
"""

import ast
import os
import signal
import subprocess
import sys
from pathlib import Path

import pydantic
from eth_consensus_specs.gloas import minimal as spec
from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector, _SSZSequence
from ssz.container import Container, ProgressiveContainer, active_fields
from ssz.exceptions import SSZTypeError, SSZValueError
from ssz.ssz_base import SSZType
from ssz.uint import BaseUint

LEAN_DIR = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(LEAN_DIR / "tools"))
import serialize  # noqa: E402
from footprint import footprint  # noqa: E402

RUNNER = LEAN_DIR / ".lake" / "build" / "bin" / "pythiafuzz"
FUEL = 1_000_000

# The type pool. Spec classes where they exist, plus small containers and lists with low limits,
# so that programs reach the limits.
Slot, Epoch, Gwei, ValidatorIndex = spec.Slot, spec.Epoch, spec.Gwei, spec.ValidatorIndex
Uint64, Uint8 = spec.Uint64, spec.Uint8
Bytes4, Bytes32, Root = spec.Bytes4, spec.Bytes32, spec.Root
Checkpoint = spec.Checkpoint


class Pt(Container):
    a: Uint64
    s: Slot
    f: Boolean
    r: Bytes4


class Gweis(List[Gwei]):
    LIMIT = 3


class Gweis2(List[Gwei]):
    """The same shape as `Gweis`, a different class."""
    LIMIT = 3


class Pts(List[Pt]):
    LIMIT = 3


class PtPair(Vector[Pt]):
    LENGTH = 2


class U64s(Vector[Uint64]):
    LENGTH = 3


class Epochs(ProgressiveList[Epoch]):
    pass


class PPts(ProgressiveList[Pt]):
    pass


class Bits(BitList):
    LIMIT = 4


class Box(Container):
    p: Pt
    q: Pt
    ps: Pts
    ns: Gweis
    es: Epochs
    bs: Bits
    i: ValidatorIndex
    k: Uint8


class PBox(ProgressiveContainer):
    ACTIVE_FIELDS = active_fields(width=3)

    g: Gwei
    pp: PPts
    pair: PtPair


class Flags(BitVector):
    LENGTH = 4


class Blob(ByteList):
    LIMIT = 4


class Misc(Container):
    fl: Flags
    bl: Blob
    n: Uint64
    cp: Checkpoint


class FuzzError(Exception):
    """The exception of a generated `raise`. The serializer keeps no `raise` expression."""


POOL = {c.__name__: c for c in [
    Slot, Epoch, Gwei, ValidatorIndex, Uint64, Uint8, Boolean, Bytes4, Bytes32, Root, Checkpoint,
    Pt, Gweis, Gweis2, Pts, PtPair, U64s, Epochs, PPts, Bits, Box, PBox, Flags, Blob, Misc]}
POOL["FuzzError"] = FuzzError
POOL["hash_tree_root"] = spec.hash_tree_root
POOL["ssz_serialize"] = spec.ssz_serialize
SSZ_NAMES = {n for n, c in POOL.items() if isinstance(c, type) and issubclass(c, SSZType)}


def fp_is_heap(t: str, steps) -> bool:
    """Does the FP pattern `(t, steps)` name a container or a list?"""
    cls = POOL.get(t)
    for x in steps:
        if cls is None:
            return False
        cls = getattr(cls, "ELEMENT_TYPE", None) if x == "*" else \
            dict(getattr(cls, "_FIELD_TYPES", [])).get(x)
    return cls is not None and not issubclass(cls, (BaseUint, Boolean, ByteVector))
SEQ_CLASSES = [Gweis, Gweis2, Pts, PtPair, U64s, Epochs, PPts, Bits, Flags, Blob]
CONTAINER_CLASSES = [Pt, Box, PBox, Checkpoint, Misc]


# ---------------------------------------------------------------------------------------------
# Results and rendering

def tag(e: BaseException) -> str:
    if isinstance(e, FuzzError):
        return "raised"
    if isinstance(e, SSZValueError):
        return "sszValue"
    if isinstance(e, pydantic.ValidationError):
        return "validation"
    if isinstance(e, IndexError):
        return "indexError"
    if isinstance(e, KeyError):
        return "keyError"
    if isinstance(e, ZeroDivisionError):
        return "divisionByZero"
    if isinstance(e, (SSZTypeError, TypeError)):
        return "typeError"
    if isinstance(e, AssertionError):
        return "assertionFailed"
    if isinstance(e, NameError):
        return "nameError"
    if isinstance(e, ValueError):
        return "valueError"
    return "other." + type(e).__name__


def err_line(e: BaseException) -> str:
    t = tag(e)
    cls = "invalid" if t in ("assertionFailed", "indexError") else "bug"
    return f"err {cls}:{t}"


def py_bool(b) -> str:
    return "True" if b else "False"


def uint_name(cls) -> str:
    parents = [b for b in cls.__bases__ if issubclass(b, BaseUint)]
    return f"Uint{cls.BITS}" if parents == [BaseUint] else cls.__name__


def ty_str(t) -> str:
    """The type string of an SSZ class, as `Fuzz.Render.tyStr` prints the `SszTy`."""
    if issubclass(t, BaseUint):
        return uint_name(t)
    if issubclass(t, Boolean):
        return "Boolean"
    if issubclass(t, (ByteVector, Container, ProgressiveContainer)):
        return t.__name__
    if issubclass(t, ProgressiveBitList):
        return "ProgressiveBitlist"
    if issubclass(t, BitList):
        return f"Bitlist[{t.LIMIT}]"
    if issubclass(t, BitVector):
        return f"Bitvector[{t.LENGTH}]"
    if issubclass(t, ByteList):
        return f"List[Uint8,{t.LIMIT}]"
    if issubclass(t, ProgressiveList):
        return f"ProgressiveList[{ty_str(t.ELEMENT_TYPE)}]"
    if issubclass(t, List):
        return f"List[{ty_str(t.ELEMENT_TYPE)},{t.LIMIT}]"
    if issubclass(t, Vector):
        return f"Vector[{ty_str(t.ELEMENT_TYPE)},{t.LENGTH}]"
    return f"<{t.__name__}>"


def is_heap(v) -> bool:
    return isinstance(v, (list, set, dict, _SSZSequence, BitList, BitVector, ProgressiveBitList,
                          ByteList, Container, ProgressiveContainer))


class Renderer:
    """The CPython side of `Fuzz.Render.render`: one label space for the whole result.
    With `labels=False`, every visit prints the whole object and no label, so two runs compare
    by value only."""

    def __init__(self, labels: bool = True):
        self.labels = labels
        self.seen: dict[int, int] = {}
        self.keep = []

    def __call__(self, v) -> str:
        if isinstance(v, Boolean):
            return f"Boolean:{py_bool(v)}"
        if type(v) is bool:
            return f"bool:{py_bool(v)}"
        if isinstance(v, BaseUint):
            return f"{uint_name(type(v))}:{int(v)}"
        if type(v) is int:
            return f"int:{v}"
        if type(v) is str:
            return f"str:{v}"
        if v is None:
            return "None"
        if isinstance(v, bytes):
            return f"{type(v).__name__}:{v.hex()}"
        if isinstance(v, tuple):
            return "(" + ",".join(self(x) for x in v) + ")"
        if not is_heap(v):
            return f"<{type(v).__name__}>"
        if self.labels and id(v) in self.seen:
            return f"#{self.seen[id(v)]}"
        k = len(self.seen)
        if self.labels:
            self.seen[id(v)] = k
        self.keep.append(v)
        if isinstance(v, list):
            body = "list[" + ",".join(self(x) for x in v) + "]"
        elif isinstance(v, set):
            body = "set{" + ",".join(sorted(self(x) for x in v)) + "}"
        elif isinstance(v, dict):
            body = "dict{" + ",".join(f"{self(a)}:{self(b)}" for a, b in v.items()) + "}"
        elif isinstance(v, (Container, ProgressiveContainer)):
            fields = ",".join(f"{f}={self(getattr(v, f))}" for f, _ in type(v)._FIELD_TYPES)
            body = type(v).__name__ + "{" + fields + "}"
        else:
            body = ty_str(type(v)) + "[" + ",".join(self(x) for x in v) + "]"
        return f"#{k}={body}" if self.labels else body


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def load(src: str) -> dict:
    ns = dict(POOL)
    ns["_cp"] = _cp
    exec(compile(src, "<fuzz>", "exec"), ns)
    return ns


def run_python(src: str, args: list, timeout: float = 2.0, labels: bool = True,
               ns: dict | None = None) -> str:
    """Run `f(*args)` in CPython and render the result. `args` is changed in place."""
    ns = load(src) if ns is None else ns
    old = signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        try:
            ret = ns["f"](*args)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old)
    except Timeout:
        raise
    except RecursionError:
        return "err other:RecursionError"
    except Exception as e:  # noqa: BLE001
        return err_line(e)
    r = Renderer(labels)
    parts = ["ret=" + r(ret)] + [f"a{i}={r(a)}" for i, a in enumerate(args)]
    return "ok " + " | ".join(parts)


# ---------------------------------------------------------------------------------------------
# The copy-on-store model
#
# The same program, but every value that goes into an object (a field or element write, a
# constructor argument, `append`, a list literal or a dict value) is a deep copy. So no two
# paths ever reach one SSZ object, as in the readable Lean, which uses values. Where the
# result differs from CPython, the program wrote through a shared object, and the write
# condition check must have a hit.

MUTATORS = {"append", "extend", "insert", "add"}


def _cp(v):
    if isinstance(v, (_SSZSequence, BitList, BitVector, ProgressiveBitList, ByteList,
                      Container, ProgressiveContainer)):
        return v.copy()
    # A Python list keeps its identity: the check does not watch Python objects, and `log`
    # must stay one list.
    return v


class CopyOnStore(ast.NodeTransformer):
    @staticmethod
    def wrap(e):
        return ast.Call(func=ast.Name(id="_cp", ctx=ast.Load()), args=[e], keywords=[])

    def visit_FunctionDef(self, node):
        if node.name == "mk":
            return node
        self.generic_visit(node)
        return node

    def visit_Assign(self, node):
        self.generic_visit(node)
        if any(isinstance(t, (ast.Attribute, ast.Subscript)) for t in node.targets):
            node.value = self.wrap(node.value)
        return node

    def visit_AnnAssign(self, node):
        self.generic_visit(node)
        if isinstance(node.target, (ast.Attribute, ast.Subscript)) and node.value is not None:
            node.value = self.wrap(node.value)
        return node

    def visit_Call(self, node):
        self.generic_visit(node)
        f = node.func
        if isinstance(f, ast.Name) and f.id in POOL:
            for k in node.keywords:
                k.value = self.wrap(k.value)
        elif isinstance(f, ast.Attribute) and f.attr in MUTATORS:
            node.args = [self.wrap(a) for a in node.args]
        return node

    def visit_List(self, node):
        self.generic_visit(node)
        if isinstance(node.ctx, ast.Load):
            node.elts = [self.wrap(e) for e in node.elts]
        return node

    def visit_ListComp(self, node):
        self.generic_visit(node)
        node.elt = self.wrap(node.elt)
        return node

    def visit_Dict(self, node):
        self.generic_visit(node)
        node.values = [self.wrap(v) for v in node.values]
        return node


def copy_model(src: str) -> str:
    return ast.unparse(ast.fix_missing_locations(CopyOnStore().visit(ast.parse(src))))


# ---------------------------------------------------------------------------------------------
# Encoding for the Lean runner

SSZ_M = {
    "BaseUint": BaseUint, "Boolean": Boolean, "ByteVector": ByteVector, "ByteList": ByteList,
    "Container": Container, "ProgressiveContainer": ProgressiveContainer, "BitList": BitList,
    "BitVector": BitVector, "ProgressiveBitList": ProgressiveBitList, "List": List,
    "ProgressiveList": ProgressiveList, "Vector": Vector, "SSZType": SSZType,
}


class Encoder:
    def __init__(self):
        self.intern = serialize.Interner()
        self.intern("bytes")
        for k in serialize.KNOWN:
            self.intern(k)
        self.types = serialize.Types(self.intern, SSZ_M)
        self.heap: list[str | None] = []
        self.addr: dict[int, int] = {}
        self.keep = []

    def value(self, v) -> str:
        if isinstance(v, Boolean):
            return f"(.boolean {'true' if v else 'false'})"
        if type(v) is bool:
            return f"(.bool {'true' if v else 'false'})"
        if isinstance(v, BaseUint):
            return f"(.uint {self.types.uint_ty(type(v))} {int(v)})"
        if type(v) is int:
            return f"(.int ({v}))"
        if type(v) is str:
            return f"(.str {serialize.lean_str(v)})"
        if v is None:
            return "(.none)"
        if isinstance(v, bytes):
            return f"(.bytes {self.intern(type(v).__name__)} [{', '.join(str(b) for b in v)}])"
        if isinstance(v, tuple):
            return f"(.tuple [{', '.join(self.value(x) for x in v)}])"
        if not is_heap(v):
            raise serialize.Unsupported(f"input value {v!r}")
        if id(v) in self.addr:
            return f"(.ref {self.addr[id(v)]})"
        a = len(self.heap)
        self.addr[id(v)] = a
        self.keep.append(v)
        self.heap.append(None)
        if isinstance(v, list):
            obj = f"(.list .pyList .any none [{', '.join(self.value(x) for x in v)}])"
        elif isinstance(v, set):
            obj = f"(.set [{', '.join(self.value(x) for x in v)}])"
        elif isinstance(v, dict):
            kvs = [f"({self.value(k)}, {self.value(x)})" for k, x in v.items()]
            obj = f"(.dict [{', '.join(kvs)}])"
        elif isinstance(v, (Container, ProgressiveContainer)):
            self.types.ssz(type(v))
            fs = [self.value(getattr(v, f)) for f, _ in type(v)._FIELD_TYPES]
            obj = f"(.container {self.intern(type(v).__name__)} [{', '.join(fs)}])"
        else:
            t = self.types.ssz(type(v))
            assert t.startswith("(.list ") and t.endswith(")")
            if isinstance(v, ByteList):
                # The interpreter models a byte list as a list of `Uint8`.
                xs = [f"(.uint (.width 8) {x})" for x in v]
            else:
                xs = [self.value(x) for x in v]
            obj = f"{t[:-1]} [{', '.join(xs)}])"
        self.heap[a] = obj
        return f"(.ref {a})"

    def program(self, src: str, args: list) -> str:
        tree = ast.parse(src)
        fns = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name != "mk"]
        names = {fn.name for fn in fns}
        arg_terms = [self.value(a) for a in args]
        globals_ = {}
        for fn in fns:
            em = serialize.Emitter(self.intern, 1)
            body = em.block(serialize.strip_docstring(fn.body), 2).replace("\n", " ")
            globals_[fn.name] = (f"(.fn {self.intern(fn.name)} {em.params(fn.args)} "
                                 f"{fn.lineno} {body})")
        for fn in fns:
            for free in sorted(serialize.free_names(fn)):
                if free in globals_ or free in names or free == "FuzzError":
                    continue
                if free in serialize.ORACLE_FUNCTIONS:
                    globals_[free] = f"(.builtin .{serialize.ORACLE_FUNCTIONS[free]})"
                elif free in serialize.BUILTINS:
                    globals_[free] = f"(.builtin .{serialize.BUILTINS[free]})"
                elif free in POOL and isinstance(POOL[free], type) and \
                        self.types.is_ssz_class(POOL[free]):
                    globals_[free] = f"(.type {self.types.ssz(POOL[free])})"
                else:
                    raise serialize.Unsupported(f"free name {free}")
        fp, _, per_fn = footprint({fn.name: fn for fn in fns}, SSZ_NAMES, fp_is_heap)
        self.intern("*")
        fp_t = ", ".join(f"({self.intern(t)}, [{', '.join(str(self.intern(x)) for x in st)}])"
                         for t, st in fp)
        fnfp_t = ", ".join(
            f"({self.intern(n)}, [" + ", ".join(
                f"({j}, [{', '.join(str(self.intern(x)) for x in st)}])" for j, st in ps) + "])"
            for n, ps in sorted(per_fn.items()) if ps)
        gl = ", ".join(f"({self.intern(k)}, {v})" for k, v in globals_.items())
        containers = ", ".join(v for v in self.types.containers.values() if v)
        names_t = ", ".join(serialize.lean_str(s) for s in self.intern.names)
        return "\n".join([
            f"names [{names_t}]",
            f"containers [{containers}]",
            f"globals [{gl}]",
            f"heap [{', '.join(self.heap)}]",
            f"entry {self.intern('f')}",
            f"args [{', '.join(arg_terms)}]",
            f"fuel {FUEL}",
            f"active [{', '.join(self.types.active.values())}]",
            f"fp [{fp_t}]",
            f"fnfp [{fnfp_t}]",
        ]) + "\n"


def encode(src: str, args: list) -> str:
    return Encoder().program(src, args)


class LeanRunner:
    """A long-lived `pythiafuzz` process: one length-prefixed program in, one line out."""

    def __init__(self, exe: Path = RUNNER, watch: bool = True):
        self.exe = exe
        self.watch = watch
        self.proc = None

    def start(self):
        self.proc = subprocess.Popen([str(self.exe)] + (["--watch"] if self.watch else []), stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, bufsize=0)

    def run(self, program: str) -> str:
        if self.proc is None or self.proc.poll() is not None:
            self.start()
        data = program.encode()
        try:
            self.proc.stdin.write(f"{len(data)}\n".encode() + data)
            self.proc.stdin.flush()
            line = self.proc.stdout.readline()
        except BrokenPipeError:
            line = b""
        if not line:
            code = self.proc.wait()
            self.proc = None
            return f"runner-crash exit {code}"
        return line.decode().rstrip("\n")

    def close(self):
        if self.proc is not None:
            self.proc.stdin.close()
            self.proc.wait()


# Hits that say that a write reached an object by two paths. FP and footprint misses are
# about the static FP tables, not about sharing.
SHARING_HITS = ("write ", "WTree ", "Reach ")


class Outcome:
    def __init__(self, py: str, lean: str, hits: list[str], py_copy: str | None = None,
                 py_plain: str | None = None):
        self.py, self.lean, self.hits = py, lean, hits
        self.py_copy, self.py_plain = py_copy, py_plain

    @property
    def sharing_hits(self) -> list[str]:
        return [h for h in self.hits if h.startswith(SHARING_HITS)]

    @property
    def copy_differs(self) -> bool:
        return self.py_copy is not None and self.py_copy != self.py_plain

    @property
    def hazard_miss(self) -> bool:
        """CPython differs from the copy-on-store model, and the check has no hit."""
        return self.copy_differs and not self.sharing_hits


def run_case(src: str, lean: LeanRunner, copy: bool = False) -> Outcome:
    """The CPython result, the Lean result and the hits of the write condition check. With
    `copy`, also CPython on the copy-on-store model, both rendered without labels."""
    ns = load(src)
    lean_in = encode(src, ns["mk"]())
    py_out = run_python(src, ns["mk"](), ns=ns)
    line = lean.run(lean_in)
    lean_out, *hits = line.split(" || HIT ")
    out = Outcome(py_out, lean_out, hits)
    if copy:
        out.py_plain = run_python(src, ns["mk"](), labels=False, ns=load(src))
        csrc = copy_model(src)
        out.py_copy = run_python(csrc, ns["mk"](), labels=False, ns=load(csrc))
    return out


if __name__ == "__main__":
    # Run one case file: python harness.py CASE.py
    src = Path(sys.argv[1]).read_text()
    runner = LeanRunner()
    o = run_case(src, runner, copy=True)
    print("python:", o.py)
    print("lean:  ", o.lean)
    for h in o.hits:
        print("HIT   ", h)
    if o.copy_differs:
        print("copy-on-store model differs:", o.py_copy)
    if os.environ.get("SHOW_LEAN_INPUT"):
        print(encode(src, load(src)["mk"]()))
    runner.close()
    sys.exit(0 if o.py == o.lean and not o.hazard_miss else 1)
