"""Random fuzz cases: small typed programs over the type pool of `harness.py`.

`gen_case(ch)` draws every choice through `ch`, a `Ch` over Hypothesis data, so Hypothesis
shrinks a case by shrinking its choices. Choice 0 is always the simplest option.

A case is Python source: `mk()` builds the arguments, `tr` logs evaluation order, `g0`, `g1`
are helpers, and `f(a0, ..., log)` is the entry function. The generator keeps every program
finite: an append to a list without a limit is guarded by `len(...) < 5`, `while` loops count,
helpers call only earlier helpers, and no loop iterates `log`. Sets are iterated only through
`sorted`, `len` or `in` (SPEC 6.3).
"""

import ast

from hypothesis import strategies as st

import harness as H

INT, BOOL, BOOLEAN, NONE = ("int",), ("bool",), ("Boolean",), ("none",)

# Known differences that a campaign can switch off, so that it looks for new ones:
# - "boolleft": a Python `bool` operand in arithmetic and comparisons with uints.
# - "mismatch": writes, appends and constructor arguments of a deliberately wrong type.
# - "ctorlen": `List(data=...)` over the limit and `Vector(data=...)` of the wrong length.
# - "livecomp": a comprehension that appends to the list it iterates (`grow`).
# - "pycopy": `.copy()` of a Python list.
# - "shortcircuit": `any` and `all` over a generator with side effects or errors.
# - "negstep": `range` with a negative step.
# - "dictorder": dict literals with more than one entry.
# - "bitlength": `int.bit_length()`.
# - "bytelist": the `ByteList` class `Blob` and the container `Misc` that holds one.
# - "dictviews": `.items()`, `.values()` and `.keys()` of a dict.
# - "setmethods": `union`, `intersection` and `difference` of a set.
# - "subfield": uint arithmetic across classes, whose result (a subclass) can reach a field of
#   the base class.
AVOID: set[str] = set()


def mis(pct):
    """The chance in percent of a deliberately wrong type."""
    return 0 if "mismatch" in AVOID else pct


def U(c):
    return ("uint", c)


def BY(c):
    return ("bytes", c)


def C(c):
    return ("cont", c)


def S(c):
    return ("seq", c)


def PL(e):
    return ("pylist", e)


def DICT(k, v):
    return ("dict", k, v)


def SET(e):
    return ("set", e)


UINTS = [H.Uint64, H.Slot, H.Epoch, H.Gwei, H.ValidatorIndex, H.Uint8]
BYTES = [H.Bytes4, H.Root, H.Bytes32]


def of_class(c):
    if issubclass(c, H.BaseUint):
        return U(c)
    if issubclass(c, H.Boolean):
        return BOOLEAN
    if issubclass(c, H.ByteVector):
        return BY(c)
    if issubclass(c, (H.Container, H.ProgressiveContainer)):
        return C(c)
    return S(c)


def fields(T):
    return [(f, of_class(ft)) for f, ft in T[1]._FIELD_TYPES]


def elem(T):
    if T[0] == "pylist":
        return T[1]
    c = T[1]
    if issubclass(c, (H.BitList, H.BitVector)):
        return BOOLEAN
    if issubclass(c, H.ByteList):
        return INT
    return of_class(c.ELEMENT_TYPE)


def is_ref(T):
    return T[0] in ("cont", "seq", "pylist", "dict", "set")


def is_seq(T):
    return T[0] in ("seq", "pylist")


def growable(T):
    """Has `append`: not a vector."""
    return T[0] == "pylist" or (T[0] == "seq" and not issubclass(T[1], (H.Vector, H.BitVector)))


def unbounded(T):
    return T[0] == "pylist" or (T[0] == "seq" and issubclass(T[1], H.ProgressiveList))


def sliceable_list(T):
    """`P[a:b]` gives the same class back for these (SPEC: `getSlice`)."""
    return T[0] == "seq" and issubclass(T[1], (H.List, H.ProgressiveList))


def numeric(T):
    return T[0] in ("int", "uint", "bool")


ARG_TYPES = [
    (6, C(H.Box)), (3, C(H.Pt)), (2, C(H.PBox)), (1, C(H.Checkpoint)), (2, S(H.Pts)),
    (2, S(H.Gweis)), (1, S(H.Gweis2)), (1, S(H.PPts)), (1, S(H.Epochs)), (1, S(H.Bits)),
    (1, S(H.U64s)), (1, S(H.PtPair)), (2, U(H.Gwei)), (1, U(H.Slot)), (1, U(H.Uint64)),
    (1, U(H.Uint8)), (1, INT), (1, BOOL), (1, BY(H.Root)), (1, PL(C(H.Pt))), (1, PL(INT)),
    (1, PL(U(H.Gwei))), (2, C(H.Misc)), (1, S(H.Flags)), (1, S(H.Blob)),
]

LOCAL_TYPES = ARG_TYPES + [(1, BY(H.Bytes32)), (1, BOOLEAN), (1, U(H.Epoch)),
                           (1, U(H.ValidatorIndex)), (1, BY(bytes))]


def avail(types):
    """The weighted types without the ones that an `AVOID` knob switches off."""
    if "bytelist" in AVOID:
        types = [(w, T) for w, T in types if T not in (S(H.Blob), C(H.Misc))]
    return types


class Ch:
    """Choices through Hypothesis. Each choice shrinks toward 0."""

    def __init__(self, draw):
        self.draw = draw

    def int(self, lo, hi):
        return self.draw(st.integers(lo, hi)) if hi > lo else lo

    def pick(self, xs):
        return xs[self.int(0, len(xs) - 1)]

    def lit(self, xs, common=6):
        """A literal: the first `common` items are three times as likely as the rest."""
        return self.weighted([(3 if i < common else 1, x) for i, x in enumerate(xs)])

    def flip(self, pct):
        return self.int(0, 99) >= 100 - pct

    def weighted(self, opts):
        opts = [(w, v) for w, v in opts if w > 0]
        r = self.int(0, sum(w for w, _ in opts) - 1)
        for w, v in opts:
            if r < w:
                return v
            r -= w
        return opts[-1][1]


def uint_lits(c):
    top = 2 ** c.BITS - 1
    return [0, 1, 2, 3, top, top - 1, 5, 2 ** c.BITS, -1]


INT_LITS = [0, 1, 2, 3, -1, 5, 7, 2 ** 64 - 1, 2 ** 64, -(2 ** 64), 255, 256, 2 ** 63, -2]


GUARDABLE = {"field", "elem", "aug", "append", "slice", "extend"}


class Scope:
    def __init__(self, vars_, in_helper):
        self.vars = dict(vars_)
        self.in_helper = in_helper

    def child(self):
        return Scope(self.vars, self.in_helper)


class Gen:
    def __init__(self, ch: Ch):
        self.ch = ch
        self.n = 0
        self.tr = 0
        self.helpers = []  # (name, param types, return type)
        # A statement that indexes with 0 or -1 is often guarded by `if len(base) > 0:`, so
        # that fewer programs end early in an IndexError.
        self.guarding = False
        self.guard_bases = []
        self.lines = []
        self.indent = 1

    def fresh(self, p):
        self.n += 1
        return f"{p}{self.n}"

    def emit(self, s):
        self.lines.append("    " * self.indent + s)

    # ---------------------------------------------------------------------------------------
    # Paths

    def walk(self, e, T, d, out):
        out.append((e, T))
        if d >= 2:
            return
        if T[0] == "cont":
            for f, ft in fields(T):
                self.walk(f"{e}.{f}", ft, d + 1, out)
        elif is_seq(T):
            self.walk(e + "[{}]", elem(T), d + 1, out)

    def paths(self, sc):
        out = []
        for v, T in sc.vars.items():
            self.walk(v, T, 0, out)
        return out

    def index(self, sc, base):
        k = self.ch.weighted([(24, "0"), (4, "1"), (6, "-1"), (1, "2"), (1, "3"), (1, "len"),
                              (2, "vi"), (1, "True"), (1, "-4"), (2, "tr")])
        if self.guarding and k in ("0", "-1") and "tr(" not in base:
            self.guard_bases.append(base)
        if k == "len":
            return f"len({base})"
        if k == "vi":
            return "ValidatorIndex(0)"
        if k == "tr":
            return self.trace("0")
        return k

    def fill(self, sc, template):
        """Fill each `{}` index slot of a path from left to right."""
        out = ""
        parts = template.split("[{}]")
        for i, p in enumerate(parts):
            out += p
            if i < len(parts) - 1:
                out += "[" + self.index(sc, out) + "]"
        return out

    def path_of(self, sc, pred, pdepth=None):
        ps = [(e, T) for e, T in self.paths(sc) if pred(T)]
        if not ps:
            return None
        e, T = self.ch.pick(ps)
        return self.fill(sc, e), T

    def path_eq(self, sc, T):
        r = self.path_of(sc, lambda t: t == T)
        return None if r is None else r[0]

    def trace(self, e):
        self.tr += 1
        return f"tr(log, {self.tr}, {e})"

    # ---------------------------------------------------------------------------------------
    # Expressions

    def expr(self, T, sc, d=2):
        e = self.expr0(T, sc, d)
        if self.ch.flip(6):
            e = self.trace(e)
        return e

    def helper_call(self, T, sc, d):
        hs = [h for h in self.helpers if h[2] == T]
        if not hs or d <= 0:
            return None
        name, ps, _ = self.ch.pick(hs)
        args = ", ".join(["log"] + [self.expr(p, sc, d - 1) for p in ps])
        return f"{name}({args})"

    def expr0(self, T, sc, d):
        ch = self.ch
        p = self.path_eq(sc, T)
        opts = [(1, "lit")]
        if p is not None:
            opts.append((8, "path"))
        if d > 0:
            opts += [(1, "ifexp"), (2, "helper")]
        kind = ch.weighted(opts)
        if kind == "path":
            return p
        if kind == "ifexp":
            return f"({self.expr(T, sc, d - 1)} if {self.expr(BOOL, sc, d - 1)} " \
                   f"else {self.expr(T, sc, d - 1)})"
        if kind == "helper":
            r = self.helper_call(T, sc, d)
            if r is not None:
                return r
        k = T[0]
        if k == "int":
            return self.int_expr(sc, d)
        if k == "bool":
            return self.bool_expr(sc, d)
        if k == "uint":
            return self.uint_expr(T[1], sc, d)
        if k == "Boolean":
            return ch.weighted([(3, "Boolean(False)"), (3, "Boolean(True)"), (2, "True"),
                                (1, "False"), (2, f"Boolean({self.expr(BOOL, sc, d - 1)})"),
                                (1, "Boolean(1)"), (mis(1), "0")])
        if k == "bytes":
            return self.bytes_expr(T[1], sc, d)
        if k == "cont":
            return self.cont_expr(T, sc, d)
        if k == "seq":
            return self.seq_expr(T, sc, d)
        if k == "pylist":
            return self.pylist_expr(T, sc, d)
        if k == "set":
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == T[1])
            j = ch.pick(["lit", "set", "comp", "empty"])
            if r and j == "set":
                return f"set({r[0]})"
            if r and j == "comp":
                return f"{{x for x in {r[0]}}}"
            if j == "lit" and d > 0:
                return "set([" + self.elems(T[1], sc, d, ch.int(1, 3)) + "])"
            return "set()"
        if k == "dict":
            n = ch.int(0, 1 if "dictorder" in AVOID else 2) if d > 0 else 0
            kvs = [f"{self.expr(T[1], sc, d - 1)}: {self.expr(T[2], sc, d - 1)}" for _ in range(n)]
            return "{" + ", ".join(kvs) + "}"
        return "None"

    def any_numeric(self, sc, d):
        T = self.ch.weighted([(4, U(H.Gwei)), (2, INT), (2, U(H.Uint64)), (1, U(H.Slot)),
                              (1, U(H.Epoch)), (1, U(H.Uint8)),
                              (0 if "boolleft" in AVOID else 1, BOOL),
                              (1, U(H.ValidatorIndex))])
        return self.expr(T, sc, d), T

    def int_expr(self, sc, d):
        ch = self.ch
        k = ch.weighted([(4, "lit"), (2, "len"), (1, "int"), (2, "binop"), (1, "neg"),
                         (1, "index"), (1, "count"), (1, "setlen"), (1, "sum"),
                         (0 if "bitlength" in AVOID else 1, "bitlen"), (1, "frombytes"),
                         (1, "serlen"), (1, "star")])
        if d <= 0 or k == "lit":
            return str(ch.lit(INT_LITS))
        if k == "bitlen":
            e, _ = self.any_numeric(sc, d - 1)
            return f"({e}).bit_length()"
        if k == "frombytes":
            b = self.expr(BY(ch.pick(BYTES + [bytes])), sc, d - 1)
            return f"int.from_bytes({b}, {ch.pick([repr('little'), repr('big')])})"
        if k == "serlen":
            e, _ = self.any_numeric(sc, d - 1)
            return f"len(ssz_serialize({e}))"
        if k == "star":
            return f"{ch.pick(['min', 'max'])}(*[{self.expr(INT, sc, d - 1)}, " \
                   f"{self.expr(INT, sc, d - 1)}])"
        if k == "len":
            r = self.path_of(sc, is_seq)
            if r:
                return f"len({r[0]})"
            return "len([])"
        if k == "int":
            e, _ = self.any_numeric(sc, d - 1)
            return f"int({e})"
        if k == "binop":
            op = ch.pick(["+", "-", "*", "//", "%", "&", "|", "^", "<<", ">>"])
            b = str(ch.int(0, 3)) if op in ("<<", ">>") else self.expr(INT, sc, d - 1)
            return f"({self.expr(INT, sc, d - 1)} {op} {b})"
        if k == "neg":
            e, _ = self.any_numeric(sc, d - 1)
            return f"(-{e})"
        if k in ("index", "count"):
            r = self.path_of(sc, is_seq)
            if r:
                return f"{r[0]}.{k}({self.expr(elem(r[1]), sc, d - 1)})"
            return "0"
        if k == "setlen":
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t)[0] in ("int", "uint"))
            if r:
                return f"len(set({r[0]}))"
            return "0"
        r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == INT)
        return f"sum({r[0]})" if r else "sum([])"

    def bool_expr(self, sc, d):
        ch = self.ch
        if d <= 0:
            return ch.pick(["True", "False"])
        k = ch.weighted([(2, "lit"), (5, "cmp"), (2, "in"), (2, "is"), (2, "eq"), (1, "not"),
                         (1, "andor"), (1, "anyall"), (1, "bytes"), (1, "setin"),
                         (1, "chain")])
        if k == "lit":
            return ch.pick(["True", "False"])
        if k in ("cmp", "chain"):
            a, ta = self.any_numeric(sc, d - 1)
            # Mostly the same class on both sides, sometimes a mix.
            tb = ta if ch.flip(70) else self.any_numeric(sc, 0)[1]
            b = self.expr(tb, sc, d - 1)
            op = ch.pick(["==", "<", ">=", "!=", "<=", ">"])
            if k == "chain":
                return f"({a} {op} {b} {ch.pick(['<', '==', '<='])} {self.expr(tb, sc, d - 1)})"
            return f"({a} {op} {b})"
        if k in ("in", "setin"):
            r = self.path_of(sc, lambda t: is_seq(t) and (k == "in" or elem(t)[0] == "uint"))
            if r:
                et = elem(r[1])
                if et[0] == "uint" and ch.flip(25):
                    et = U(ch.pick(UINTS))
                coll = f"set({r[0]})" if k == "setin" else r[0]
                return f"({self.expr(et, sc, d - 1)} {ch.pick(['in', 'not in'])} {coll})"
            return "False"
        if k in ("is", "eq"):
            T = ch.weighted([(3, C(H.Pt)), (2, C(H.Box)), (1, S(H.Gweis)), (1, S(H.Pts)),
                             (1, PL(INT))])
            a, b = self.expr(T, sc, d - 1), self.expr(T, sc, d - 1)
            op = ch.pick(["is", "is not"]) if k == "is" else ch.pick(["==", "!="])
            return f"({a} {op} {b})"
        if k == "not":
            return f"(not {self.expr(BOOL, sc, d - 1)})"
        if k == "andor":
            return f"({self.expr(BOOL, sc, d - 1)} {ch.pick(['and', 'or'])} " \
                   f"{self.expr(BOOL, sc, d - 1)})"
        if k == "anyall":
            fn = ch.pick(["any", "all"])
            if "shortcircuit" not in AVOID and ch.flip(40):
                r = self.path_of(sc, lambda t: is_seq(t) and elem(t)[0] in ("uint", "int"))
                if r:
                    body = ch.pick([f"{self.trace('x')} > 0", "1 // x > 0", "x > 0",
                                    f"{self.trace('x == 0')}"])
                    return f"{fn}({body} for x in {r[0]})"
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == C(H.Pt))
            if r:
                return f"{fn}(x.f for x in {r[0]})"
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t)[0] == "uint")
            if r:
                return f"{fn}(x > 1 for x in {r[0]})"
            return f"{fn}([])"
        ta = BY(ch.pick(BYTES))
        tb = ta if ch.flip(60) else BY(ch.pick(BYTES + [bytes]))
        return f"({self.expr(ta, sc, d - 1)} {ch.pick(['==', '!='])} {self.expr(tb, sc, d - 1)})"

    def uint_expr(self, c, sc, d):
        ch = self.ch
        k = ch.weighted([(4, "lit"), (4, "binop"), (2, "minmax"), (1, "conv"), (1, "sum")])
        if d <= 0 or k == "lit":
            return f"{c.__name__}({ch.lit(uint_lits(c), 4)})"
        if k == "binop":
            op = ch.weighted([(4, "+"), (3, "-"), (2, "*"), (2, "//"), (1, "%"), (1, "&"),
                              (1, "|"), (1, "^"), (1, "<<"), (1, ">>"), (1, "**")])
            a = self.expr(U(c), sc, d - 1)
            ob = ch.weighted([(5, "same"), (3, "int"), (0 if "subfield" in AVOID else 1, "other"),
                              (0 if "boolleft" in AVOID else 1, "bool")])
            if op in ("<<", ">>", "**"):
                b = str(ch.int(0, 3))
            elif ob == "same":
                b = self.expr(U(c), sc, d - 1)
            elif ob == "int":
                b = str(ch.lit(INT_LITS))
            elif ob == "other":
                b = self.expr(U(ch.pick(UINTS)), sc, d - 1)
            else:
                b = ch.pick(["True", "False"])
            if ch.flip(20) and op not in ("<<", ">>", "**"):
                a, b = b, a
            return f"({a} {op} {b})"
        if k == "minmax":
            fn = ch.pick(["min", "max"])
            n = ch.int(2, 3)
            args = [self.expr(U(c), sc, d - 1) if i == 0 or ch.flip(70)
                    else ch.pick([str(x) for x in INT_LITS[:6]]) for i in range(n)]
            return f"{fn}({', '.join(args)})"
        if k == "conv":
            return f"{c.__name__}({self.expr(INT, sc, d - 1)})"
        r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == U(c))
        return f"sum({r[0]})" if r else f"{c.__name__}(sum([]))"

    def bytes_expr(self, c, sc, d):
        ch = self.ch
        if c is H.Root and d > 0 and ch.flip(30):
            r = self.path_of(sc, lambda t: t[0] in ("cont", "seq"))
            if r:
                return f"hash_tree_root({r[0]})"
        if c is bytes and d > 0 and ch.flip(25):
            k = ch.pick(["ser", "method", "blob"])
            if k == "ser":
                e = self.expr(ch.pick([U(H.Uint64), U(H.Gwei), U(H.Uint8), BOOLEAN]), sc, d - 1)
                return f"ssz_serialize({e})"
            r = self.path_of(sc, lambda t: t[0] in ("cont", "seq") and
                             (k == "method" or t == S(H.Blob)))
            if r:
                return f"{r[0]}.hash_tree_root()" if k == "method" else f"{r[0]}[0:2]"
        if c is bytes:
            r = self.path_of(sc, lambda t: t[0] == "bytes")
            if r and d > 0:
                k = ch.pick(["slice", "concat", "slice"])
                if k == "slice":
                    lo, hi = ch.pick(["0", "1", "", "-1"]), ch.pick(["2", "", "1", "-1", "9"])
                    return f"{r[0]}[{lo}:{hi}]"
                return f"({r[0]} + {self.expr(BY(bytes), sc, d - 1)})"
            return ch.pick(["b''", "b'\\x01\\x02'", "b'\\x00\\x00\\x00\\x00'"])
        n = c.LENGTH
        if ch.flip(mis(4)):
            n = n + ch.pick([1, -1])
        byte = ch.pick([0, 1, 255])
        return f"{c.__name__}(b'{''.join(f'\\x{byte:02x}' for _ in range(n))}')"

    def cont_expr(self, T, sc, d):
        ch = self.ch
        c = T[1]
        k = ch.weighted([(8, "ctor"), (1, "copy"), (1, "empty")])
        if k == "copy" and d > 0:
            p = self.path_eq(sc, T)
            if p:
                return f"{p}.copy()"
        if k == "empty" or d <= 0:
            return f"{c.__name__}()"
        kws = []
        for f, ft in fields(T):
            if ch.flip(75):
                ft2 = ch.weighted(avail(LOCAL_TYPES)) if ch.flip(mis(3)) else ft
                kws.append(f"{f}={self.expr(ft2, sc, d - 1)}")
        return f"{c.__name__}({', '.join(kws)})"

    def elems(self, E, sc, d, n):
        return ", ".join(self.expr(E, sc, d - 1) for _ in range(n))

    def seq_expr(self, T, sc, d):
        ch = self.ch
        c = T[1]
        E = elem(T)
        k = ch.weighted([(6, "data"), (2, "share"), (1, "empty"), (1, "slice"), (1, "copy")])
        name = c.__name__
        if d <= 0 or k == "empty":
            return f"{name}()"
        if k == "share":
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
            if r:
                return f"{name}(data={r[0]})"
        if k == "slice" and sliceable_list(T):
            p = self.path_eq(sc, T)
            if p:
                return f"{p}[{ch.pick(['0', '1', ''])}:{ch.pick(['1', '2', '', '-1'])}]"
        if k == "copy":
            p = self.path_eq(sc, T)
            if p:
                return f"{p}.copy()"
        bad = 0 if "ctorlen" in AVOID else 1
        if issubclass(c, (H.Vector, H.BitVector)):
            n = ch.pick([0, c.LENGTH + 1]) if ch.flip(5 * bad) else c.LENGTH
        else:
            size = getattr(c, "LIMIT", None) or 3
            n = ch.weighted([(3, size), (2, 0), (3, 1), (bad, size + 1)])
        return f"{name}(data=[{self.elems(E, sc, d, n)}])"

    def pylist_expr(self, T, sc, d):
        ch = self.ch
        E = elem(T)
        k = ch.weighted([(3, "lit"), (3, "comp"), (1, "list"), (1, "sorted"), (1, "key"),
                         (1, "filter"), (1, "vecslice"),
                         (0 if "livecomp" in AVOID else 1, "grow"),
                         (0 if "pycopy" in AVOID else 1, "copy")])
        if d <= 0 or k == "lit":
            return f"[{self.elems(E, sc, d, ch.int(0, 3))}]"
        if ch.flip(15):
            r = self.path_of(sc, lambda t: t[0] == "set" and t[1] == E)
            if r:
                other = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
                arg = f"set({other[0]})" if other else "set()"
                m = "" if "setmethods" in AVOID else ch.pick(["union", "intersection", "difference", ""])
                return f"sorted({r[0]}.{m}({arg}))" if m else f"sorted({r[0]})"
            r = self.path_of(sc, lambda t: t[0] == "dict" and t[2] == E)
            if r and "dictviews" not in AVOID:
                return ch.pick([f"list({r[0]}.values())", f"[v for k, v in {r[0]}.items()]"])
            r = self.path_of(sc, lambda t: t[0] == "dict" and t[1] == E)
            if r:
                return ch.pick([f"[k for k in {r[0]}]"] +
                               ([] if "dictviews" in AVOID else [f"list({r[0]}.keys())"]))
        if k == "grow":
            r = self.path_of(sc, lambda t: growable(t) and elem(t) == E)
            if r:
                return f"[grow({r[0]}, x) for x in {r[0]}]"
        if k == "copy":
            p = self.path_eq(sc, T)
            if p:
                return f"{p}.copy()"
        if k == "comp":
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
            if r:
                cond = ch.pick(["", " if x == x", " if (x is not None)"])
                return f"[x for x in {r[0]}{cond}]"
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t)[0] == "cont"
                             and any(ft == E for _, ft in fields(elem(t))))
            if r:
                f = ch.pick([f for f, ft in fields(elem(r[1])) if ft == E])
                return f"[x.{f} for x in {r[0]}]"
        if k in ("list", "sorted"):
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
            if r and (k == "list" or numeric(E)):
                rev = ", reverse=True" if k == "sorted" and ch.flip(30) else ""
                return f"{k}({r[0]}{rev})"
        if k == "key" and E[0] == "cont":
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
            if r:
                nums = [f for f, ft in fields(E) if ft[0] == "uint"]
                if nums:
                    return f"sorted({r[0]}, key=lambda x: x.{ch.pick(nums)})"
        if k == "filter":
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
            if r:
                return f"list(filter(lambda x: x == x, {r[0]}))"
        if k == "vecslice":
            r = self.path_of(sc, lambda t: t[0] == "seq" and issubclass(t[1], H.Vector)
                             and elem(t) == E)
            if r:
                return f"{r[0]}[0:{ch.pick(['1', '2', ''])}]"
        return f"[{self.elems(E, sc, d, ch.int(0, 2))}]"

    # ---------------------------------------------------------------------------------------
    # Statements

    def block(self, sc, n, in_loop):
        start = len(self.lines)
        for _ in range(n):
            self.stmt(sc, in_loop)
        if len(self.lines) == start:
            self.emit("pass")

    def nested(self, sc, n, in_loop):
        self.indent += 1
        self.block(sc.child(), n, in_loop)
        self.indent -= 1

    def guard_append(self, p, T, value):
        if unbounded(T):
            self.emit(f"if len({p}) < 5:")
            self.indent += 1
            self.emit(f"{p}.append({value})")
            self.indent -= 1
        else:
            self.emit(f"{p}.append({value})")

    def stmt(self, sc, in_loop):
        ch = self.ch
        k = ch.weighted([(4, "local"), (5, "field"), (3, "elem"), (3, "aug"), (3, "append"),
                         (4, "pattern"), (2, "for"), (1, "while"), (2, "if"), (1, "assert"),
                         (2, "call"), (1, "raise"), (1, "swap"), (1, "multi"), (1, "slice"),
                         (1, "extend"), (1, "ret"), (1, "brk" if in_loop else "local"),
                         (1, "unpack"), (1, "each"), (2, "dict"), (2, "set"), (1, "closure"),
                         (1, "hazard")])
        if k in GUARDABLE and ch.flip(80):
            self.guarding, self.guard_bases = True, []
            start = len(self.lines)
            bound = dict(sc.vars)
            getattr(self, "s_" + k)(sc, in_loop)
            self.guarding = False
            bases = list(dict.fromkeys(self.guard_bases))
            # A statement that binds a name stays unguarded, so that no later read of the
            # name fails.
            if bases and len(self.lines) > start and sc.vars == bound:
                body = ["    " + line for line in self.lines[start:]]
                cond = " and ".join(f"len({b}) > 0" for b in bases)
                self.lines[start:] = ["    " * self.indent + f"if {cond}:"] + body
        else:
            getattr(self, "s_" + k)(sc, in_loop)

    def s_local(self, sc, in_loop):
        ch = self.ch
        locs = [v for v in sc.vars if v != "log"]
        if locs and ch.flip(25):
            v = ch.pick(locs)
            T = sc.vars[v]
        else:
            T = ch.weighted(avail(LOCAL_TYPES))
            v = self.fresh("v")
        e = self.expr(T, sc)
        if ch.flip(10):
            self.emit(f"{v}: {self.annot(T)} = {e}")
        else:
            self.emit(f"{v} = {e}")
        sc.vars[v] = T

    def annot(self, T):
        if T[0] in ("uint", "cont", "seq") or (T[0] == "bytes" and T[1] is not bytes):
            return T[1].__name__
        return {"int": "int", "bool": "bool", "Boolean": "Boolean", "pylist": "list", "dict": "dict",
                "set": "set", "bytes": "bytes"}.get(T[0],
                                                                                         "int")

    def s_field(self, sc, in_loop):
        r = self.path_of(sc, lambda t: t[0] == "cont")
        if r is None:
            return self.s_local(sc, in_loop)
        p, T = r
        f, ft = self.ch.pick(fields(T))
        if self.ch.flip(mis(5)):
            ft = self.ch.weighted(avail(LOCAL_TYPES))
        self.emit(f"{p}.{f} = {self.expr(ft, sc)}")

    def s_elem(self, sc, in_loop):
        r = self.path_of(sc, is_seq)
        if r is None:
            return self.s_local(sc, in_loop)
        p, T = r
        E = elem(T)
        if self.ch.flip(mis(5)):
            E = self.ch.weighted(avail(LOCAL_TYPES))
        idx = self.index(sc, p)
        self.emit(f"{p}[{idx}] = {self.expr(E, sc)}")

    def s_aug(self, sc, in_loop):
        ch = self.ch
        ps = [(e, T) for e, T in self.paths(sc) if T[0] in ("uint", "int")
              and (e.endswith("]") or "." in e or e in sc.vars)]
        if not ps:
            return self.s_local(sc, in_loop)
        e, T = ch.pick(ps)
        p = self.fill(sc, e)
        op = ch.weighted([(4, "+="), (3, "-="), (1, "*="), (1, "//="), (1, "%="), (1, "|=")])
        rhs = self.expr(T, sc, 1) if ch.flip(60) else str(ch.lit(INT_LITS))
        self.emit(f"{p} {op} {rhs}")

    def s_append(self, sc, in_loop):
        r = self.path_of(sc, growable)
        if r is None:
            return self.s_local(sc, in_loop)
        p, T = r
        E = self.ch.weighted(avail(LOCAL_TYPES)) if self.ch.flip(mis(5)) else elem(T)
        self.guard_append(p, T, self.expr(E, sc))

    def s_extend(self, sc, in_loop):
        r = self.path_of(sc, lambda t: t[0] == "pylist")
        if r is None:
            return self.s_local(sc, in_loop)
        p, T = r
        E = elem(T)
        src = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
        arg = src[0] if src and self.ch.flip(60) else f"[{self.elems(E, sc, 2, self.ch.int(0, 2))}]"
        self.emit(f"if len({p}) < 5:")
        self.indent += 1
        self.emit(f"{p}.extend({arg})")
        self.indent -= 1

    def s_slice(self, sc, in_loop):
        r = self.path_of(sc, lambda t: t[0] in ("seq", "pylist"))
        if r is None:
            return self.s_local(sc, in_loop)
        p, T = r
        lo, hi = self.ch.pick(["0", "1", ""]), self.ch.pick(["1", "2", ""])
        self.emit(f"{p}[{lo}:{hi}] = [{self.elems(elem(T), sc, 2, self.ch.int(0, 2))}]")

    def s_pattern(self, sc, in_loop):
        ch = self.ch
        k = ch.pick(["rebind", "fieldshare", "elemshare", "twofields", "loopalias",
                     "evalorder", "augorder", "retref"])
        if k == "rebind":
            # v = s.a[0]; s.a[0] = X(); v.f = 1
            r = self.path_of(sc, lambda t: t[0] == "cont")
            if r is None or ("." not in r[0] and "[" not in r[0]):
                return self.s_field(sc, in_loop)
            p, T = r
            v = self.fresh("v")
            self.emit(f"{v} = {p}")
            sc.vars[v] = T
            self.emit(f"{p} = {self.cont_expr(T, sc, 1)}")
            f, ft = ch.pick(fields(T))
            self.emit(f"{v}.{f} = {self.expr(ft, sc, 1)}")
        elif k == "fieldshare":
            T = ch.pick([C(H.Box), C(H.Pt), C(H.PBox)])
            v = self.fresh("v")
            kws = []
            for f, ft in fields(T):
                q = self.path_eq(sc, ft)
                if q and ch.flip(70):
                    kws.append(f"{f}={q}")
            self.emit(f"{v} = {T[1].__name__}({', '.join(kws)})")
            sc.vars[v] = T
            self.s_field(sc, in_loop)
        elif k == "elemshare":
            T = ch.pick([S(H.Pts), S(H.PPts), S(H.PtPair)])
            q = self.path_eq(sc, C(H.Pt))
            if q is None:
                return self.s_local(sc, in_loop)
            v = self.fresh("v")
            n = 2 if T[1] is H.PtPair else ch.int(1, 3)
            self.emit(f"{v} = {T[1].__name__}(data=[{', '.join([q] * n)}])")
            sc.vars[v] = T
            self.emit(f"{v}[{ch.pick(['0', '-1'])}].a = {self.expr(U(H.Uint64), sc, 1)}")
        elif k == "twofields":
            r = self.path_of(sc, lambda t: t in (C(H.Box), C(H.PBox)))
            if r is None:
                return self.s_field(sc, in_loop)
            p, T = r
            if T == C(H.Box):
                a, b = ch.pick([("p", "q"), ("q", "p")])
                self.emit(f"{p}.{a} = {p}.{b}")
                self.emit(f"{p}.{a}.{ch.pick(['a', 's', 'f'])} = 1")
            else:
                self.emit(f"{p}.pair[0] = {p}.pair[1]")
                self.emit(f"{p}.pair[1].a = 2")
        elif k == "loopalias":
            r = self.path_of(sc, lambda t: is_seq(t) and elem(t)[0] == "cont")
            if r is None:
                return self.s_for(sc, in_loop)
            p, T = r
            x = self.fresh("x")
            self.emit(f"for {x} in {p}:")
            self.indent += 1
            f, ft = ch.pick(fields(elem(T)))
            self.emit(f"{x}.{f} = {self.expr(ft, sc.child(), 1)}")
            self.indent -= 1
        elif k in ("evalorder", "augorder"):
            ps = [(e, T) for e, T in self.paths(sc) if is_seq(T) and
                  (k == "evalorder" or elem(T)[0] in ("uint", "int"))]
            if not ps:
                return self.s_local(sc, in_loop)
            e, T = ch.pick(ps)
            p = self.fill(sc, e)
            idx = self.trace(ch.weighted([(4, "0"), (2, "-1"), (1, "1"), (1, "5")]))
            obj = self.trace(p) if ch.flip(50) else p
            if k == "evalorder":
                self.emit(f"{obj}[{idx}] = {self.trace(self.expr(elem(T), sc, 1))}")
            else:
                self.emit(f"{obj}[{idx}] += {self.trace(ch.pick(['1', '0', '-1']))}")
        else:
            self.s_call(sc, in_loop)

    def s_for(self, sc, in_loop):
        ch = self.ch
        r = self.path_of(sc, is_seq)
        if r is None:
            return self.s_local(sc, in_loop)
        p, T = r
        inner = sc.child()
        k = ch.weighted([(4, "plain"), (2, "enum"), (1, "zip"), (1, "range"), (1, "sorted")])
        x = self.fresh("x")
        if k == "enum":
            i = self.fresh("i")
            self.emit(f"for {i}, {x} in enumerate({p}):")
            inner.vars[i] = INT
            inner.vars[x] = elem(T)
        elif k == "zip":
            r2 = self.path_of(sc, is_seq)
            y = self.fresh("x")
            self.emit(f"for {x}, {y} in zip({p}, {r2[0]}):")
            inner.vars[x] = elem(T)
            inner.vars[y] = elem(r2[1])
        elif k == "range":
            bounds = [f"len({p})", "3", "0", "1, 3", "0, 4, 2"]
            if "negstep" not in AVOID:
                bounds.append("3, 0, -1")
            self.emit(f"for {x} in range({ch.pick(bounds)}):")
            inner.vars[x] = INT
        elif k == "sorted" and numeric(elem(T)):
            self.emit(f"for {x} in sorted({p}):")
            inner.vars[x] = elem(T)
        else:
            self.emit(f"for {x} in {p}:")
            inner.vars[x] = elem(T)
        self.indent += 1
        live = ch.weighted([(3, "none"), (2, "append"), (1, "replace")])
        if live == "append" and growable(T):
            self.guard_append(p, T, self.expr(elem(T), inner, 1))
        elif live == "replace" and "." in p and not p.endswith("]"):
            self.emit(f"{p} = {self.seq_expr(T, inner, 1) if T[0] == 'seq' else '[]'}")
        self.block(inner, ch.int(0, 2), True)
        self.indent -= 1

    def s_while(self, sc, in_loop):
        w = self.fresh("w")
        self.emit(f"{w} = 0")
        self.emit(f"while {w} < {self.ch.int(1, 3)}:")
        self.indent += 1
        self.emit(f"{w} += 1")
        inner = sc.child()
        self.block(inner, self.ch.int(0, 2), True)
        self.indent -= 1

    def s_if(self, sc, in_loop):
        self.emit(f"if {self.expr(BOOL, sc)}:")
        self.nested(sc, self.ch.int(1, 2), in_loop)
        if self.ch.flip(50):
            self.emit("else:")
            self.nested(sc, self.ch.int(1, 2), in_loop)

    def s_assert(self, sc, in_loop):
        self.emit(f"assert {self.expr(BOOL, sc)}")

    def s_raise(self, sc, in_loop):
        self.emit(f"if {self.expr(BOOL, sc)}:")
        self.indent += 1
        self.emit("raise FuzzError()")
        self.indent -= 1

    def s_call(self, sc, in_loop):
        if not self.helpers:
            return self.s_local(sc, in_loop)
        name, ps, _ = self.ch.pick(self.helpers)
        args = ", ".join(["log"] + [self.expr(p, sc, 1) for p in ps])
        if self.ch.flip(20):
            args = f"*[{args}]"
        self.emit(f"{name}({args})")

    def s_unpack(self, sc, in_loop):
        ta, tb = self.ch.weighted(avail(LOCAL_TYPES)), self.ch.weighted(avail(LOCAL_TYPES))
        a, b = self.fresh("v"), self.fresh("v")
        self.emit(f"{a}, {b} = {self.expr(ta, sc)}, {self.expr(tb, sc)}")
        sc.vars[a], sc.vars[b] = ta, tb

    def s_each(self, sc, in_loop):
        """`for_ops` style: a function value called on each item of a live list."""
        r = self.path_of(sc, is_seq)
        if r is None:
            return self.s_local(sc, in_loop)
        p, T = r
        body = self.ch.pick([self.trace("x"), f"grow({p}, x)", "x", f"1 // len({p})"])
        if "grow" in body and not growable(T) or "livecomp" in AVOID and "grow" in body:
            body = self.trace("x")
        self.emit(f"each({p}, lambda x: {body})")

    def s_set(self, sc, in_loop):
        ch = self.ch
        ss = [v for v, t in sc.vars.items() if t[0] == "set"]
        if not ss or ch.flip(30):
            T = SET(ch.pick([U(H.Gwei), U(H.Slot), INT, BY(H.Root)]))
            v = self.fresh("s")
            self.emit(f"{v} = {self.expr(T, sc)}")
            sc.vars[v] = T
            if ch.flip(50):
                return
        else:
            v = ch.pick(ss)
        E = sc.vars[v][1]
        k = ch.pick(["add", "add", "in", "len", "iter", "method", "method"])
        if k == "method":
            other = self.path_of(sc, lambda t: is_seq(t) and elem(t) == E)
            arg = f"set({other[0]})" if other else f"set([{self.expr(E, sc, 1)}])"
            ms = ["union", "intersection"] + ([] if "setmethods" in AVOID else ["difference"])
            w = self.fresh("s")
            self.emit(f"{w} = {v}.{ch.pick(ms)}({arg})")
            sc.vars[w] = sc.vars[v]
            self.emit(f"log.append(sorted({w}))")
        elif k == "add":
            self.emit(f"{v}.add({self.expr(E, sc, 1)})")
        elif k == "in":
            self.emit(f"log.append({self.expr(E, sc, 1)} in {v})")
        elif k == "len":
            self.emit(f"log.append(len({v}))")
        else:
            x = self.fresh("x")
            self.emit(f"for {x} in sorted({v}):")
            self.indent += 1
            self.emit(f"log.append({x})")
            self.indent -= 1

    def s_closure(self, sc, in_loop):
        """A nested `def` that reads only its parameter and `log`, then a call of it."""
        ch = self.ch
        c = self.fresh("c")
        self.emit(f"def {c}(x):")
        self.indent += 1
        self.emit(f"log.append({ch.pick(['x', '1', 'len(log)'])})")
        self.emit("return x")
        self.indent -= 1
        r = self.path_of(sc, is_seq)
        if r and ch.flip(60):
            self.emit(f"each({r[0]}, {c})")
        else:
            self.emit(f"{c}({self.expr(ch.weighted(avail(LOCAL_TYPES)), sc, 1)})")

    def s_hazard(self, sc, in_loop):
        """A write through an object that a second path reaches (SPEC 9.4)."""
        ch = self.ch
        k = ch.pick(["ctorshare", "appendshared", "fieldcopy", "calleealias"])
        if k == "ctorshare":
            r = self.path_of(sc, lambda t: t == C(H.Box))
            if r is None:
                return self.s_pattern(sc, in_loop)
            v = self.fresh("v")
            self.emit(f"{v} = Box(ps={r[0]}.ps, p={r[0]}.q)")
            sc.vars[v] = C(H.Box)
            self.emit(ch.pick([f"{v}.p.a = Uint64(3)", f"{v}.ps.append(Pt())",
                               f"{r[0]}.q.s = Slot(4)"]))
        elif k == "appendshared":
            r = self.path_of(sc, lambda t: t == C(H.Box))
            if r is None:
                return self.s_pattern(sc, in_loop)
            self.emit(f"{r[0]}.ps.append({r[0]}.{ch.pick(['p', 'q'])})")
            self.emit(f"{r[0]}.ps[-1].a = Uint64(5)")
        elif k == "fieldcopy":
            r = self.path_of(sc, lambda t: t in (C(H.Box), C(H.PBox)))
            if r is None:
                return self.s_pattern(sc, in_loop)
            if r[1] == C(H.Box):
                self.emit(f"{r[0]}.q = {r[0]}.p")
                self.emit(f"{r[0]}.p.f = True")
            else:
                self.emit(f"{r[0]}.pair[1] = {r[0]}.pair[0]")
                self.emit(f"{r[0]}.pair[0].a = Uint64(6)")
        else:
            hs = [h for h in self.helpers if C(H.Pt) in h[1]]
            r = self.path_of(sc, lambda t: t == C(H.Box))
            if not hs or r is None:
                return self.s_pattern(sc, in_loop)
            name, ps, _ = ch.pick(hs)
            self.emit(f"{r[0]}.q = {r[0]}.p")
            args = ", ".join(["log"] + [f"{r[0]}.p" if p == C(H.Pt) else self.expr(p, sc, 1)
                                        for p in ps])
            self.emit(f"{name}({args})")

    def s_dict(self, sc, in_loop):
        ch = self.ch
        ds = [v for v, t in sc.vars.items() if t[0] == "dict"]
        if not ds or ch.flip(25):
            T = DICT(ch.pick([U(H.Slot), BY(H.Root), INT]),
                     ch.weighted([(3, C(H.Pt)), (2, U(H.Gwei)), (1, S(H.Gweis)), (1, INT)]))
            v = self.fresh("d")
            self.emit(f"{v} = {self.expr(T, sc)}")
            sc.vars[v] = T
            if ch.flip(50):
                return
        else:
            v = ch.pick(ds)
        T = sc.vars[v]
        key = self.expr(T[1], sc, 1)
        k = ch.weighted([(4, "set"), (2, "get"), (2, "index"), (1, "in"), (1, "iter"),
                         (1, "write"), (0 if "dictviews" in AVOID else 1, "items"),
                         (0 if "dictviews" in AVOID else 1, "values")])
        if k == "set":
            self.emit(f"{v}[{key}] = {self.expr(T[2], sc)}")
        elif k == "get":
            w = self.fresh("v")
            dflt = ch.pick(["", ", " + self.expr(T[2], sc, 1)])
            self.emit(f"{w} = {v}.get({key}{dflt})")
            if dflt:
                sc.vars[w] = T[2]
        elif k == "index":
            w = self.fresh("v")
            self.emit(f"{w} = {v}[{key}]")
            sc.vars[w] = T[2]
        elif k == "in":
            self.emit(f"assert ({key} {ch.pick(['in', 'not in'])} {v}) or len({v}) >= 0")
        elif k == "items":
            x, y = self.fresh("x"), self.fresh("x")
            self.emit(f"for {x}, {y} in {v}.items():")
            self.indent += 1
            self.emit(f"log.append({x})")
            self.indent -= 1
        elif k == "values":
            x = self.fresh("x")
            self.emit(f"for {x} in {v}.values():")
            self.indent += 1
            self.emit(f"log.append({x})")
            self.indent -= 1
        elif k == "iter":
            x = self.fresh("x")
            self.emit(f"for {x} in {ch.pick([v, f'sorted({v})'])}:")
            self.indent += 1
            self.emit(f"log.append({x})")
            self.indent -= 1
        elif T[2][0] == "cont":
            f, ft = ch.pick(fields(T[2]))
            self.emit(f"{v}[{key}].{f} = {self.expr(ft, sc, 1)}")
        else:
            self.emit(f"{v}[{key}] = {self.expr(T[2], sc, 1)}")

    def s_swap(self, sc, in_loop):
        locs = [v for v in sc.vars if v != "log"]
        if len(locs) < 2:
            return self.s_local(sc, in_loop)
        a, b = self.ch.pick(locs), self.ch.pick(locs)
        if sc.vars[a] != sc.vars[b]:
            return self.s_local(sc, in_loop)
        self.emit(f"{a}, {b} = {b}, {a}")

    def s_multi(self, sc, in_loop):
        T = self.ch.weighted(avail(LOCAL_TYPES))
        a, b = self.fresh("v"), self.fresh("v")
        self.emit(f"{a} = {b} = {self.expr(T, sc)}")
        sc.vars[a] = sc.vars[b] = T

    def s_ret(self, sc, in_loop):
        self.emit(f"if {self.expr(BOOL, sc, 1)}:")
        self.indent += 1
        self.emit(f"return {self.expr(self.ret_type, sc, 1)}")
        self.indent -= 1

    def s_brk(self, sc, in_loop):
        self.emit(f"if {self.expr(BOOL, sc, 1)}:")
        self.indent += 1
        self.emit(self.ch.pick(["break", "continue"]))
        self.indent -= 1

    # ---------------------------------------------------------------------------------------
    # Functions and inputs

    def function(self, name, params, ret, n_stmts, in_helper):
        ps = [f"{p}: {self.annot(T)}" for p, T in params]
        ps = ["log"] + ps if in_helper else ps + ["log"]
        rann = f" -> {self.annot(ret)}" if in_helper and ret[0] in ("cont", "seq") else ""
        self.lines.append(f"def {name}({', '.join(ps)}){rann}:")
        sc = Scope(params, in_helper)
        self.indent = 1
        self.ret_type = ret
        self.block(sc, n_stmts, False)
        locs = [v for v in sc.vars if v not in dict(params)]
        if not in_helper and locs and self.ch.flip(50):
            # Return every local, so that sharing between locals and arguments shows.
            self.emit(f"return ({', '.join(locs)},)")
        else:
            self.emit(f"return {self.expr(ret, sc)}")
        self.lines.append("")
        self.lines.append("")


def mk_value(ch, T, lines, objs, d=0):
    k = T[0]
    if k == "uint":
        c = T[1]
        return f"{c.__name__}({ch.pick([n for n in uint_lits(c) if 0 <= n < 2 ** c.BITS])})"
    if k == "int":
        return str(ch.lit(INT_LITS))
    if k == "bool":
        return ch.pick(["False", "True"])
    if k == "Boolean":
        return ch.pick(["Boolean(False)", "Boolean(True)"])
    if k == "bytes":
        c = T[1]
        return f"{c.__name__}(bytes([{', '.join(str(ch.pick([0, 1, 7, 255])) for _ in range(c.LENGTH))}]))"
    same = [name for name, t in objs if t == T]
    if same and ch.flip(30):
        return ch.pick(same)
    if k == "cont":
        kws = [f"{f}={mk_value(ch, ft, lines, objs, d + 1)}" for f, ft in fields(T)
               if d < 2 and ch.flip(85)]
        e = f"{T[1].__name__}({', '.join(kws)})"
    elif k == "seq" and T[1] is H.Blob:
        e = f"Blob(data=bytes([{', '.join(str(ch.pick([0, 1, 255])) for _ in range(ch.int(0, 4)))}]))"
    elif k == "seq":
        c = T[1]
        if issubclass(c, (H.Vector, H.BitVector)):
            n = c.LENGTH
        else:
            n = ch.weighted([(4, 1), (1, 0), (3, 2), (3, getattr(c, "LIMIT", None) or 4)])
        es = [mk_value(ch, elem(T), lines, objs, d + 1) for _ in range(n)] if d < 3 else []
        if len(es) != n:
            return f"{c.__name__}()"
        e = f"{c.__name__}(data=[{', '.join(es)}])"
    else:
        n = ch.weighted([(4, 1), (1, 0), (3, 2), (2, 3)]) if d < 3 else 0
        e = f"[{', '.join(mk_value(ch, T[1], lines, objs, d + 1) for _ in range(n))}]"
    name = f"o{len(objs)}"
    lines.append(f"    {name} = {e}")
    objs.append((name, T))
    return name


TR = '''def tr(log, k, v):
    log.append(k)
    return v


def grow(xs, v):
    if len(xs) < 5:
        xs.append(v)
    return v


def each(xs, fn):
    for x in xs:
        fn(x)

'''


def gen_case(ch: Ch) -> str:
    g = Gen(ch)
    arg_types = [ch.weighted(avail(ARG_TYPES)) for _ in range(ch.int(1, 3))]
    mk_lines, objs = [], []
    arg_names = [mk_value(ch, T, mk_lines, objs) for T in arg_types]
    mk = "def mk():\n" + "\n".join(mk_lines) + \
         f"\n    return [{', '.join(arg_names)}, []]\n\n"
    for i in range(ch.weighted([(3, 0), (4, 1), (3, 2), (1, 3), (1, 4)])):
        ps = [(f"p{j}", ch.weighted(avail(ARG_TYPES))) for j in range(ch.int(1, 2))]
        ret = ch.weighted([(3, NONE)] + avail(ARG_TYPES))
        g.function(f"g{i}", ps, ret, ch.int(1, 3), True)
        g.helpers.append((f"g{i}", [t for _, t in ps], ret))
    params = [(f"a{i}", T) for i, T in enumerate(arg_types)]
    ret = ch.weighted([(2, NONE)] + avail(ARG_TYPES))
    g.function("f", params, ret, ch.int(1, 6), False)
    src = mk + TR + "\n".join(g.lines)
    ast.parse(src)
    return src


@st.composite
def cases(draw):
    return gen_case(Ch(draw))
