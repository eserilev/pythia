"""Generate the layer 4 theorems (SPEC 10) of the spec functions and keep the ones that check.

For each function it writes one candidate theorem `<f>_den`: `den` of the function on the
encoded arguments, with errors mapped through `SpecError.fail`, equals the readable function.
The proof is the same for every function: one step of `den` per syntax node
(`SpecLean.Layer4.GenSteps`), the value rules, the readable rules, and the rewrites of the
classes (`SpecLean/Layer4/Gen/Classes.lean`, also generated).

Run from the repository root:

    python3 tools/gen_l4.py [--only f,g] [--jobs 4]

It checks each candidate with `lake env lean` under a memory cap, in parallel, and writes the
proved ones to `SpecLean/Layer4/Gen/Funcs.lean`. It prints the count and the reason of each
failure.
"""

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import l4_ast  # noqa: E402
from l4_ast import ctor  # noqa: E402

MEM = os.environ.get("L4_MEM", "6G")
THREADS = os.environ.get("L4_THREADS", "4")
TIMEOUT = int(os.environ.get("L4_TIMEOUT", "600"))
GEN = ROOT / "SpecLean/Layer4/Gen"


# ---------------------------------------------------------------------------
# The scope and the readable Lean

class Model:
    def __init__(self):
        scope = (ROOT / "SpecLean/Gen/Scope.lean").read_text()
        self.fns, self.ids, self.globs = l4_ast.load_scope(str(ROOT / "SpecLean/Gen/Scope.lean"))
        self.scope = scope
        self.name_id = {v: k for k, v in self.ids.items()}
        rd = (ROOT / "SpecLean/Gen/Readable.lean").read_text()
        self.rd = rd
        self.uint = {}   # class -> bits
        for m in re.finditer(r"^instance : UintC (\w+) := ⟨(\d+),", rd, re.M):
            self.uint[m.group(1)] = int(m.group(2))
        self.bytes = {}  # class -> length
        for m in re.finditer(r"^instance : BytesC (\w+) := ⟨(\d+),", rd, re.M):
            self.bytes[m.group(1)] = int(m.group(2))
        self.sigs = {}
        self.bodies = {}
        for m in re.finditer(r"^def (\w+) (.*?): SpecM (.+?) :=", rd, re.M):
            ps = [strip_parens(x) for x in split_top(m.group(2))]
            if any(" : " not in x for x in ps) or "{" in m.group(2):
                continue
            ps = [tuple(t.strip() for t in x.split(" : ", 1)) for x in ps]
            self.sigs[m.group(1)] = ([(a, strip_parens(b)) for a, b in ps], m.group(3).strip())
            self.bodies[m.group(1)] = def_text(rd, m.start())
        # Functions generic over a uint class: one theorem set per class.
        self.generic = set()
        for m in re.finditer(r"^def (\w+) \{β : Type\} \[UintC β\] \((\w+) : β\) : SpecM (.+?) :=", rd, re.M):
            self.sigs[m.group(1)] = ([(m.group(2), "β")], m.group(3).strip())
            self.bodies[m.group(1)] = def_text(rd, m.start())
            self.generic.add(m.group(1))
        for m in re.finditer(r"^def (\w+)\.loop\d+ ", rd, re.M):
            if m.group(1) in self.bodies:
                self.bodies[m.group(1)] += "\n" + def_text(rd, m.start())
        self.consts = set(re.findall(r"^def ([A-Z][A-Z0-9_]*) : ", rd, re.M))
        self.structs = {}
        for m in re.finditer(r"^structure (\w+) where\n((?:  \w+ : [^\n]+\n)+)", rd, re.M):
            self.structs[m.group(1)] = re.findall(r"  (\w+) : ([^\n]+)", m.group(2))
        self.containers = {}  # readable name -> [(field, ssz type, readable type)]
        c = scope[scope.index("def containers"):]
        c = c[:c.index("\ndef ")]
        for m in re.finditer(r"^  \((\d+), \[(.*)\]\),?$", c, re.M):
            name = self.ids.get(int(m.group(1)))
            st = self.structs.get(name)
            fs = split_top(m.group(2))
            if st is None or len(st) != len(fs):
                continue
            self.containers[name] = [(fn, f.split(", ", 1)[1], ft) for f, (fn, ft) in zip(fs, st)]
        self.cid = {n: self.name_id[n] for n in self.containers}
        # `Footprint f`: function id -> [(parameter index, [step names])].
        self.fnfp = {}
        c = scope[scope.index("def fnFootprint"):]
        c = c[:c.index("\n\n")]
        for m in re.finditer(r"^  \((\d+), \[(.*)\]\)[,\]]*$", c, re.M):
            self.fnfp[int(m.group(1))] = [(int(k), [self.ids[int(x)] for x in st.split(",") if x])
                                          for k, st in re.findall(r"\((\d+), \[([\d,]*)\]\)", m.group(2))]

    def glob_kind(self, g):
        s = self.globs.get(g, "")
        if s.startswith(".fn fn_"):
            return "fn", s[len(".fn fn_"):]
        if s.startswith(".type"):
            return "type", s[len(".type "):]
        if s.startswith(".builtin"):
            return "builtin", s.split(".")[-1]
        if s.startswith(".const"):
            return "const", s[len(".const "):]
        return "other", s

    def uint_ty(self, cls):
        """The `UintTy` of a readable uint class."""
        g = self.name_id.get(cls)
        if g is not None:
            k, s = self.glob_kind(g)
            if k == "type":
                m = re.fullmatch(r"\(\.uint (.*)\)", s)
                if m:
                    return m.group(1)
        m = re.fullmatch(r"Uint(\d+)", cls)
        if m:
            return "(.width %s)" % m.group(1)
        if g is not None and cls in self.uint:
            return "(.nominal %d %d)" % (g, self.uint[cls])
        return None

    def bytes_id(self, cls):
        g = self.name_id.get(cls)
        if g is not None:
            k, s = self.glob_kind(g)
            if k == "type" and s.startswith("(.bytes"):
                return g
            if cls in self.bytes:
                return g
        return None

    def callees(self, name):
        """The spec functions that the readable body of `name` calls."""
        body = self.bodies.get(name, "")
        body = body[body.index(":="):] if ":=" in body else body
        return sorted({w for w in re.findall(r"\b([a-z_][a-z0-9_]*)\b", body)
                       if w in self.sigs and w != name})

    def consts_of(self, name):
        body = self.bodies.get(name, "")
        return sorted({w for w in re.findall(r"\b([A-Z][A-Z0-9_]*)\b", body) if w in self.consts})


def def_text(rd, start):
    """The text of the definition at `start`: up to the next line that starts a new item."""
    m = re.compile(r"\n(?=\S)").search(rd, rd.index("\n", start))
    return rd[start:m.start() if m else len(rd)]


def split_top(body):
    """`(a, t), (b, u)` -> ["a, t", "b, u"]: the items of a list of pairs, without the parens."""
    out, depth, cur = [], 0, ""
    for ch in body:
        if ch == "(":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        if ch == ")":
            depth -= 1
            if depth == 0:
                out.append(cur)
                continue
        if depth >= 1:
            cur += ch
    return out


def strip_parens(t):
    t = t.strip()
    while t.startswith("(") and t.endswith(")"):
        d = 0
        for i, ch in enumerate(t):
            d += ch == "("
            d -= ch == ")"
            if d == 0 and i < len(t) - 1:
                return t
        t = t[1:-1].strip()
    return t


def rep_of(m, ssz, rt, y):
    """The DV term of a readable value `y : rt` of SSZ type `ssz`, or Unsupported."""
    ssz, rt = strip_parens(ssz), strip_parens(rt)
    mm = re.fullmatch(r"\.uint (.*)", ssz)
    if mm and rt in m.uint:
        return "(.leaf (.uint %s %s.val))" % (mm.group(1), y)
    if ssz == ".boolean" and rt == "Boolean":
        return "(.leaf (.boolean %s.val))" % y
    mm = re.fullmatch(r"\.bytes (\d+) \d+", ssz)
    if mm and rt in m.bytes:
        return "(.leaf (.bytes %s %s.data))" % (mm.group(1), y)
    mm = re.fullmatch(r"\.container (\d+)", ssz)
    if mm and m.ids.get(int(mm.group(1))) == rt and rt in m.containers:
        if rt not in m.reps:
            raise Unsupported("container " + rt)
        return "(.cont %s (kids_%s %s))" % (mm.group(1), rt, y)
    mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz)
    mr = re.fullmatch(r"List (.*)", rt)
    if mm and mr:
        z = "z%d" % (len(y) % 7)
        inner = rep_of(m, mm.group(2), mr.group(1), z)
        return "(.list %s %s %s (%s.map fun %s => %s))" % (mm.group(1), mm.group(2), mm.group(3), y, z, inner)
    raise Unsupported("field %s : %s" % (ssz, rt))


def raw_of(m, ssz, rt):
    """A written value of a field or an element: (binders, its DV pattern, its readable value)."""
    ssz, rt = strip_parens(ssz), strip_parens(rt)
    mm = re.fullmatch(r"\.uint (.*)", ssz)
    if mm and rt in m.uint:
        return "(n : Nat)", "(.leaf (.uint %s n))" % mm.group(1), "(⟨n⟩ : %s)" % rt
    if ssz == ".boolean" and rt == "Boolean":
        return "(b : Bool)", "(.leaf (.boolean b))", "(⟨b⟩ : Boolean)"
    mm = re.fullmatch(r"\.bytes (\d+) \d+", ssz)
    if mm and rt in m.bytes:
        return "(b : List UInt8)", "(.leaf (.bytes %s b))" % mm.group(1), "(⟨b⟩ : %s)" % rt
    mm = re.fullmatch(r"\.container (\d+)", ssz)
    if mm and rt in m.reps:
        return "(y : %s)" % rt, "(.cont %s (kids_%s y))" % (mm.group(1), rt), "y"
    mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz)
    mr = re.fullmatch(r"List (.*)", rt)
    if mm and mr:
        inner = rep_of(m, mm.group(2), mr.group(1), "z")
        return ("(ys : %s)" % paren(rt), "(.list %s %s %s (ys.map fun z => %s))" % (mm.group(1), mm.group(2), mm.group(3), inner),
                "ys")
    raise Unsupported("field %s : %s" % (ssz, rt))


def paren(t):
    return t if t.startswith("(") else "(" + t + ")"


M = None


def model():
    global M
    if M is None:
        M = Model()
        build_reps(M)
    return M


class Unsupported(Exception):
    pass


# ---------------------------------------------------------------------------
# Encodings of arguments and results

def param(m, i, pn, pt, sub=None, isub=False):
    """(binder, root DV, readable argument) of parameter `pn : pt`. `sub` is the class of the
    value that a caller passes to a width class parameter."""
    v = "a_" + pn
    if pt in m.uint:
        ty = m.uint_ty(sub if sub and pt.startswith("Uint") else pt)
        if ty is None:
            raise Unsupported("uint class " + pt)
        return "(%s : Nat)" % v, "(.leaf (.uint %s %s))" % (ty, v), "⟨%s⟩" % v
    if pt == "Bool":
        return "(%s : Bool)" % v, "(.leaf (.bool %s))" % v, v
    if pt == "Int" and isub and sub:
        return "(%s : Nat)" % v, "(.leaf (.uint %s %s))" % (m.uint_ty(sub), v), "(%s : Int)" % v
    if pt == "Int":
        return "(%s : Int)" % v, "(.leaf (.int %s))" % v, v
    if pt in m.bytes:
        g = m.bytes_id(pt)
        if g is None:
            raise Unsupported("bytes class " + pt)
        return "(%s : List UInt8)" % v, "(.leaf (.bytes %d %s))" % (g, v), "⟨%s⟩" % v
    if pt == "Bytes":
        return "(%s : List UInt8)" % v, "(.leaf (.bytes 0 %s))" % v, v
    if pt in m.reps:
        return "(%s : %s)" % (v, pt), "(.cont %d (kids_%s %s))" % (m.cid[pt], pt, v), v
    # An optional parameter: the caller passes a value (`some`).
    mo = re.fullmatch(r"\(?Option (\w+)\)?", pt)
    if mo:
        b, r, a = param(m, i, pn, mo.group(1), sub, isub)
        return b, r, "(some %s)" % a
    # A sequence: the caller passes a Python list.
    mr = re.fullmatch(r"\(?List (\w+)\)?", pt)
    if mr and elem_ssz(m, mr.group(1)):
        inner = rep_of(m, elem_ssz(m, mr.group(1)), mr.group(1), "z")
        return "(%s : List %s)" % (v, mr.group(1)), "(.list .pyList .any none (%s.map fun z => %s))" % (v, inner), v
    raise Unsupported("param type " + pt)


def elem_ssz(m, rt):
    """The SSZ type of an item of readable class `rt` in a Python list, or None."""
    if rt in m.reps:
        return ".container %d" % m.cid[rt]
    if rt in m.uint and m.uint_ty(rt):
        return ".uint %s" % m.uint_ty(rt)
    if rt in m.bytes and m.bytes_id(rt) is not None:
        return ".bytes %d %d" % (m.bytes_id(rt), m.bytes[rt])
    if rt == "Boolean":
        return ".boolean"
    return None


def result(m, rt, sub=None):
    """The `DRes` of a readable result `x : rt`."""
    if rt in m.uint:
        return "DRes.val (.uint %s x.val)" % m.uint_ty(sub if sub and rt.startswith("Uint") else rt)
    if rt == "Bool":
        return "DRes.val (.bool x)"
    if rt == "Int":
        return "DRes.val (.int x)"
    if rt == "Unit":
        return "DRes.val .none"
    if rt in m.bytes and m.bytes_id(rt) is not None:
        return "DRes.val (.bytes %d x.data)" % m.bytes_id(rt)
    if rt == "Bytes":
        return "DRes.val (.bytes 0 x)"
    mm = re.fullmatch(r"\(?List (\w+)\)?", rt)
    if mm and mm.group(1) in m.uint:
        return "DRes.tree (.list .pyList .any none (x.map fun y => DV.leaf (.uint %s y.val)))" % m.uint_ty(mm.group(1))
    if rt in m.reps:
        return "DRes.tree (.cont %d (kids_%s x))" % (m.cid[rt], rt)
    raise Unsupported("result type " + rt)


# ---------------------------------------------------------------------------
# Fuel

def depth(t):
    """The nesting depth of a syntax tree: an upper bound on the `den` levels it needs."""
    if isinstance(t, tuple):
        if t[0] == "list":
            return max([depth(x) for x in t[1]] + [0])
        if t[0] == "app":
            return 1 + max([depth(x) for x in t[2:]] + [0])
        if t[0] == "tuple":
            return max([depth(x) for x in t[1:]] + [0])
    return 0


# ---------------------------------------------------------------------------
# Generated Lean

HEADER = """import SpecLean.Layer4.GenBridge
import SpecLean.Validation.Tactic
"""

OPEN = """
open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd SpecLean.Rd.Gen SpecLean.Layer4.GenSteps

attribute [local instance high] LibModel.toLibValues
attribute [local instance] Cfg.default

variable [Spec]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
"""

OPENX = OPEN + "\nvariable [ExtSet]\n"


def classes_file(m):
    out = [HEADER, "/-!\n# Layer 4: the rewrites of the readable classes\n\n"
           "Generated by tools/gen_l4.py. Do not edit.\n-/\n",
           "namespace SpecLean.Layer4.Gen\n", OPEN,
           "/-- Every path of length at most 6 under a root of class `ty`. -/",
           "def fpAll (ty : Name) : Footprint :=\n  [%s]\n" % ", ".join(
               "⟨ty, [%s]⟩" % ", ".join([".any"] * k) for k in range(7)),
           "/-- The footprints: a function that returns its updated argument may write anywhere under it. -/",
           "def fpsGen : Name → Footprint\n%s  | _ => []\n" % "".join(
               "  | %d => %s\n" % (m.fns[n]["id"], footprint(m, n, w)) for n, w in sorted(writers(m).items()))]
    for c in sorted(m.uint):
        out.append("@[l4_simp] theorem uv_%s (y : %s) : UintC.val y = y.val :=\n  Eq.trans rfl rfl" % (c, c))
        out.append("@[l4_simp] theorem ub_%s : UintC.bits %s = %d :=\n  Eq.trans rfl rfl" % (c, c, m.uint[c]))
        out.append("@[l4_simp] theorem uo_%s (n : Nat) : (UintC.ofNat n : %s) = ⟨n⟩ :=\n  Eq.trans rfl rfl" % (c, c))
    for c in sorted(m.bytes):
        out.append("@[l4_simp] theorem bd_%s (y : %s) : BytesC.data y = y.data :=\n  Eq.trans rfl rfl" % (c, c))
        out.append("@[l4_simp] theorem bl_%s : BytesC.len %s = %d :=\n  Eq.trans rfl rfl" % (c, c, m.bytes[c]))
        out.append("@[l4_simp] theorem bo_%s (b : List UInt8) : (BytesC.ofBytes b : %s) = ⟨b⟩ :=\n  Eq.trans rfl rfl" % (c, c))
    for c, rhs in re.findall(r"^instance : PyOrd (\w+) := ⟨fun a b => (decide \(a\.val < b\.val\))⟩", m.rd, re.M):
        out.append("@[l4_simp] theorem po_%s (a b : %s) : PyOrd.lt a b = decide (a.val < b.val) := Eq.trans rfl rfl"
                   % (c, c))
    cfg = m.rd[m.rd.index("def Cfg.default : Cfg where"):]
    cfg = cfg[:cfg.index("\n\n")]
    for f, v in re.findall(r"^  (\w+) := (.+)$", cfg, re.M):
        out.append("@[l4_simp] theorem cfg_%s : @Cfg.%s Cfg.default = %s := Eq.trans rfl rfl" % (f, f, v))
    out.append("")
    for n in sorted(m.fns):
        f = m.fns[n]
        nd = len([x for x in split_top(f["defaults"])]) if f["defaults"].strip() else 0
        out.append("@[l4_simp] theorem fnlen_%s : Scope.fn_%s.params.names.length = %d := Eq.trans rfl rfl"
                   % (n, n, len(f["params"])))
        out.append("@[l4_simp] theorem fndef_%s : Scope.fn_%s.params.defaults.length = %d := Eq.trans rfl rfl"
                   % (n, n, nd))
    out.append("")
    for n in m.rep_order:
        out.append("/-- The children of the decoded tree of a `%s`. -/" % n)
        out.append("def kids_%s (x : %s) : List DV :=\n  [%s]\n" % (n, n, ",\n    ".join(m.reps[n])))
        for i, r in enumerate(m.reps[n]):
            out.append("@[l4_simp] theorem kids_%s_%d (x : %s) : (kids_%s x)[%d]? = some %s :=\n  Eq.trans rfl rfl"
                       % (n, i, n, n, i, r))
        out.append("@[l4_simp] theorem kids_%s_len (x : %s) : (kids_%s x).length = %d :=\n  Eq.trans rfl rfl\n"
                   % (n, n, n, len(m.reps[n])))
        fns = [fn for fn, _, _ in m.containers[n]]
        mk_reps = [r for r in m.reps[n]]
        if not all(r.startswith("(.leaf") for r in mk_reps):
            fns = []
        for fn in fns:
            mk_reps = [re.sub(r"\bx\.%s\b" % fn, "a_%s" % fn, r) for r in mk_reps]
        if fns:
          out.append("theorem kids_%s_mk %s :\n    kids_%s { %s } =\n      [%s] :=\n  Eq.trans rfl rfl\n"
                   % (n, " ".join("(a_%s : %s)" % (fn, strip_parens(rt)) for fn, _, rt in m.containers[n]), n,
                      ", ".join("%s := a_%s" % (fn, fn) for fn in fns), ", ".join(mk_reps)))
          # A new container from its flat fields, as the readable value (an appended item).
          raws = []
          for fn, ssz, rt in m.containers[n]:
              try:
                  b, pat, rv = raw_of(m, ssz, rt)
              except Unsupported:
                  raws = None
                  break
              tag = "_" + fn
              raws.append((re.sub(r"\((\w+) :", lambda mm: "(%s%s :" % (mm.group(1), tag), b, count=1),
                           re.sub(r"\b(n|b)\b", lambda mm: mm.group(1) + tag, pat),
                           fn, re.sub(r"\b(n|b)\b", lambda mm: mm.group(1) + tag, rv)))
          if raws:
              out.append("@[l4_simp] theorem kids_%s_fold %s :\n    (DV.cont %d [%s] : DV) =\n      DV.cont %d (kids_%s { %s }) :=\n  Eq.trans rfl rfl\n"
                         % (n, " ".join(r[0] for r in raws), m.cid[n], ", ".join(r[1] for r in raws), m.cid[n], n,
                            ", ".join("%s := %s" % (r[2], r[3]) for r in raws)))
        for i, (fn, ssz, rt) in enumerate(m.containers[n]):
            b, pat, rv = raw_of(m, ssz, rt)
            out.append("@[l4_simp] theorem kids_%s_set_%d (x : %s) %s :\n    (kids_%s x).set %d %s = kids_%s { x with %s := %s } :=\n  Eq.trans rfl rfl"
                       % (n, i, n, b, n, i, pat, n, fn, rv))
        out.append("")
    # A write into a list element: the list of the readable list with the element set.
    seen = {}
    for n in m.rep_order:
        for fn, ssz, rt in m.containers[n]:
            ssz2, rt2 = strip_parens(ssz), strip_parens(rt)
            mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz2)
            mr = re.fullmatch(r"List (.*)", rt2)
            if not (mm and mr):
                continue
            try:
                b, pat, rv = raw_of(m, mm.group(2), mr.group(1))
            except Unsupported:
                continue
            inner = rep_of(m, mm.group(2), mr.group(1), "z")
            if inner in seen:
                continue
            k = seen[inner] = len(seen)
            out.append("@[l4_simp] theorem lset_%d (xs : %s) (i : Nat) %s :\n    (xs.map fun z => (%s : DV)).set i %s =\n      (xs.set i %s).map fun z => (%s : DV) := by\n  rw [List.map_set]"
                       % (k, paren(rt2), b, inner, pat, rv, inner))
            out.append("@[l4_simp] theorem lapp_%d (xs : %s) %s :\n    (xs.map fun z => (%s : DV)) ++ [%s] =\n      (xs ++ [%s]).map fun z => (%s : DV) := by\n  rw [List.map_append]; rfl"
                       % (k, paren(rt2), b, inner, pat, rv, inner))
    out.append("/-! The range facts of the readable values. -/\n")
    for n in m.rep_order:
        out.append(ok_def(m, n))
    out.append("/-! The decoded tree of a readable value, from its decoder. -/\n")
    for n in m.rep_order:
        if ("def dec_%s : Dec %s := fun h v => do" % (n, n)) not in m.rd:
            continue
        try:
            out.append("set_option maxHeartbeats 1000000 in\n" + bridge_theorem(m, n))
            m.bridged.add(n)
        except Unsupported:
            pass
        try:
            out.append("set_option maxHeartbeats 1000000 in\n" + okb_theorem(m, n))
            m.okb.add(n)
        except Unsupported:
            pass
    out.append("/-! The readable value of a decoded tree. -/\n")
    m.undv = set()
    for n in m.rep_order:
        try:
            out.append(undv_text(m, n))
            m.undv.add(n)
        except Unsupported:
            pass
    OPAQUE.clear()
    fails = {}
    fp = ROOT / ".lake/l4_fails.json"
    if fp.exists():
        import json
        fails = json.loads(fp.read_text())
    runf = parse_runf(m)
    stmts = parse_runf(m, "SpecLean/Validation/Gen/Stmts.lean", stmt=True)
    for c in sorted(set(runf) | set(stmts)):
        # A callee that layer 4 did not prove: from the tactic's theorem, or else from its
        # statement (the conditional tier).
        if c in fails:
            OPAQUE[c] = runf.get(c) or stmts[c]
    out.append(ext_text(m))
    for n in m.rep_order:
        if ("def enc_%s : Enc %s := fun x =>" % (n, n)) not in m.rd:
            continue
        try:
            out.append("set_option maxHeartbeats 1000000 in\n" + encdec_theorem(m, n))
            m.encdec.add(n)
        except Unsupported:
            pass
    out.append("\nend SpecLean.Layer4.Gen\n")
    return "\n".join(out)


def dec_fields(m, n):
    """The fields of the readable decoder of `n`: (name, decoder text) each, or Unsupported."""
    i = m.rd.find("def dec_%s : Dec %s := fun h v => do\n" % (n, n))
    if i < 0:
        raise Unsupported("no decoder")
    body = m.rd[i:m.rd.index("\n\n", i)]
    out = []
    for k, (fn, idx, d) in enumerate(re.findall(r"^  let (\S+) ← fs\[(\d+)\]\? >>= (.+) h$", body, re.M)):
        if int(idx) != k:
            raise Unsupported("field order")
        out.append((fn, d))
    if len(out) != len(m.containers[n]):
        raise Unsupported("decoder fields")
    return out


def undv_of(m, d):
    """The decoder of a tree and its `DecOf` proof, for a readable field decoder `d`."""
    d = d.strip()
    if d.startswith("(") and d.endswith(")"):
        a = split_args(d)
        if a[0] == "decListT" and len(a) == 5:
            u, p = undv_of(m, a[4])
            return ("(GenBridge.undvList %s %s %s %s)" % (a[1], a[2], a[3], u),
                    "(GenBridge.decOf_list %s _ _ _)" % p)
        raise Unsupported("decoder " + d)
    if d == "decBooleanV":
        return "(GenBridge.undvLeaf decBooleanV)", "GenBridge.decOf_boolean"
    mm = re.fullmatch(r"dec_(\w+)", d)
    if not mm:
        raise Unsupported("decoder " + d)
    y = mm.group(1)
    if y in m.reps:
        if y not in m.undv:
            raise Unsupported("undv of " + y)
        return "undv_%s" % y, "decOf_%s" % y
    if y in m.uint:
        return "(GenBridge.undvLeaf dec_%s)" % y, "(GenBridge.decOf_uint _)"
    if y in m.bytes:
        return "(GenBridge.undvLeaf dec_%s)" % y, "(GenBridge.decOf_bytes _)"
    raise Unsupported("decoder " + d)


def undv_kid(m, d, rt, t, hok, depth=0):
    """A proof that the tree decoder of `d` gives back `t : rt` from its tree; `hok` proves the
    range fact of `t` (or is None)."""
    d, rt = d.strip(), strip_parens(rt)
    if d.startswith("("):
        a = split_args(d)
        mr = re.fullmatch(r"List (.*)", rt)
        y = "y%d" % depth
        inner = undv_kid(m, a[4], mr.group(1), y, "(%s %s hy%d)" % (hok, y, depth) if hok else None, depth + 1)
        return "(GenBridge.undvList_map _ _ _ %s (fun %s hy%d => %s))" % (t, y, depth, inner)
    if d == "decBooleanV":
        return "(GenBridge.undv_boolean %s)" % t
    y = d[len("dec_"):]
    if y in m.reps:
        return "(undv_kids_%s %s %s)" % (y, t, hok)
    if y in m.uint:
        return "(GenBridge.undv_uint _ %s %s)" % (t, hok)
    return "(GenBridge.undv_bytes _ %s %s)" % (t, hok)


def parse_runf(m, path="SpecLean/Validation/Gen/Loops.lean", stmt=False):
    """The tactic's `_runF` theorems (or, with `stmt`, its unproved `_stmtF` statements) that
    layer 4 can take as callee statements: each argument a container (decoded by `dec_X`), a
    sequence or a uint, the result a uint, a `Bool` or a new list of uints."""
    txt = (ROOT / path).read_text()
    out = {}
    if stmt:
        pat = (r"^def (\w+)_stmtF : Prop :=\n  ∀ \(gfp : Footprint\) \(h : Heap\) (.*?) \(F : Nat\) \(hF : (.*?) ≤ F\),\n"
               r"\s+ResultMatches gfp \[\] h \[(.*?)\] \(fun \(r : (.*?)\) h' v => (.*?)\)\n"
               r"\s+\(interp \(Scope\.env sha\) F Scope\.Id\.«\w+» \[.*?\] h\) \((.*?)\)\n")
    else:
        pat = (r"^theorem (\w+)_runF \(gfp : Footprint\) \(h : Heap\) (.*?) \(F : Nat\) \(hF : (.*?) ≤ F\) :\n"
               r"\s+ResultMatches gfp \[\] h \[(.*?)\] \(fun \(r : (.*?)\) h' v => (.*?)\)\n"
               r"\s+\(interp \(Scope\.env sha\) F Scope\.Id\.«\w+» \[.*?\] h\) \((.*?)\) := by")
    for mm in re.finditer(pat, txt, re.M):
        c, binders, bound, args, rt, pred, call = mm.groups()
        if "Shaped" in binders or "OracleBls" in binders or ("(ho : " in binders and not stmt):
            continue
        if c not in m.fns or c not in m.sigs:
            continue
        bnames = re.findall(r"\((\w+) :", binders)
        ok = True
        arglist = []
        ranges = {}
        for a in top_items(args):
            ma = re.fullmatch(r"\(\.ref r(\d+)\)", a)
            mu = re.fullmatch(r"\(\.uint (.*) x(\d+)\)", a)
            mby = re.fullmatch(r"\(\.bytes (\S+) x(\d+)\)", a)
            if ma:
                i = ma.group(1)
                md = re.search(r"\(x%s : (\w+)\) \(hy%s : dec_(\w+) h \(\.ref r%s\) = some x%s\)" % (i, i, i, i), binders)
                ml = re.search(r"\(hy%s : \(decListE (.*?) (dec\w+)\) h \(\.ref r%s\) = some x%s\)" % (i, i, i), binders)
                if ml:
                    try:
                        u, pf = undv_of(m, ml.group(2))
                    except Unsupported:
                        ok = False
                        break
                    arglist.append(("list", (ml.group(1), u, pf), int(i)))
                    continue
                if not md or md.group(1) != md.group(2) or md.group(1) not in m.undv:
                    ok = False
                    break
                arglist.append(("cont", md.group(1), int(i)))
            elif mby:
                ml = re.search(r"\(hl%s : x%s\.length = (\d+)\)" % (mby.group(2), mby.group(2)), binders)
                if not ml:
                    ok = False
                    break
                arglist.append(("bytes", (mby.group(1), int(ml.group(1))), int(mby.group(2))))
            elif mu:
                arglist.append(("uint", mu.group(1), int(mu.group(2))))
                mr = re.search(r"\(hr%s : x%s < 2 \^ (\d+)\)" % (mu.group(2), mu.group(2)), binders)
                if mr:
                    ranges[int(mu.group(2))] = int(mr.group(1))
            else:
                ok = False
                break
        if not ok:
            continue
        if re.match(r"v = \(enc_(\w+) r h'\)\.1 ∧ UintC\.val r < 2 \^ \d+", pred) and rt in m.uint:
            rkind = "uint"
        elif pred.startswith("v = .bool r") and rt == "Bool":
            rkind = "bool"
        elif (re.match(r"ListRes h h' v \(r\.map fun x => Value\.uint (.*?) x\.val\)", pred)
              and re.fullmatch(r"\(List (\w+)\)", rt) and re.fullmatch(r"\(List (\w+)\)", rt).group(1) in m.uint):
            rkind = "list"
        else:
            continue
        lens = {}
        for i, fld in re.findall(r"\bx(\d+)\.(\w+)\.length\b", bound):
            lens[(int(i), fld)] = lens.get((int(i), fld), 0) + 1
        for i in re.findall(r"\bx(\d+)\.length\b", bound):
            lens[(int(i), None)] = lens.get((int(i), None), 0) + 1
        nW = len(re.findall(r"\bx\d+ \+ ", bound))
        # A constant of 2 ^ 64 or more is `bigFuel` (irreducible): a numeral that large is slow.
        nW += sum(int(t) for t in re.findall(r"(?<![\w.])\d{18,}(?![\w.])", bound)) // 2 ** 64
        bound_c = re.sub(r"\bx\d+ \+ ", "", bound.strip())
        mD = re.fullmatch(r"(?:.*? \+ )??(\d+(?: \+ \d+)*)", bound_c)
        if not mD or re.sub(r"\bx\d+(\.\w+)?\.length \+ ", "", bound_c) != mD.group(1):
            continue
        if any(fld is None and n > 1 for (_, fld), n in lens.items()):
            continue
        pos = {i: k for k, (_, _, i) in enumerate(arglist)}
        bound = re.sub(r"(?<![\w.])\d{18,}(?![\w.])", lambda q: " + ".join(
            ["bigFuel"] * (int(q.group(0)) // 2 ** 64) + [str(int(q.group(0)) % 2 ** 64)]), bound)
        out[c] = dict(args=arglist, bound=bound, rt=rt, rkind=rkind, call=call, binders=bnames,
                      stmt=stmt, ranges=ranges, conj=" ∧ " in pred,
                      D=sum(int(t) for t in mD.group(1).split(" + ")) % 2 ** 64, ho="(ho : " in binders,
                      lens=[(pos[i], fld if n == 1 else "%s*%d" % (fld, n)) for (i, fld), n in lens.items()]
                      + [("W", j) for j in range(nW)],
                      cls=arglist[0][1] if arglist and arglist[0][0] == "cont" else None)
    return out


def ext_args(o):
    """The match of an ext entry on its roots: the patterns, the scrutinees, and the conditions."""
    rs = ["r%d" % i for i in range(len(o["args"]))]
    scr, pat, conds = [], [], []
    for (k, ty, i), r in zip(o["args"], rs):
        if k == "cont":
            scr.append("undv_%s %s" % (ty, r))
            pat.append("some x%d" % i)
        elif k == "list":
            scr.append("GenBridge.undvListE %s %s %s" % (ty[0], ty[1], r))
            pat.append("some x%d" % i)
        elif k == "bytes":
            scr.append("GenBridge.leafBytes %s" % r)
            pat.append("some (c%d, x%d)" % (i, i))
            conds.append("c%d = %s" % (i, ty[0]))
            conds.append("x%d.length = %d" % (i, ty[1]))
        else:
            scr.append("GenBridge.leafUint %s" % r)
            pat.append("some (t%d, x%d)" % (i, i))
            conds.append("t%d = %s" % (i, ty))
            if i in o.get("ranges", {}):
                conds.append("x%d < 2 ^ %d" % (i, o["ranges"][i]))
    return rs, scr, pat, conds


def ext_text(m):
    """The callees taken from statements: one `ExtFn` each, and the table `extGen`."""
    out = ["/-! The callees taken from statements (`ExtOK`). -/\n"]
    ents, entsW = [], []
    for c, o in sorted(OPAQUE.items()):
        rs, scr, pat, conds = ext_args(o)
        rt = o["rt"]
        if o["rkind"] == "uint":
            enc = "DRes.val (.uint %s y.val)" % m.uint_ty(rt)
        elif o["rkind"] == "list":
            enc = "DRes.tree (.list .pyList .any none (y.map fun z => DV.leaf (.uint %s z.val)))" % m.uint_ty(
                re.fullmatch(r"\(List (\w+)\)", rt).group(1))
        else:
            enc = "DRes.val (.bool y)"
        cond = " ∧ ".join(conds) if conds else "True"
        out.append("def ext_%s : ExtFn where\n"
                   "  bound := fun rs => match rs with\n"
                   "    | [%s] => match %s with\n"
                   "      | %s => %s\n"
                   "      | %s => 0\n"
                   "    | _ => 0\n"
                   "  run := fun rs => match rs with\n"
                   "    | [%s] => match %s with\n"
                   "      | %s => if %s then GenBridge.extRes (fun y : %s => %s) (%s) else none\n"
                   "      | %s => none\n"
                   "    | _ => none\n"
                   % (c, ", ".join(rs), ", ".join(scr), ", ".join(pat), o["bound"], ", ".join("_" for _ in rs),
                      ", ".join(rs), ", ".join(scr), ", ".join(pat), cond, rt, enc, o["call"],
                      ", ".join("_" for _ in rs)))
        ents.append((m.fns[c]["id"], c))
    body = "fun g => " + "".join("if g = %d then some ext_%s else " % (i, c) for i, c in ents) + "none"
    bodyW = "fun g => " + "".join("if g = %d then some extW_%s else " % (i, c) for i, c in entsW) + "none"
    out.append("/-- The table of the generated theorems: the entries of the allowed set. -/\n"
               "instance extGen [ExtSet] : ExtTab :=\n  ⟨fun g => if g ∈ ExtSet.S then (%s) g else none,\n"
               "   fun g => if g ∈ ExtSet.S then (%s) g else none⟩\n" % (body, bodyW))
    out.append("@[l4_simp] theorem extGen_ext [ExtSet] (g : Name) :\n    ExtTab.ext g = if g ∈ ExtSet.S then (%s) g else none := rfl\n"
               % body.replace("fun g => ", "fun g : Name => ", 1))
    out.append("@[l4_simp] theorem extGen_extW [ExtSet] (g : Name) :\n    ExtTab.extW g = if g ∈ ExtSet.S then (%s) g else none := rfl\n"
               % bodyW.replace("fun g => ", "fun g : Name => ", 1))
    return "\n".join(out)


def undv_text(m, n):
    fs = dec_fields(m, n)
    us = [undv_of(m, d) for _, d in fs]
    K = len(fs)
    lines = ["def undv_%s : DV → Option %s\n  | .cont ty ds =>\n    if ty = %d then do" % (n, n, m.cid[n])]
    for i, ((fn, d), (u, p)) in enumerate(zip(fs, us)):
        lines.append("      let %s ← ds[%d]?.bind %s" % (fn, i, u))
    lines.append("      pure { %s }\n    else none\n  | _ => none\n" % ", ".join(fn for fn, _ in fs))
    pat = "\n".join("      obtain ⟨y%d, h%d, hu⟩ := Option.bind_eq_some_iff.mp hu" % (i, i) for i in range(K))
    fl = ", ".join("GenBridge.field_decOf %s hm %d h%d" % (p, i, i) for i, (u, p) in enumerate(us))
    lines.append("theorem decOf_%s : GenBridge.DecOf dec_%s undv_%s := by\n"
                 "  intro h n v d x hd hu\n"
                 "  cases d with\n"
                 "  | cont ty ds =>\n"
                 "    simp only [undv_%s] at hu\n"
                 "    split at hu\n"
                 "    · next hty =>\n"
                 "      subst hty\n"
                 "      obtain ⟨a, m, fs, rfl, rfl, ho, hm⟩ := dec_cont hd\n"
                 "      simp only [Option.bind_eq_bind] at hu\n%s\n"
                 "      simp only [Option.pure_def, Option.some.injEq] at hu; subst hu\n"
                 "      simp only [dec_%s, containerFieldsT, ho, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, %s]\n"
                 "      try rfl\n"
                 "    · cases hu\n"
                 "  | _ => simp [undv_%s] at hu\n" % (n, n, n, n, pat, n, fl, n))
    facts = []
    for fn, ssz, rt in m.containers[n]:
        facts.append(ok_fact(m, ssz, rt, "x.%s" % fn) is not None)
    haves = []
    j = 0
    for i, ((fn, d), (u, p), (_, ssz, rt)) in enumerate(zip(fs, us, m.containers[n])):
        hok = None
        if facts[i]:
            hok = "hx" + ".2" * j + ".1"
            j += 1
        haves.append("  have e%d : %s %s = some x.%s :=\n    %s" % (i, u, m.reps[n][i], fn,
                                                                undv_kid(m, d, rt, "x.%s" % fn, hok)))
    lines.append("theorem undv_kids_%s (x : %s) (hx : ok_%s x) :\n"
                 "    undv_%s (.cont %d (kids_%s x)) = some x := by\n"
                 "  simp only [ok_%s] at hx\n%s\n"
                 "  simp only [undv_%s, kids_%s, ↓reduceIte, List.getElem?_cons_zero, List.getElem?_cons_succ,\n"
                 "    Option.bind_some, Option.bind_eq_bind, Option.pure_def, %s]\n"
                 % (n, n, n, n, m.cid[n], n, n, "\n".join(haves), n, n,
                    ", ".join("e%d" % i for i in range(K))))
    return "\n".join(lines)


def bridge_field(m, ssz, rt, hy):
    """A proof that the field or element decodes to its tree, from `hy : dec_T h w = some y`."""
    ssz, rt = strip_parens(ssz), strip_parens(rt)
    if re.fullmatch(r"\.uint (.*)", ssz) and rt in m.uint:
        return "(GenBridge.uintT_dec %s)" % hy
    if ssz == ".boolean" and rt == "Boolean":
        return "(GenBridge.boolean_dec %s)" % hy
    if re.fullmatch(r"\.bytes (\d+) \d+", ssz) and rt in m.bytes:
        return "(GenBridge.bytesT_dec %s)" % hy
    if re.fullmatch(r"\.container (\d+)", ssz) and rt in m.reps:
        return "(bridge_%s hc %s)" % (rt, hy)
    mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz)
    mr = re.fullmatch(r"List (.*)", rt)
    if mm and mr:
        d = hy.count("'") + 1
        he = "he" + "'" * d
        return "(GenBridge.listT_dec %s (fun _ _ %s => %s))" % (hy, he, bridge_field(m, mm.group(2), mr.group(1), he))
    raise Unsupported("bridge field")


def encdec_field(m, ssz, rt, t, depth=0):
    """A proof of `EncDec` of the encoder of a field or an element `t`, or Unsupported."""
    ssz, rt = strip_parens(ssz), strip_parens(rt)
    if re.fullmatch(r"\.uint (.*)", ssz) and rt in m.uint:
        return "(GenBridge.encDec_flat rfl)"
    if ssz == ".boolean" and rt == "Boolean":
        return "(GenBridge.encDec_flat rfl)"
    if re.fullmatch(r"\.bytes (\d+) \d+", ssz) and rt in m.bytes:
        return "(GenBridge.encDec_flat rfl)"
    if re.fullmatch(r"\.container (\d+)", ssz) and rt in m.reps:
        if rt not in m.encdec:
            raise Unsupported("encdec of " + rt)
        return "(encDec_%s %s)" % (rt, t)
    mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz)
    mr = re.fullmatch(r"List (.*)", rt)
    if mm and mr:
        y = "y%d" % depth
        return "(GenBridge.encDec_list (fun %s => %s) %s)" % (y, encdec_field(m, mm.group(2), mr.group(1), y, depth + 1), t)
    raise Unsupported("encdec field")


def encdec_theorem(m, n):
    fs = m.containers[n]
    K = len(fs)
    cases = []
    for i, (fn, ssz, rt) in enumerate(fs):
        cases.append("  | %d, hg, hd =>\n    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hg\n"
                     "    simp only [kids_%s_%d, Option.some.injEq] at hd\n    subst hg; subst hd\n    exact %s"
                     % (i, n, i, encdec_field(m, ssz, rt, "x.%s" % fn)))
    return ("theorem encDec_%s (x : %s) : GenBridge.EncDec (enc_%s x) (.cont %d (kids_%s x)) := by\n"
            "  show GenBridge.EncDec (encContainer _ _) _\n"
            "  refine GenBridge.encDec_container (by rfl) fun i g d hg hd => ?_\n"
            "  match i, hg, hd with\n%s\n"
            "  | _ + %d, _, hd =>\n"
            "    rw [List.getElem?_eq_none (by simp only [kids_%s_len]; omega)] at hd; cases hd\n\n"
            "theorem htr_call_%s {sha : Oracle} (ho : Validation.HtrBridge.OracleHtr sha) (x : %s) {γ : Type}\n"
            "    (K : DRes → DM γ) :\n"
            "    Option.map (Except.mapError SpecError.fail) (DM.bind (dHtr (Scope.env sha) (.cont %d (kids_%s x))) K) =\n"
            "      callK (htr enc_%s x) fun r =>\n"
            "        Option.map (Except.mapError SpecError.fail) (K (.val (.bytes (Scope.env sha).nm.root r))) :=\n"
            "  bind_call (GenBridge.htr_den ho enc_%s x (encDec_%s x)) K\n"
            % (n, n, n, m.cid[n], n, "\n".join(cases), K, n, n, n, m.cid[n], n, n, n, n))


def ok_fact(m, ssz, rt, t, depth=0):
    """The range fact of a field or an element `t`, or None when it has none."""
    ssz, rt = strip_parens(ssz), strip_parens(rt)
    if re.fullmatch(r"\.uint (.*)", ssz) and rt in m.uint:
        return "%s.val < 2 ^ %d" % (t, m.uint[rt])
    if re.fullmatch(r"\.bytes (\d+) \d+", ssz) and rt in m.bytes:
        return "%s.data.length = %d" % (t, m.bytes[rt])
    if re.fullmatch(r"\.container (\d+)", ssz) and rt in m.reps:
        return "ok_%s %s" % (rt, t)
    mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz)
    mr = re.fullmatch(r"List (.*)", rt)
    if mm and mr:
        y = "y%d" % depth
        inner = ok_fact(m, mm.group(2), mr.group(1), y, depth + 1)
        if inner:
            return "(∀ %s ∈ %s, %s)" % (y, t, inner)
    return None


def ok_proof(m, ssz, rt, hy, depth=0):
    """A proof of `ok_fact` from `hy : dec_T h w = some y`, or Unsupported."""
    ssz, rt = strip_parens(ssz), strip_parens(rt)
    if re.fullmatch(r"\.uint (.*)", ssz) and rt in m.uint:
        return "(by have := GenBridge.uintT_ok %s; simpa only [uv_%s, ub_%s] using this)" % (hy, rt, rt)
    if re.fullmatch(r"\.bytes (\d+) \d+", ssz) and rt in m.bytes:
        return "(by have := GenBridge.bytesT_ok %s; simpa only [bd_%s, bl_%s] using this)" % (hy, rt, rt)
    if re.fullmatch(r"\.container (\d+)", ssz) and rt in m.reps:
        if rt not in m.okb:
            raise Unsupported("ok of " + rt)
        return "(okb_%s %s)" % (rt, hy)
    mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz)
    mr = re.fullmatch(r"List (.*)", rt)
    if mm and mr:
        he = "he%d" % depth
        return "(GenBridge.listT_ok %s (fun _ _ %s => %s))" % (hy, he, ok_proof(m, mm.group(2), mr.group(1), he,
                                                                                depth + 1))
    raise Unsupported("ok field")


def ok_def(m, n):
    facts = [f for f in (ok_fact(m, ssz, rt, "x.%s" % fn) for fn, ssz, rt in m.containers[n]) if f]
    return ("/-- The fields of a `%s` are in range, as its decoder checks. -/\n"
            "def ok_%s (x : %s) : Prop :=\n  %s\n" % (n, n, n, " ∧\n  ".join(facts + ["True"])))


def okb_theorem(m, n):
    fs = m.containers[n]
    K = len(fs)
    pat = ", ".join("y%d, ⟨w%d, hw%d, hy%d⟩" % (i, i, i, i) for i in range(K))
    prfs = [ok_proof(m, ssz, rt, "hy%d" % i) for i, (fn, ssz, rt) in enumerate(fs)
            if ok_fact(m, ssz, rt, "x.%s" % fn)]
    return ("theorem okb_%s {h : Heap} {v : Value} {x : %s} (hd : dec_%s h v = some x) : ok_%s x := by\n"
            "  simp only [dec_%s, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,\n"
            "    Option.some.injEq] at hd\n"
            "  obtain ⟨fs, hfs, %s, rfl⟩ := hd\n"
            "  unfold ok_%s\n"
            "  exact ⟨%s⟩\n" % (n, n, n, n, n, pat, n, ", ".join(prfs + ["trivial"])))


def bridge_theorem(m, n):
    fs = m.containers[n]
    K = len(fs)
    pat = ", ".join("y%d, ⟨w%d, hw%d, hy%d⟩" % (i, i, i, i) for i in range(K))
    cases = []
    for i, (fn, ssz, rt) in enumerate(fs):
        cases.append("  | %d, hw, hd =>\n    rw [hw%d] at hw; cases hw\n    simp only [kids_%s_%d, Option.some.injEq] at hd; subst hd\n"
                     "    exact %s" % (i, i, n, i, bridge_field(m, ssz, rt, "hy%d" % i)))
    return ("theorem bridge_%s {h : Heap} (hc : GenBridge.ContWF h) {v : Value} {x : %s}\n"
            "    (hd : dec_%s h v = some x) : GenBridge.DecTo h v (.cont %d (kids_%s x)) := by\n"
            "  simp only [dec_%s, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,\n"
            "    Option.some.injEq] at hd\n"
            "  obtain ⟨fs, hfs, %s, rfl⟩ := hd\n"
            "  obtain ⟨a, rfl, ho⟩ := GenBridge.fieldsT_some hfs\n"
            "  have hl : fs.length = %d := by\n"
            "    have := hc a %d fs _ ho (by first | (simp only [Validation.Tactic.lookup_lit]; done) |\n"
            "      (simp only [Validation.Tactic.lookup_lit]; rfl)); simpa using this\n"
            "  refine GenBridge.cont_of_fields ho (by rw [hl]; rfl) fun i w d hw hd => ?_\n"
            "  match i, hw, hd with\n%s\n"
            "  | _ + %d, _, hd =>\n"
            "    rw [List.getElem?_eq_none (by simp only [kids_%s_len]; omega)] at hd; cases hd\n"
            % (n, n, n, m.cid[n], n, n, pat, K, m.cid[n], "\n".join(cases), K, n))


def build_reps(m):
    """The containers whose fields all have a DV form, in dependency order."""
    m.reps, m.rep_order = {}, []
    m.bridged = set()
    m.okb = set()
    m.encdec = set()
    todo = dict(m.containers)
    while True:
        done = False
        for n, fs in list(todo.items()):
            deps = set(re.findall(r"\.container (\d+)", " ".join(f[1] for f in fs)))
            deps = {m.ids.get(int(d)) for d in deps}
            if any(d in todo and d != n for d in deps):
                continue
            if any(d not in m.reps and d not in todo for d in deps):
                del todo[n]
                done = True
                continue
            try:
                m.reps[n] = [rep_of(m, ssz, rt, "x.%s" % fn) for fn, ssz, rt in fs]
                m.rep_order.append(n)
            except Unsupported:
                pass
            del todo[n]
            done = True
        if not done:
            break


def fpat(m, cls, steps):
    """The `FPat` of a footprint pattern rooted at readable class `cls`, or None."""
    out, cur = [], ".container %d" % m.cid[cls]
    for st in steps:
        mc = re.fullmatch(r"\.container (\d+)", cur)
        ml = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", cur)
        if st == "*":
            if not ml:
                return None
            out.append(".any")
            cur = strip_parens(ml.group(2))
        else:
            if not mc:
                return None
            fs = m.containers.get(m.ids.get(int(mc.group(1))))
            if not fs:
                return None
            fi = [i for i, (fn, _, _) in enumerate(fs) if fn == st]
            if not fi:
                return None
            out.append(".exact %d" % fi[0])
            cur = strip_parens(fs[fi[0]][1])
    return "⟨%d, [%s]⟩" % (m.cid[cls], ", ".join(out))


def footprint(m, name, cls):
    """The footprint term of writer `name` from `Scope.fnFootprint`, else every path."""
    f = m.fns[name]
    pats = []
    params = m.sigs[name][0]
    for k, steps in m.fnfp.get(f["id"], []):
        if k >= len(params) or params[k][1] not in m.containers:
            return "fpAll %d" % m.cid[cls]
        p = fpat(m, params[k][1], steps)
        if p is None:
            return "fpAll %d" % m.cid[cls]
        if p not in pats:
            pats.append(p)
    return "[%s]" % ", ".join(pats) if pats else "fpAll %d" % m.cid[cls]


def writers(m):
    """The functions that return their updated container argument: name -> its class."""
    out = {}
    for n, (ps, rt) in m.sigs.items():
        if n in m.fns and rt in m.reps and [p for p in ps if p[1] == rt]:
            out[n] = rt
    return out


def variants(m, name):
    """The classes that a caller may pass to the width class parameters of `name`: each nominal
    class of the same width."""
    params, _ = m.sigs.get(name, ([], None))
    ws = {m.uint[t] for _, t in params if t in m.uint and t.startswith("Uint")}
    if len(ws) != 1:
        return []
    w = ws.pop()
    return [c for c in sorted(m.uint) if m.uint[c] == w and (m.uint_ty(c) or "").startswith("(.nominal")]


def top_items(text):
    """The top-level items of a Lean list literal `[a, b, ...]` (the text inside the brackets)."""
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch in "([":
            depth += 1
        if ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
            continue
        cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def body_text(m, name):
    s = m.scope
    i = s.index("def fn_%s : FunctionDef where" % name)
    i = s.index("  body := [", i) + len("  body := [")
    depth, j = 1, i
    while depth:
        depth += {"[": 1, "]": -1}.get(s[j], 0)
        j += 1
    return s[i:j - 1]


def last_list(item):
    """The text of the last `[...]` of an item: the body of a `for`."""
    j = item.rindex("]")
    depth, i = 0, j
    while True:
        depth += {"]": 1, "[": -1}.get(item[i], 0)
        if depth == 0:
            return item[i:j + 1]
        i -= 1


def loops(m, name, params, roots, rds):
    """The top-level `for` loops of `name`: one dict each, or Unsupported."""
    out = []
    items = top_items(body_text(m, name))
    f = m.fns[name]
    pids = f["params"]
    for idx, (it, st) in enumerate(zip(items, f["body"][1])):
        k, a = ctor(st)
        if k != "forStmt":
            continue
        tk, ta = ctor(a[1])
        if tk != "name":
            raise Unsupported("loop target")
        lv = ta[1][1]
        ik, ia = ctor(a[2])
        if ik == "name" and ia[1][1] in pids:
            # `for x in xs` over a list parameter.
            pk = pids.index(ia[1][1])
            mr = re.fullmatch(r"\(?List (\w+)\)?", params[pk][1])
            if not mr or mr.group(1) not in m.reps:
                raise Unsupported("loop over a list of flat values")
            out.append(dict(idx=idx, text=it, lv=lv, line=a[0][1], k=pk, path=[], body=last_list(it),
                            len="%s.length" % rds[pk], depth=depth(a[3])))
            continue
        if ik != "attr" or ctor(ia[1])[0] != "name":
            raise Unsupported("loop iterable")
        pv = ctor(ia[1])[1][1][1]
        fid = ia[2][1]
        if pv not in pids:
            raise Unsupported("loop over a local")
        pk = pids.index(pv)
        pt = params[pk][1]
        if pt not in m.containers:
            raise Unsupported("loop over a non-container")
        fn = m.ids[fid]
        fi = [i for i, (n2, _, _) in enumerate(m.containers[pt]) if n2 == fn]
        if not fi:
            raise Unsupported("loop field")
        fi = fi[0]
        ssz = strip_parens(m.containers[pt][fi][1])
        mm = re.fullmatch(r"\.list (\.\w+) (\(.*\)|\.\w+) (none|\(some \d+\))", ssz)
        if not mm or not mm.group(2).startswith("(.container"):
            raise Unsupported("loop over a list of flat values")
        out.append(dict(idx=idx, text=it, lv=lv, line=a[0][1], k=pk, path=[fi], body=last_list(it),
                        len="%s.%s.length" % (rds[pk], fn), depth=depth(a[3])))
    n = len(out)
    for j, lp in enumerate(out):
        lname = "%s.loop%d" % (name, j + 1)
        sig = re.search(r"^def %s ((?:\(\w+ : [^)]+\) )*): SpecM (.+?) :=" % re.escape(lname), m.rd, re.M)
        if not sig:
            raise Unsupported("loop signature")
        ps = re.findall(r"\((\w+) : ([^)]+)\)", sig.group(1))
        if sig.group(2).strip().startswith(("Option", "(")):
            raise Unsupported("loop result " + sig.group(2))
        names = [p for p, _ in ps]
        ni = names.index("i_")
        lp["pre"] = names[:ni - 1]
        lp["carried"] = [(p[:-3], t) for p, t in ps[ni + 1:]]
        if len(lp["carried"]) != 1 or not all(p.endswith("_in") for p, _ in ps[ni + 1:]):
            raise Unsupported("loop carries %d values" % len(lp["carried"]))
        if lp["carried"][0][1] not in m.uint:
            raise Unsupported("loop carries " + lp["carried"][0][1])
        lp["rt"] = sig.group(2).strip()
        lp["lname"] = lname
    return out


def loop_theorems(m, name, params, bs, roots, rds, xs, lps):
    """The induction lemma of each loop and its form for a `bind`."""
    out = []
    pids = m.fns[name]["params"]
    rdmap = {pn: rd for (pn, _), rd in zip(params, rds)}
    rs = "[%s]" % ", ".join(roots)
    hyps, hnames = [], []
    for (pn, pt), pid, r in zip(params, pids, roots):
        v = "(.val %s)" % r[len("(.leaf "):-1] if r.startswith("(.leaf ") else "(.place %d [])" % pids.index(pid)
        hyps.append("B %d = some %s" % (pid, v))
        hnames.append("hB%d" % pid)
    for j, lp in enumerate(lps):
        cname, ct = lp["carried"][0]
        cid = m.name_id[cname]
        ty = m.uint_ty(ct)
        C = lp["depth"] + 6
        LEN = lp["len"]
        car = "setLoc B %d (.val (.uint %s c))" % (cid, ty)
        last = "(.place %d [%s])" % (lp["k"], ", ".join([str(x) for x in lp["path"]] + ["%s - 1" % LEN]))
        fin = ("(if i < %s then setLoc (setLoc B %d %s) %d (.val (.uint %s r.val)) else setLoc B %d (.val (.uint %s r.val)))"
               % (LEN, lp["lv"], last, cid, ty, cid, ty))
        pre = " ".join(rdmap[p] for p in lp["pre"])
        loop1 = "%s %s %s i ⟨c⟩" % (lp["lname"], pre, LEN)
        ls = "⟨%d, [%s], false⟩" % (lp["k"], ", ".join(str(x) for x in lp["path"]))
        st = "(.name %d %d)" % (lp["line"], lp["lv"])
        nm = "%s_loop%d" % (name, j + 1)
        comm = "setLoc_comm_%s" % nm
        hy = " → ".join(hyps)
        out.append(
            "theorem %s (sha : Oracle) (L4n : Nat) (L4B : Name → Option DRes) (L4x : DRes) (L4a L4b : Nat) :\n"
            "    True := trivial\n" % comm if False else "")
        out.append(
            "theorem %s_swap (B : Name → Option DRes) (it v : DRes) :\n"
            "    setLoc (setLoc B %d v) %d it = setLoc (setLoc B %d it) %d v := by\n"
            "  funext y; simp only [setLoc]; split <;> split <;> simp_all\n" % (nm, cid, lp["lv"], lp["lv"], cid))
        out.append(
            "theorem %s (sha : Oracle) %s :\n"
            "    ∀ (k i n : Nat) (B : Name → Option DRes) (c : Nat), %s - i = k → k + %d ≤ n → %s →\n"
            "      Option.map (Except.mapError SpecError.fail)\n"
            "        ((den (Scope.env sha) fpsGen n).loop [] (DSt.mk %s (%s)) %s %s i\n"
            "          %s) =\n"
            "      some ((fun r : %s => (DOut.normal, DSt.mk %s %s)) <$> %s) := by\n"
            "  intro k\n"
            "  induction k with\n"
            "  | zero =>\n"
            "    intro i n B c hk hn %s\n"
            "    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩\n"
            "    have hi : ¬ i < %s := by omega\n"
            "    rw [s_loop, %s]\n"
            "    simp only [loopStep, dif_neg hi, if_neg hi]\n"
            "    l4_eval\n"
            "    simp (disch := omega) only [List.getElem?_eq_none, Option.map_none]\n"
            "    all_goals (try l4_eval)\n"
            "    all_goals l4_close\n"
            "  | succ k ih =>\n"
            "    intro i n B c hk hn %s\n"
            "    obtain ⟨n', rfl⟩ : ∃ n', n = n' + %d := ⟨n - %d, by omega⟩\n"
            "    rw [show n' + %d = (n' + %d) + 1 from rfl, s_loop, %s]\n"
            "    have hi : i < %s := by omega\n"
            "    simp only [loopStep, dif_pos hi, if_pos hi]\n"
            "    l4_eval [bindLoop, Sem.block, fpsGen, fpAll, List.getElem?_eq_getElem hi, hi, %s, %s_swap]\n"
            "    all_goals (try simp (disch := l4_disch) only [ih])\n"
            "    all_goals (try l4_eval)\n"
            "    all_goals (by_cases hlast : i + 1 < %s <;>\n"
            "      (try simp only [hlast, hi, ↓reduceIte, setLoc_same]))\n"
            "    all_goals (try rw [show %s - 1 = i by omega])\n"
            "    all_goals l4_close\n"
            % (nm, " ".join(bs), LEN, C, hy, rs, car, st, ls, lp["body"], lp["rt"], rs, fin, loop1,
               " ".join(hnames), LEN, lp["lname"], " ".join(hnames), C, C, C, C - 1, lp["lname"], LEN,
               ", ".join(hnames), nm, LEN, LEN))
        out.append(
            "@[l4_simp] theorem %s_call (sha : Oracle) %s (i n : Nat) (B : Name → Option DRes) (c : Nat)\n"
            "    (hn : %s - i + %d ≤ n) %s {γ : Type} (K : DOut × DSt → DM γ) :\n"
            "    Option.map (Except.mapError SpecError.fail)\n"
            "        (DM.bind ((den (Scope.env sha) fpsGen n).loop [] (DSt.mk %s (%s)) %s %s i\n"
            "          %s) K) =\n"
            "      callK (%s) fun r => Option.map (Except.mapError SpecError.fail) (K (DOut.normal, DSt.mk %s %s)) :=\n"
            "  bind_call (%s sha %s _ i n B c rfl hn %s) K\n"
            % (nm, " ".join(bs), LEN, C, " ".join("(%s : %s)" % (h, y) for h, y in zip(hnames, hyps)),
               rs, car, st, ls, lp["body"], loop1, rs, fin, nm, " ".join(xs), " ".join(hnames)))
    return "\n".join(x for x in out if x)


def whiles(m, name, params, roots, rds):
    """The top-level `while` loops of `name`: one dict each, or Unsupported. Each loop carries
    uint locals only, and its body reads only parameters and carried locals."""
    out = []
    items = top_items(body_text(m, name))
    f = m.fns[name]
    pids = f["params"]
    nfor = sum(1 for st in f["body"][1] if ctor(st)[0] == "forStmt")
    for idx, (it, st) in enumerate(zip(items, f["body"][1])):
        k, a = ctor(st)
        if k != "whileStmt":
            continue
        j = nfor + len(out) + 1
        lname = "%s.loop%d" % (name, j)
        sig = re.search(r"^def %s ((?:\(\w+ : [^)]+\) )*): SpecM (.+?) :=" % re.escape(lname), m.rd, re.M)
        msig = re.search(r"^def %s\.μ ((?:\(\w+ : [^)]+\) )*): Nat :=" % re.escape(lname), m.rd, re.M)
        if not sig or not msig:
            raise Unsupported("while signature")
        ps = re.findall(r"\((\w+) : ([^)]+)\)", sig.group(1))
        mps = re.findall(r"\((\w+) : ([^)]+)\)", msig.group(1))
        pre = [p for p, _ in ps if not p.endswith("_in")]
        car = [(p[:-3], t) for p, t in ps if p.endswith("_in")]
        if [p for p, _ in mps] != pre + [c for c, _ in car]:
            raise Unsupported("while measure arguments")
        if not car or any(t not in m.uint or not m.uint_ty(t) for _, t in car):
            raise Unsupported("while carries a non-uint")
        pnames = [p for p, _ in params]
        if any(p not in pnames for p in pre):
            raise Unsupported("while reads a local")
        rt = sig.group(2).strip()
        if rt.strip("()") != " × ".join(t for _, t in car):
            raise Unsupported("while result " + rt)
        cids = [m.name_id[c] for c, _ in car]
        a2 = split_args(it)
        cond, body = a2[2], a2[3]
        used = {int(x) for x in re.findall(r"\(\.name \d+ (\d+)\)", cond + body)}
        if not used <= set(pids) | set(cids) or "(.call " in cond + body:
            raise Unsupported("while body")
        out.append(dict(idx=idx, line=a[0][1] if isinstance(a[0], tuple) else a2[1], lname=lname,
                        pre=pre, car=car, cids=cids, rt=rt, cond=cond, body=body,
                        C=max(depth(a[1]), depth(a[2])) + 6))
    return out


def while_theorems(m, name, params, bs, roots, rds, xs, wls):
    """The measure induction lemma of each `while` loop and its form for a `bind`."""
    out = []
    pids = m.fns[name]["params"]
    rdmap = {pn: rd for (pn, _), rd in zip(params, rds)}
    rs = "[%s]" % ", ".join(roots)
    hyps, hnames = [], []
    for (pn, pt), pid, r in zip(params, pids, roots):
        v = "(.val %s)" % r[len("(.leaf "):-1] if r.startswith("(.leaf ") else "(.place %d [])" % pids.index(pid)
        hyps.append("B %d = some %s" % (pid, v))
        hnames.append("hB%d" % pid)
    for wl in wls:
        nm = "%s_while%s" % (name, wl["lname"].rsplit("loop", 1)[1])
        K = len(wl["car"])
        cs = ["c%d" % (i + 1) for i in range(K)]
        tys = [m.uint_ty(t) for _, t in wl["car"]]

        def chain(vals):
            t = "B"
            for cid, ty, v in zip(wl["cids"], tys, vals):
                t = "(setLoc %s %d (.val (.uint %s %s)))" % (t, cid, ty, v)
            return t

        def proj(i):
            return "r" + ".2" * i + (".1" if i < K - 1 else "")

        st0 = chain(cs)
        st1 = chain(["%s.val" % proj(i) for i in range(K)])
        pre = " ".join(rdmap[p] for p in wl["pre"])
        args = " ".join("⟨%s⟩" % c for c in cs)
        mu = "%s.μ %s %s" % (wl["lname"], pre, args)
        loop1 = "%s %s %s" % (wl["lname"], pre, args)
        C = wl["C"]
        swaps = []
        for i in range(K):
            for j in range(i + 1, K):
                sw = "%s_swap%d_%d" % (nm, i + 1, j + 1)
                swaps.append(sw)
                out.append(
                    "theorem %s (B : Name → Option DRes) (a b : DRes) :\n"
                    "    setLoc (setLoc B %d b) %d a = setLoc (setLoc B %d a) %d b := by\n"
                    "  funext y; simp only [setLoc]; split <;> split <;> simp_all\n"
                    % (sw, wl["cids"][j], wl["cids"][i], wl["cids"][i], wl["cids"][j]))
        side = "simp [%s.μ, uv, UintC.val] at hk hc ⊢; omega" % wl["lname"]
        hy = " → ".join(hyps)
        out.append(
            "theorem %s (sha : Oracle) %s :\n"
            "    ∀ (k nf : Nat) (B : Name → Option DRes) (%s : Nat), %s = k → k + %d ≤ nf → %s →\n"
            "      Option.map (Except.mapError SpecError.fail)\n"
            "        ((den (Scope.env sha) fpsGen nf).whl [] (DSt.mk %s %s) %s\n"
            "          %s) =\n"
            "      some ((fun r : %s => (DOut.normal, DSt.mk %s %s)) <$> %s) := by\n"
            "  intro k\n"
            "  induction k using Nat.strongRecOn with\n"
            "  | ind k ih =>\n"
            "  intro nf B %s hk hn %s\n"
            "  obtain ⟨n', rfl⟩ : ∃ n', nf = n' + %d := ⟨nf - %d, by omega⟩\n"
            "  rw [show n' + %d = (n' + %d) + 1 from rfl, den_whl]\n"
            "  unfold whileStep\n"
            "  rw [%s]\n"
            "  l4_eval [%s]\n"
            "  l4_bycases\n"
            "  · simp only [hc, ↓reduceIte, Bool.true_eq_false, decide_true, decide_false]\n"
            "    rw [dif_pos ?hμ, ih _ ?hlt _ B %s rfl ?hf %s]\n"
            "    case hμ => %s\n"
            "    case hlt => %s\n"
            "    case hf => %s\n"
            "  · simp only [Bool.not_eq_true] at hc\n"
            "    simp only [hc, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false]\n"
            % (nm, " ".join(bs), " ".join(cs), mu, C, hy, rs, st0, wl["cond"], wl["body"], wl["rt"], rs, st1, loop1,
               " ".join(cs), " ".join(hnames), C, C, C, C - 1, wl["lname"],
               ", ".join(hnames + swaps + ["Sem.block", "blockOf", "setLoc_same"]),
               " ".join("_" for _ in cs), " ".join(hnames), side, side, side))
        out.append(
            "@[l4_simp] theorem %s_call (sha : Oracle) %s (nf : Nat) (B : Name → Option DRes) (%s : Nat)\n"
            "    (hk : %s ≤ bigFuel) (hn : bigFuel + %d ≤ nf) %s {γ : Type} (K : DOut × DSt → DM γ) :\n"
            "    Option.map (Except.mapError SpecError.fail)\n"
            "        (DM.bind ((den (Scope.env sha) fpsGen nf).whl [] (DSt.mk %s %s) %s\n"
            "          %s) K) =\n"
            "      callK (%s) fun r => Option.map (Except.mapError SpecError.fail) (K (DOut.normal, DSt.mk %s %s)) :=\n"
            "  bind_call (%s sha %s _ nf B %s rfl (by omega) %s) K\n"
            % (nm, " ".join(bs), " ".join(cs), mu, C, " ".join("(%s : %s)" % (h, y) for h, y in zip(hnames, hyps)),
               rs, st0, wl["cond"], wl["body"], loop1, rs, st1, nm, " ".join(xs), " ".join(cs), " ".join(hnames)))
    return "\n".join(out)


def split_args(t):
    """The space-separated arguments of a parenthesized application `(.f a b c)`."""
    t = t.strip()[1:-1]
    out, depth, cur = [], 0, ""
    for ch in t:
        if ch in "([":
            depth += 1
        if ch in ")]":
            depth -= 1
        if ch == " " and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
            continue
        cur += ch
    if cur:
        out.append(cur)
    return out


def paren_at(t, i):
    """The parenthesized term that starts at `t[i] == '('`."""
    depth = 0
    for j in range(i, len(t)):
        depth += {"(": 1, ")": -1}.get(t[j], 0)
        if depth == 0:
            return t[i:j + 1]
    raise ValueError


def f_body_items(m, name):
    return top_items(body_text(m, name))


def comps(m, name, params, roots, rds):
    """The list comprehension of `name` (at most one), as a dict, or Unsupported."""
    bt = body_text(m, name)
    if bt.count("(.comp ") == 0:
        return []
    if bt.count("(.comp ") > 1:
        raise Unsupported("two comprehensions")
    c = paren_at(bt, bt.index("(.comp "))
    a = split_args(c)
    if len(a) != 5 or a[2] != ".list":
        raise Unsupported("comprehension kind")
    elt = a[3]
    gens = a[4].strip()[1:-1].strip()
    g = split_args(gens)
    if g[0] != ".mk":
        raise Unsupported("comprehension generator")
    tgt, it, ifs = g[1], g[2], g[3]
    pnames = [p for p, _ in params]
    pids = m.fns[name]["params"]
    mm = re.fullmatch(r"\(\.call \d+ \(\.name \d+ (\d+)\) \[\(\.pos \(\.attr \d+ \(\.name \d+ (\d+)\) (\d+)\)\)\]\)", it)
    mp = re.fullmatch(r"\(\.call \d+ \(\.name \d+ (\d+)\) \[\(\.pos \(\.name \d+ (\d+)\)\)\]\)", it)
    enum = True
    mn = re.fullmatch(r"\(\.name \d+ (\d+)\)", it)
    if mn and int(mn.group(1)) in pids:
        # `for x in xs` of a list parameter.
        pk = pids.index(int(mn.group(1)))
        if not re.fullmatch(r"\(?List (\w+)\)?", params[pk][1]):
            raise Unsupported("comprehension iterable")
        path, LEN, enum = [], "%s.length" % rds[pk], False
    elif mp and m.ids.get(int(mp.group(1))) == "enumerate" and int(mp.group(2)) in pids:
        # `enumerate(xs)` of a list parameter.
        pk = pids.index(int(mp.group(2)))
        if not re.fullmatch(r"\(?List (\w+)\)?", params[pk][1]):
            raise Unsupported("comprehension iterable")
        path, LEN = [], "%s.length" % rds[pk]
    else:
        if not mm:
            raise Unsupported("comprehension iterable")
        if m.ids.get(int(mm.group(1))) != "enumerate":
            raise Unsupported("comprehension over a call")
        pv, fid = int(mm.group(2)), int(mm.group(3))
        if pv not in pids:
            raise Unsupported("comprehension over a local")
        pk = pids.index(pv)
        pt = params[pk][1]
        fn = m.ids[fid]
        fi = [i for i, (n2, _, _) in enumerate(m.containers.get(pt, [])) if n2 == fn]
        if not fi:
            raise Unsupported("comprehension field")
        path, LEN = [fi[0]], "%s.%s.length" % (rds[pk], fn)
    rd = m.bodies[name]
    kind = "filterMapM"
    j = rd.find(".filterMapM fun")
    if j < 0:
        kind = "mapM"
        j = rd.find(".mapM fun")
    if j < 0:
        raise Unsupported("readable comprehension")
    # X: the parenthesized list before `.filterMapM`; F: the function after it.
    depth, i = 0, j - 1
    while True:
        depth += {")": 1, "(": -1}.get(rd[i], 0)
        if depth == 0:
            break
        i -= 1
    X = rd[i:j]
    k = j + len(".%s " % kind)
    depth, e = 0, k
    while e < len(rd):
        if rd[e] == "(":
            depth += 1
        elif rd[e] == ")":
            if depth == 0:
                break
            depth -= 1
        e += 1
    F = rd[k:e].strip()
    sub = {pn: rds[pnames.index(pn)] for pn in pnames}
    rep = lambda t: re.sub(r"\b(%s)\b" % "|".join(map(re.escape, pnames)),
                           lambda mm2: "(%s)" % sub[mm2.group(1)], t)
    rt = m.sigs[name][1]
    ms = re.search(r"sumU \(⟨0⟩ : (\w+)\) \(← \(", rd)
    if ms:
        rt = "List " + ms.group(1)
    mr = re.fullmatch(r"\(?List (\w+)\)?", rt)
    if not mr or mr.group(1) not in m.uint:
        raise Unsupported("comprehension result " + rt)
    # Locals that the comprehension reads: each assigned once before it, from a call.
    tnames = {int(t) for t in re.findall(r"\(\.name \d+ (\d+)\)", tgt)}
    used = {int(g) for g in re.findall(r"\(\.name \d+ (\d+)\)", ifs + elt)}
    locs = []
    for st in f_body_items(m, name):
        mm2 = re.match(r"\(\.assign \d+ \[\(\.name \d+ (\d+)\)\]", st)
        if mm2 and int(mm2.group(1)) in used and int(mm2.group(1)) not in tnames:
            lid = int(mm2.group(1))
            ln = m.ids[lid]
            mm3 = re.search(r"let %s := \(← (\w+) " % re.escape(ln), rd)
            if not mm3 or mm3.group(1) not in m.sigs or m.sigs[mm3.group(1)][1] not in m.uint:
                raise Unsupported("comprehension reads local " + ln)
            lt = m.sigs[mm3.group(1)][1]
            locs.append((lid, ln, lt))
    for g in used:
        if g in pids or g in tnames or g in [l[0] for l in locs]:
            continue
        if m.glob_kind(g)[0] == "other":
            raise Unsupported("comprehension reads an unknown name")
    F = rep(F)
    lsub = {ln: "(⟨lv_%s⟩ : %s)" % (ln, lt) for _, ln, lt in locs}
    if lsub:
        F = re.sub(r"\b(%s)\b" % "|".join(map(re.escape, lsub)), lambda mm4: lsub[mm4.group(1)], F)
    enc = "(DV.leaf (.uint %s y.val))" % m.uint_ty(mr.group(1))
    return [dict(tgt=tgt, ifs=ifs, elt=elt, k=pk, path=path, X=rep(X), F=F, enc=enc, et=mr.group(1), locs=locs,
                 len=LEN, depth=depth_text(c), enum=enum, kind=kind)]


def depth_text(t):
    d, best = 0, 0
    for ch in t:
        if ch == "(":
            d += 1
            best = max(best, d)
        elif ch == ")":
            d -= 1
    return best


def comp_theorems(m, name, params, bs, roots, rds, xs, cps):
    out = []
    pids = m.fns[name]["params"]
    rs = "[%s]" % ", ".join(roots)
    hyps, hnames = [], []
    for (pn, pt), pid, r in zip(params, pids, roots):
        v = "(.val %s)" % r[len("(.leaf "):-1] if r.startswith("(.leaf ") else "(.place %d [])" % pids.index(pid)
        hyps.append("B %d = some %s" % (pid, v))
        hnames.append("hB%d" % pid)
    for cp in cps:
        gl = sorted({int(g) for g in re.findall(r"\(\.name \d+ (\d+)\)", cp["ifs"] + cp["elt"])
                     if int(g) not in pids and m.glob_kind(int(g))[0] != "other"})
        hyps2 = hyps + ["B %d = none" % g for g in gl]
        hnames2 = hnames + ["hG%d" % g for g in gl]
        hyps, hnames = hyps2, hnames2
        nm = "%s_items" % name
        loc = "B"
        lbs = ""
        lxs = ""
        for lid, ln, lt in cp["locs"]:
            loc = "(setLoc %s %d (.val (.uint %s lv_%s)))" % (loc, lid, m.uint_ty(lt), ln)
            lbs += " (lv_%s : Nat)" % ln
            lxs += " lv_%s" % ln
        C = cp["depth"] + 6
        LEN = cp["len"]
        ls = "⟨%d, [%s], %s⟩" % (cp["k"], ", ".join(str(x) for x in cp["path"]), "true" if cp["enum"] else "false")
        swaps = []
        tids = [int(t) for t in re.findall(r"\(\.name \d+ (\d+)\)", cp["tgt"])]
        for lid, ln, lt in cp["locs"]:
            for t in tids:
                sw = "%s_swap_%d_%d" % (nm, lid, t)
                swaps.append(sw)
                out.append(
                    "theorem %s (L : Name → Option DRes) (a b : DRes) :\n"
                    "    setLoc (setLoc L %d a) %d b = setLoc (setLoc L %d b) %d a := by\n"
                    "  funext y; simp only [setLoc]; split <;> split <;> simp_all\n" % (sw, lid, t, t, lid))
        X = cp["X"]
        lhs = ("Option.map (Except.mapError SpecError.fail)\n"
               "        (DM.bind ((den (Scope.env sha) fpsGen n).items [] (DSt.mk %s %s) %s %s\n          %s %s i) K)"
               % (rs, loc, cp["tgt"], cp["ifs"], cp["elt"], ls))
        rhs = ("callK ((%s).drop i |>.%s %s)\n"
               "        fun ys => Option.map (Except.mapError SpecError.fail) (K (ys.map fun y => %s))"
               % (X, cp["kind"], cp["F"], cp["enc"]))
        out.append(
            "theorem %s (sha : Oracle) %s%s :\n"
            "    ∀ (k i n : Nat) (B : Name → Option DRes), %s - i = k → k + %d ≤ n → %s →\n"
            "      ∀ {γ : Type} (K : List DV → DM γ),\n"
            "      %s =\n      %s := by\n"
            "  intro k\n"
            "  induction k with\n"
            "  | zero =>\n"
            "    intro i n B hk hn %s γ K\n"
            "    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩\n"
            "    have hi : ¬ i < %s := by omega\n"
            "    rw [s_items]\n"
            "    simp only [itemsStep]\n"
            "    l4_eval\n"
            "    simp (disch := first | omega | (simp only [List.length_map, List.length_zipIdx]; omega)) only\n"
            "      [List.getElem?_eq_none, List.drop_eq_nil_of_le, Option.map_none, List.filterMapM_nil, List.mapM_nil]\n"
            "    all_goals (try l4_eval [List.map_nil])\n"
            "    all_goals l4_close\n"
            "  | succ k ih =>\n"
            "    intro i n B hk hn %s γ K\n"
            "    obtain ⟨n', rfl⟩ : ∃ n', n = n' + %d := ⟨n - %d, by omega⟩\n"
            "    rw [show n' + %d = (n' + %d) + 1 from rfl, s_items]\n"
            "    have hi : i < %s := by omega\n"
            "    rw [List.drop_eq_getElem_cons (by first | omega | (simp only [List.length_map, List.length_zipIdx]; omega))]\n"
            "    simp only [itemsStep]\n"
            "    l4_eval [bindLoop, ifsOf, fpsGen, fpAll, List.getElem?_eq_getElem hi, hi, %s%s, List.getElem_map,\n"
            "      List.getElem_zipIdx, List.filterMapM_cons, List.mapM_cons, List.map_cons, List.cons_append, List.nil_append]\n"
            "    all_goals (repeat (first | (simp (disch := l4_disch) only [ih]) |\n"
            "      ((l4_bycases <;> (try l4_eval_star))) |\n"
            "      ((refine callK_congr _ fun _ => ?_) <;> (try l4_eval_star)) |\n"
            "      ((split <;> (try l4_eval_star) <;> (try subst_vars) <;> (try l4_eval_star)))))\n"
            "    all_goals (try l4_eval [List.map_cons, List.cons_append, List.nil_append])\n"
            "    all_goals l4_close\n"
            % (nm, " ".join(bs), lbs, LEN, C, " → ".join(hyps), lhs, rhs, " ".join(hnames), LEN,
               " ".join(hnames), C, C, C, C - 1, LEN, ", ".join(hnames), "".join(", " + w for w in swaps)))
        out.append(
            "@[l4_simp] theorem %s_call (sha : Oracle) %s%s (i n : Nat) (B : Name → Option DRes)\n"
            "    (hn : %s - i + %d ≤ n) %s {γ : Type} (K : List DV → DM γ) :\n"
            "    %s =\n    %s :=\n"
            "  %s sha %s%s _ i n B rfl hn %s K\n"
            % (nm, " ".join(bs), lbs, LEN, C, " ".join("(%s : %s)" % (h, y) for h, y in zip(hnames, hyps)),
               lhs, rhs, nm, " ".join(xs), lxs, " ".join(hnames)))
    return "\n".join(out)


CLOSE = "l4_dbg" if os.environ.get("L4_DBG") else "l4_close"

_CF = {}


def classes_file_cache(m):
    if "t" not in _CF:
        _CF["t"] = classes_file(m)
    return _CF["t"]


LENS_OF = {}   # function -> [(parameter position, field)]: the list lengths its fuel grows with


def callee_lens(m, name, params):
    """The lengths that the fuel of `name` needs for its callees, as (position, field) of its own
    parameters. A callee argument must be a parameter of `name`."""
    out = []
    body = m.bodies.get(name, "")
    pnames = [p for p, _ in params]
    for c in m.callees(name):
        if not LENS_OF.get(c):
            continue
        cps = [p for p, _ in m.sigs[c][0]]
        nw = len([1 for pos, _ in LENS_OF[c] if pos == "W"])
        for j in range(nw):
            if ("W", j) not in out and ("W", None if j == 0 else j) not in out:
                out.append(("W", j))
        for mm in re.finditer(r"\b%s((?:\s+\(?\w+\)?)+)" % re.escape(c), body):
            args = [a.strip("()") for a in mm.group(1).split()]
            for pos, fld in LENS_OF[c]:
                if pos == "W":
                    continue
                if pos >= len(args) or args[pos] not in pnames:
                    raise Unsupported("callee fuel through a local")
                item = (pnames.index(args[pos]), fld)
                if item not in out:
                    out.append(item)
    return out


HTR = {}
# Callees taken from a statement of the tactic (`ExtOK`): the class of the argument, the fuel
# bound of the statement on the readable argument `x`, the lengths it grows with, its constant.
OPAQUE = {}
COND = {}   # unproved callee -> (its call statement as a hypothesis, its fuel)
NONE_OK = set()
RNG = set()


def rng_theorem(m, name):
    """`<f>_rng`: the bytes of an ok result have the length of the result class, or None."""
    params, rt = m.sigs[name]
    if rt not in m.bytes:
        return None
    body = m.bodies.get(name, "")
    callees = [c for c in m.callees(name) if c in RNG]
    binders = " ".join("(%s : %s)" % (pn, paren(pt)) for pn, pt in params)
    binders += "".join(" (hok_%s : ok_%s %s)" % (pn, pt, pn) for pn, pt in params if pt in m.reps)
    args = " ".join(pn for pn, _ in params)
    okdefs = ", ".join("ok_" + n for n in m.rep_order)
    closers = ["(have := bytesOf_ok_len' ‹bytesOf _ _ = _›; simpa only [l4_simp] using this)"]
    closers += ["(apply %s_rng <;> assumption)" % c for c in callees]
    closers += ["(have hm := lget_mem ‹lget _ _ = _›; simp only [%s] at *; simp_all)" % okdefs]
    return ("theorem %s_rng %s (x : %s) (h : %s %s = .ok x) : x.data.length = %d := by\n"
            "  unfold %s at h\n"
            "  simp only [bind, Except.bind, pure, Except.pure] at h\n"
            "  repeat' split at h\n"
            "  all_goals (try (cases h; done))\n"
            "  all_goals (try (simp only [Except.ok.injEq] at h; subst h))\n"
            "  all_goals first | %s\n"
            % (name, binders, rt, name, args, m.bytes[rt], name, " | ".join(closers)))


BLS = {}


def uses_bls(m, name):
    """`name` or a callee calls the BLS oracle."""
    if name not in BLS:
        BLS[name] = False
        body = m.bodies.get(name, "")
        BLS[name] = "Spec.bls" in body or any(uses_bls(m, c) for c in m.callees(name))
    return BLS[name]


SHA = {}


def uses_sha(m, name):
    """`name` or a callee calls `sha256`."""
    if name not in SHA:
        SHA[name] = False
        SHA[name] = "Spec.sha256" in m.bodies.get(name, "") or any(uses_sha(m, c) for c in m.callees(name))
    return SHA[name]


def oracle_args(m, c):
    """The oracle hypotheses that the call lemmas of `c` take after `sha`."""
    return " ".join(["sha"] + (["ho"] if uses_htr(m, c) else []) + (["hbl"] if uses_bls(m, c) else []))


def needs_oracle(m, c):
    return uses_htr(m, c) or uses_bls(m, c)


def uses_htr(m, name):
    """`name` or a callee hashes an object with the oracle."""
    if name not in HTR:
        HTR[name] = False
        body = m.bodies.get(name, "")
        HTR[name] = bool(re.search(r"\bhtr(Obj)? |Spec\.sha256", body)) or any(uses_htr(m, c) for c in m.callees(name))
    return HTR[name]


def hok_binder(m, pn, pt):
    """The range hypothesis of parameter `pn : pt` in `ok` mode, or None."""
    mo = re.fullmatch(r"\(?Option (\w+)\)?", pt)
    if mo:
        pt = mo.group(1)
    if pt in m.reps:
        return "(hok_%s : ok_%s a_%s)" % (pn, pt, pn)
    if pt in m.uint:
        return "(hok_%s : a_%s < 2 ^ %d)" % (pn, pn, m.uint[pt])
    if pt in m.bytes:
        return "(hok_%s : a_%s.length = %d)" % (pn, pn, m.bytes[pt])
    mr = re.fullmatch(r"\(?List (\w+)\)?", pt)
    if mr and elem_ssz(m, mr.group(1)):
        f = ok_fact(m, elem_ssz(m, mr.group(1)), mr.group(1), "y")
        if f:
            return "(hok_%s : ∀ y ∈ a_%s, %s)" % (pn, pn, f)
    return None


def ext_closure(m, name, seen=None):
    """The callees taken from statements that a call of `name` reaches, through callees with a
    den theorem."""
    seen = set() if seen is None else seen
    out = set()
    for c in m.callees(name):
        if c in OPAQUE:
            out.add(c)
        elif c not in seen:
            seen.add(c)
            out |= ext_closure(m, c, seen)
    return out


def hs_binders(m, name):
    """The membership hypotheses of the callees taken from statements that `name` reaches."""
    return "".join(" (hS_%s : (%d : Name) ∈ ExtSet.S := by assumption)" % (c, m.fns[c]["id"])
                   for c in sorted(ext_closure(m, name)))


def add_hs(m, name, text):
    """Each theorem of `name` takes the membership hypotheses, after its other binders."""
    hs = hs_binders(m, name)
    if not hs:
        return text
    out, i = [], 0
    for mm in re.finditer(r"^theorem ", text, re.M):
        j = text.find(" :\n", mm.start())
        k = text.find(":=", mm.start())
        if j < 0 or (0 <= k < j):
            continue
        out.append(text[i:j] + hs)
        i = j
    out.append(text[i:])
    return "".join(out)


def candidate(m, name, proved, sub=None, isub=False, ok=False, nonep=False):
    if name in m.generic and not getattr(m, "_inst", False):
        t, d = candidate_generic(m, name, proved, ok)
    else:
        t, d = candidate1(m, name, proved, sub, isub, ok, nonep)
    return add_hs(m, name, t), d


def candidate_generic(m, name, proved, ok):
    """A function generic over a uint class: the theorems of each class, with the class in the
    theorem names and given to the readable function."""
    sig = m.sigs[name]
    texts, D = [], 0
    try:
        m._inst = True
        for C in sorted(m.uint):
            if not m.uint_ty(C):
                continue
            m.sigs[name] = ([(pn, C if pt == "β" else pt) for pn, pt in sig[0]], sig[1])
            try:
                t, d = candidate1(m, name, proved, ok=ok)
            except Unsupported:
                continue
            t = re.sub(r"\b%s_(den|call|fcall|l4|l4r)\b" % name, lambda mm: "%s_%s_%s" % (name, mm.group(1), C), t)
            t = re.sub(r"\b%s (⟨)" % name, lambda mm: "%s (β := %s) %s" % (name, C, mm.group(1)), t)
            texts.append(t)
            D = max(D, d)
    finally:
        m._inst = False
        m.sigs[name] = sig
    if not texts:
        raise Unsupported("generic " + name)
    return "\n".join(texts), D


def candidate1(m, name, proved, sub=None, isub=False, ok=False, nonep=False):
    """The theorems of `name` (its `_den` and `_call`) and its fuel, or Unsupported. `proved` maps
    each proved function to its fuel."""
    if name not in m.sigs:
        raise Unsupported("signature")
    params, rt = m.sigs[name]
    f = m.fns[name]
    if len(params) != len(f["params"]):
        raise Unsupported("params")
    if f["vararg"] != "none":
        raise Unsupported("defaults")
    for c in m.callees(name):
        if c not in proved and c not in COND and c not in OPAQUE:
            raise Unsupported("callee " + c)
    proved = dict(proved)
    for c in m.callees(name):
        if c in OPAQUE and c not in proved:
            proved[c] = OPAQUE[c]["D"]
            LENS_OF[c] = OPAQUE[c]["lens"]
    for c in m.callees(name):
        if c not in proved:
            proved[c] = COND[c][1]
    bs, roots, rds, xs = [], [], [], []
    hoks = []
    objs = []
    for i, (pn, pt) in enumerate(params):
        if pt == "SszObj":
            # Any SSZ object: its tree, and an encoder that decodes to it.
            bs.append("(a_%s : SszObj) (t_%s : Name) (ds_%s : List DV) "
                      "(he_%s : GenBridge.EncDec a_%s.enc (.cont t_%s ds_%s))" % ((pn,) * 7))
            roots.append("(.cont t_%s ds_%s)" % (pn, pn))
            rds.append("a_%s" % pn)
            xs.extend(["a_" + pn, "t_" + pn, "ds_" + pn, "he_" + pn])
            objs.append(pn)
            continue
        if nonep and re.fullmatch(r"\(?Option (\w+)\)?", pt):
            # The caller leaves the argument out: `None`.
            roots.append("(.leaf .none)")
            rds.append("none")
            continue
        b, r, a = param(m, i, pn, pt, sub, isub)
        bs.append(b)
        roots.append(r)
        rds.append(a)
        xs.append("a_" + pn)
        hb = hok_binder(m, pn, pt) if ok and not sub else None
        if hb:
            bs.append(hb)
            xs.append("hok_" + pn)
            if "ok_" in hb.split(":", 1)[1]:
                hoks.append("hok_" + pn)
    w = writers(m).get(name)
    if w:
        ks = [i for i, (_, pt) in enumerate(params) if pt == w]
        if len(ks) != 1:
            raise Unsupported("two arguments of the returned class")
        rroots = list(roots)
        rroots[ks[0]] = "(.cont %d (kids_%s x))" % (m.cid[w], w)
        enc = "DRes.val .none"
        rs_out = "[%s]" % ", ".join(rroots)
    else:
        enc = result(m, rt, sub)
        rs_out = None
    lps = loops(m, name, params, roots, rds) if not sub else []
    cps = comps(m, name, params, roots, rds) if not sub else []
    wls = whiles(m, name, params, roots, rds) if not sub else []
    if uses_bls(m, name):
        bs.insert(0, "(hbl : Validation.BlsBridge.OracleBls sha)")
        xs.insert(0, "hbl")
    if uses_htr(m, name):
        bs.insert(0, "(ho : Validation.HtrBridge.OracleHtr sha)")
        xs.insert(0, "ho")
    if sub and any(ctor(st)[0] in ("forStmt", "whileStmt") for st in f["body"][1]):
        raise Unsupported("variant with a loop")
    tag = ("_" + sub if sub else "") + ("_i" if isub else "") + ("_none" if nonep else "")
    D = depth(f["body"]) + 4 + max([proved[c] + 2 for c in m.callees(name)] + [0])
    items = [(lp["k"], lp["path"] and lp["len"].split(".")[-2] or None) for lp in lps + cps]
    if wls:
        items.append(("W", None))
    for it in callee_lens(m, name, params):
        if it not in items:
            items.append(it)
    LENS = "".join("bigFuel + " if k == "W" else
                   ("%s.%s.length + " % (rds[k], fld.split("*")[0])) * int(fld.split("*")[1]) if fld and "*" in fld else
                   ("%s.%s.length + " % (rds[k], fld)) if fld else ("%s.length + " % rds[k])
                   for k, fld in items)
    fcalls = ["%s_fcall" % c for c in m.callees(name) if LENS_OF.get(c) and not needs_oracle(m, c)
              and c not in COND and c not in OPAQUE]
    hyps = []
    for c in m.callees(name):
        if c in COND:
            # An unproved callee: its call statement is a hypothesis.
            hyps.append("(%s_fcall : CallHyp (%s))" % (c, COND[c][0]))
            fcalls.append(" ".join(["%s_fcall.out" % c] + oracle_args(m, c).split()[1:]))
    bs = bs + hyps
    xs = xs + [h[1:h.index(" :")] for h in hyps]
    for c in m.callees(name):
        if not needs_oracle(m, c) or c in COND or c in OPAQUE:
            continue
        oa = oracle_args(m, c)
        objcls = re.findall(r"\b%s \(⟨enc_(\w+)" % re.escape(c), m.bodies.get(name, ""))
        if objcls:
            fcalls += ["%s_fcall_%s %s" % (c, X, oa) for X in sorted(set(objcls))]
        else:
            fcalls += ["%s_fcall %s" % (c, oa)]
            if c in NONE_OK:
                fcalls += ["%s_fcall_none %s" % (c, oa)]
    if lps or cps:
        D += 6
    if wls:
        D += max(wl["C"] for wl in wls) + 2
    rs = "[%s]" % ", ".join(roots)
    rs_out = rs_out or rs
    fp = "(fpsGen %d)" % f["id"] if w else "[]"
    unf = ["Scope.fn_" + name, name, "fpsGen", "fpAll"] + m.consts_of(name)
    if uses_htr(m, name):
        unf += ["htr_call_%s ho" % c for c in sorted(set(re.findall(r"\bhtr enc_(\w+)", m.bodies.get(name, ""))))]
        unf += ["GenBridge.callK_htr_root ho", "GenBridge.callK_htr_len ho"]
        unf += ["GenBridge.htr_obj_call ho a_%s he_%s" % (pn, pn) for pn in objs]
        unf += ["GenBridge.callK_htrObj_len ho" for _ in objs[:1]]
        unf += ["ho", "ho.sha256"]
    if uses_bls(m, name):
        unf += ["hbv"]
    for c in m.callees(name):
        if c in OPAQUE:
            unf += ["GenBridge.dbind_assoc", "GenBridge.extRes_call", "ext_" + c, "hS_" + c]
            for a in re.findall(r"\b%s (\w+)\b" % re.escape(c), m.bodies.get(name, "")):
                if ("hok_" + a) in xs and OPAQUE[c]["cls"]:
                    unf.append("undv_kids_%s a_%s hok_%s" % (OPAQUE[c]["cls"], a, a))
    if rt in m.reps and ("theorem kids_%s_mk" % rt) in classes_file_cache(m):
        unf.append("kids_%s_mk" % rt)
    loopstep = ""
    if lps or fcalls or cps or wls or any(c in RNG for c in m.callees(name)):
        disch = "l4_disch"
        if wls:
            disch = "first | l4_disch | " + " | ".join(
                "(simp [%s.μ, uv, UintC.val, bigFuel_eq]; omega)" % wl["lname"] for wl in wls)
        rngs = ["%s_rng" % c for c in m.callees(name) if c in RNG]
        if rngs:
            disch = "first | l4_disch | " + " | ".join("(apply %s <;> assumption)" % r for r in rngs)
        haves = ""
        for c in m.callees(name):
            if c in RNG:
                hk = "".join(" (hok_%s := by assumption)" % pn for pn, pt in m.sigs[c][0] if pt in m.reps)
                haves += " <;> (try have := %s_rng (h := hy)%s)" % (c, hk)
        loopstep = ("  all_goals (repeat (first | (simp (disch := %s) only [%s]) |\n"
                    "    ((l4_bycases <;> (try l4_eval_star))) |\n"
                    "    ((refine callK_congr' _ fun _ hy => ?_)%s <;> (try l4_eval_star))))\n  all_goals (try l4_eval)\n"
                    % (disch, ", ".join(["%s_loop%d_call" % (name, j + 1) for j in range(len(lps))] +
                                ["%s_while%s_call" % (name, wl["lname"].rsplit("loop", 1)[1]) for wl in wls] + fcalls +
                                ["%s_items_call" % name for _ in cps]), haves))
    thm = ("theorem %s_den%s (sha : Oracle) (m : Nat) %s :\n"
           "    ((den (Scope.env sha) fpsGen (%sm + %d)).fn %s Scope.fn_%s %s).map (Except.mapError SpecError.fail) =\n"
           "      some ((fun x : %s => (%s, %s)) <$> %s %s) := by\n"
           "  rw [s_fn]\n"
           "%s%s"
           "  l4_eval [%s]\n"
           "%s%s"
           % (name, tag, " ".join(bs), LENS, D, fp, name, rs, rt, enc, rs_out, name, " ".join(rds),
              ("".join("  have %s' := %s\n" % (h, h) for h in hoks) +
               "  simp only [%s] at %s\n" % (", ".join("ok_" + n for n in m.rep_order), " ".join(h + "'" for h in hoks)))
              if hoks else "", ("  have hbv := hbl.verify\n  simp only [Scope.Id.«Verify»] at hbv\n" if uses_bls(m, name) else "") +
              ("  have hsl := ho.sha256_len\n" if uses_sha(m, name) else ""), ", ".join(unf), loopstep,
              "" if os.environ.get("L4_NOCLOSE") else
              "  all_goals l4_dbg\n" if os.environ.get("L4_DBG") else "  all_goals l4_close\n"))
    call = ("@[l4_simp] theorem %s_call%s (sha : Oracle) (m : Nat) %s {γ : Type} (k : DRes × List DV → DM γ) :\n"
            "    Option.map (Except.mapError SpecError.fail)\n"
            "        (DM.bind ((den (Scope.env sha) fpsGen (%sm + %d)).fn %s Scope.fn_%s %s) k) =\n"
            "      callK (%s %s) fun x => Option.map (Except.mapError SpecError.fail) (k (%s, %s)) :=\n"
            "  bind_call (%s_den%s sha m %s) k\n"
            % (name, tag, " ".join(bs), LENS, D, fp, name, rs, name, " ".join(rds), enc, rs_out, name, tag, " ".join(xs)))
    if LENS or needs_oracle(m, name):
        call = call.replace("@[l4_simp] theorem", "theorem")
        call += ("\ntheorem %s_fcall%s (sha : Oracle) %s (n : Nat) (hn : %s%d ≤ n) {γ : Type}\n"
                 "    (k : DRes × List DV → DM γ) :\n"
                 "    Option.map (Except.mapError SpecError.fail)\n"
                 "        (DM.bind ((den (Scope.env sha) fpsGen n).fn %s Scope.fn_%s %s) k) =\n"
                 "      callK (%s %s) fun x => Option.map (Except.mapError SpecError.fail) (k (%s, %s)) := by\n"
                 "  obtain ⟨m, rfl⟩ : ∃ m, n = %sm + %d := ⟨n - (%s%d), by omega⟩\n"
                 "  exact %s_call%s sha m %s k\n"
                 % (name, tag, " ".join(bs), LENS, D, fp, name, rs, name, " ".join(rds), enc, rs_out,
                    LENS, D, LENS, D, name, tag, " ".join(xs)))
    if objs and len(objs) == 1 and (LENS or needs_oracle(m, name)):
        # The call with an object of each class: its encoder decodes to its tree.
        pn = objs[0]
        for X in sorted(m.encdec):
            bsX = [b for b in bs if not b.startswith("(a_%s : SszObj)" % pn)]
            xsX = []
            for x in xs:
                xsX.append({"a_" + pn: "(⟨enc_%s x_%s⟩ : SszObj)" % (X, pn), "t_" + pn: str(m.cid[X]),
                            "ds_" + pn: "(kids_%s x_%s)" % (X, pn), "he_" + pn: "(encDec_%s x_%s)" % (X, pn)}.get(x, x))
            bsX.insert(len([b for b in bsX if b.startswith(("(ho :", "(hbl :"))]), "(x_%s : %s)" % (pn, X))
            rsX = rs.replace("(.cont t_%s ds_%s)" % (pn, pn), "(.cont %d (kids_%s x_%s))" % (m.cid[X], X, pn))
            rdsX = " ".join(rds).replace("a_%s" % pn, "(⟨enc_%s x_%s⟩ : SszObj)" % (X, pn))
            routX = rs_out.replace("(.cont t_%s ds_%s)" % (pn, pn), "(.cont %d (kids_%s x_%s))" % (m.cid[X], X, pn))
            call += ("\ntheorem %s_fcall_%s (sha : Oracle) %s (n : Nat) (hn : %s%d ≤ n) {γ : Type}\n"
                     "    (k : DRes × List DV → DM γ) :\n"
                     "    Option.map (Except.mapError SpecError.fail)\n"
                     "        (DM.bind ((den (Scope.env sha) fpsGen n).fn %s Scope.fn_%s %s) k) =\n"
                     "      callK (%s %s) fun x => Option.map (Except.mapError SpecError.fail) (k (%s, %s)) :=\n"
                     "  %s_fcall sha %s n hn k\n"
                     % (name, X, " ".join(b for b in bsX if not b.startswith("(t_%s" % pn) and
                                         not b.startswith("(ds_%s" % pn) and not b.startswith("(he_%s" % pn)),
                        LENS, D, fp, name, rsX, name, rdsX, enc, routX, name,
                        " ".join(x for x in xsX)))
    if not sub and not nonep:
        LENS_OF[name] = items
    out = ((loop_theorems(m, name, params, bs, roots, rds, xs, lps) + "\n" if lps else "") +
           (while_theorems(m, name, params, bs, roots, rds, xs, wls) + "\n" if wls else "") +
           (comp_theorems(m, name, params, bs, roots, rds, xs, cps) + "\n" if cps else "") + thm + "\n" + call)
    if not sub and not nonep:
        out += "\n" + wrapper(m, name, params, bs, roots, rds, xs, enc, w, D, f, LENS)
    out = re.sub(r"^(@\[l4_simp\] )?theorem ", lambda mm: "set_option maxHeartbeats %s in\n" % os.environ.get("L4_HB", "1000000") + mm.group(0), out,
                 flags=re.M)
    return out.replace("all_goals l4_close", "all_goals " + CLOSE), D


def wrapper(m, name, params, bs, roots, rds, xs, enc, w, D, f, LENS=""):
    """`<f>_l4`: SPEC 9.2 from `<f>_den`, through `GenWrap.l4_wrap`."""
    vs, hyps, decs = [], [], []
    for i, ((pn, pt), r) in enumerate(zip(params, roots)):
        if r.startswith("(.leaf "):
            vs.append(r[len("(.leaf "):-1])
            decs.append("(GenWrap.dec_leaf rfl)")
        else:
            vs.append("(.ref r_%s)" % pn)
            hyps.append("(r_%s : Nat) (hr_%s : ∃ n, dec h n (.ref r_%s) = some %s)" % (pn, pn, pn, r))
            decs.append("hr_%s" % pn)
    hdec = "(GenWrap.decArgs_nil h)"
    for dd in reversed(decs):
        hdec = "(GenWrap.decArgs_cons %s %s)" % (dd, hdec)
    VS = "[%s]" % ", ".join(vs)
    fp = "(fpsGen %d)" % f["id"] if w else "[]"
    hw = " (hw : WTree h %s %s) (hcw : ContRun.CW (Scope.env sha) h)" % (VS, fp) if w else ""
    hwt = "hw" if w else "(Examples.wtree_nil h _)"
    if w:
        k = [i for i, (_, pt) in enumerate(params) if pt == w][0]
        pn = params[k][0]
        E = ("(fun (x : %s) h' v => v = .none ∧ ∃ n, dec h' n (.ref r_%s) = some (.cont %d (kids_%s x)))"
             % (w, pn, m.cid[w], w))
        hE = "(fun x h' v hx => ⟨hx.1.1, GenWrap.decArgs_get hx.2 %d rfl rfl⟩)" % k
    elif enc.startswith("DRes.tree "):
        T = enc[len("DRes.tree "):]
        E = "(fun (x : %s) h' v => ∃ n, dec h' n v = some %s)" % (m.sigs[name][1], T)
        hE = "(fun x h' v hx => hx.1.1)"
    else:
        V = enc[len("DRes.val "):]
        E = "(fun (x : %s) _ v => v = %s)" % (m.sigs[name][1], V)
        hE = "(fun x h' v hx => hx.1.1)"
    return ("theorem %s_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h)\n"
            "    (hh : Examples2.HtrDec (Scope.env sha)) (hX : ExtOK (Scope.env sha)) %s %s%s :\n"
            "    ∀ fuel, %s%d ≤ fuel →\n"
            "      ResultMatches gfp %s h %s %s\n"
            "        (interp (Scope.env sha) fuel Scope.Id.«%s» %s h) (%s %s) := by\n"
            "  intro fuel hf\n"
            "  have hden := %s_den sha 0 %s\n"
            "  simp only [Nat.add_zero, Nat.zero_add] at hden\n"
            "  exact GenWrap.l4_mono hf (GenWrap.l4_wrap (by simp only [env_globals, Validation.Tactic.lookup_lit])\n"
            "    hwf hh %s %s hden %s)\n"
            % (name, " ".join(bs), " ".join(hyps), hw, LENS, D, fp, VS, E, name, VS, name, " ".join(rds),
               name, " ".join(xs), hdec, hwt, hE)) + bridged_wrapper(m, name, params, bs, rds, xs, vs, hw, LENS, D, fp,
                                                                    VS, E, f)


def bridged_wrapper(m, name, params, bs, rds, xs, vs, hw, LENS, D, fp, VS, E, f):
    """`<f>_l4r`: `<f>_l4` with each container argument given by its readable decoder."""
    conts = [(pn, pt) for (pn, pt), v in zip(params, vs) if v.startswith("(.ref ")]
    if not conts or any(pt not in m.bridged for _, pt in conts):
        return ""
    bs = list(bs)
    xs = list(xs)
    for pn, pt in conts:
        hb = "(hok_%s : ok_%s a_%s)" % (pn, pt, pn)
        if hb in bs:
            if pt not in m.okb:
                return ""
            bs.remove(hb)
            xs[xs.index("hok_" + pn)] = "(okb_%s hy_%s)" % (pt, pn)
    hyps = " ".join("(r_%s : Nat) (hy_%s : dec_%s h (.ref r_%s) = some a_%s)" % (pn, pn, pt, pn, pn)
                    for pn, pt in conts)
    args = " ".join("r_%s (bridge_%s hc hy_%s)" % (pn, pt, pn) for pn, pt in conts)
    hw = hw.replace(" (hcw : ContRun.CW (Scope.env sha) h)", "")
    return ("\ntheorem %s_l4r (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h)\n"
            "    (hh : Examples2.HtrDec (Scope.env sha)) (hX : ExtOK (Scope.env sha))\n"
            "    (hc : GenBridge.ContWF h) %s %s%s :\n"
            "    ∀ fuel, %s%d ≤ fuel →\n"
            "      ResultMatches gfp %s h %s %s\n"
            "        (interp (Scope.env sha) fuel Scope.Id.«%s» %s h) (%s %s) :=\n"
            "  %s_l4 sha gfp h hwf hh hX %s %s%s\n"
            % (name, " ".join(bs), hyps, hw, LENS, D, fp, VS, E, name, VS, name, " ".join(rds),
               name, " ".join(xs), args, " hw hc" if hw else ""))


def check(text, tag, full=False):
    """Check a candidate file. Returns (ok, first error)."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", prefix="l4_%s_" % tag, dir=ROOT / ".lake",
                                     delete=False) as fh:
        fh.write(text)
        path = fh.name
    try:
        cmd = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=" + MEM, "-p", "MemorySwapMax=0",
               "env", "LEAN_NUM_THREADS=" + THREADS, "lake", "env", "lean", path]
        try:
            p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return False, "timeout"
        out = p.stdout + p.stderr
        if full:
            return p.returncode == 0, text + "\n----\n" + out
        if p.returncode == 0 and "sorry" not in out:
            return True, ""
        errs = [l for l in out.splitlines() if "error" in l]
        if p.returncode != 0 and not errs:
            return False, "exit %d (memory cap?)" % p.returncode
        return False, (errs[0] if errs else out[:200]).split(".lean:")[-1][:160]
    finally:
        os.unlink(path)


def order(m, names):
    """Callees first."""
    seen, out = set(), []

    def go(n, stack):
        if n in seen or n in stack:
            return
        for c in m.callees(n):
            if c in names:
                go(c, stack | {n})
        seen.add(n)
        out.append(n)
    for n in sorted(names):
        go(n, set())
    return out


def build(target):
    r = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=" + MEM, "-p",
                        "MemorySwapMax=0", "env", "LEAN_NUM_THREADS=" + THREADS, "lake", "build", target],
                       cwd=ROOT, capture_output=True, text=True)
    return r.returncode == 0, r.stdout[-3000:] + r.stderr[-3000:]


def call_hyp(text, name, hyps=()):
    """The `_call` statement of `name` in its candidate text, as a hypothesis over any fuel above
    its bound: `∀ binders (n : Nat), bound ≤ n → ∀ {γ} k, statement`. The hypothesis binders
    `hyps` of a conditional theorem are left out."""
    mm = re.search(r"theorem %s_call \(sha : Oracle\) \(m : Nat\) (.*?) \{γ : Type\} "
                   r"\(k : DRes × List DV → DM γ\)(.*?) :\n(.*?) :=\n" % re.escape(name), text, re.S)
    if not mm:
        return None
    binders, stmt = mm.group(1) + mm.group(2).replace(" := by assumption", ""), mm.group(3)
    for h in hyps:
        binders = binders.replace(" " + h, "").replace(h, "")
    mf = re.search(r"\.fn (?:\[\]|\(fpsGen \d+\)) Scope\.fn_", stmt)
    fu = re.search(r"fpsGen \((.*?m \+ \d+)\)\)\.fn", stmt)
    if not mf or not fu:
        return None
    bound = fu.group(1).replace("m + ", "")
    stmt = stmt.replace("fpsGen (%s))" % fu.group(1), "fpsGen n)")
    return "∀ %s (n : Nat), %s ≤ n → ∀ {γ : Type} (k : DRes × List DV → DM γ),\n%s" % (
        binders.strip(), bound, stmt.rstrip())


CALLHYP = """/-- The call statement of an unproved callee, as a hypothesis. The wrapper keeps `simp [*]` from
rewriting with it. -/
structure CallHyp (P : Prop) : Prop where
  out : P

"""


def ext_entry(m, c, o):
    """The `ExtOK` case of the ext entry of `c`, from the tactic's `c_runF`."""
    N = len(o["args"])
    rs = ["r_%d" % i for i in range(N)]
    vs = ["v_%d" % i for i in range(N)]
    L = []
    L.append("  · next hg =>")
    L.append("    subst hg")
    L.append("    simp only [Option.some.injEq] at hx; subst hx")
    pat = "".join("⟨%s, " % r for r in rs) + "_ | ⟨_, _⟩" + "⟩" * N
    nested = lambda xs: "_ | " + "".join("⟨%s, _ | " % x for x in xs[:-1]) + "⟨%s, _ | ⟨_, _⟩⟩" % xs[-1] + "⟩" * (len(xs) - 1)
    L.append("    obtain ⟨%s, rfl⟩ : ∃ %s, roots = [%s] := by" % (", ".join(rs), " ".join(rs), ", ".join(rs)))
    L.append("      rcases roots with %s <;> simp [ext_%s] at hr ⊢" % (nested(rs), c))
    L.append("    obtain ⟨%s, rfl⟩ : ∃ %s, vs = [%s] := by" % (", ".join(vs), " ".join(vs), ", ".join(vs)))
    L.append("      rcases vs with %s <;> simp [DecArgs] at hdec ⊢ <;> omega" % nested(vs))
    for i in range(N):
        L.append("    obtain ⟨k%d, hk%d⟩ := hdec.2 %d v_%d r_%d rfl rfl" % (i, i, i, i, i))
    hus, tys, byts = [], [], []
    for (k, ty, i), r, v in zip(o["args"], rs, vs):
        if k == "cont" or k == "list":
            u = ("undv_%s %s" % (ty, r)) if k == "cont" else ("GenBridge.undvListE %s %s %s" % (ty[0], ty[1], r))
            pf = ("decOf_%s" % ty) if k == "cont" else ("(GenBridge.decOf_listE %s %s)" % (ty[2], ty[0]))
            L.append("    cases hu%d : %s with" % (i, u))
            L.append("    | none => simp [ext_%s, %s] at hr" % (c, ", ".join(hus + ["hu%d" % i])))
            L.append("    | some x%d =>" % i)
            hus.append("hu%d" % i)
            L.append("    have hy%d := %s h k%d %s %s x%d hk%d hu%d" % (i, pf, i, v, r, i, i, i))
            L.append("    obtain ⟨r%d, rfl⟩ : ∃ a, %s = .ref a := by" % (i, v))
            if k == "cont":
                L.append("      cases %s <;> simp [dec_%s, containerFieldsT] at hy%d; exact ⟨_, rfl⟩" % (v, ty, i))
            else:
                L.append("      cases %s <;> simp [Validation.decListE] at hy%d; exact ⟨_, rfl⟩" % (v, i))
            L.append("    have hb%d : Below h (.ref r%d) := dec_below hwf k%d _ %s hk%d" % (i, i, i, r, i))
        elif k == "bytes":
            L.append("    cases hq%d : GenBridge.leafBytes %s with" % (i, r))
            L.append("    | none => simp [ext_%s, %s] at hr" % (c, ", ".join(hus + ["hq%d" % i])))
            L.append("    | some p%d =>" % i)
            L.append("    obtain ⟨c%d, x%d⟩ := p%d" % (i, i, i))
            hus.append("hq%d" % i)
            byts.append((i, ty))
        else:
            L.append("    cases hl%d : GenBridge.leafUint %s with" % (i, r))
            L.append("    | none => simp [ext_%s, %s] at hr" % (c, ", ".join(hus + ["hl%d" % i])))
            L.append("    | some p%d =>" % i)
            L.append("    obtain ⟨t%d, x%d⟩ := p%d" % (i, i, i))
            hus.append("hl%d" % i)
            tys.append((i, ty))
    for i, (nm, ln) in byts:
        L.append("    by_cases hc%d : c%d ≠ %s" % (i, i, nm))
        L.append("    · simp [ext_%s, %s, hc%d] at hr" % (c, ", ".join(hus), i))
        L.append("    rw [ne_eq, Classical.not_not] at hc%d" % i)
        L.append("    subst hc%d" % i)
        L.append("    by_cases hl%d : x%d.length ≠ %d" % (i, i, ln))
        L.append("    · simp [ext_%s, %s, hl%d] at hr" % (c, ", ".join(hus), i))
        L.append("    rw [ne_eq, Classical.not_not] at hl%d" % i)
        L.append("    obtain rfl := GenBridge.leafBytes_spec hq%d" % i)
        L.append("    obtain ⟨rfl, -⟩ := dec_leaf hk%d" % i)
        L.append("    have hb%d : Below h (.bytes %s x%d) := fun q a e => absurd e (fun e' => follow_nonref_ref (fun b e => by cases e) e')" % (i, nm, i))
        hus.append("hl%d" % i)
    for i, ty in tys:
        L.append("    by_cases ht%d : t%d ≠ %s" % (i, i, ty))
        L.append("    · simp [ext_%s, %s, ht%d] at hr" % (c, ", ".join(hus), i))
        L.append("    rw [ne_eq, Classical.not_not] at ht%d" % i)
        L.append("    subst ht%d" % i)
        L.append("    obtain rfl := GenBridge.leafUint_spec hl%d" % i)
        L.append("    obtain ⟨rfl, -⟩ := dec_leaf hk%d" % i)
        L.append("    have hb%d : Below h (.uint %s x%d) := fun q a e => absurd e (fun e' => follow_nonref_ref (fun b e => by cases e) e')" % (i, ty, i))
        if i in o.get("ranges", {}):
            L.append("    by_cases hr%d : ¬ x%d < 2 ^ %d" % (i, i, o["ranges"][i]))
            L.append("    · simp [ext_%s, %s, hr%d] at hr" % (c, ", ".join(hus), i))
            L.append("    rw [Classical.not_not] at hr%d" % i)
            hus.append("hr%d" % i)
    L.append("    simp only [ext_%s, %s] at hr hb" % (c, ", ".join(hus)))
    L.append("    try simp only [and_self, ↓reduceIte, true_and] at hr")
    VS = "[%s]" % ", ".join("(.ref r%d)" % i if k in ("cont", "list") else
                            "(.bytes %s x%d)" % (ty[0], i) if k == "bytes" else "(.uint %s x%d)" % (ty, i)
                            for k, ty, i in o["args"])
    L.append("    have haw : ArgsWF h %s := by" % VS)
    L.append("      intro kk q a ha")
    L.append("      obtain ⟨w, hw, hf⟩ := at?_some ha")
    L.append("      match kk, hw with")
    for (k, ty, i) in o["args"]:
        if k in ("cont", "list"):
            L.append("      | %d, hw => simp at hw; subst hw; exact dec_exists k%d _ r_%d hk%d q a hf" % (i, i, i, i))
        else:
            L.append("      | %d, hw => simp at hw; subst hw; exact absurd hf (fun e' => follow_nonref_ref (fun b e => by cases e) e')" % i)
    L.append("      | _ + %d, hw => simp at hw" % N)
    margs = []
    for b in o["binders"]:
        if b in ("hwf", "haw"):
            margs.append(b)
        else:
            margs.append(b)
    hbt = "(by have := hb; simp only [bigFuel_eq] at this ⊢; omega)" if "bigFuel" in o["bound"] else "hb"
    if o.get("stmt") and o.get("ho"):
        L.append("    obtain ⟨ho, hst⟩ := hst_%s (Classical.not_not.mp hmem)" % c)
        L.append("    have hm := hst [] h %s n %s" % (" ".join(margs), hbt))
    elif o.get("stmt"):
        L.append("    have hm := hst_%s (Classical.not_not.mp hmem) [] h %s n %s" % (c, " ".join(margs), hbt))
    else:
        L.append("    have hm := Validation.Gen.%s_runF sha [] h %s n %s" % (c, " ".join(margs), hbt))
    L.append("    rw [interp, callName, callValue_glob_fn _ _ _ hd] at hm")
    L.append("    have hba : BelowArgs h %s := by" % VS)
    L.append("      intro kk w' hw'")
    L.append("      match kk, hw' with")
    for (k, ty, i) in o["args"]:
        L.append("      | %d, hw' => simp at hw'; subst hw'; exact hb%d" % (i, i))
    L.append("      | _ + %d, hw' => simp at hw'" % N)
    L.append("    revert hm")
    L.append("    cases hc : callFn (Scope.env sha) n d.params (ClosureBody.stmts d.body) Locals.empty %s [] h with" % VS)
    L.append("    | error e' =>")
    L.append("      cases hg : %s with" % o["call"])
    L.append("      | ok y => intro hm; simp [ResultMatches] at hm")
    L.append("      | error f =>")
    L.append("        simp only [hg, GenBridge.extRes, Option.some.injEq] at hr; subst hr")
    L.append("        rintro ⟨hne, hf⟩")
    L.append("        refine ⟨?_, rep_ne_oof f⟩")
    L.append("        rw [normE_of_ne hne, normE_of_ne (rep_ne_oof f), GenBridge.rep_fail, hf]")
    L.append("    | ok q =>")
    L.append("      obtain ⟨w, h'⟩ := q")
    L.append("      cases hg : %s with" % o["call"])
    L.append("      | error f => intro hm; simp [ResultMatches] at hm")
    L.append("      | ok y =>")
    L.append("        simp only [hg, GenBridge.extRes, Option.some.injEq] at hr; subst hr")
    L.append("        rintro ⟨hw, hfr, hfresh, -⟩")
    L.append("        have he : Ext h h' := ext_of_frame hfr hfresh (NoFill.callFn_noFill _ NoFill.ssz_libKeeps hc)")
    tlo = "trivial"
    if o["rkind"] == "uint":
        erel = "⟨by have := hw.1; simp only [enc_%s, encUint] at this; exact this, rfl⟩" % o["rt"]
    elif o["rkind"] == "list":
        el = re.fullmatch(r"\(List (\w+)\)", o["rt"]).group(1)
        L.append("        have hLR := ExtBridge.listRes_rel y (fun z : %s => Value.uint %s z.val) (fun _ => rfl) hw.1 hwf hdec hba he"
                 % (el, m.uint_ty(el)))
        erel, tlo = "hLR.1", "hLR.2"
    else:
        erel = "⟨hw.1, rfl⟩" if o.get("conj", True) else "⟨hw, rfl⟩"
    L.append("        refine ⟨%s, %s, ⟨rfl, fun j w' d' hw' hd' => ?_⟩," % (erel, tlo))
    L.append("          hfr, Skel_of_Ext he, fun _ => he, fun kg q b kg' q' hab hle _ => ?_⟩")
    L.append("        · match j, hw', hd' with")
    for (k, ty, i) in o["args"]:
        L.append("          | %d, hw', hd' => simp at hw' hd'; subst hw'; subst hd'; exact ⟨k%d, by rw [dec_ext he hb%d k%d]; exact hk%d⟩" % (i, i, i, i, i))
    L.append("          | _ + %d, hw', _ => simp at hw'" % N)
    L.append("        · have := at?_below0 hwf hdec ((at?_Ext he hba kg q b).mp hab); omega")
    return "\n".join(L)


def ext_file(m, proved, texts):
    """`extGen_ok`: each callee taken from a statement agrees with the interpreter, from the
    tactic's `_runF` theorem; and the full theorem of each caller."""
    ents = sorted(OPAQUE.items())
    body = ["import SpecLean.Layer4.Gen.Funcs\nimport SpecLean.Layer4.ExtBridge\nimport SpecLean.Validation.Gen.Loops\nimport SpecLean.Validation.Gen.Stmts\n",
            "/-!\n# Layer 4: the callees taken from statements\n\nGenerated by tools/gen_l4.py. Do not edit. "
            "`extGen_ok` proves `ExtOK` of the table from the tactic's theorems; each `_l4f` theorem is then "
            "the `_l4` theorem without the hypothesis.\n-/\n",
            "namespace SpecLean.Layer4.Gen\n", OPEN, "open SpecLean.Layer4.ExtBridge\n"]
    sts = [c for c, o in ents if o.get("stmt")]
    prf = ["theorem extGen_ok [ExtSet] (sha : Oracle)%s : ExtOK (Scope.env sha) := by" % "".join(
               "\n    (hst_%s : (%d : Name) ∈ ExtSet.S → %sValidation.Gen.%s_stmtF sha)" % (
                   c, m.fns[c]["id"], "Validation.HtrBridge.OracleHtr sha ∧ " if OPAQUE[c].get("ho") else "", c)
               for c in sts),
           "  refine ⟨?_, fun g x d hx => by simp [extGen_extW] at hx⟩",
           "  intro g x d hx hd n roots vs h r hdec hwf hlen hb hr",
           "  simp only [extGen_ext] at hx",
           "  by_cases hmem : g ∉ ExtSet.S",
           "  · rw [if_neg hmem] at hx; cases hx",
           "  rw [if_pos (Classical.not_not.mp hmem)] at hx",
           "  try dsimp only at hx"]
    for c, o in ents:
        prf.append("  split at hx")
        prf.append(ext_entry(m, c, o))
    prf.append("  · cases hx")
    body.append("set_option maxHeartbeats 4000000 in\n" + "\n".join(prf) + "\n")
    for n in order(m, set(proved)):
        if not any(c in OPAQUE for c in m.callees(n)):
            continue
        mm = re.search(r"theorem %s_l4 \(sha : Oracle\) (.*?) :\n    (∀ fuel.*?) := by" % re.escape(n), texts.get(n, ""), re.S)
        if not mm:
            continue
        bs = mm.group(1).replace(" (hX : ExtOK (Scope.env sha))", "")
        bs = re.sub(r" \(hS_\w+ : \(\d+ : Name\) ∈ ExtSet\.S := by assumption\)", "", bs)
        args = " ".join(re.findall(r"\((\w+) :", bs))
        ids = sorted(m.fns[c]["id"] for c in ext_closure(m, n))
        hs = " ".join("(hS_%s := by decide)" % c for c in sorted(ext_closure(m, n)))
        cl = ext_closure(m, n)
        sbs = "".join(" (hst_%s : Validation.Gen.%s_stmtF sha)" % (c, c) for c in sts if c in cl)
        sargs = " ".join(("(fun _ => ⟨ho, hst_%s⟩)" if OPAQUE[c].get("ho") else "(fun _ => hst_%s)") % c
                         if c in cl else "(fun hm => absurd hm (by decide))" for c in sts)
        if any(OPAQUE[c].get("ho") for c in sts if c in cl) and "(ho : " not in bs:
            sbs = " (ho : Validation.HtrBridge.OracleHtr sha)" + sbs
        body.append("theorem %s_l4f (sha : Oracle) %s%s :\n    %s :=\n  letI : ExtSet := ⟨[%s]⟩\n  %s_l4 sha %s %s\n" % (
            n, bs, sbs, mm.group(2), ", ".join(map(str, ids)), n,
            re.sub(r"\bhh\b", "hh (extGen_ok sha %s)" % sargs if sargs else "hh (extGen_ok sha)", args, count=1), hs))
    body.append("end SpecLean.Layer4.Gen\n")
    return "\n".join(body)


def cond_file(m, texts):
    body = ["import SpecLean.Layer4.Gen.Funcs\n",
            "/-!\n# Layer 4: the conditional theorems\n\nGenerated by tools/gen_l4.py. Do not edit. "
            "Each theorem takes the call statement of each unproved callee as a hypothesis.\n-/\n",
            "namespace SpecLean.Layer4.Gen\n", OPENX, CALLHYP]
    for n in order(m, set(texts)):
        body.append(texts[n])
    body.append("end SpecLean.Layer4.Gen\n")
    return "\n".join(body)


def funcs_file(m, proved, texts, total):
    body = ["import SpecLean.Layer4.Gen.Classes\n",
            "/-!\n# Layer 4: the generated theorems\n\nGenerated by tools/gen_l4.py. Do not edit. "
            "The generator proves %d of the %d functions.\n-/\n" % (len(proved), total),
            "namespace SpecLean.Layer4.Gen\n", OPENX]
    for n in order(m, set(proved)):
        body.append(texts[n])
    body.append("end SpecLean.Layer4.Gen\n")
    return "\n".join(body)


def cond_pass(m, proved, fails, jobs):
    """Conditional theorems: a function whose callees are proved, or failed only in the proof (so
    their call statements are in the den fragment), takes those call statements as hypotheses.
    A conditionally proved function is a hypothesis for its callers in turn."""
    pre = "import SpecLean.Layer4.Gen.Funcs\n" + OPENX + "\nnamespace SpecLean.Layer4.Gen\n\n" + CALLHYP
    COND.clear()
    for c, e in fails.items():
        if e.startswith(("unsupported", "callee")) or "@" in c:
            continue
        for ok in (True, False):
            try:
                t, d = candidate(m, c, proved, ok=ok)
            except Unsupported:
                continue
            h = call_hyp(t, c)
            if h:
                COND[c] = (h, d)
                break
    ctexts, cfails = {}, {}
    pending = [n for n, e in fails.items() if e.startswith("callee")]
    rnd = 0
    while pending:
        rnd += 1
        ready, wait = [], []
        for n in pending:
            cs = m.callees(n)
            if all(c in proved or c in COND for c in cs):
                ready.append(n)
            elif any(c in cfails or (c in fails and c not in COND and c not in pending) for c in cs):
                cfails[n] = "callee not proved: " + ", ".join(c for c in cs if c not in proved and c not in COND)
            else:
                wait.append(n)
        if not ready:
            for n in wait:
                cfails[n] = "callee not proved: " + ", ".join(
                    c for c in m.callees(n) if c not in proved and c not in COND)
            break
        cands = {}
        for n in ready:
            for ok in (False, True):
                try:
                    cands[(n, ok)] = candidate(m, n, proved, ok=ok)
                except Unsupported as e:
                    cfails[n] = "unsupported: " + str(e)
        print("cond round %d: %d candidates" % (rnd, len(cands)), flush=True)
        with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
            futs = {ex.submit(check, pre + t + "\nend SpecLean.Layer4.Gen\n", "%s_cond%s" % (n, "_ok" if ok else "")):
                    (n, ok) for (n, ok), (t, _) in cands.items()}
            res = {}
            for fu in concurrent.futures.as_completed(futs):
                res[futs[fu]] = fu.result()
        for n in ready:
            for ok in (False, True):
                if (n, ok) not in res:
                    continue
                good, err = res[(n, ok)]
                print("%-55s %s" % (n + (" (cond, ok)" if ok else " (cond)"), "ok" if good else err), flush=True)
                if good:
                    t, d = cands[(n, ok)]
                    ctexts[n] = t
                    hyps = ["(%s_fcall : CallHyp (%s))" % (c, COND[c][0]) for c in m.callees(n) if c in COND]
                    h = call_hyp(t, n, hyps)
                    if h:
                        COND[n] = (h, d)
                    cfails.pop(n, None)
                    break
                cfails[n] = err
        pending = wait
    return ctexts, cfails


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--show", default="", help="check one function and print the whole output")
    ap.add_argument("--cond", action="store_true", help="only the conditional pass, after a full run")
    ap.add_argument("--ext", action="store_true", help="only Classes and Ext, against the last Funcs")
    args = ap.parse_args()
    m = model()
    GEN.mkdir(parents=True, exist_ok=True)
    (GEN / "Classes.lean").write_text(classes_file(m))
    ok, out = build("SpecLean.Layer4.Gen.Classes")
    if not ok:
        print(out)
        sys.exit(1)
    if args.ext:
        txt = (GEN / "Funcs.lean").read_text()
        proved = dict.fromkeys(re.findall(r"theorem (\w+)_den \(sha : Oracle\)", txt), 0)
        (GEN / "Ext.lean").write_text(ext_file(m, proved, dict.fromkeys(proved, txt)))
        okx, outx = build("SpecLean.Layer4.Gen.Ext")
        print("ext build %s" % ("ok" if okx else "FAILED\n" + outx[-6000:]))
        return
    if args.cond:
        import json
        txt = (GEN / "Funcs.lean").read_text()
        fuel = {k: int(v) for k, v in re.findall(
            r"theorem (\w+)_den \(sha : Oracle\) \(m : Nat\) .*?m \+ (\d+)\)\)\.fn", txt, re.S)}
        for g in m.generic:
            mg = re.search(r"theorem %s_den_\w+ \(sha : Oracle\) \(m : Nat\) .*?m \+ (\d+)\)\)\.fn" % g, txt, re.S)
            if mg:
                fuel[g] = int(mg.group(1))
        NONE_OK.update(re.findall(r"theorem (\w+)_fcall_none ", txt))
        RNG.update(re.findall(r"theorem (\w+)_rng ", txt))
        for n in order(m, set(fuel)):
            try:
                candidate(m, n, fuel)
            except Unsupported:
                pass
        fails = json.loads((ROOT / ".lake/l4_fails.json").read_text())
        report_cond(m, fuel, fails, args.jobs)
        return
    if args.show:
        # Against the proved functions of the last run.
        fuel = dict(re.findall(r"theorem (\w+)_den \(sha : Oracle\) \(m : Nat\) .*?m \+ (\d+)\)\)\.fn",
                               (GEN / "Funcs.lean").read_text(), re.S)) if (GEN / "Funcs.lean").exists() else {}
        fuel = {k: int(v) for k, v in fuel.items()}
        for g in m.generic:
            mg = re.search(r"theorem %s_den_\w+ \(sha : Oracle\) \(m : Nat\) .*?m \+ (\d+)\)\)\.fn" % g,
                           (GEN / "Funcs.lean").read_text(), re.S)
            if mg:
                fuel[g] = int(mg.group(1))
        NONE_OK.update(re.findall(r"theorem (\w+)_fcall_none ", (GEN / "Funcs.lean").read_text()))
        RNG.update(re.findall(r"theorem (\w+)_rng ", (GEN / "Funcs.lean").read_text()))
        for n in order(m, set(fuel)):
            try:
                candidate(m, n, fuel)
            except Unsupported:
                pass
        pre = ("import SpecLean.Layer4.Gen.Funcs\n" if fuel else "import SpecLean.Layer4.Gen.Classes\n") + \
            OPENX + "\nnamespace SpecLean.Layer4.Gen\n\n"
        print(check(pre + candidate(m, args.show, fuel, ok=bool(os.environ.get("L4_OK")))[0] +
                    "\nend SpecLean.Layer4.Gen\n", "show", True)[1])
        return
    names = list(m.fns) if not args.only else args.only.split(",")
    names = order(m, set(names))
    total = len(names)
    proved, texts, fails, vtexts = {}, {}, {}, {}
    pending = list(names)
    t0 = time.time()
    rnd = 0
    while pending:
        rnd += 1
        ready, wait = [], []
        for n in pending:
            cs = [c for c in m.callees(n) if c in names and c not in OPAQUE]
            if all(c in proved for c in cs):
                ready.append(n)
            elif any(c in fails for c in cs):
                fails[n] = "callee not proved: " + ", ".join(c for c in cs if c in fails)
            else:
                wait.append(n)
        if not ready:
            for n in wait:
                fails[n] = "callee cycle"
            break
        (GEN / "Funcs.lean").write_text(funcs_file(m, proved, texts, total))
        ok, out = build("SpecLean.Layer4.Gen.Funcs")
        if not ok:
            print(out)
            sys.exit(1)
        pre = "import SpecLean.Layer4.Gen.Funcs\n" + OPENX + "\nnamespace SpecLean.Layer4.Gen\n\n"
        cands = {}
        for n in ready:
            try:
                cands[n] = candidate(m, n, proved)
            except Unsupported as e:
                fails[n] = "unsupported: " + str(e)
                continue
            if any(re.fullmatch(r"\(?Option (\w+)\)?", t) for _, t in m.sigs[n][0]):
                try:
                    cands[n + "@none"] = candidate(m, n, proved, ok=True, nonep=True)
                except Unsupported:
                    pass
            for c in variants(m, n):
                for isub in ([False, True] if any(t == "Int" for _, t in m.sigs[n][0]) else [False]):
                    try:
                        cands[n + "@" + c + ("i" if isub else "")] = candidate(m, n, proved, c, isub)
                    except Unsupported:
                        pass
        print("round %d: %d candidates" % (rnd, len(cands)), flush=True)
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
            futs = {ex.submit(check, pre + t + "\nend SpecLean.Layer4.Gen\n", n): n for n, (t, _) in cands.items()}
            for fu in concurrent.futures.as_completed(futs):
                n = futs[fu]
                ok, err = fu.result()
                if "@" in n:
                    if ok:
                        vtexts.setdefault(n.split("@")[0], []).append(cands[n][0])
                        if n.endswith("@none"):
                            NONE_OK.add(n.split("@")[0])
                    continue
                if ok:
                    proved[n] = cands[n][1]
                    texts[n] = cands[n][0]
                else:
                    fails[n] = err
                print("%-55s %s" % (n, "ok" if ok else err), flush=True)
        # A failed function again, with range hypotheses on its inputs.
        retry = {}
        for n in cands:
            if "@" in n or n in proved or fails.get(n) == "timeout":
                continue
            try:
                retry[n] = candidate(m, n, proved, ok=True)
            except Unsupported:
                pass
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
            futs = {ex.submit(check, pre + t + "\nend SpecLean.Layer4.Gen\n", n): n for n, (t, _) in retry.items()}
            for fu in concurrent.futures.as_completed(futs):
                n = futs[fu]
                ok, err = fu.result()
                if ok:
                    proved[n] = retry[n][1]
                    texts[n] = retry[n][0]
                    del fails[n]
                print("%-55s %s" % (n + " (ok)", "ok" if ok else err), flush=True)
        # A heartbeat timeout again, with four times the heartbeats.
        retry2 = {}
        for n in cands:
            if "@" in n or n in proved or "maximum number of heartbeats" not in fails.get(n, ""):
                continue
            t = retry.get(n, cands[n])
            retry2[n] = (t[0].replace("maxHeartbeats 1000000 in", "maxHeartbeats 4000000 in"), t[1])
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
            futs = {ex.submit(check, pre + t + "\nend SpecLean.Layer4.Gen\n", n): n for n, (t, _) in retry2.items()}
            for fu in concurrent.futures.as_completed(futs):
                n = futs[fu]
                ok, err = fu.result()
                if ok:
                    proved[n] = retry2[n][1]
                    texts[n] = retry2[n][0]
                    del fails[n]
                print("%-55s %s" % (n + " (4M)", "ok" if ok else err), flush=True)
        # A check killed at the memory cap again, alone.
        for n in cands:
            if "@" in n or n in proved or "memory cap" not in fails.get(n, ""):
                continue
            t = retry.get(n, cands[n])
            ok, err = check(pre + t[0] + "\nend SpecLean.Layer4.Gen\n", n)
            if ok:
                proved[n] = t[1]
                texts[n] = t[0]
                del fails[n]
            print("%-55s %s" % (n + " (alone)", "ok" if ok else err), flush=True)
        # The range lemmas of the new functions with a bytes result.
        rngc = {}
        for n in cands:
            if "@" in n or n not in proved or n in RNG:
                continue
            t = rng_theorem(m, n)
            if t:
                rngc[n] = t
        if rngc:
            (GEN / "Funcs.lean").write_text(funcs_file(m, proved, texts, total))
            okb, outb = build("SpecLean.Layer4.Gen.Funcs")
            if okb:
                with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
                    futs = {ex.submit(check, pre + t + "\nend SpecLean.Layer4.Gen\n", n + "_rng"): n
                            for n, t in rngc.items()}
                    for fu in concurrent.futures.as_completed(futs):
                        n = futs[fu]
                        ok, err = fu.result()
                        if ok:
                            RNG.add(n)
                            vtexts.setdefault(n, []).append(rngc[n])
                        print("%-55s %s" % (n + " (rng)", "ok" if ok else err), flush=True)
        for n, vs in vtexts.items():
            if n in texts and not texts[n].endswith("-- variants\n"):
                texts[n] = texts[n] + "\n" + "\n".join(vs) + "-- variants\n"
        pending = wait
    (GEN / "Funcs.lean").write_text(funcs_file(m, proved, texts, total))
    ok, out = build("SpecLean.Layer4.Gen.Funcs")
    print("\nproved %d / %d in %.0fs (final build %s)" % (len(proved), total, time.time() - t0,
                                                      "ok" if ok else "FAILED"))
    import json
    (ROOT / ".lake/l4_fails.json").write_text(json.dumps(fails, indent=1))
    reasons = {}
    for n, e in fails.items():
        k = e.split(":")[0] if e.startswith(("unsupported", "callee")) else "proof"
        reasons.setdefault(k, []).append(n)
    for k, v in sorted(reasons.items(), key=lambda kv: -len(kv[1])):
        print("%3d %s" % (len(v), k))
    (GEN / "Ext.lean").write_text(ext_file(m, proved, texts))
    okx, outx = build("SpecLean.Layer4.Gen.Ext")
    print("ext build %s" % ("ok" if okx else "FAILED\n" + outx[-3000:]))
    report_cond(m, proved, fails, args.jobs)


def report_cond(m, proved, fails, jobs):
    ctexts, cfails = cond_pass(m, proved, fails, jobs)
    (GEN / "Cond.lean").write_text(cond_file(m, ctexts))
    okc, outc = build("SpecLean.Layer4.Gen.Cond")
    stc = {c for c, o in OPAQUE.items() if o.get("stmt")}
    full = [n for n in proved if not (ext_closure(m, n) & stc)]
    print("\nconditional %d / %d, full %d / %d (cond build %s)" % (
        len(proved) + len(ctexts), len(m.fns), len(full), len(m.fns), "ok" if okc else "FAILED"))
    print("on statements: " + ", ".join(sorted(set(proved) - set(full))))
    if not okc:
        print(outc[-3000:])
    # What fails even conditionally, ranked by the functions it blocks.
    done = set(proved) | set(ctexts) | set(OPAQUE)
    deps = {}
    for n in m.fns:
        for c in m.callees(n):
            deps.setdefault(c, set()).add(n)
    def blocked(c, seen):
        for d in deps.get(c, ()):
            if d not in seen and d not in done:
                seen.add(d)
                blocked(d, seen)
        return seen
    roots = {n: (cfails.get(n) or fails.get(n, "")) for n in m.fns if n not in done and
             not (cfails.get(n) or fails.get(n, "")).startswith("callee")}
    rank = sorted(roots, key=lambda n: -len(blocked(n, set())))
    print("\nfails even conditionally (callers blocked, first cause):")
    for n in rank:
        print("%3d %-45s %s" % (len(blocked(n, set())), n, roots[n].split("\n")[0][:90]))

if __name__ == "__main__":
    main()
