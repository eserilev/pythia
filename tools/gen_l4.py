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

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
"""


def classes_file(m):
    out = [HEADER, "/-!\n# Layer 4: the rewrites of the readable classes\n\n"
           "Generated by tools/gen_l4.py. Do not edit.\n-/\n",
           "namespace SpecLean.Layer4.Gen\n", OPEN,
           "/-- Every path of length at most 6 under a root of class `ty`. -/",
           "def fpAll (ty : Name) : Footprint :=\n  [%s]\n" % ", ".join(
               "⟨ty, [%s]⟩" % ", ".join([".any"] * k) for k in range(7)),
           "/-- The footprints: a function that returns its updated argument may write anywhere under it. -/",
           "def fpsGen : Name → Footprint\n%s  | _ => []\n" % "".join(
               "  | %d => fpAll %d\n" % (m.fns[n]["id"], m.cid[w]) for n, w in sorted(writers(m).items()))]
    for c in sorted(m.uint):
        out.append("@[l4_simp] theorem uv_%s (y : %s) : UintC.val y = y.val :=\n  Eq.trans rfl rfl" % (c, c))
        out.append("@[l4_simp] theorem ub_%s : UintC.bits %s = %d :=\n  Eq.trans rfl rfl" % (c, c, m.uint[c]))
        out.append("@[l4_simp] theorem uo_%s (n : Nat) : (UintC.ofNat n : %s) = ⟨n⟩ :=\n  Eq.trans rfl rfl" % (c, c))
    for c in sorted(m.bytes):
        out.append("@[l4_simp] theorem bd_%s (y : %s) : BytesC.data y = y.data :=\n  Eq.trans rfl rfl" % (c, c))
        out.append("@[l4_simp] theorem bl_%s : BytesC.len %s = %d :=\n  Eq.trans rfl rfl" % (c, c, m.bytes[c]))
    for c, rhs in re.findall(r"^instance : PyOrd (\w+) := ⟨fun a b => (decide \(a\.val < b\.val\))⟩", m.rd, re.M):
        out.append("@[l4_simp] theorem po_%s (a b : %s) : PyOrd.lt a b = decide (a.val < b.val) := Eq.trans rfl rfl"
                   % (c, c))
    cfg = m.rd[m.rd.index("def Cfg.default : Cfg where"):]
    cfg = cfg[:cfg.index("\n\n")]
    for f, v in re.findall(r"^  (\w+) := (.+)$", cfg, re.M):
        out.append("@[l4_simp] theorem cfg_%s : @Cfg.%s Cfg.default = %s := Eq.trans rfl rfl" % (f, f, v))
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
    out.append("\nend SpecLean.Layer4.Gen\n")
    return "\n".join(out)


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
    if mp and m.ids.get(int(mp.group(1))) == "enumerate" and int(mp.group(2)) in pids:
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
    j = rd.find(".filterMapM fun")
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
    k = j + len(".filterMapM ")
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
                 len=LEN, depth=depth_text(c))]


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
        ls = "⟨%d, [%s], true⟩" % (cp["k"], ", ".join(str(x) for x in cp["path"]))
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
        rhs = ("callK ((%s).drop i |>.filterMapM %s)\n"
               "        fun ys => Option.map (Except.mapError SpecError.fail) (K (ys.map fun y => %s))"
               % (X, cp["F"], cp["enc"]))
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
            "    simp (disch := (simp only [List.length_map, List.length_zipIdx]; omega)) only\n"
            "      [List.getElem?_eq_none, List.drop_eq_nil_of_le, Option.map_none, List.filterMapM_nil]\n"
            "    all_goals (try l4_eval [List.map_nil])\n"
            "    all_goals l4_close\n"
            "  | succ k ih =>\n"
            "    intro i n B hk hn %s γ K\n"
            "    obtain ⟨n', rfl⟩ : ∃ n', n = n' + %d := ⟨n - %d, by omega⟩\n"
            "    rw [show n' + %d = (n' + %d) + 1 from rfl, s_items]\n"
            "    have hi : i < %s := by omega\n"
            "    rw [List.drop_eq_getElem_cons (by simp only [List.length_map, List.length_zipIdx]; omega)]\n"
            "    simp only [itemsStep]\n"
            "    l4_eval [bindLoop, ifsOf, fpsGen, fpAll, List.getElem?_eq_getElem hi, hi, %s%s, List.getElem_map,\n"
            "      List.getElem_zipIdx, List.filterMapM_cons, List.map_cons, List.cons_append, List.nil_append]\n"
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
        for mm in re.finditer(r"\b%s((?:\s+\(?\w+\)?)+)" % re.escape(c), body):
            args = [a.strip("()") for a in mm.group(1).split()]
            for pos, fld in LENS_OF[c]:
                if pos >= len(args) or args[pos] not in pnames:
                    raise Unsupported("callee fuel through a local")
                item = (pnames.index(args[pos]), fld)
                if item not in out:
                    out.append(item)
    return out


def hok_binder(m, pn, pt):
    """The range hypothesis of parameter `pn : pt` in `ok` mode, or None."""
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


def candidate(m, name, proved, sub=None, isub=False, ok=False):
    """The theorems of `name` (its `_den` and `_call`) and its fuel, or Unsupported. `proved` maps
    each proved function to its fuel."""
    if name not in m.sigs:
        raise Unsupported("signature")
    params, rt = m.sigs[name]
    f = m.fns[name]
    if len(params) != len(f["params"]):
        raise Unsupported("params")
    if f["defaults"] or f["vararg"] != "none":
        raise Unsupported("defaults")
    for c in m.callees(name):
        if c not in proved:
            raise Unsupported("callee " + c)
    bs, roots, rds, xs = [], [], [], []
    hoks = []
    for i, (pn, pt) in enumerate(params):
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
    if sub and any(ctor(st)[0] == "forStmt" for st in f["body"][1]):
        raise Unsupported("variant with a loop")
    tag = ("_" + sub if sub else "") + ("_i" if isub else "")
    D = depth(f["body"]) + 4 + max([proved[c] + 2 for c in m.callees(name)] + [0])
    items = [(lp["k"], lp["path"] and lp["len"].split(".")[-2] or None) for lp in lps + cps]
    for it in callee_lens(m, name, params):
        if it not in items:
            items.append(it)
    LENS = "".join(("%s.%s.length + " % (rds[k], fld)) if fld else ("%s.length + " % rds[k]) for k, fld in items)
    fcalls = ["%s_fcall" % c for c in m.callees(name) if LENS_OF.get(c)]
    if lps or cps:
        D += 6
    rs = "[%s]" % ", ".join(roots)
    rs_out = rs_out or rs
    fp = "(fpsGen %d)" % f["id"] if w else "[]"
    unf = ["Scope.fn_" + name, name, "fpsGen", "fpAll"] + m.consts_of(name)
    if rt in m.reps and ("theorem kids_%s_mk" % rt) in classes_file_cache(m):
        unf.append("kids_%s_mk" % rt)
    loopstep = ""
    if lps or fcalls or cps:
        loopstep = ("  all_goals (repeat (first | (simp (disch := l4_disch) only [%s]) |\n"
                    "    ((l4_bycases <;> (try l4_eval_star)))))\n  all_goals (try l4_eval)\n"
                    % ", ".join(["%s_loop%d_call" % (name, j + 1) for j in range(len(lps))] + fcalls +
                                ["%s_items_call" % name for _ in cps]))
    thm = ("theorem %s_den%s (sha : Oracle) (m : Nat) %s :\n"
           "    ((den (Scope.env sha) fpsGen (%sm + %d)).fn %s Scope.fn_%s %s).map (Except.mapError SpecError.fail) =\n"
           "      some ((fun x : %s => (%s, %s)) <$> %s %s) := by\n"
           "  rw [s_fn]\n"
           "%s"
           "  l4_eval [%s]\n"
           "%s%s"
           % (name, tag, " ".join(bs), LENS, D, fp, name, rs, rt, enc, rs_out, name, " ".join(rds),
              ("  simp only [%s] at %s\n" % (", ".join("ok_" + n for n in m.rep_order), " ".join(hoks)))
              if hoks else "", ", ".join(unf), loopstep,
              "" if os.environ.get("L4_NOCLOSE") else
              "  all_goals l4_dbg\n" if os.environ.get("L4_DBG") else "  all_goals l4_close\n"))
    call = ("@[l4_simp] theorem %s_call%s (sha : Oracle) (m : Nat) %s {γ : Type} (k : DRes × List DV → DM γ) :\n"
            "    Option.map (Except.mapError SpecError.fail)\n"
            "        (DM.bind ((den (Scope.env sha) fpsGen (%sm + %d)).fn %s Scope.fn_%s %s) k) =\n"
            "      callK (%s %s) fun x => Option.map (Except.mapError SpecError.fail) (k (%s, %s)) :=\n"
            "  bind_call (%s_den%s sha m %s) k\n"
            % (name, tag, " ".join(bs), LENS, D, fp, name, rs, name, " ".join(rds), enc, rs_out, name, tag, " ".join(xs)))
    if LENS:
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
    if not sub:
        LENS_OF[name] = items
    out = ((loop_theorems(m, name, params, bs, roots, rds, xs, lps) + "\n" if lps else "") +
           (comp_theorems(m, name, params, bs, roots, rds, xs, cps) + "\n" if cps else "") + thm + "\n" + call)
    if not sub:
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
    hw = " (hw : WTree h %s %s)" % (VS, fp) if w else ""
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
    return ("theorem %s_l4 (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h) %s %s%s :\n"
            "    ∀ fuel, %s%d ≤ fuel →\n"
            "      ResultMatches gfp %s h %s %s\n"
            "        (interp (Scope.env sha) fuel Scope.Id.«%s» %s h) (%s %s) := by\n"
            "  intro fuel hf\n"
            "  have hden := %s_den sha 0 %s\n"
            "  simp only [Nat.add_zero, Nat.zero_add] at hden\n"
            "  exact GenWrap.l4_mono hf (GenWrap.l4_wrap (by simp only [env_globals, Validation.Tactic.lookup_lit])\n"
            "    hwf %s %s hden %s)\n"
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
    return ("\ntheorem %s_l4r (sha : Oracle) (gfp : Footprint) (h : Heap) (hwf : HeapWF h)\n"
            "    (hc : GenBridge.ContWF h) %s %s%s :\n"
            "    ∀ fuel, %s%d ≤ fuel →\n"
            "      ResultMatches gfp %s h %s %s\n"
            "        (interp (Scope.env sha) fuel Scope.Id.«%s» %s h) (%s %s) :=\n"
            "  %s_l4 sha gfp h hwf %s %s%s\n"
            % (name, " ".join(bs), hyps, hw, LENS, D, fp, VS, E, name, VS, name, " ".join(rds),
               name, " ".join(xs), args, " hw" if hw else ""))


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


def funcs_file(m, proved, texts, total):
    body = ["import SpecLean.Layer4.Gen.Classes\n",
            "/-!\n# Layer 4: the generated theorems\n\nGenerated by tools/gen_l4.py. Do not edit. "
            "The generator proves %d of the %d functions.\n-/\n" % (len(proved), total),
            "namespace SpecLean.Layer4.Gen\n", OPEN]
    for n in order(m, set(proved)):
        body.append(texts[n])
    body.append("end SpecLean.Layer4.Gen\n")
    return "\n".join(body)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--show", default="", help="check one function and print the whole output")
    args = ap.parse_args()
    m = model()
    GEN.mkdir(parents=True, exist_ok=True)
    (GEN / "Classes.lean").write_text(classes_file(m))
    ok, out = build("SpecLean.Layer4.Gen.Classes")
    if not ok:
        print(out)
        sys.exit(1)
    if args.show:
        # Against the proved functions of the last run.
        fuel = dict(re.findall(r"theorem (\w+)_den \(sha : Oracle\) \(m : Nat\) .*?m \+ (\d+)\)\)\.fn",
                               (GEN / "Funcs.lean").read_text(), re.S)) if (GEN / "Funcs.lean").exists() else {}
        fuel = {k: int(v) for k, v in fuel.items()}
        for n in order(m, set(fuel)):
            try:
                candidate(m, n, fuel)
            except Unsupported:
                pass
        pre = ("import SpecLean.Layer4.Gen.Funcs\n" if fuel else "import SpecLean.Layer4.Gen.Classes\n") + \
            OPEN + "\nnamespace SpecLean.Layer4.Gen\n\n"
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
            cs = [c for c in m.callees(n) if c in names]
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
        pre = "import SpecLean.Layer4.Gen.Funcs\n" + OPEN + "\nnamespace SpecLean.Layer4.Gen\n\n"
        cands = {}
        for n in ready:
            try:
                cands[n] = candidate(m, n, proved)
            except Unsupported as e:
                fails[n] = "unsupported: " + str(e)
                continue
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


if __name__ == "__main__":
    main()
