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

def param(m, i, pn, pt, sub=None):
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
    raise Unsupported("param type " + pt)


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

HEADER = """import SpecLean.Layer4.GenSteps
import SpecLean.Validation.Tactic
"""

OPEN = """
open SpecLean SpecLean.Encode SpecLean.Layer4 SpecLean.Rd SpecLean.Rd.Gen SpecLean.Layer4.GenSteps

attribute [local instance high] LibModel.toLibValues

set_option linter.unusedSimpArgs false
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
    out.append("")
    for n in m.rep_order:
        out.append("/-- The children of the decoded tree of a `%s`. -/" % n)
        out.append("def kids_%s (x : %s) : List DV :=\n  [%s]\n" % (n, n, ",\n    ".join(m.reps[n])))
        for i, r in enumerate(m.reps[n]):
            out.append("@[l4_simp] theorem kids_%s_%d (x : %s) : (kids_%s x)[%d]? = some %s :=\n  Eq.trans rfl rfl"
                       % (n, i, n, n, i, r))
        out.append("@[l4_simp] theorem kids_%s_len (x : %s) : (kids_%s x).length = %d :=\n  Eq.trans rfl rfl\n"
                   % (n, n, n, len(m.reps[n])))
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
    out.append("\nend SpecLean.Layer4.Gen\n")
    return "\n".join(out)


def build_reps(m):
    """The containers whose fields all have a DV form, in dependency order."""
    m.reps, m.rep_order = {}, []
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


def candidate(m, name, proved, sub=None):
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
    for i, (pn, pt) in enumerate(params):
        b, r, a = param(m, i, pn, pt, sub)
        bs.append(b)
        roots.append(r)
        rds.append(a)
        xs.append("a_" + pn)
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
    tag = "_" + sub if sub else ""
    D = depth(f["body"]) + 4 + max([proved[c] + 2 for c in m.callees(name)] + [0])
    rs = "[%s]" % ", ".join(roots)
    rs_out = rs_out or rs
    fp = "(fpsGen %d)" % f["id"] if w else "[]"
    unf = ["Scope.fn_" + name, name, "fpsGen", "fpAll"] + m.consts_of(name)
    thm = ("theorem %s_den%s (sha : Oracle) (m : Nat) %s :\n"
           "    ((den (Scope.env sha) fpsGen (m + %d)).fn %s Scope.fn_%s %s).map (Except.mapError SpecError.fail) =\n"
           "      some ((fun x : %s => (%s, %s)) <$> %s %s) := by\n"
           "  rw [s_fn]\n"
           "  l4_eval [%s]\n"
           "%s"
           % (name, tag, " ".join(bs), D, fp, name, rs, rt, enc, rs_out, name, " ".join(rds), ", ".join(unf),
              "" if os.environ.get("L4_NOCLOSE") else
              "  all_goals l4_dbg\n" if os.environ.get("L4_DBG") else "  all_goals l4_close\n"))
    call = ("@[l4_simp] theorem %s_call%s (sha : Oracle) (m : Nat) %s {γ : Type} (k : DRes × List DV → DM γ) :\n"
            "    Option.map (Except.mapError SpecError.fail)\n"
            "        (DM.bind ((den (Scope.env sha) fpsGen (m + %d)).fn %s Scope.fn_%s %s) k) =\n"
            "      callK (%s %s) fun x => Option.map (Except.mapError SpecError.fail) (k (%s, %s)) :=\n"
            "  bind_call (%s_den%s sha m %s) k\n"
            % (name, tag, " ".join(bs), D, fp, name, rs, name, " ".join(rds), enc, rs_out, name, tag, " ".join(xs)))
    return thm + "\n" + call, D


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
        fuel = dict(re.findall(r"theorem (\w+)_den \(sha : Oracle\) \(m : Nat\) .*?\(m \+ (\d+)\)\)\.fn",
                               (GEN / "Funcs.lean").read_text(), re.S)) if (GEN / "Funcs.lean").exists() else {}
        fuel = {k: int(v) for k, v in fuel.items()}
        pre = ("import SpecLean.Layer4.Gen.Funcs\n" if fuel else "import SpecLean.Layer4.Gen.Classes\n") + \
            OPEN + "\nnamespace SpecLean.Layer4.Gen\n\n"
        print(check(pre + candidate(m, args.show, fuel)[0] + "\nend SpecLean.Layer4.Gen\n", "show", True)[1])
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
                try:
                    cands[n + "@" + c] = candidate(m, n, proved, c)
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
