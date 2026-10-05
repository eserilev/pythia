"""Generate the validation theorems (SPEC 9.2) of the readable Lean and keep the ones that the
tactic proves.

Run from the consensus-specs checkout, in its uv environment:

    cd ../consensus-specs-safe
    uv run python ../consensus-specs-lean/tools/gen_valid.py --tier leaves

It writes one candidate theorem per function of the tier, checks each with `lake env lean` in
parallel, and writes the proved ones to `SpecLean/Validation/Gen/<Tier>.lean`. It prints the
count and the reason of each failure.
"""

import argparse
import ast
import concurrent.futures
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rd_emit  # noqa: E402
import rd_fn  # noqa: E402
import rd_types as T  # noqa: E402
import serialize as S  # noqa: E402
import translate  # noqa: E402

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

HEADER = """import SpecLean.Gen.Readable
import SpecLean.Validation.Tactic
import SpecLean.Validation.Steps
"""

PRELUDE = """
namespace SpecLean.Validation.Gen

open SpecLean SpecLean.Rd SpecLean.Rd.Gen SpecLean.Encode SpecLean.Validation.Tactic
open SpecLean.Validation.Steps

variable (sha : Oracle) [Spec]

attribute [local instance] Cfg.default

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

-- `whnf` of a result would evaluate a range check on a literal in unary.
attribute [local irreducible] ResultMatches
"""

FOOTER = "\nend SpecLean.Validation.Gen\n"


class Unsupported(Exception):
    pass


def classify(fns):
    """`loops`, `whiles` and the spec callees of each function."""
    out = {}
    for n, t in fns.items():
        loops = any(isinstance(x, (ast.For, ast.While, ast.comprehension)) for x in ast.walk(t))
        whiles = any(isinstance(x, ast.While) for x in ast.walk(t))
        calls = sorted(c for c in S.free_names(t) if c in fns and c != n)
        out[n] = dict(loops=loops, whiles=whiles, calls=calls)
    return out


class Gen:
    def __init__(self, b, em):
        self.b, self.em, self.n = b, em, b.names

    def arg(self, j, t):
        """The binder, the interpreter value and the readable value of argument `j`."""
        x = f"x{j}"
        k = t[0]
        if k == "uint":
            ty = translate.uint_ty_term(self.n, t[1])
            return f"({x} : Nat)", f"(.uint {ty} {x})", f"(⟨{x}⟩ : {self.n.cls(t[1])})"
        if k == "bytesN":
            return (f"({x} : List UInt8)", f"(.bytes Scope.Id.«{self.n.scope(t[1])}» {x})",
                    f"(⟨{x}⟩ : {self.n.cls(t[1])})")
        if k == "bool":
            return f"({x} : Bool)", f"(.bool {x})", x
        if k == "int":
            return f"({x} : Int)", f"(.int {x})", x
        if k == "boolean":
            return f"({x} : Bool)", f"(.boolean {x})", f"(⟨{x}⟩ : Boolean)"
        if k == "bytes":
            return f"({x} : List UInt8)", f"(.bytes 0 {x})", x
        raise Unsupported(f"argument type {k}")

    def expect(self, t):
        """`Expect r h' v` of a pure function with return type `t`, and its simp names."""
        k = t[0]
        if k in ("uint", "bytesN"):
            c = self.n.cls(t[1])
            return f"(v, h') = enc_{c} r h", [f"enc_{c}", "encUint", "encBytesN"]
        if k == "bool":
            return "v = .bool r ∧ h' = h", []
        if k == "int":
            return "v = .int r ∧ h' = h", []
        if k == "boolean":
            return "v = .boolean r.val ∧ h' = h", []
        if k == "bytes":
            return "v = .bytes 0 r ∧ h' = h", []
        if k == "none":
            return "v = .none ∧ h' = h", []
        raise Unsupported(f"return type {k}")

    def theorem(self, name, sig, tree):
        if sig.mutated:
            raise Unsupported("mutates an argument")
        if any(t[0] in ("tvar", "utvar") for _, t in sig.params):
            raise Unsupported("generic")
        args = [self.arg(j, t) for j, (_, t) in enumerate(sig.params)]
        ret = sig.ret
        rt = self.em.lean_param(ret) if ret != T.NONE else "Unit"
        exp, encs = self.expect(ret)
        binders = " ".join(a[0] for a in args)
        vs = "[" + ", ".join(a[1] for a in args) + "]"
        rargs = " ".join(a[2] for a in args)
        free = S.free_names(tree)
        consts = [T.ident(c) for c in sorted(free) if c in self.b.consts]
        cfg = sorted({n.attr for n in ast.walk(tree) if isinstance(n, ast.Attribute) and
                      isinstance(n.value, ast.Name) and n.value.id == "config"} |
                     {c for c in free if c in self.b.config_vars})
        defs = ([f"Scope.fn_{name}", T.ident(name), "Scope.env", "Scope.knownNames"] + consts + [f"Cfg.{c}" for c in cfg] +
                (["Cfg.default"] if cfg else []) + encs)
        fname = T.ident(name)
        return f"""
theorem {name}_valid (h : Heap) {binders} :
    ∃ N, ∀ fuel ≥ N,
      ResultMatches [] h {vs} (fun (r : {rt}) h' v => {exp})
        (interp (Scope.env sha) fuel Scope.Id.«{name}» {vs} h)
        ({fname} {rargs}) := by
  refine ⟨64, fun fuel hf => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  clear hf
  simp [rd_simp, lookup_lit, unfold_known, {", ".join(defs)}]
  repeat' (rd_split <;> (try rd_step))
  all_goals rd_finish
"""


def check(name, text, workdir):
    """Compile one candidate. Returns (name, ok, seconds, first error line)."""
    f = Path(workdir) / f"{name}.lean"
    f.write_text(HEADER + PRELUDE + text + FOOTER)
    t0 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=ROOT, capture_output=True,
                           text=True, timeout=600)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and "error" not in out and "sorry" not in out
    except subprocess.TimeoutExpired:
        out, ok = "timeout", False
    err = next((ln.split(".lean:", 1)[-1] for ln in out.splitlines() if "error" in ln), out[:200])
    return name, ok, time.time() - t0, err


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default="889a389f9")
    ap.add_argument("--preset", default="minimal")
    ap.add_argument("--tier", default="leaves", choices=["leaves"])
    ap.add_argument("--only", default=None)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    commit, spec_object, sources, spec, fns, sources_text, _ = S.load_scope(
        args.rev, "gloas", args.preset, translate.scope_roots())
    names = T.Names(spec)
    b = translate.Build(spec, fns, names)
    b.sources, b.sources_text, b.config_vars = sources, sources_text, spec_object.config_vars
    em = rd_emit.Emitter(b)
    em.collect()
    em.emit_constants()
    em.emit_config()
    em.build_sigs()
    cls = classify(fns)
    if args.tier == "leaves":
        tier = sorted(n for n, c in cls.items() if not c["loops"] and not c["calls"])
    if args.only:
        tier = [n for n in tier if n in args.only.split(",")]
    g = Gen(b, em)
    cands, skipped = {}, {}
    for n in tier:
        try:
            cands[n] = g.theorem(n, em.sigs[n], fns[n])
        except (Unsupported, S.Unsupported, ValueError) as e:
            skipped[n] = f"no statement: {e}"
    work = tempfile.mkdtemp(prefix="gen-valid-")
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        results = list(ex.map(lambda kv: check(kv[0], kv[1], work), cands.items()))
    proved = sorted(n for n, ok, _, _ in results if ok)
    failed = {n: e for n, ok, _, e in results if not ok}
    secs = {n: round(s, 1) for n, _, s, _ in results}
    out = Path(args.out) if args.out else ROOT / "SpecLean/Validation/Gen" / (
        args.tier.capitalize() + ".lean")
    out.parent.mkdir(parents=True, exist_ok=True)
    body = "".join(cands[n] for n in proved)
    doc = (f"\n/-!\n# Validation theorems: {args.tier}\n\nGenerated by tools/gen_valid.py. "
           f"Do not edit. The tactic proves {len(proved)} of the {len(tier)} functions of the "
           f"tier.\n-/\n")
    out.write_text(f"-- Generated by tools/gen_valid.py. Do not edit.\n{HEADER}{doc}{PRELUDE}"
                   f"{body}{FOOTER}")
    print(f"tier {args.tier}: {len(proved)}/{len(tier)} proved, wrote {out}")
    for n in sorted(skipped):
        print(f"  SKIP {n}: {skipped[n]}")
    for n in sorted(failed):
        print(f"  FAIL {n} ({secs[n]}s): {failed[n][:160]}")
    for n in proved:
        print(f"  OK {n} ({secs[n]}s)")
    json.dump({"proved": proved, "failed": failed, "skipped": skipped, "secs": secs},
              open(Path(work) / "result.json", "w"), indent=1)
    print(f"candidates in {work}")


if __name__ == "__main__":
    main()
