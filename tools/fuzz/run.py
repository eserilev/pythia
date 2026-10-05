"""Differential fuzzing of the interpreter against CPython (SPEC 11, item 2).

Run from this repository, in the pyspec environment with Hypothesis added:

    lake build pythiafuzz
    uv run --project ../consensus-specs-safe --with hypothesis \
        python tools/fuzz/run.py --n 2000

Each round runs Hypothesis until it finds a difference with a new signature, shrinks it, and
saves the minimal case to `tools/fuzz/corpus/`. Known signatures (from the corpus and from
`--ignore`) count as a pass, so the next round looks for a different difference. A corpus file
is a runnable case: `python tools/fuzz/harness.py tools/fuzz/corpus/<file>.py`. `corpus/fixed/`
holds the differences that the interpreter has fixed, and `corpus/hazard/` the hand-written
programs for the write condition check (`--hazard-tests`).
"""

import argparse
import ast
import hashlib
import re
import sys
import time
from pathlib import Path

from hypothesis import HealthCheck, Phase, assume, given, settings

import gen as G
import harness as H

CORPUS = Path(__file__).resolve().parent / "corpus"
TOKEN = re.compile(r"[,|{}\[\]()= ]+")


def kind(out: str) -> str:
    if out.startswith("ok "):
        return "ok"
    if out.startswith("err "):
        return out.split(" ")[1]
    return out.split(" ")[0]


def tok_kind(t: str) -> str:
    if t.startswith("#"):
        return "label"
    return t.split(":")[0] if ":" in t else t


def signature(py: str, lean: str) -> str:
    """A coarse name of a difference: the two outcomes, and for two `ok` results, the kinds of
    the first tokens that differ."""
    a, b = kind(py), kind(lean)
    if a == "ok" and b == "ok":
        ta, tb = TOKEN.split(py), TOKEN.split(lean)
        for x, y in zip(ta, tb):
            if x != y:
                return f"ok-ok {tok_kind(x)}/{tok_kind(y)}"
        return "ok-ok length"
    return f"{a} / {b}"


def classify(o: H.Outcome) -> str | None:
    """The signature of a finding, or `None`. A finding is a difference between CPython and
    the interpreter, or a hazard miss: CPython differs from the copy-on-store model and the
    write condition check has no hit."""
    if o.py != o.lean:
        return signature(o.py, o.lean)
    if o.hazard_miss:
        return "hazard-miss " + kind(o.py)
    return None


def known_signatures() -> set[str]:
    out = set()
    for f in CORPUS.glob("*.py"):
        for line in f.read_text().splitlines():
            if line.startswith("# signature: "):
                out.add(line.removeprefix("# signature: "))
    return out


def header(sig: str, o: H.Outcome) -> str:
    lines = [f"# signature: {sig}", f"# python: {o.py}", f"# lean:   {o.lean}"]
    lines += [f"# hit:    {h}" for h in o.hits]
    if o.copy_differs:
        lines.append(f"# copy-on-store model: {o.py_copy}")
    return "\n".join(lines) + "\n\n"


def save_to(d: Path, sig: str, src: str, o: H.Outcome, n: int):
    slug = re.sub(r"[^A-Za-z0-9]+", "_", sig).strip("_")[:60]
    (d / f"{slug}_{n}.py").write_text(header(sig, o) + src)


def save(sig: str, src: str, o: H.Outcome) -> Path:
    slug = re.sub(r"[^A-Za-z0-9]+", "_", sig).strip("_")[:60]
    h = hashlib.sha256(src.encode()).hexdigest()[:8]
    path = CORPUS / f"{slug}_{h}.py"
    path.write_text(header(sig, o) + src)
    return path


def hazard_tests(lean) -> int:
    """Run `corpus/hazard/*.py`. Each file says `# expect-hit: TEXT` (a hit that contains
    TEXT) or `# expect-no-sharing-hit`. CPython and the interpreter must also agree."""
    bad = 0
    for f in sorted((CORPUS / "hazard").glob("*.py")):
        src = f.read_text()
        first = src.splitlines()[0]
        o = H.run_case(src, lean, copy=True)
        if first.startswith("# expect-hit: "):
            want = first.removeprefix("# expect-hit: ")
            ok = any(want in h for h in o.hits)
        else:
            ok = not o.sharing_hits
        ok = ok and o.py == o.lean and not o.hazard_miss
        bad += not ok
        print(f"{'pass' if ok else 'FAIL'} {f.name}: {first[2:]}")
        for h in o.hits:
            print(f"       hit {h}")
    return bad


def blocks(lines):
    """Each removable unit: a line with its indented children. `mk`, `tr`, `grow` and `each` stay."""
    out = []
    keep = False
    for i, line in enumerate(lines):
        if line.startswith("def "):
            keep = line.startswith(("def mk", "def tr", "def grow", "def each"))
        if keep or not line.strip():
            continue
        ind = len(line) - len(line.lstrip())
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or
                                  len(lines[j]) - len(lines[j].lstrip()) > ind):
            j += 1
        out.append((i, j))
    return out


def minimize(src: str, sig: str, lean) -> str:
    """Delete statements and functions while the signature stays the same. A body that loses
    its last statement gets `pass`."""
    def same(cand):
        try:
            ast.parse(cand)
            o = H.run_case(cand, lean, copy=True)
        except Exception:  # noqa: BLE001
            return False
        return classify(o) == sig

    changed = True
    while changed:
        changed = False
        lines = src.split("\n")
        for i, j in reversed(blocks(lines)):
            ind = len(lines[i]) - len(lines[i].lstrip())
            for cand_lines in (lines[:i] + lines[j:], lines[:i] + [" " * ind + "pass"] + lines[j:]):
                cand = "\n".join(cand_lines)
                if cand != src and same(cand):
                    src = cand
                    changed = True
                    break
            if changed:
                break
    return src


class Stats:
    def __init__(self):
        self.runs = 0
        self.generated = 0
        self.skipped = 0
        self.same = 0
        self.seconds = 0.0
        self.outcomes: dict[str, int] = {}
        self.known_hits: dict[str, int] = {}
        self.lean_hit = 0
        self.copy_differs = 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2000, help="programs to generate in total")
    ap.add_argument("--ignore", action="append", default=[], help="signature to treat as known")
    ap.add_argument("--max-rounds", type=int, default=30)
    ap.add_argument("--samples", default=None,
                    help="directory for up to 5 unshrunk examples of each known signature")
    ap.add_argument("--avoid", default="", help="comma-separated names from gen.AVOID")
    ap.add_argument("--hazard-tests", action="store_true",
                    help="run the hand-written hazard programs in corpus/hazard and stop")
    args = ap.parse_args()
    G.AVOID |= {a for a in args.avoid.split(",") if a}

    CORPUS.mkdir(exist_ok=True)
    known = known_signatures() | set(args.ignore)
    lean = H.LeanRunner()
    if args.hazard_tests:
        bad = hazard_tests(lean)
        lean.close()
        sys.exit(1 if bad else 0)
    stats = Stats()
    found = []

    class Diff(Exception):
        def __init__(self, sig, src):
            super().__init__(sig)
            self.sig, self.src = sig, src

    start = time.perf_counter()
    for _ in range(args.max_rounds):
        budget = args.n - stats.generated
        if budget <= 0:
            break
        shrinking = [False]

        @settings(max_examples=budget, database=None, deadline=None,
                  suppress_health_check=list(HealthCheck), report_multiple_bugs=False,
                  phases=[Phase.generate, Phase.shrink], print_blob=False)
        @given(G.cases())
        def test(src):
            t0 = time.perf_counter()
            stats.runs += 1
            try:
                o = H.run_case(src, lean, copy=True)
            except (H.Timeout, H.serialize.Unsupported):
                stats.skipped += 1
                assume(False)
            if not shrinking[0]:
                stats.generated += 1
                stats.seconds += time.perf_counter() - t0
                stats.outcomes[kind(o.py)] = stats.outcomes.get(kind(o.py), 0) + 1
                stats.lean_hit += bool(o.sharing_hits)
                stats.copy_differs += o.copy_differs
            sig = classify(o)
            if sig is None:
                if not shrinking[0]:
                    stats.same += 1
                return
            if sig in known:
                if not shrinking[0]:
                    n = stats.known_hits.get(sig, 0)
                    stats.known_hits[sig] = n + 1
                    if args.samples and n < 5:
                        d = Path(args.samples)
                        d.mkdir(parents=True, exist_ok=True)
                        save_to(d, sig, src, o, n)
                return
            shrinking[0] = True
            raise Diff(sig, src)

        try:
            test()
        except Diff as d:
            known.add(d.sig)
            src = minimize(d.src, d.sig, lean)
            path = save(d.sig, src, H.run_case(src, lean, copy=True))
            found.append((d.sig, path))
            print(f"new difference [{d.sig}] -> {path.name}", flush=True)
            continue
        break

    lean.close()
    wall = time.perf_counter() - start
    rate = stats.generated / stats.seconds if stats.seconds else 0
    print(f"generated {stats.generated} programs ({stats.skipped} skipped), "
          f"{stats.same} same, {rate:.1f} programs/s (run time only), "
          f"{stats.generated / wall:.1f} programs/s (wall, with generation and shrinking), "
          f"{stats.runs} runs with shrinking")
    print("CPython outcomes:", dict(sorted(stats.outcomes.items(), key=lambda kv: -kv[1])))
    print(f"Lean outcome hit (a sharing hit of the write condition check): {stats.lean_hit}; "
          f"CPython differs from the copy-on-store model: {stats.copy_differs}")
    print("known signatures seen:", stats.known_hits)
    for sig, path in found:
        print(f"  {sig}: {path.name}")
    sys.exit(1 if found else 0)


if __name__ == "__main__":
    main()
