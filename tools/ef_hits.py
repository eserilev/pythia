"""Summarize a run log of tools/ef_run.sh: counts per runner and handler, failures, and the hits
of the write condition check, with the spec lines of each write.

    python3 tools/ef_hits.py RUN_LOG [SCOPE_FP]

`SCOPE_FP` is the write site list of the serializer (default `SpecLean/Gen/Scope.fp`).
"""

import re
import sys
from collections import defaultdict
from pathlib import Path


def main():
    log = Path(sys.argv[1]).read_text().splitlines()
    fp_path = Path(sys.argv[2]) if len(sys.argv) > 2 else (
        Path(__file__).resolve().parent.parent / "SpecLean/Gen/Scope.fp")
    sites = defaultdict(list)
    for line in fp_path.read_text().splitlines():
        if line.startswith("WRITE "):
            _, where, pattern = line.split(" ")
            fn, src, ln = where.rsplit(":", 2)
            sites[(fn, pattern)].append(f"{src}:{ln}")

    counts = defaultdict(lambda: [0, 0])
    fails = []
    hits = defaultdict(lambda: [0, set()])
    for line in log:
        m = re.match(r"^(PASS|FAIL) (\S+)", line)
        if m:
            case = m.group(2)
            group = "/".join(case.split("/")[:2]) if not case.startswith("/") else "?"
            counts[group][0 if m.group(1) == "PASS" else 1] += 1
            if m.group(1) == "FAIL":
                fails.append(line)
            continue
        m = re.match(r"^  HIT (\S+): (.*) \(x(\d+)\)$", line)
        if m:
            case, msg, n = m.groups()
            hits[msg][0] += int(n)
            hits[msg][1].add(case)

    for g in sorted(counts):
        p, f = counts[g]
        print(f"{g}: {p} pass, {f} fail")
    for line in fails:
        print(line)
    for msg in sorted(hits):
        n, cases = hits[msg]
        lines = ""
        m = re.match(r"^(write|FP miss) (\S+): (\S+)", msg)
        if m:
            pattern = re.sub(r"^\w+", lambda r: r.group(0), m.group(3))
            lines = " at " + ", ".join(sites.get((m.group(2), pattern), ["?"]))
        print(f"HIT {msg}{lines}: {n} times in {len(cases)} cases, e.g. {sorted(cases)[0]}")


if __name__ == "__main__":
    main()
