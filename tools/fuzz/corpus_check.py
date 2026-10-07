"""Run every corpus repro (`corpus/*.py` and `corpus/fixed/*.py`) in CPython and in the
interpreter. Each must give one result and no hazard miss. Exit status 1 on a failure.

    uv run --project ../consensus-specs-safe python tools/fuzz/corpus_check.py
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import harness as H  # noqa: E402

CORPUS = Path(__file__).resolve().parent / "corpus"

lean = H.LeanRunner()
files = [f for f in sorted(CORPUS.glob("**/*.py")) if f.parent.name != "hazard"]
bad = 0
for f in files:
    o = H.run_case(f.read_text(), lean, copy=True)
    if o.py != o.lean or o.hazard_miss:
        bad += 1
        print(f"FAIL {f.name}\n  python: {o.py[:200]}\n  lean:   {o.lean[:200]}")
lean.close()
print(f"{len(files) - bad} of {len(files)} corpus repros pass")
sys.exit(1 if bad else 0)
