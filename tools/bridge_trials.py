"""Run the bridge trial files (one theorem each) and list the ones that pass.

    python3 tools/bridge_trials.py TRIALS_DIR [--jobs 3] [--timeout 1200]

Each trial runs as `lake env lean` in Bridge/, under a 6 GB memory cap. It passes when Lean exits
with 0 and prints no `sorry` warning. The script writes TRIALS_DIR/proved.txt and one log per
trial.
"""

import argparse
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run(f, timeout):
    cmd = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0",
           "timeout", str(timeout), "lake", "env", "lean", str(f)]
    r = subprocess.run(cmd, cwd=ROOT / "Bridge", capture_output=True, text=True,
                       env={**__import__("os").environ, "LEAN_NUM_THREADS": "4"})
    out = r.stdout + r.stderr
    if len(out) > 20000:
        out = out[:8000] + "\n[...]\n" + out[-12000:]
    f.with_suffix(".log").write_text(out)
    ok = r.returncode == 0 and "sorry" not in out and "error" not in out
    return f.stem, ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--only", default=None)
    args = ap.parse_args()
    d = Path(args.dir)
    files = sorted(d.glob("*.lean"))
    if args.only:
        files = [f for f in files if f.stem in args.only.split(",")]
    with ThreadPoolExecutor(args.jobs) as ex:
        res = list(ex.map(lambda f: run(f, args.timeout), files))
    proved = sorted(n for n, ok in res if ok)
    (d / "proved.txt").write_text("\n".join(proved) + "\n")
    print(f"{len(proved)} of {len(res)} pass")


if __name__ == "__main__":
    main()
