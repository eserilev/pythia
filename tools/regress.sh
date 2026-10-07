#!/bin/sh
# The quick regression (SPEC 11): build, value-rule probes, constructs, difftest, corpus repros
# and hazard tests. With --ef CASES_DIR, also the EF minimal cases with the sharing check and the
# readable Lean. One summary line per check; the exit status is 1 when any check fails.
#
# Usage: tools/regress.sh [--ef CASES_DIR] [--jobs N] [--timeout SECONDS]
# SPECS is the consensus-specs checkout with the pyspec environment (default ../consensus-specs-safe).
# Each build and run is capped at 8 GB (24 GB for the EF runners). EF uses EF_JOBS parallel runners
# (default 4) and stops a case after EF_TIMEOUT seconds (default 3600). The flags override them.

ROOT=$(cd "$(dirname "$0")/.." && pwd)
SPECS=${SPECS:-$ROOT/../consensus-specs-safe}
EF=""
EF_JOBS=${EF_JOBS:-4}
EF_TIMEOUT=${EF_TIMEOUT:-3600}
while [ $# -gt 0 ]; do
  case $1 in
    --ef) EF=$2; shift 2 ;;
    --jobs) EF_JOBS=$2; shift 2 ;;
    --timeout) EF_TIMEOUT=$2; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
export LEAN_NUM_THREADS=4
CAP="systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0"
LOG=$(mktemp -d)
FAILED=0

check() {  # check NAME COMMAND...: run, print one line, keep the log
  name=$1; shift
  if "$@" > "$LOG/$name.log" 2>&1; then status=pass; else status=FAIL; FAILED=1; fi
  echo "$status $name: $(tail -n 1 "$LOG/$name.log")"
}

pyspec() { (cd "$SPECS" && $CAP uv run python "$@"); }

cd "$ROOT" || exit 1
check build $CAP lake build SpecLean Tests efrunner pythiafuzz
check probes pyspec "$ROOT/tools/probes/value_rules.py"
check probes-check $CAP lake build Tests
check constructs pyspec "$ROOT/tools/constructs.py"
check difftest pyspec "$ROOT/tools/difftest.py"
check corpus $CAP uv run --project "$SPECS" python tools/fuzz/corpus_check.py
hazard() {
  (cd tools/fuzz && $CAP uv run --project "$SPECS" --with hypothesis python run.py --hazard-tests)
  s=$?
  echo "$(grep -c '^pass' "$LOG/hazard.log") of $(ls tools/fuzz/corpus/hazard/*.py | wc -l) hazard tests pass"
  return $s
}
check hazard hazard

if [ -n "$EF" ]; then
  BIN="$ROOT/.lake/build/bin/efrunner"
  efrun() {
    systemd-run --user --scope -q -p MemoryMax=24G -p MemorySwapMax=0 sh -c \
      "find '$EF' -name '*.case' | sort | xargs -P $EF_JOBS -I{} sh -c \"out=\\\$(timeout $EF_TIMEOUT $BIN --watch --readable {} | grep -E '^(PASS|FAIL|RD-|  HIT)'); [ -n \\\"\\\$out\\\" ] && echo \\\"\\\$out\\\" || echo 'FAIL {} timeout'\""
  }
  efrun > "$LOG/ef-raw.log" 2>&1
  n=$(find "$EF" -name '*.case' | wc -l)
  p=$(grep -c '^PASS' "$LOG/ef-raw.log")
  r=$(grep -c '^RD-PASS' "$LOG/ef-raw.log")
  hits=$(grep -c 'HIT' "$LOG/ef-raw.log")
  bad=$(grep -vc '^PASS\|^RD-PASS' "$LOG/ef-raw.log")
  if [ "$p" -eq "$n" ] && [ "$r" -eq "$n" ] && [ "$bad" -eq 0 ]; then status=pass; else status=FAIL; FAILED=1; fi
  echo "$status ef: $p of $n pass, readable $r of $n, $hits sharing hits"
fi

echo "logs in $LOG"
exit $FAILED
