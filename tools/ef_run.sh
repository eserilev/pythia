#!/bin/sh
# Run the EF case files, one process per case, in parallel. One line per case, then the hits
# of the write condition check when FLAGS has --watch.
# Usage: tools/ef_run.sh CASES_DIR [SECONDS_PER_CASE] [FLAGS] [RUNNER] > log
# RUNNER is efrunner (minimal, the default) or efrunner-mainnet.
DIR=$1
LIMIT=${2:-600}
FLAGS=$3
BIN=$(cd "$(dirname "$0")/.." && pwd)/.lake/build/bin/${4:-efrunner}
find "$DIR" -name '*.case' | sort | xargs -P "$(nproc)" -I{} sh -c \
  "out=\$(timeout $LIMIT $BIN $FLAGS {} | grep -E '^(PASS|FAIL|  HIT)'); [ -n \"\$out\" ] && echo \"\$out\" || echo 'FAIL {} timeout after ${LIMIT}s'"
