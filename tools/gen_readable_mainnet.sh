#!/bin/sh
# Generate the readable Lean of the mainnet preset for the bridge:
# Bridge/Bridge/Mainnet/Readable.lean, namespace SpecLean.Rd.GenMainnet, on SpecLean.Gen.ScopeMainnet.
# tools/translate.py writes the minimal module layout; this script renames the namespace and the scope.
# Run from the consensus-specs checkout: gen_readable_mainnet.sh
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT="$HERE/../Bridge/Bridge/Mainnet/Readable.lean"
mkdir -p "$(dirname "$OUT")"
uv run python "$HERE/translate.py" --preset mainnet --out "$OUT.tmp"
sed -e 's/^import SpecLean.Gen.Scope$/import SpecLean.Gen.ScopeMainnet/' \
    -e 's/\bScope\.Id\./ScopeMainnet.Id./g' \
    -e 's/^namespace SpecLean.Rd.Gen$/namespace SpecLean.Rd.GenMainnet/' \
    -e 's/^end SpecLean.Rd.Gen$/end SpecLean.Rd.GenMainnet/' \
    "$OUT.tmp" > "$OUT"
rm "$OUT.tmp"
echo "wrote $OUT"
