#!/usr/bin/env bash
# Check the candidate v0.2 declaration types and axiom reports against the
# committed snapshot. Use --update only for an intentional, reviewed API edit.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

LAKE="${LAKE:-$HOME/.elan/bin/lake}"
SNAPSHOT="tests/public_api/v0.2.txt"
COMPAT_SNAPSHOT="tests/public_api/v0.1-compat.txt"
TMP="$(mktemp "${TMPDIR:-/tmp}/formalslt-api.XXXXXX")"
COMPAT_TMP="$(mktemp "${TMPDIR:-/tmp}/formalslt-v01-api.XXXXXX")"
trap 'rm -f "$TMP" "$COMPAT_TMP"' EXIT

CHECKERS=(
  "examples/stable_imports/CheckPACBayesV02.lean"
  "examples/stable_imports/CheckSequentialV02.lean"
  "examples/stable_imports/CheckStochasticDynamicsV02.lean"
  "examples/stable_imports/CheckVCV02.lean"
)
EXPECTED_IMPORTS=(
  "import FormalSLT.PACBayes"
  "import FormalSLT.Sequential"
  "import FormalSLT.StochasticDynamics"
  "import FormalSLT.VC"
)

for index in "${!CHECKERS[@]}"; do
  imports="$(grep -E '^import ' "${CHECKERS[$index]}" || true)"
  if [ "$imports" != "${EXPECTED_IMPORTS[$index]}" ]; then
    echo "ERROR: ${CHECKERS[$index]} must import only '${EXPECTED_IMPORTS[$index]}'" >&2
    printf 'found:\n%s\n' "$imports" >&2
    exit 1
  fi
done

compat_imports="$(grep -E '^import ' examples/CheckV01Compatibility.lean || true)"
if [ "$compat_imports" != "import FormalSLT.Stability.BousquetElisseeff" ]; then
  echo "ERROR: examples/CheckV01Compatibility.lean has an unexpected import surface" >&2
  exit 1
fi
if [ "$(grep -Ec '^#check ' examples/CheckV01Compatibility.lean)" -ne 2 ] ||
    [ "$(grep -Ec '^#print axioms ' examples/CheckV01Compatibility.lean)" -ne 2 ]; then
  echo "ERROR: v0.1 compatibility checker must contain 2 checks and 2 axiom reports" >&2
  exit 1
fi

check_count=0
print_count=0
for file in "${CHECKERS[@]}"; do
  check_count=$((check_count + $(grep -Ec '^#check ' "$file")))
  print_count=$((print_count + $(grep -Ec '^#print axioms ' "$file")))
done

"$LAKE" env lean examples/CheckV01Compatibility.lean > "$COMPAT_TMP" 2>&1

if [ "$check_count" -ne 19 ] || [ "$print_count" -ne 19 ]; then
  echo "ERROR: expected 19 #check and 19 #print axioms entries; found $check_count and $print_count" >&2
  exit 1
fi

for file in "${CHECKERS[@]}"; do
  printf '== %s ==\n' "$file" >> "$TMP"
  "$LAKE" env lean "$file" >> "$TMP" 2>&1
done

if [ "${1:-}" = "--update" ]; then
  cp "$TMP" "$SNAPSHOT"
  cp "$COMPAT_TMP" "$COMPAT_SNAPSHOT"
  echo "updated $SNAPSHOT"
  echo "updated $COMPAT_SNAPSHOT"
  exit 0
fi

if [ "$#" -ne 0 ]; then
  echo "usage: $0 [--update]" >&2
  exit 2
fi

diff -u "$SNAPSHOT" "$TMP"
diff -u "$COMPAT_SNAPSHOT" "$COMPAT_TMP"
echo "public API snapshot passed: 19 candidate declarations and 2 v0.1 compatibility declarations"
