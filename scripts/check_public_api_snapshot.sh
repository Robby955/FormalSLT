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

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--update" ]; }; then
  echo "usage: $0 [--update]" >&2
  exit 2
fi
UPDATE=false
if [ "${1:-}" = "--update" ]; then
  UPDATE=true
fi

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

# Keep the public policy, literature ledger, theorem map, and isolated Lean
# checkers on the same exact declaration list. The Lean runs below remain the
# authority for types and axiom sets; this static check prevents documentation
# from silently retaining shortened, stale, or renamed endpoints.
python3 - "${CHECKERS[@]}" <<'PY'
from pathlib import Path
import re
import sys


def bounded_section(text: str, start: str, end: str) -> str:
    if text.count(start) != 1 or text.count(end) != 1:
        raise SystemExit(
            f"ERROR: ambiguous or missing public-API section markers: "
            f"{start!r}, {end!r}"
        )
    return text.split(start, 1)[1].split(end, 1)[0]


checker_names: list[str] = []
checker_axiom_names: list[str] = []
for raw_path in sys.argv[1:]:
    checker = Path(raw_path).read_text(encoding="utf-8")
    checker_names.extend(
        re.findall(
            r"^#check\s+(FormalSLT\.[A-Za-z0-9_.]+)\s*$",
            checker,
            re.MULTILINE,
        )
    )
    checker_axiom_names.extend(
        re.findall(
            r"^#print\s+axioms\s+(FormalSLT\.[A-Za-z0-9_.]+)\s*$",
            checker,
            re.MULTILINE,
        )
    )

api = Path("docs/api-stability.md").read_text(encoding="utf-8")
api_block = bounded_section(api, "The 19 declarations below", "For patch releases")
api_names = re.findall(
    r"^- `(FormalSLT\.[A-Za-z0-9_.]+)`\s*$", api_block, re.MULTILINE
)

if len(api_names) != 19 or len(set(api_names)) != 19:
    raise SystemExit(
        "ERROR: docs/api-stability.md must contain exactly 19 unique allowlisted FQNs"
    )
if checker_names != api_names:
    raise SystemExit(
        "ERROR: isolated stable-import #check order differs from docs/api-stability.md"
    )
if checker_axiom_names != api_names:
    raise SystemExit(
        "ERROR: isolated stable-import #print axioms order differs from "
        "docs/api-stability.md"
    )

literature = Path("docs/LITERATURE.md").read_text(encoding="utf-8")
literature_block = bounded_section(
    literature,
    "### Exact candidate-v0.2 endpoint provenance",
    "### Proof-assistant and reusable-interface crosswalk",
)
literature_names = re.findall(
    r"^\|\s*\d+\s*\|\s*`(FormalSLT\.[A-Za-z0-9_.]+)`\s*\|",
    literature_block,
    re.MULTILINE,
)
if literature_names != api_names:
    raise SystemExit(
        "ERROR: docs/LITERATURE.md exact endpoint matrix differs from the "
        "public allowlist"
    )

theorem_map = Path("docs/theorem-map.md").read_text(encoding="utf-8")
map_block = bounded_section(
    theorem_map,
    "## Candidate v0.2 endpoint index",
    "## Core definitions",
)
map_names = re.findall(
    r"^\|\s*`(FormalSLT\.[A-Za-z0-9_.]+)`\s*\|", map_block, re.MULTILINE
)
if map_names != api_names:
    raise SystemExit(
        "ERROR: docs/theorem-map.md stable endpoint index differs from the public allowlist"
    )

print(
    "public API provenance passed: 19 exact endpoints across policy, "
    "literature, map, and checkers"
)
PY

for file in "${CHECKERS[@]}"; do
  printf '== %s ==\n' "$file" >> "$TMP"
  "$LAKE" env lean "$file" >> "$TMP" 2>&1
done

if [ "$UPDATE" = true ]; then
  cp "$TMP" "$SNAPSHOT"
  cp "$COMPAT_TMP" "$COMPAT_SNAPSHOT"
  echo "updated $SNAPSHOT"
  echo "updated $COMPAT_SNAPSHOT"
  exit 0
fi

diff -u "$SNAPSHOT" "$TMP"
diff -u "$COMPAT_SNAPSHOT" "$COMPAT_TMP"
echo "public API snapshot passed: 19 candidate declarations and 2 v0.1 compatibility declarations"
