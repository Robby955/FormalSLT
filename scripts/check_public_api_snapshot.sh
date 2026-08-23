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
import hashlib
import json
import re
import sys


def bounded_section(text: str, start: str, end: str) -> str:
    if text.count(start) != 1 or text.count(end) != 1:
        raise SystemExit(
            f"ERROR: ambiguous or missing public-API section markers: "
            f"{start!r}, {end!r}"
        )
    return text.split(start, 1)[1].split(end, 1)[0]


def markdown_table_cells(line: str) -> list[str]:
    """Split a one-line Markdown table row, respecting escaped pipes."""
    stripped = line.strip()
    if not stripped.startswith("|") or not stripped.endswith("|"):
        raise ValueError("not a Markdown table row")
    cells: list[str] = []
    current: list[str] = []
    body = stripped[1:-1]
    code_delimiter_length = 0
    index = 0
    while index < len(body):
        character = body[index]
        if character == "\\":
            slash_end = index + 1
            while slash_end < len(body) and body[slash_end] == "\\":
                slash_end += 1
            if slash_end < len(body) and body[slash_end] == "|":
                current.extend(body[index : slash_end + 1])
                index = slash_end + 1
                continue
            if code_delimiter_length == 0 and index + 1 < len(body):
                current.extend((character, body[index + 1]))
                index += 2
                continue
        if character == "`":
            run_end = index + 1
            while run_end < len(body) and body[run_end] == "`":
                run_end += 1
            run_length = run_end - index
            current.extend(body[index:run_end])
            if code_delimiter_length == 0:
                code_delimiter_length = run_length
            elif run_length == code_delimiter_length:
                code_delimiter_length = 0
            index = run_end
            continue
        if character == "|":
            if code_delimiter_length != 0:
                raise ValueError("unescaped pipe inside inline-code span")
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(character)
        index += 1
    if code_delimiter_length != 0:
        raise ValueError("unclosed inline-code span")
    cells.append("".join(current).strip())
    return cells


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
endpoint_matrix = bounded_section(
    literature,
    "### Exact candidate-v0.2 endpoint provenance",
    "### Candidate-v0.2 endpoint audit join",
)
endpoint_rows: dict[int, list[str]] = {}
for line in endpoint_matrix.splitlines():
    if not re.match(r"^\s{0,3}\|\s*\d+\s*\|", line):
        continue
    try:
        cells = markdown_table_cells(line)
    except ValueError as error:
        raise SystemExit(
            "ERROR: malformed exact-endpoint row in docs/LITERATURE.md: "
            f"{error}: {line}"
        ) from error
    if len(cells) != 6:
        raise SystemExit(
            "ERROR: malformed exact-endpoint row in docs/LITERATURE.md: " + line
        )
    row_number = int(cells[0])
    if row_number in endpoint_rows:
        raise SystemExit(
            f"ERROR: duplicate exact-endpoint row {row_number} in docs/LITERATURE.md"
        )
    endpoint_rows[row_number] = cells

if list(endpoint_rows) != list(range(1, 20)):
    raise SystemExit(
        "ERROR: docs/LITERATURE.md exact endpoint rows must be numbered 1 through 19"
    )
endpoint_names: list[str] = []
for row_number in range(1, 20):
    name_match = re.fullmatch(
        r"`(FormalSLT\.[A-Za-z0-9_.]+)`", endpoint_rows[row_number][1]
    )
    if name_match is None:
        raise SystemExit(
            f"ERROR: docs/LITERATURE.md row {row_number} has a malformed endpoint FQN"
        )
    endpoint_names.append(name_match.group(1))
if endpoint_names != api_names:
    raise SystemExit(
        "ERROR: docs/LITERATURE.md exact endpoint matrix differs from the "
        "public allowlist"
    )

expected_classifications = [
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"DERIVED VARIANT"},
    {"SPECIALIZATION"},
    {"SPECIALIZATION"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"DERIVED VARIANT"},
    {"DERIVED VARIANT"},
    {"DERIVED VARIANT"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"SPECIALIZATION", "DERIVED VARIANT"},
    {"SPECIALIZATION"},
    {"REPRODUCTION"},
    {"DERIVED VARIANT"},
    {"DERIVED VARIANT"},
]
for row_number, expected in enumerate(expected_classifications, start=1):
    classification = endpoint_rows[row_number][3]
    tokens = re.findall(
        r"\*\*(REPRODUCTION|SPECIALIZATION|DERIVED VARIANT|CANDIDATE NEW)\*\*",
        classification,
    )
    bold_labels = re.findall(r"\*\*([^*]+)\*\*", classification)
    unexpected_bold_labels = [
        label for label in bold_labels
        if label.upper() == label
        and label not in {
            "REPRODUCTION", "SPECIALIZATION", "DERIVED VARIANT", "CANDIDATE NEW"
        }
    ]
    if (
        "CANDIDATE NEW" in classification
        or unexpected_bold_labels
        or len(tokens) != len(set(tokens))
        or set(tokens) != expected
    ):
        raise SystemExit(
            f"ERROR: docs/LITERATURE.md row {row_number} classification tokens "
            f"are {tokens!r}, expected {sorted(expected)!r}"
        )

join_block = bounded_section(
    literature,
    "### Candidate-v0.2 endpoint audit join",
    "#### Prior-formalization profiles",
)
join_rows: list[tuple[str, str, str, str]] = []
for line in join_block.splitlines():
    if not re.match(r"^\s{0,3}\|\s*\d+\s*\|", line):
        continue
    try:
        cells = markdown_table_cells(line)
    except ValueError as error:
        raise SystemExit(
            "ERROR: malformed endpoint audit row in docs/LITERATURE.md: "
            f"{error}: {line}"
        ) from error
    if (
        len(cells) != 4
        or re.fullmatch(r"M\d+", cells[2]) is None
        or re.fullmatch(r"P\d+", cells[3]) is None
    ):
        raise SystemExit(
            "ERROR: malformed endpoint audit row in docs/LITERATURE.md: " + line
        )
    join_rows.append((cells[0], cells[1], cells[2], cells[3]))
join_numbers = [int(number) for number, _assumptions, _mathlib, _paper in join_rows]
if join_numbers != list(range(1, 20)):
    raise SystemExit(
        "ERROR: docs/LITERATURE.md endpoint audit rows must be numbered 1 through 19"
    )

expected_mathlib_profiles = [
    "M1", "M2", "M2", "M2", "M3", "M4", "M2", "M5", "M6", "M7",
    "M8", "M9", "M10", "M11", "M12", "M8", "M13", "M14", "M15",
]
expected_paper_profiles = [
    "P1", "P0", "P0", "P0", "P0", "P1", "P0", "P0", "P0", "P0",
    "P2", "P3", "P4", "P5", "P6", "P0", "P0", "P0", "P0",
]
actual_mathlib_profiles = [mathlib for _n, _a, mathlib, _paper in join_rows]
actual_paper_profiles = [paper for _n, _a, _mathlib, paper in join_rows]
if actual_mathlib_profiles != expected_mathlib_profiles:
    raise SystemExit(
        "ERROR: docs/LITERATURE.md endpoint Mathlib-profile assignment drifted"
    )
if actual_paper_profiles != expected_paper_profiles:
    raise SystemExit(
        "ERROR: docs/LITERATURE.md endpoint paper-profile assignment drifted"
    )
for number, assumptions, _mathlib, _paper in join_rows:
    if not assumptions or re.search(r"\b(?:TBD|UNSWEPT)\b", assumptions):
        raise SystemExit(
            f"ERROR: docs/LITERATURE.md endpoint row {number} has an incomplete "
            "assumptions/constants cell"
        )

expected_formalization_profiles = [
    "F2", "F2", "F2", "F2", "F2", "F1", "F2", "F2", "F2", "F2",
    "F2", "F2", "F2", "F2", "F2", "F2", "F1", "F2", "F1",
]
formalization_profiles_block = bounded_section(
    literature,
    "#### Prior-formalization profiles",
    "#### Mathlib profiles",
)
formalization_profile_definitions = re.findall(
    r"^\s{0,3}- \*\*(F\d+)\s+—[^*]+\*\*:\s+\S.*$",
    formalization_profiles_block,
    re.MULTILINE,
)
formalization_profile_lines = re.findall(
    r"^\s{0,3}- \*\*F\d+\s+—[^*]+\*\*.*$",
    formalization_profiles_block,
    re.MULTILINE,
)
if (
    formalization_profile_definitions != ["F1", "F2"]
    or len(formalization_profile_lines) != 2
):
    raise SystemExit(
        "ERROR: docs/LITERATURE.md must define formalization profiles F1 and F2 once"
    )

formalization_rows: list[tuple[int, str]] = []
for line in formalization_profiles_block.splitlines():
    if not re.match(r"^\s{0,3}\|\s*\d+\s*\|", line):
        continue
    try:
        cells = markdown_table_cells(line)
    except ValueError as error:
        raise SystemExit(
            "ERROR: malformed formalization-profile row in docs/LITERATURE.md: "
            f"{error}: {line}"
        ) from error
    if len(cells) != 2 or re.fullmatch(r"F[12]", cells[1]) is None:
        raise SystemExit(
            "ERROR: malformed formalization-profile row in docs/LITERATURE.md: " + line
        )
    formalization_rows.append((int(cells[0]), cells[1]))

if [number for number, _profile in formalization_rows] != list(range(1, 20)):
    raise SystemExit(
        "ERROR: docs/LITERATURE.md formalization rows must be numbered 1 through 19"
    )
actual_formalization_profiles = [profile for _number, profile in formalization_rows]
if actual_formalization_profiles != expected_formalization_profiles:
    raise SystemExit(
        "ERROR: docs/LITERATURE.md endpoint formalization-profile assignment drifted"
    )
for row_number, expected_profile in enumerate(expected_formalization_profiles, start=1):
    prior_cell = endpoint_rows[row_number][5]
    profile_match = re.match(r"^\*\*(F[12])\*\*\s+—\s+", prior_cell)
    if profile_match is None or profile_match.group(1) != expected_profile:
        raise SystemExit(
            f"ERROR: docs/LITERATURE.md row {row_number} prior-formalization cell "
            f"must start with **{expected_profile}**"
        )
    if "UNSWEPT" in prior_cell:
        raise SystemExit(
            f"ERROR: docs/LITERATURE.md row {row_number} retains an UNSWEPT "
            "prior-formalization status"
        )

mathlib_profiles_block = bounded_section(
    literature,
    "#### Mathlib profiles",
    "#### Paper profiles",
)
paper_profiles_block = bounded_section(
    literature,
    "#### Paper profiles",
    "### Proof-assistant and reusable-interface crosswalk",
)
mathlib_profile_definitions = re.findall(
    r"^\s{0,3}- \*\*(M\d+)\*\*:\s+\S.*$",
    mathlib_profiles_block,
    re.MULTILINE,
)
paper_profile_definitions = re.findall(
    r"^\s{0,3}- \*\*(P\d+)\*\*:\s+\S.*$",
    paper_profiles_block,
    re.MULTILINE,
)
mathlib_profile_lines = re.findall(
    r"^\s{0,3}- \*\*M\d+\*\*.*$", mathlib_profiles_block, re.MULTILINE
)
paper_profile_lines = re.findall(
    r"^\s{0,3}- \*\*P\d+\*\*.*$", paper_profiles_block, re.MULTILINE
)
if (
    len(mathlib_profile_definitions) != 15
    or len(mathlib_profile_lines) != len(mathlib_profile_definitions)
    or mathlib_profile_definitions != [f"M{i}" for i in range(1, 16)]
):
    raise SystemExit(
        "ERROR: docs/LITERATURE.md must define each Mathlib profile M1 through M15 once"
    )
if (
    len(paper_profile_definitions) != 7
    or len(paper_profile_lines) != len(paper_profile_definitions)
    or paper_profile_definitions != [f"P{i}" for i in range(7)]
):
    raise SystemExit(
        "ERROR: docs/LITERATURE.md must define each paper profile P0 through P6 once"
    )

# The structured checks above give targeted failures. This digest additionally
# binds the reviewed source, boundary, assumption, profile-body, and nonclaim
# text so a prose mutation cannot retain a misleading green provenance gate.
expected_endpoint_provenance_sha256 = (
    "91c42ba1cad70edd5cfc80a85fba7d2577872e58c7c00824c5f10513f0b14ada"
)
actual_endpoint_provenance_sha256 = hashlib.sha256(
    literature_block.encode("utf-8")
).hexdigest()
if actual_endpoint_provenance_sha256 != expected_endpoint_provenance_sha256:
    raise SystemExit(
        "ERROR: docs/LITERATURE.md exact endpoint provenance bytes drifted; "
        "review the change and update the expected digest deliberately"
    )

toolchain = Path("lean-toolchain").read_text(encoding="utf-8").strip()
expected_toolchain = "leanprover/lean4:v4.32.2"
if toolchain != expected_toolchain:
    raise SystemExit(
        f"ERROR: unexpected Lean toolchain {toolchain!r}; expected {expected_toolchain!r}"
    )
manifest = json.loads(Path("lake-manifest.json").read_text(encoding="utf-8"))
mathlib_packages = [
    package for package in manifest.get("packages", [])
    if package.get("name") == "mathlib"
]
expected_mathlib_revision = "905b95818eb32af7874a58b427f50c1711a5e96c"
expected_mathlib_url = "https://github.com/leanprover-community/mathlib4.git"
if (
    len(mathlib_packages) != 1
    or mathlib_packages[0].get("rev") != expected_mathlib_revision
    or mathlib_packages[0].get("url") != expected_mathlib_url
    or mathlib_packages[0].get("type") != "git"
    or mathlib_packages[0].get("inputRev") != "v4.32.2"
):
    raise SystemExit(
        "ERROR: lake-manifest.json does not pin the documented Mathlib revision"
    )
mathlib_boundary = bounded_section(
    literature,
    "### Mathlib import boundary at the v0.2 code freeze",
    "## Stationary and unknown-kernel source dictionary",
)
expected_mathlib_boundary_sha256 = (
    "e85019191995ff9bbad6b83c6a31710e7c4aa267f364efce5a206060f30bdec1"
)
actual_mathlib_boundary_sha256 = hashlib.sha256(
    mathlib_boundary.encode("utf-8")
).hexdigest()
if actual_mathlib_boundary_sha256 != expected_mathlib_boundary_sha256:
    raise SystemExit(
        "ERROR: docs/LITERATURE.md Mathlib-boundary bytes drifted; review the "
        "change and update the expected digest deliberately"
    )
for documented_value in (
    "v4.32.2",
    expected_mathlib_revision,
    "15b444e75a3e0ce734968c8f58b28881959eb313",
):
    if f"`{documented_value}`" not in mathlib_boundary:
        raise SystemExit(
            "ERROR: docs/LITERATURE.md Mathlib boundary is missing documented "
            f"value {documented_value}"
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

# The displayed Lake dependency must use the package name declared by
# lakefile.lean. This catches install snippets that look plausible but cannot
# resolve because Lake dependency names are exact.
lakefile = Path("lakefile.lean").read_text(encoding="utf-8")
package_match = re.search(r"^package\s+(\S+)\s+where\s*$", lakefile, re.MULTILINE)
if package_match is None:
    raise SystemExit("ERROR: could not read the package name from lakefile.lean")
package_name = package_match.group(1)

install_surfaces = {
    "README.md": 2,
    "docs/site/readers/lean/index.html": 2,
}
for path, expected_count in install_surfaces.items():
    text = Path(path).read_text(encoding="utf-8")
    dependency_names = re.findall(r"require\s+(\S+)\s+from\s+git", text)
    if dependency_names != [package_name] * expected_count:
        raise SystemExit(
            f"ERROR: {path} must contain {expected_count} FormalSLT install "
            f"snippets using the Lake package name {package_name!r}; "
            f"found {dependency_names!r}"
        )

print(
    "public API provenance passed: 19 exact endpoints, audit rows, and bounded "
    "formalization profiles across policy, literature, map, and checkers; "
    "install snippets and dependency pins match"
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
