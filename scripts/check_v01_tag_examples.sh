#!/usr/bin/env bash
# Replay the exact Lean examples published in the annotated v0.1.0 tag against
# the current library. This is intentionally narrower than full internal API
# compatibility.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

LAKE="${LAKE:-$HOME/.elan/bin/lake}"
TAG="v0.1.0^{}"
EXPECTED_TAG_OBJECT="0e1c79926b59a66e246f8b03051136477ba21f7f"
EXPECTED_TAG_COMMIT="4da0a3b4f91da67346624b5809385387c306fe17"
OUTPUT="$(mktemp "${TMPDIR:-/tmp}/formalslt-v01.XXXXXX")"
trap 'rm -f "$OUTPUT"' EXIT

if ! git rev-parse --verify --quiet "$TAG" >/dev/null; then
  echo "ERROR: annotated tag v0.1.0 is unavailable; fetch tags before running this gate" >&2
  exit 1
fi

actual_tag_commit="$(git rev-parse "$TAG")"
actual_tag_object="$(git rev-parse v0.1.0)"
if [ "$actual_tag_object" != "$EXPECTED_TAG_OBJECT" ]; then
  echo "ERROR: v0.1.0 tag object is $actual_tag_object, expected $EXPECTED_TAG_OBJECT" >&2
  exit 1
fi
if [ "$actual_tag_commit" != "$EXPECTED_TAG_COMMIT" ]; then
  echo "ERROR: v0.1.0 resolves to $actual_tag_commit, expected $EXPECTED_TAG_COMMIT" >&2
  exit 1
fi

count=0
while IFS= read -r file; do
  [ -n "$file" ] || continue
  echo "$file"
  if ! "$LAKE" env lean <(git show "$TAG:$file") >"$OUTPUT" 2>&1; then
    cat "$OUTPUT" >&2
    exit 1
  fi
  count=$((count + 1))
done < <(
  git ls-tree -r --name-only "$TAG" examples |
    grep -E '\.lean$' |
    sort
)

if [ "$count" -eq 0 ]; then
  echo "ERROR: v0.1.0 contains no Lean examples" >&2
  exit 1
fi

echo "v0.1 compatibility passed: $count tagged examples"
