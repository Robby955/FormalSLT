#!/usr/bin/env bash
# Install an existing FormalSLT release tag into a fresh downstream Lake
# package and build all four supported topic imports. Missing or ambiguous
# remote tags are hard failures; this script never falls back to a branch.
set -euo pipefail

usage() {
  echo "usage: $0 <release-tag>" >&2
}

if [ "$#" -ne 1 ]; then
  usage
  exit 64
fi

TAG="$1"
REPOSITORY_URL="${FORMALSLT_REPOSITORY_URL:-https://github.com/Robby955/FormalSLT.git}"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"

if [[ ! "$TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+([.-][0-9A-Za-z.-]+)?$ ]]; then
  echo "ERROR: release tag must be an exact semver-style tag such as v0.2.0: $TAG" >&2
  exit 64
fi

if [[ ! "$REPOSITORY_URL" =~ ^[0-9A-Za-z._:/@+-]+$ ]]; then
  echo "ERROR: repository URL contains unsupported characters: $REPOSITORY_URL" >&2
  exit 64
fi

if ! command -v "$LAKE" >/dev/null 2>&1; then
  echo "ERROR: Lake executable not found at $LAKE" >&2
  exit 69
fi

set +e
tag_query="$(git ls-remote --refs "$REPOSITORY_URL" "refs/tags/$TAG" 2>&1)"
tag_query_status=$?
set -e
if [ "$tag_query_status" -ne 0 ]; then
  echo "ERROR: unable to query $REPOSITORY_URL for $TAG" >&2
  printf '%s\n' "$tag_query" >&2
  exit 2
fi

if [ -z "$tag_query" ]; then
  echo "ERROR: remote tag $TAG does not exist at $REPOSITORY_URL" >&2
  exit 3
fi

tag_lines="$(printf '%s\n' "$tag_query" | wc -l | tr -d '[:space:]')"
tag_object="$(printf '%s\n' "$tag_query" | awk -v ref="refs/tags/$TAG" '$2 == ref {print $1}')"
if [ "$tag_lines" -ne 1 ] || [ -z "$tag_object" ]; then
  echo "ERROR: remote tag query for $TAG was ambiguous" >&2
  printf '%s\n' "$tag_query" >&2
  exit 4
fi

set +e
peeled_query="$(git ls-remote "$REPOSITORY_URL" "refs/tags/$TAG^{}" 2>&1)"
peeled_query_status=$?
set -e
if [ "$peeled_query_status" -ne 0 ]; then
  echo "ERROR: unable to resolve remote tag $TAG" >&2
  printf '%s\n' "$peeled_query" >&2
  exit 2
fi

if [ -n "$peeled_query" ]; then
  expected_commit="$(printf '%s\n' "$peeled_query" | awk -v ref="refs/tags/$TAG^{}" '$2 == ref {print $1}')"
else
  expected_commit="$tag_object"
fi
if [[ ! "$expected_commit" =~ ^[0-9a-f]{40}$ ]]; then
  echo "ERROR: remote tag $TAG did not resolve to one commit" >&2
  exit 4
fi

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/formalslt-tag-install.XXXXXX")"
trap 'rm -rf "$WORKDIR"' EXIT

cp "$ROOT/tests/downstream/lean-toolchain" "$WORKDIR/lean-toolchain"
cp -R "$ROOT/tests/downstream/Downstream" "$WORKDIR/Downstream"
{
  printf '%s\n' 'import Lake'
  printf '%s\n' 'open Lake DSL'
  printf '\n'
  printf '%s\n' 'package «formal-slt-tag-install-smoke»'
  printf '\n'
  printf '%s\n' 'require «formal-slt» from git'
  printf '  "%s" @ "%s"\n' "$REPOSITORY_URL" "$TAG"
  printf '\n'
  printf '%s\n' '@[default_target]'
  printf '%s\n' 'lean_lib Downstream where'
  printf '%s\n' '  roots := #['
  printf '%s\n' '    `Downstream.PACBayes,'
  printf '%s\n' '    `Downstream.Sequential,'
  printf '%s\n' '    `Downstream.StochasticDynamics,'
  printf '%s\n' '    `Downstream.VC'
  printf '%s\n' '  ]'
} > "$WORKDIR/lakefile.lean"

cd "$WORKDIR"
"$LAKE" update

PACKAGE_DIR="$WORKDIR/.lake/packages/formal-slt"
if [ ! -d "$PACKAGE_DIR/.git" ]; then
  echo "ERROR: Lake did not install FormalSLT as a git dependency" >&2
  exit 5
fi

actual_commit="$(git -C "$PACKAGE_DIR" rev-parse HEAD)"
if [ "$actual_commit" != "$expected_commit" ]; then
  echo "ERROR: Lake installed $actual_commit, but $TAG resolves to $expected_commit" >&2
  exit 5
fi

"$LAKE" exe cache get
"$LAKE" build Downstream

echo "tag install smoke passed: $TAG -> $actual_commit"
