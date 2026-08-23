#!/usr/bin/env bash
# Install an existing FormalSLT release tag into a fresh downstream Lake
# package and build all four supported topic imports. The expected tag object
# and peeled commit come from one prior resolver; later lookups only detect
# mutation and never silently establish a new identity.
set -euo pipefail

usage() {
  echo "usage: $0 <release-tag> <expected-tag-object> <expected-commit>" >&2
}

if [ "$#" -ne 3 ]; then
  usage
  exit 64
fi

TAG="$1"
EXPECTED_TAG_OBJECT="$2"
EXPECTED_COMMIT="$3"
REPOSITORY_URL="${FORMALSLT_REPOSITORY_URL:-https://github.com/Robby955/FormalSLT.git}"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ ! "$TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+([.-][0-9A-Za-z.-]+)?$ ]]; then
  echo "ERROR: release tag must be an exact semver-style tag such as v0.2.0: $TAG" >&2
  exit 64
fi

if [[ ! "$REPOSITORY_URL" =~ ^[0-9A-Za-z._:/@+-]+$ ]]; then
  echo "ERROR: repository URL contains unsupported characters: $REPOSITORY_URL" >&2
  exit 64
fi

if [[ ! "$EXPECTED_TAG_OBJECT" =~ ^[0-9a-f]{40}$ ]]; then
  echo "ERROR: expected tag object must be one full SHA-1 object id" >&2
  exit 64
fi

if [[ ! "$EXPECTED_COMMIT" =~ ^[0-9a-f]{40}$ ]]; then
  echo "ERROR: expected commit must be one full SHA-1 commit id" >&2
  exit 64
fi

if ! command -v "$LAKE" >/dev/null 2>&1; then
  echo "ERROR: Lake executable not found at $LAKE" >&2
  exit 69
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "ERROR: python3 is required for exact tag-identity checks" >&2
  exit 69
fi

verify_remote_identity() {
  python3 "$ROOT/scripts/release_tag_identity.py" verify \
    --tag "$TAG" \
    --repository-url "$REPOSITORY_URL" \
    --expected-tag-object "$EXPECTED_TAG_OBJECT" \
    --expected-commit "$EXPECTED_COMMIT"
}

# Detect a move after the resolver job and before dependency installation.
verify_remote_identity

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
if [ "$actual_commit" != "$EXPECTED_COMMIT" ]; then
  echo "ERROR: Lake installed $actual_commit, but resolver fixed $EXPECTED_COMMIT" >&2
  exit 5
fi

"$LAKE" exe cache get
"$LAKE" build Downstream

# Detect a move during dependency installation or the downstream build.
verify_remote_identity

echo "tag install smoke passed: $TAG ($EXPECTED_TAG_OBJECT) -> $actual_commit"
