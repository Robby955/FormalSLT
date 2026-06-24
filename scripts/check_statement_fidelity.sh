#!/usr/bin/env bash
# Statement-fidelity / non-vacuity gate (BLOCKING).
#
# Why this exists: a theorem can build, be axiom-clean, and still be vacuous
# (e.g. a quantifier-inverted ∀var ∃const bound, a `: True` conclusion, or a
# `: False` hypothesis). The build/axiom/witness gates do not catch those
# shapes at the statement level. This gate lints the common near-vacuity shapes
# on the .lean files touched by a change and FAILS the build on any unsigned
# flag. A genuinely non-vacuous statement that trips the lint carries an inline
# `-- fidelity:` sign-off explaining why (e.g. why the constant is uniform);
# the checker downgrades a signed flag to `ok(signed)`.
#
# Scope: it runs on the .lean files CHANGED by the current PR/push (diff vs the
# base ref), so a clean PR is not blocked by a pre-existing statement elsewhere.
# When no base ref is resolvable (e.g. a manual run on a detached checkout) it
# falls back to scanning every tracked .lean file.
#
# It then runs a fixture pair to prove the detector discriminates: a synthetic
# vacuous theorem MUST be flagged (gate would fail), and a synthetic genuine
# theorem MUST pass. This proves the gate itself works, so a regression that
# silently neuters the checker is caught.
#
# Run from CI alongside the build, axiom, and witness-quality gates.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

CHECKER="$ROOT/scripts/statement_fidelity_check.py"
if [ ! -f "$CHECKER" ]; then
  echo "FAIL: $CHECKER not found" >&2
  exit 1
fi

# --- Resolve the set of changed .lean files. ---------------------------------
# Priority:
#   1. explicit base ref in FIDELITY_BASE_REF (lets CI pass the PR base sha)
#   2. GitHub PR base (origin/$GITHUB_BASE_REF) on pull_request events
#   3. the previous commit (HEAD~1) on a push with history
#   4. fall back: every tracked .lean file
base_ref=""
if [ -n "${FIDELITY_BASE_REF:-}" ] && git rev-parse --verify --quiet "${FIDELITY_BASE_REF}^{commit}" >/dev/null; then
  base_ref="${FIDELITY_BASE_REF}"
elif [ -n "${GITHUB_BASE_REF:-}" ]; then
  git fetch --quiet --depth=1 origin "${GITHUB_BASE_REF}" 2>/dev/null || true
  if git rev-parse --verify --quiet "origin/${GITHUB_BASE_REF}^{commit}" >/dev/null; then
    base_ref="origin/${GITHUB_BASE_REF}"
  fi
elif git rev-parse --verify --quiet "HEAD~1^{commit}" >/dev/null; then
  base_ref="HEAD~1"
fi

declare -a CHANGED=()
if [ -n "$base_ref" ]; then
  mb="$(git merge-base "$base_ref" HEAD 2>/dev/null || echo "$base_ref")"
  echo "== statement-fidelity gate: changed .lean files vs ${base_ref} (merge-base ${mb}) =="
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    case "$f" in *.lean) [ -f "$f" ] && CHANGED+=("$f") ;; esac
  done < <(git diff --name-only --diff-filter=ACMR "$mb" HEAD)
else
  echo "== statement-fidelity gate: no base ref resolvable, scanning all tracked .lean files =="
  while IFS= read -r f; do
    [ -n "$f" ] && CHANGED+=("$f")
  done < <(git ls-files '*.lean')
fi

fail=0

if [ "${#CHANGED[@]}" -eq 0 ]; then
  echo "  (no .lean files in scope)"
else
  for f in "${CHANGED[@]}"; do
    out="$(python3 "$CHECKER" "$f" 2>&1)" && rc=0 || rc=$?
    if [ "$rc" -ne 0 ]; then
      echo "  FLAG in $f" >&2
      echo "$out" | sed 's/^/    /' >&2
      fail=1
    elif echo "$out" | grep -q 'ok(signed)'; then
      echo "  ok (signed flag) $f"
      echo "$out" | grep 'ok(signed)' | sed 's/^/    /'
    fi
  done
  [ "$fail" -eq 0 ] && echo "  ok: ${#CHANGED[@]} changed .lean file(s), no unsigned fidelity flags"
fi

# --- Fixture pair: prove the detector actually discriminates. -----------------
echo "== detector fixture pair =="
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

VACUOUS_FIX="$WORK/FixtureVacuous.lean"
cat > "$VACUOUS_FIX" <<'EOF'
-- ∀t ∃c, ‖f t‖ ≤ c * g t : the constant is chosen after the variable, so the
-- bound is trivially satisfiable. The detector MUST flag this (quantifier
-- inversion). The genuine form is ∃c, ∀t.
theorem fixture_vacuous {t : ℝ} (f g : ℝ → ℝ) : ∃ c : ℝ, ‖f t‖ ≤ c * (g t) := by
  sorry
EOF

GENUINE_FIX="$WORK/FixtureGenuine.lean"
cat > "$GENUINE_FIX" <<'EOF'
-- ∃c, ∀t : the constant is uniform over t (quantified inside the ∃). The
-- detector MUST NOT flag this; it is the genuine, non-vacuous shape.
theorem fixture_genuine (f g : ℝ → ℝ) : ∃ c : ℝ, ∀ t : ℝ, ‖f t‖ ≤ c * (g t) := by
  sorry
EOF

if python3 "$CHECKER" "$VACUOUS_FIX" >/dev/null 2>&1; then
  echo "  FAIL vacuous fixture was NOT flagged (detector broken)" >&2
  fail=1
else
  echo "  ok   vacuous fixture flagged (detector RED-flags quantifier inversion)"
fi

if python3 "$CHECKER" "$GENUINE_FIX" >/dev/null 2>&1; then
  echo "  ok   genuine (∃c ∀t) fixture passed"
else
  echo "  FAIL genuine fixture was flagged (detector over-eager)" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "statement-fidelity gate FAILED" >&2
  exit 1
fi

echo "statement-fidelity gate passed: no unsigned fidelity flags, detector verified"
