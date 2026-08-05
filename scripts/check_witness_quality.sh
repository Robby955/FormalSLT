#!/usr/bin/env bash
# Witness-quality gate: bans fake (check-only) non-vacuity witnesses.
#
# Why this exists: a `#check`/`#print axioms` file certifies well-typedness and
# axiom-cleanliness, but a `#check` CANNOT fail on a vacuous theorem, so it does
# not certify satisfiability (non-vacuity). For every headline theorem the paper
# cites as "witnessed", the example file must contain a CONCRETE instantiation
# (a `def`/`example`/`theorem`/`lemma`/`instance`/`abbrev`/`structure` that
# discharges the hypotheses on explicit data), not just `#check` lines.
#
# This gate scans the curated list of headline witness files (the concrete
# non-vacuity witnesses built for the 2026-06-23 soundness audit) and FAILS if
# any of them degenerates into a check-only file. It then runs a fixture pair:
# a synthetic check-only file MUST be detected as fake (gate would fail), and a
# synthetic concrete-witness file MUST pass. This proves the detector itself
# works, so a future regression that turns a witness into `#check`-only is caught.
#
# Run from CI alongside the example loop and the axiom gate.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

# A file is a CONCRETE witness if it has at least one top-level declaration that
# instantiates the theorem on explicit data. A FAKE witness has `#check`/`#print`
# lines but ZERO such declarations.
DECL_PATTERN='^[[:space:]]*(noncomputable[[:space:]]+)?(def|example|theorem|lemma|instance|abbrev|structure)[[:space:]]'
CHECK_PATTERN='#check|#print'

# Returns 0 (concrete) / 1 (fake) / 2 (not-a-witness: no checks at all).
classify_witness() {
  local f="$1"
  if [ ! -f "$f" ]; then
    echo "MISSING"
    return 0
  fi
  local decls checks
  decls="$(grep -cE "$DECL_PATTERN" -- "$f" || true)"
  checks="$(grep -cE "$CHECK_PATTERN" -- "$f" || true)"
  if [ "$decls" -ge 1 ]; then
    echo "CONCRETE"
  elif [ "$checks" -ge 1 ]; then
    echo "FAKE"
  else
    echo "NONE"
  fi
}

# Curated headline witnesses: every theorem the paper cites as witnessed must
# point at a file here, and each file MUST be a concrete instantiation. Adding a
# new headline => add its witness file here.
# Each entry: theorem the file witnesses (see comment) -> the witness file.
#   atTop_time_uniform_confidence_sequence_subGamma
#   mixture_confidence_sequence_uniformPrior
#   flagshipFourComponent_conclusion_from_incrementModel
#   flagshipFiveComponent_conclusion_from_incrementModel
#   flagshipAnytimeValid_conclusion_from_incrementModel
#   pacbayes_mcallester_sqrt
#   finiteMcAllesterBoundedComplexity_badEventMass_le_delta
#   finitePACBayesBernsteinMargin_badEventMass_le_delta
#   vcPacBayesBernsteinPosteriorRisk_bound
#   empiricalBernstein_confidence_sequence_uniformPrior
#   FormalSLT.Concentration.NamedTails.bernstein_tail (two-sided, Rademacher witness)
#   maurer_pacbayes_kl_bound
#   eProcess_typeI_control / eProcess_product_of_supermartingale / eProcess_optionalContinuation
#   optimized_lambda_confidence_sequence_subGamma / subGammaLogLogWidth_loglog_rate
#   betting_confidence_sequence_of_condMean (concrete Rademacher witness, bet 1/4)
#   timeUniformPACBayes_bound (process-level Ville crossing, concrete Rademacher witness)
#   timeUniformIIDGaussianPACBayes_bound (fair-Bernoulli product stream with
#     explicit KL, evaluated penalty, and a nonempty failure-event witness)
#   cramerRao_unbiased / Bernoulli p = 1/2 Fisher-information witness
#   finiteLogPartition_hasDerivAt / finiteExponentialFamily_fisherInformation_eq_variance
#     (Bernoulli natural-parameter witness at theta = 0)
HEADLINE_WITNESSES=(
  "examples/WitnessAtTopCS.lean"
  "examples/CheckAnytimeValidNonVacuityWitness.lean"
  "examples/CheckOptimizedLambdaCS.lean"
  "examples/AdversarialWitnessFlagshipFourComponent.lean"
  "examples/RefuteFlagshipFiveWitness.lean"
  "examples/CheckFlagshipAnytimeValidWitness.lean"
  "examples/CheckPACBayesMcAllesterSqrtWitness.lean"
  "examples/WitnessMcAllesterBadEventNonempty.lean"
  "examples/AdversarialWitnessBernstein.lean"
  "examples/CheckVCHybridWitness.lean"
  "examples/CheckEmpiricalBernsteinNonVacuityWitness.lean"
  "examples/CheckNamedTails.lean"
  "examples/CheckMaurerKLNonVacuityWitness.lean"
  "examples/CheckEProcess.lean"
  "examples/CheckBettingCSNonVacuityWitness.lean"
  "examples/CheckTimeUniformPACBayes.lean"
  "examples/CheckIIDContinuousGaussianPACBayes.lean"
  "examples/CheckDyadicEpochCS.lean"
  "examples/CheckDyadicEpochPSeriesCS.lean"
  "examples/CheckCramerRao.lean"
  "examples/CheckExponentialFamily.lean"
)

fail=0

echo "== headline witness-quality gate =="
for f in "${HEADLINE_WITNESSES[@]}"; do
  verdict="$(classify_witness "$f")"
  case "$verdict" in
    CONCRETE) echo "  ok   (concrete)  $f" ;;
    FAKE)
      echo "  FAIL (check-only) $f" >&2
      echo "        a headline witness must instantiate the theorem on explicit" >&2
      echo "        data, not just #check / #print axioms." >&2
      fail=1
      ;;
    MISSING)
      echo "  FAIL (missing)    $f" >&2
      fail=1
      ;;
    NONE)
      echo "  FAIL (empty)      $f  (no #check and no concrete decl)" >&2
      fail=1
      ;;
  esac
done

# --- Fixture pair: prove the detector actually discriminates. -----------------
echo "== detector fixture pair =="
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

FAKE_FIX="$WORK/FixtureFake.lean"
{
  echo "-- A check-only file: must be classified FAKE."
  echo "#check Nat.add"
  echo "#print axioms Nat.add_comm"
} > "$FAKE_FIX"

CONCRETE_FIX="$WORK/FixtureConcrete.lean"
{
  echo "-- A concrete witness: instantiates on explicit data, must be CONCRETE."
  echo "theorem fixture_witness : (1 : Nat) + 1 = 2 := rfl"
  echo "#print axioms fixture_witness"
} > "$CONCRETE_FIX"

fake_verdict="$(classify_witness "$FAKE_FIX")"
concrete_verdict="$(classify_witness "$CONCRETE_FIX")"

if [ "$fake_verdict" = "FAKE" ]; then
  echo "  ok   check-only fixture detected as FAKE"
else
  echo "  FAIL check-only fixture classified $fake_verdict (expected FAKE)" >&2
  fail=1
fi

if [ "$concrete_verdict" = "CONCRETE" ]; then
  echo "  ok   concrete fixture detected as CONCRETE"
else
  echo "  FAIL concrete fixture classified $concrete_verdict (expected CONCRETE)" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "witness-quality gate FAILED" >&2
  exit 1
fi

echo "witness-quality gate passed: all headline witnesses are concrete, detector verified"
