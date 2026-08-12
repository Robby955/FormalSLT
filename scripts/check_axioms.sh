#!/usr/bin/env bash
# Axiom gate for the flagship public theorem.
#
# Why this exists: the "Verify no custom axioms" grep step only catches literal
# `axiom` declarations. It does NOT catch axioms pulled in transitively by
# kernel-trusting tactics such as `native_decide`, which leaks
# `Lean.ofReduceBool`. This script runs `#print axioms` over the flagship public
# theorems and fails if any axiom outside the allowed set appears.
#
# Allowed axioms: propext, Classical.choice, Quot.sound (the standard Lean
# classical foundation). Anything else, in particular Lean.ofReduceBool,
# Lean.trustCompiler, or sorryAx, fails the gate.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

LAKE="${LAKE:-$HOME/.elan/bin/lake}"

# Flagship public theorems to audit (fully qualified).
THEOREMS=(
  "FormalSLT.TestTimeMeta.flagshipFourComponent_four_slots_positive"
  "FormalSLT.TestTimeMeta.flagshipFourComponent_scalarBounds_from_incrementModel"
  "FormalSLT.TestTimeMeta.flagshipFourComponent_population_le_bound_from_incrementModel"
  "FormalSLT.TestTimeMeta.flagshipFourComponent_conclusion_from_incrementModel"
  "FormalSLT.TestTimeMeta.flagshipAnytimeValid_conclusion_from_incrementModel"
  "FormalSLT.PACBayes.IIDContinuousGaussian.timeUniformIIDGaussianPACBayes_bound"
  "FormalSLT.PACBayes.IIDContinuousGaussian.fairBoolGaussianPACBayesFailure_mass_ge_twoPowNegHundred"
  "FormalSLT.PACBayes.IIDContinuousGaussian.fairBoolGaussianPACBayesFailure_mass_pos"
  "FormalSLT.PACBayes.IIDContinuousGaussian.fairBoolThreshold_endToEnd_certificate"
  "FormalSLT.PACBayes.IIDContinuousGaussianGrid.timeUniformIIDGaussianPACBayes_grid_bound"
  "FormalSLT.PACBayes.IIDContinuousGaussianGrid.timeUniformIIDGaussianPACBayes_selected_bound"
  "FormalSLT.PACBayes.IIDContinuousGaussianGrid.fairBoolThreshold_twoGaussianGrid_certificate"
  "FormalSLT.PACBayes.IIDContinuousGaussianGrid.fairBoolThreshold_twoGaussianSelected_certificate"
  "FormalSLT.Probability.BernsteinMGF.bennett_mgf_le_one_add"
  "FormalSLT.PACBayes.IndicatorVariance.indicatorDeviation_secondMoment_eq"
  "FormalSLT.PACBayes.FiniteProductBernstein.indicator_product_normalizedMGF_le_one"
  "FormalSLT.PACBayes.IndicatorBernsteinMoment.indicator_expectedPriorBernsteinExpMoment_le_one"
  "FormalSLT.PACBayes.IndicatorBernsteinConfidence.indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta"
  "FormalSLT.PACBayes.IndicatorBernsteinLowRisk.indicator_posteriorRisk_le_min_one_twoThirds_of_not_mem"
  "FormalSLT.PACBayes.IndicatorBernsteinLowRisk.indicator_finitePACBayesBernstein_twoThirds_badEventMass_le_delta"
  "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta"
  "FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog.indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalVariance.finiteEmpiricalVariance_eq_pairwise"
  "FormalSLT.PACBayes.FiniteEmpiricalVariance.finiteEmpiricalVariance_unbiased_finiteProduct"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF.finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin"
  "FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes.finiteEmpiricalVariancePACBayes_badEventMass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes.posteriorPopulationVariance_le_empiricalVariance_of_not_mem"
  "FormalSLT.Probability.FiniteUnionBound.finiteWeightedUnionBound_sum_le_of_exists_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog.finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog.posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk.finiteEmpiricalBernsteinRisk_badEventMass_le"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk.posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog.finiteEmpiricalBernsteinRisk_weightedCatalog_badEventMass_le"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog.posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteExponentialTilt.finiteExponentialTiltPMF_isPMF"
  "FormalSLT.PACBayes.FiniteExponentialTilt.finiteExponentialTilt_changeOfMeasure"
  "FormalSLT.PACBayes.FiniteExponentialTiltProduct.finiteProductSampleWeight_mul_exp_sum_eq"
  "FormalSLT.PACBayes.FiniteExponentialTiltProduct.finiteProductExponentialTilt_changeOfMeasure"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finiteBoundedLossTiltPMF_isPMF"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finiteBoundedLossTilt_changeOfMeasure"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finiteBoundedLossTiltProduct_changeOfMeasure"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finiteBoundedLossTiltNormalizer_le_one"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finiteBoundedLossTilt_exp_neg_mul_le"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finiteWeightedSquaredError_eq_populationVariance_add_sq"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finitePopulationVariance_le_weightedSquaredError"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finitePopulationVariance_mul_exp_neg_le_tilted"
  "FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt.finiteBoundedLoss_centeredBennettNormalizer_le"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceMGF.finiteJointMeanVarianceKappa_nonneg_of_eta_mul_card_le"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceMGF.finiteBoundedLossTilt_negativeEmpiricalVarianceMGF_le"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceMGF.finiteJointMeanVarianceMGF_le"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceMGF.finiteJointMeanVariance_normalizedMGF_le_one"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_priorMoment_expectation_le_one"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_masterMixture_expectation_le_one"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_catalogBadSamples_mass_le_delta"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_priorMoment_le_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_posteriorScore_le_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_posteriorGap_le_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_posteriorGap_div_le_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_posteriorGap_le_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_posteriorGap_div_le_selected_of_not_mem"
  "FormalSLT.StochasticDynamics.pathSquaredLoss_condExp"
  "FormalSLT.StochasticDynamics.markovRiskInnovation_condSecondMoment_le_one_fourth"
  "FormalSLT.StochasticDynamics.markovPrequentialRiskExceptionalEvent_mass_le_delta"
  "FormalSLT.StochasticDynamics.averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem"
  "FormalSLT.StochasticDynamics.markovPACBayesExceptionalEvent_mass_le_delta"
  "FormalSLT.StochasticDynamics.markovPACBayes_prequentialRisk_certificate"
)

# Axioms permitted in a clean proof.
ALLOWED=("propext" "Classical.choice" "Quot.sound")

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
CHECK="$WORK/CheckAxiomsGate.lean"

{
  echo "import FormalSLT.TestTimeMeta.FlagshipFourComponentAssembly"
  echo "import FormalSLT.TestTimeMeta.FlagshipAnytimeValid"
  echo "import FormalSLT.PACBayes.IIDContinuousGaussian"
  echo "import FormalSLT.PACBayes.IIDContinuousGaussianGrid"
  echo "import FormalSLT.Probability.BernsteinMGF"
  echo "import FormalSLT.PACBayes.IndicatorVariance"
  echo "import FormalSLT.PACBayes.FiniteProductBernstein"
  echo "import FormalSLT.PACBayes.IndicatorBernsteinMoment"
  echo "import FormalSLT.PACBayes.IndicatorBernsteinConfidence"
  echo "import FormalSLT.PACBayes.IndicatorBernsteinLowRisk"
  echo "import FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVariance"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog"
  echo "import FormalSLT.PACBayes.FiniteExponentialTilt"
  echo "import FormalSLT.PACBayes.FiniteExponentialTiltProduct"
  echo "import FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt"
  echo "import FormalSLT.PACBayes.FiniteJointMeanVarianceMGF"
  echo "import FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes"
  echo "import FormalSLT.StochasticDynamics.MarkovRisk"
  echo "import FormalSLT.StochasticDynamics.MarkovPACBayes"
  for t in "${THEOREMS[@]}"; do
    echo "#print axioms $t"
  done
} > "$CHECK"

echo "== building flagship modules =="
"$LAKE" build \
  FormalSLT.TestTimeMeta.FlagshipFourComponentAssembly \
  FormalSLT.TestTimeMeta.FlagshipAnytimeValid \
  FormalSLT.PACBayes.IIDContinuousGaussian \
  FormalSLT.PACBayes.IIDContinuousGaussianGrid \
  FormalSLT.Probability.BernsteinMGF \
  FormalSLT.PACBayes.IndicatorVariance \
  FormalSLT.PACBayes.FiniteProductBernstein \
  FormalSLT.PACBayes.IndicatorBernsteinMoment \
  FormalSLT.PACBayes.IndicatorBernsteinConfidence \
  FormalSLT.PACBayes.IndicatorBernsteinLowRisk \
  FormalSLT.PACBayes.IndicatorBernsteinTiltCatalog \
  FormalSLT.PACBayes.FiniteEmpiricalVariance \
  FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF \
  FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes \
  FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog \
  FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk \
  FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog \
  FormalSLT.PACBayes.FiniteExponentialTilt \
  FormalSLT.PACBayes.FiniteExponentialTiltProduct \
  FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt \
  FormalSLT.PACBayes.FiniteJointMeanVarianceMGF \
  FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes \
  FormalSLT.StochasticDynamics.MarkovRisk \
  FormalSLT.StochasticDynamics.MarkovPACBayes >/dev/null

echo "== axiom audit =="
RAW="$("$LAKE" env lean "$CHECK" 2>&1)"
echo "$RAW"

# `#print axioms` wraps long axiom lists over several lines, so flatten them.
# Then strip the allowed axiom names and the structural words. Any remaining
# capitalized/qualified identifier is a forbidden axiom.
FLAT="$(printf '%s\n' "$RAW" | tr '\n' ' ')"

STRIPPED="$FLAT"
for a in "${ALLOWED[@]}"; do
  STRIPPED="${STRIPPED//$a/}"
done

# Hard failures: explicitly flag the usual offenders for a clear message.
# `native_decide` surfaces either `Lean.ofReduceBool` or a generated
# `..._native.native_decide.ax_*` axiom depending on the toolchain; match both.
FORBIDDEN_PATTERN='Lean\.ofReduceBool|Lean\.trustCompiler|Lean\.reduceBool|ofReduceBool|native_decide|_native\.|sorryAx'
if printf '%s\n' "$FLAT" | grep -Eq "$FORBIDDEN_PATTERN"; then
  echo "ERROR: forbidden axiom detected in flagship public API." >&2
  printf '%s\n' "$FLAT" | grep -Eo "$FORBIDDEN_PATTERN" | sort -u >&2
  exit 1
fi

# Catch-all: after removing allowed names, no dotted/qualified axiom token or a
# bare "depends on axioms: [Foo" residue should remain inside the bracketed
# lists. We extract the bracketed axiom lists and re-scan them.
LISTS="$(printf '%s\n' "$FLAT" | grep -Eo '\[[^]]*\]' || true)"
RESIDUE="$LISTS"
for a in "${ALLOWED[@]}"; do
  RESIDUE="${RESIDUE//$a/}"
done
# Remove brackets, commas, and whitespace; anything left is an unexpected axiom.
RESIDUE="$(printf '%s' "$RESIDUE" | tr -d '[],[:space:]')"
if [ -n "$RESIDUE" ]; then
  echo "ERROR: unexpected axiom(s) outside the allowed set: $RESIDUE" >&2
  exit 1
fi

# Sanity: each theorem must actually have been printed (guards against a rename
# silently dropping a target from the audit).
MISSING=0
for t in "${THEOREMS[@]}"; do
  # An axiom-free theorem prints "does not depend on any axioms" (no "depends on
  # axioms" substring), which is the cleanest case, so accept both phrasings.
  if grep -qF "'$t' depends on axioms" <<< "$RAW"; then
    continue
  fi
  if grep -qF "'$t' does not depend on any axioms" <<< "$RAW"; then
    continue
  fi
  echo "ERROR: no axiom report for $t (renamed or removed?)" >&2
  MISSING=1
done
[ "$MISSING" -eq 0 ] || exit 1

echo "axiom gate passed: only {propext, Classical.choice, Quot.sound}"
