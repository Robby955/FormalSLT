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
  "FormalSLT.PACBayesKL.informationTheory_klDiv_toPMF_eq_of_support"
  "FormalSLT.PACBayesKL.toReal_informationTheory_klDiv_toPMF_eq_of_support"
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
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching.average_perm_pair_eq_average_all_pairs"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching.average_perm_pairSquaredDifference_eq_sampleVarianceBessel"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching.average_perm_pairCatalog_eq_sampleVarianceBessel"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching.finitePairBlock_factorization"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching.average_perm_finiteCanonicalPairMean_eq_sampleVarianceBessel"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF.finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin"
  "FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes.finiteEmpiricalVariance_posteriorGap_le_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes.finiteEmpiricalVariancePACBayes_badEventMass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes.posteriorPopulationVariance_le_empiricalVariance_of_not_mem"
  "FormalSLT.Probability.FiniteUnionBound.finiteWeightedUnionBound_sum_le_of_exists_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog.finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog.posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk.finiteEmpiricalBernsteinRisk_badEventMass_le"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk.posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem"
  "FormalSLT.PACBayes.FiniteBoundedLossBernstein.boundedLoss_product_normalizedMGF_le_one"
  "FormalSLT.PACBayes.FiniteBoundedLossBernstein.boundedLoss_expectedPriorBernsteinExpMoment_le_one"
  "FormalSLT.PACBayes.FiniteBoundedLossBernstein.boundedLoss_posteriorRisk_le_populationVariance_of_not_mem"
  "FormalSLT.PACBayes.FiniteBoundedLossBernstein.finiteBoundedLossBernstein_badEventMass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog.finiteBoundedLossBernstein_weightedCatalog_badEventMass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog.posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_of_not_mem"
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
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_logResidual_nonpos_of_balance"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_posteriorRisk_le_empiricalRisk_add_empiricalVariance_zeroResidual_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes.finiteJointMeanVariance_posteriorRisk_le_empiricalRisk_add_empiricalVariance_zeroResidual_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceResidual.finiteJointMeanVarianceResidual_le_xi"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceResidual.finiteJointMeanVarianceXi_attained"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceResidual.finiteJointMeanVarianceXi_isGreatest"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceResidual.finiteJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceResidual.finiteJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteJointMeanVariance_balance_of_tilt"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteJointMeanVariance_balance_of_scale"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinScale_badSamples_mass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernstein_posteriorRisk_le_scale_selected_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.exists_dyadicScale_optimizer_bound"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinDyadic_posteriorRisk_le_sqrt_of_not_mem"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinGridDepth_coverage"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinSqrt_badSamples_mass_le_delta"
  "FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt.finiteEmpiricalBernsteinSqrt_posteriorRisk_le_of_not_mem"
  "FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.infiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta"
  "FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.infiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem"
  "FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.exists_infiniteEmpiricalBernstein_event"
  "FormalSLT.AnytimeValid.forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel"
  "FormalSLT.AnytimeValid.forwardPredictorProcess_one_sub"
  "FormalSLT.AnytimeValid.incrementAdapted_one_sub"
  "FormalSLT.AnytimeValid.forwardPredictorProcess_mem_Icc_of_mem_Icc"
  "FormalSLT.AnytimeValid.sum_mean_sub_eq_mul_sub_forwardPrefixMean"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinProcess_le_of_mem_Icc"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinFactor_le_of_mem_Icc"
  "FormalSLT.AnytimeValid.forwardPredictableQuadratic_le_half_add_three_halves_besselQ"
  "FormalSLT.AnytimeValid.forwardPredictableQuadratic_abel_welford"
  "FormalSLT.AnytimeValid.forwardPredictableQuadratic_le_harmonic_bessel"
  "FormalSLT.AnytimeValid.forwardPredictableQuadratic_le_hybrid_bessel"
  "FormalSLT.AnytimeValid.forwardBessel_coefficient_one_bool_obstruction"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinProcess_eProcess_of_bounded"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerProcess_atTop_crossing_mass_le_delta"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerBesselEnvelope_le_lowerProcess"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerBesselFailure_mass_le_delta"
  "FormalSLT.AnytimeValid.exists_forwardEmpiricalBernsteinLowerBessel_event"
  "FormalSLT.AnytimeValid.finiteWeightedProcess_eProcess"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerTiltMixtureProcess_eProcess_of_bounded"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerTiltMixtureProcess_atTop_crossing_mass_le_delta"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerTiltCatalogFailure_mass_le_delta"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerTiltCatalog_all_of_not_mem"
  "FormalSLT.AnytimeValid.forwardEmpiricalBernsteinLowerTiltCatalog_selected_of_not_mem"
  "FormalSLT.AnytimeValid.exists_forwardEmpiricalBernsteinLowerTiltCatalog_event"
  "FormalSLT.AnytimeValid.exists_forwardEmpiricalBernsteinLowerTiltCatalog_selected_event"
  "FormalSLT.PACBayes.ForwardBesselPACBayes.posteriorAverage_forwardBesselPACBayesScore"
  "FormalSLT.PACBayes.ForwardBesselPACBayes.forwardBesselPACBayesMasterProcess_eProcess_of_bounded"
  "FormalSLT.PACBayes.ForwardBesselPACBayes.forwardBesselPACBayesExceptionalEvent_mass_le_delta"
  "FormalSLT.PACBayes.ForwardBesselPACBayes.forwardBesselPACBayes_boundaryFailure_mem_exceptionalEvent"
  "FormalSLT.PACBayes.ForwardBesselPACBayes.forwardBesselPACBayes_allPosteriors_of_not_mem"
  "FormalSLT.PACBayes.ForwardBesselPACBayes.forwardBesselPACBayes_selected_of_not_mem"
  "FormalSLT.PACBayes.ForwardBesselPACBayes.exists_forwardBesselPACBayes_event"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.forwardPrefixMean_iidObservedLoss"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.posteriorAverage_forwardPrefixMean_iidObservedLoss"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.iidObservedLoss_incrementAdapted"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.iidObservedLoss_integrable"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.iidObservedLoss_condExp_eq_populationRisk"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.forwardIIDBesselPACBayesExceptionalEvent_mass_le_delta"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.forwardIIDBesselPACBayes_allPosteriors_of_not_mem"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.forwardIIDBesselPACBayes_selected_of_not_mem"
  "FormalSLT.PACBayes.ForwardBesselPACBayesIID.exists_forwardIIDBesselPACBayes_event"
  "FormalSLT.PACBayes.TimeUniformContinuous.continuousPriorMixture_submartingale"
  "FormalSLT.PACBayes.FiniteJointMeanVarianceReverse.reverseJointMeanVarianceEpochExponentialProcess_samplePermutation"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.continuousReverseJointMeanVarianceEpochPriorMixture_submartingale_of_integrable"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.reverseJointMeanVarianceEpochExponentialProcess_integrable_prod"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.continuousReverseJointMeanVarianceEpochPriorMixture_submartingale_of_measurable_bounded"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.continuousReverseJointMeanVarianceEpochPriorMixture_endpoint_integral_le_one"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.continuousReverseJointMeanVarianceEpochPriorMixture_maximal_le_one"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.continuousReverseJointMeanVarianceEpochBadPaths_mass_le_delta_of_measurable_bounded"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.continuousReverseJointMeanVarianceEpochCatalogBadPaths_mass_le_delta"
  "FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse.continuousReverseJointMeanVarianceEpochCatalog_posteriorRisk_prefix_lt_selected_of_not_mem"
  "FormalSLT.PACBayes.ContinuousEmpiricalBernsteinReverseSqrt.continuousEmpiricalBernsteinReverseSqrtFailure_mass_le_delta"
  "FormalSLT.PACBayes.ContinuousEmpiricalBernsteinReverseSqrt.continuousEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem"
  "FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.continuousInfiniteEmpiricalBernsteinReverseSqrtFailure_measurable"
  "FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.continuousInfiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta"
  "FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.continuousInfiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem"
  "FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch.exists_continuousInfiniteEmpiricalBernstein_event"
  "FormalSLT.PACBayes.CountableJointMeanVariancePACBayes.countableJointMeanVarianceMasterMixture_nonneg"
  "FormalSLT.PACBayes.CountableJointMeanVariancePACBayes.countableJointMeanVariance_weightedPriorMoments_summable_of_sampleWeight_pos"
  "FormalSLT.PACBayes.CountableJointMeanVariancePACBayes.countableJointMeanVariance_masterMixture_expectation_le_weightTsum"
  "FormalSLT.PACBayes.CountableJointMeanVariancePACBayes.countableJointMeanVariance_masterMixture_expectation_le_one"
  "FormalSLT.PACBayes.CountableJointMeanVariancePACBayes.countableJointMeanVariance_not_mem_catalogBadSamples_iff"
  "FormalSLT.PACBayes.CountableJointMeanVariancePACBayes.countableJointMeanVariance_catalogBadSamples_mass_le_delta"
  "FormalSLT.PACBayes.CountableJointMeanVariancePACBayes.countableJointMeanVariance_priorMoment_le_of_not_mem"
  "FormalSLT.PACBayes.CountableJointMeanVariancePosterior.countableJointMeanVariance_posteriorScore_le_of_not_mem"
  "FormalSLT.PACBayes.CountableJointMeanVariancePosterior.countableJointMeanVariance_posteriorGap_le_of_not_mem"
  "FormalSLT.PACBayes.CountableJointMeanVariancePosterior.countableJointMeanVariance_posteriorRisk_le_with_xi_of_not_mem"
  "FormalSLT.PACBayes.CountableJointMeanVariancePosterior.countableJointMeanVariance_posteriorRisk_le_with_xi_selected_of_not_mem"
  "FormalSLT.PACBayes.TimeUniformScore.scorePriorMixture_eProcess"
  "FormalSLT.PACBayes.TimeUniformScore.timeUniformScorePACBayesAnyPosteriorFailure_subset_crossing"
  "FormalSLT.PACBayes.TimeUniformScore.timeUniformScorePACBayes_allPosteriors_bound"
  "FormalSLT.PACBayes.TimeUniformScore.posteriorTarget_le_of_not_mem_timeUniformScorePACBayesFailure"
  "FormalSLT.PACBayes.TimeUniform.pacBayesPriorTiltMixture_eProcess"
  "FormalSLT.PACBayes.TimeUniform.pacBayesPriorTiltMixture_optionalContinuation"
  "FormalSLT.PACBayes.TimeUniform.timeUniformPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_crossing"
  "FormalSLT.PACBayes.TimeUniform.timeUniformPACBayes_tiltMixture_allPosteriors_bound"
  "FormalSLT.PACBayes.TimeUniform.timeUniformPACBayes_tiltMixture_selected_of_not_mem"
  "FormalSLT.PACBayes.TimeUniformIIDTiltMixture.timeUniformIIDPACBayesTiltMixtureMeasurableExceptionalEvent_measurable"
  "FormalSLT.PACBayes.TimeUniformIIDTiltMixture.timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_measurableExceptionalEvent"
  "FormalSLT.PACBayes.TimeUniformIIDTiltMixture.timeUniformIIDPACBayesTiltMixtureAnyPosteriorUpperFailure_subset_processFailure"
  "FormalSLT.PACBayes.TimeUniformIIDTiltMixture.timeUniformIIDPACBayes_tiltMixture_allPosteriors_bound"
  "FormalSLT.PACBayes.TimeUniformIIDTiltMixture.timeUniformIIDPACBayes_tiltMixture_measurableExceptionalEvent_spec"
  "FormalSLT.PACBayes.TimeUniformIIDTiltMixture.timeUniformIIDPACBayes_tiltMixture_allPosteriors_of_not_mem_measurableExceptionalEvent"
  "FormalSLT.PACBayes.TimeUniformIIDTiltMixture.timeUniformIIDPACBayes_tiltMixture_selected_of_not_mem_measurableExceptionalEvent"
  "FormalSLT.StochasticDynamics.observedTrajectoryScore_condExp"
  "FormalSLT.StochasticDynamics.trajectoryRiskInnovation_incrementAdapted"
  "FormalSLT.StochasticDynamics.trajectoryRiskInnovation_condExp_eq_zero"
  "FormalSLT.StochasticDynamics.trajectoryRiskInnovation_condSecondMoment_le_one_fourth"
  "FormalSLT.StochasticDynamics.pathSquaredLoss_condExp_via_trajectory"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_observedTrajectoryScore_succ_of_joint"
  "FormalSLT.StochasticDynamics.measurable_observedTrajectoryScore_of_joint"
  "FormalSLT.StochasticDynamics.integrable_observedTrajectoryScore_of_joint"
  "FormalSLT.StochasticDynamics.integral_observedTrajectoryScore_traj_of_joint"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_conditionalTrajectoryRisk_of_joint"
  "FormalSLT.StochasticDynamics.conditionalTrajectoryRisk_mem_Icc_of_joint"
  "FormalSLT.StochasticDynamics.integrable_conditionalTrajectoryRisk_of_joint"
  "FormalSLT.StochasticDynamics.observedTrajectoryScore_condExp_of_joint"
  "FormalSLT.StochasticDynamics.trajectoryRiskInnovation_incrementAdapted_of_joint"
  "FormalSLT.StochasticDynamics.integrable_trajectoryRiskInnovation_of_joint"
  "FormalSLT.StochasticDynamics.abs_trajectoryRiskInnovation_le_one_of_joint"
  "FormalSLT.StochasticDynamics.trajectoryRiskInnovation_condExp_eq_zero_of_joint"
  "FormalSLT.StochasticDynamics.trajectoryRiskInnovation_condSecondMoment_le_one_fourth_of_joint"
  "FormalSLT.StochasticDynamics.measurableTrajectoryRiskShortfall_eq_neg_innovation"
  "FormalSLT.StochasticDynamics.measurableTrajectoryRiskShortfall_incrementAdapted_of_joint"
  "FormalSLT.StochasticDynamics.abs_measurableTrajectoryRiskShortfall_le_one_of_joint"
  "FormalSLT.StochasticDynamics.measurableTrajectoryRiskShortfall_condExp_eq_zero_of_joint"
  "FormalSLT.StochasticDynamics.measurableTrajectoryRiskShortfall_condSecondMoment_le_one_fourth_of_joint"
  "FormalSLT.StochasticDynamics.clippedRealTrajectoryScore_jointlyStronglyMeasurable"
  "FormalSLT.StochasticDynamics.clippedRealTrajectoryScore_mem_Icc"
  "FormalSLT.StochasticDynamics.clippedRealTrajectoryScore_condExp"
  "FormalSLT.StochasticDynamics.clippedRealTrajectoryRisk_zero_prefix"
  "FormalSLT.StochasticDynamics.jointlyStronglyMeasurableTrajectoryScore_section"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_observedTrajectoryScore_parameter_of_joint"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint"
  "FormalSLT.StochasticDynamics.integrable_conditionalTrajectoryRisk_parameter_of_joint"
  "FormalSLT.StochasticDynamics.observedTrajectoryScore_incrementAdapted_parameterized_of_joint"
  "FormalSLT.StochasticDynamics.conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint"
  "FormalSLT.StochasticDynamics.observedTrajectoryScore_condExp_parameterized_of_joint"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_observedTrajectoryScore_joint_filtered"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_continuousMeasurableTrajectoryLowerProcess_filtered"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_trajectory_ambient_of_filtered_prod"
  "FormalSLT.StochasticDynamics.exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event"
  "FormalSLT.StochasticDynamics.pathSquaredLoss_condExp"
  "FormalSLT.StochasticDynamics.markovRiskInnovation_condSecondMoment_le_one_fourth"
  "FormalSLT.StochasticDynamics.markovPrequentialRiskExceptionalEvent_mass_le_delta"
  "FormalSLT.StochasticDynamics.averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem"
  "FormalSLT.StochasticDynamics.markovPACBayesExceptionalEvent_mass_le_delta"
  "FormalSLT.StochasticDynamics.markovPACBayes_prequentialRisk_certificate"
  "FormalSLT.StochasticDynamics.markovPACBayesTiltMixtureExceptionalEvent_mass_le_delta"
  "FormalSLT.StochasticDynamics.markovPACBayes_tiltMixture_prequentialRisk_certificate"
  "FormalSLT.StochasticDynamics.trajectoryRiskShortfall_condExp_eq_zero"
  "FormalSLT.StochasticDynamics.trajectoryRiskShortfall_condSecondMoment_le_one_fourth"
  "FormalSLT.StochasticDynamics.trajectoryPACBayesTiltMixtureExceptionalEvent_mass_le_delta"
  "FormalSLT.StochasticDynamics.trajectoryPACBayes_tiltMixture_prequentialRisk_certificate"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.forwardPredictableMeanEmpiricalBernsteinLowerProcess_le_exp_card"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.stronglyMeasurable_forwardPrefixMean_parameter"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.stronglyMeasurable_forwardBesselQ_parameter"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.stronglyMeasurable_forwardHybridBesselPenalty_parameter"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.forwardPrefixMean_mem_Icc_of_unit"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.forwardHybridBesselPenalty_nonneg_of_unit"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.forwardHybridBesselPenalty_le_of_unit"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.continuousForwardPredictableMeanBesselPriorProcess_eProcess"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.continuousForwardPredictableMeanBesselMasterProcess_eProcess"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.continuousForwardPredictableMeanBesselExceptionalEvent_mass_le_delta"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.stronglyMeasurable_continuousForwardPredictableMeanBesselScore"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.continuousForwardPredictableMeanBesselScore_eq_prefixMeans"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.integrable_forwardPrefixMean_parameter_of_unit"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.integrable_forwardHybridBesselPenalty_parameter_of_unit"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.integrable_continuousForwardPredictableMeanBesselScore"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.integrable_exp_continuousForwardPredictableMeanBesselScore"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.integral_continuousForwardPredictableMeanBesselScore"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.continuousForwardPredictableMeanBessel_boundaryFailure_mem_exceptionalEvent"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.continuousForwardPredictableMeanBessel_allPosteriors_of_not_mem"
  "FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes.exists_continuousForwardPredictableMeanBesselPACBayes_event"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_uncurry_of_finite_discrete_right"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_conditionalTrajectoryRisk_parameter"
  "FormalSLT.StochasticDynamics.measurableSpace_prod_piLE_le_ambient"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_observedTrajectoryScore_parameter_prod"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_conditionalTrajectoryRisk_parameter_prod"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_continuousTrajectoryLowerProcess_filtered"
  "FormalSLT.StochasticDynamics.stronglyMeasurable_continuousTrajectoryLowerProcess_ambient"
  "FormalSLT.StochasticDynamics.continuousTrajectoryEmpiricalBernsteinPACBayesBoundary_eq_generic"
  "FormalSLT.StochasticDynamics.continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic"
  "FormalSLT.StochasticDynamics.continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic"
  "FormalSLT.StochasticDynamics.exists_continuousTrajectoryEmpiricalBernsteinPACBayes_event"
)

# Axioms permitted in a clean proof.
ALLOWED=("propext" "Classical.choice" "Quot.sound")

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
CHECK="$WORK/CheckAxiomsGate.lean"

{
  echo "import FormalSLT.PACBayes.FinitePMFBridge"
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
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk"
  echo "import FormalSLT.PACBayes.FiniteBoundedLossBernstein"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog"
  echo "import FormalSLT.PACBayes.FiniteExponentialTilt"
  echo "import FormalSLT.PACBayes.FiniteExponentialTiltProduct"
  echo "import FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt"
  echo "import FormalSLT.PACBayes.FiniteJointMeanVarianceMGF"
  echo "import FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes"
  echo "import FormalSLT.PACBayes.FiniteJointMeanVarianceResidual"
  echo "import FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt"
  echo "import FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch"
  echo "import FormalSLT.AnytimeValid.ForwardBesselProcess"
  echo "import FormalSLT.PACBayes.ForwardBesselPACBayes"
  echo "import FormalSLT.PACBayes.ForwardBesselPACBayesIID"
  echo "import FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch"
  echo "import FormalSLT.PACBayes.CountableJointMeanVariancePACBayes"
  echo "import FormalSLT.PACBayes.CountableJointMeanVariancePosterior"
  echo "import FormalSLT.PACBayes.TimeUniformScorePACBayes"
  echo "import FormalSLT.PACBayes.TimeUniformTiltMixture"
  echo "import FormalSLT.PACBayes.TimeUniformIIDTiltMixture"
  echo "import FormalSLT.StochasticDynamics.TrajectoryRisk"
  echo "import FormalSLT.StochasticDynamics.MeasurableTrajectoryRisk"
  echo "import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes"
  echo "import FormalSLT.StochasticDynamics.MarkovRisk"
  echo "import FormalSLT.StochasticDynamics.MarkovPACBayes"
  echo "import FormalSLT.StochasticDynamics.MarkovPACBayesTiltMixture"
  echo "import FormalSLT.StochasticDynamics.TrajectoryPACBayes"
  echo "import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes"
  echo "import FormalSLT.StochasticDynamics.ContinuousTrajectoryEmpiricalBernsteinPACBayes"
  for t in "${THEOREMS[@]}"; do
    echo "#print axioms $t"
  done
} > "$CHECK"

echo "== building flagship modules =="
"$LAKE" build \
  FormalSLT.PACBayes.FinitePMFBridge \
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
  FormalSLT.PACBayes.FiniteEmpiricalVarianceMatching \
  FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF \
  FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes \
  FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog \
  FormalSLT.PACBayes.FiniteEmpiricalBernsteinRisk \
  FormalSLT.PACBayes.FiniteBoundedLossBernstein \
  FormalSLT.PACBayes.FiniteEmpiricalBernsteinRiskCatalog \
  FormalSLT.PACBayes.FiniteExponentialTilt \
  FormalSLT.PACBayes.FiniteExponentialTiltProduct \
  FormalSLT.PACBayes.FiniteBoundedLossExponentialTilt \
  FormalSLT.PACBayes.FiniteJointMeanVarianceMGF \
  FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes \
  FormalSLT.PACBayes.FiniteJointMeanVarianceResidual \
  FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt \
  FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch \
  FormalSLT.AnytimeValid.ForwardBesselProcess \
  FormalSLT.PACBayes.ForwardBesselPACBayes \
  FormalSLT.PACBayes.ForwardBesselPACBayesIID \
  FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch \
  FormalSLT.PACBayes.CountableJointMeanVariancePACBayes \
  FormalSLT.PACBayes.CountableJointMeanVariancePosterior \
  FormalSLT.PACBayes.TimeUniformScorePACBayes \
  FormalSLT.PACBayes.TimeUniformTiltMixture \
  FormalSLT.PACBayes.TimeUniformIIDTiltMixture \
  FormalSLT.StochasticDynamics.TrajectoryRisk \
  FormalSLT.StochasticDynamics.MeasurableTrajectoryRisk \
  FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes \
  FormalSLT.StochasticDynamics.MarkovRisk \
  FormalSLT.StochasticDynamics.MarkovPACBayes \
  FormalSLT.StochasticDynamics.MarkovPACBayesTiltMixture \
  FormalSLT.StochasticDynamics.TrajectoryPACBayes \
  FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes \
  FormalSLT.StochasticDynamics.ContinuousTrajectoryEmpiricalBernsteinPACBayes >/dev/null

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
