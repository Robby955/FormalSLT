# Theorem Map

This page lists the public theorem spine by family. Names are Lean
declarations; modules are relative to `FormalSLT`.

## Core definitions

| Declaration | Module | Role |
|---|---|---|
| `risk` | `Risk` | Expected loss under a measure |
| `empiricalRisk` | `Risk` | Sample average loss |
| `IsERM` | `ERM` | Predicate selecting empirical risk minimizers over a finite class |
| `genGap` | `GhostSample` | One-sided uniform generalization gap |
| `piMeasure` | `GhostSample` | IID product measure on `Fin n -> Z` |
| `empiricalRademacherComplexity` | `Rademacher.FiniteSample` | Finite-sample empirical Rademacher complexity |
| `effectiveClass` | `VC.Rademacher` | Distinct loss vectors realized on a sample |
| `binaryClassTrace` | `VC.PACBridge` | Binary label patterns realized on a sample |
| `FiniteNet` | `Covering.FiniteSubGaussianChaining` | Finite net with an explicit nearest projection |

## Finite union and budget allocation

| Theorem | Module | Bound |
|---|---|---|
| `finiteMeasureUnionBound` | `Probability.FiniteUnionBound` | Finite-index measure union bound |
| `finiteMeasureUnionBound_budget` | `Probability.FiniteUnionBound` | Supplied finite per-event budgets whose sum is bounded by a total budget |
| `finiteMeasureUnionBound_const` | `Probability.FiniteUnionBound` | Common per-event budget gives `card * β` total mass |
| `finiteMeasureUnionBound_equalBudget` | `Probability.FiniteUnionBound` | Explicit per-event budget whose finite sum is bounded by a total budget |
| `finiteMeasureUnionBound_cardInv` | `Probability.FiniteUnionBound` | Nonempty finite class with per-event budget `α / card` has union mass `≤ α` |

## Uniform-convergence probability bridges

| Theorem | Module | Bound |
|---|---|---|
| `finiteClassUniformDeviationUnionBound` | `UniformConvergence` | Pointwise finite-class bad-event tails imply a simultaneous `card * tail` bound |
| `finiteClassUniformDeviationUnionBound_cardInv` | `UniformConvergence` | Equal split of a target failure budget gives simultaneous mass `≤ δ` |
| `finiteClassTwoSidedUniformDeviationUnionBound` | `UniformConvergence` | Pointwise absolute-deviation tails imply a simultaneous finite-class bound |
| `finiteClassTwoSidedUniformDeviationUnionBound_cardInv` | `UniformConvergence` | Equal-budget absolute-deviation bridge for finite hypothesis classes |
| `finiteTimeClassUnionBound_cardInv` | `UniformConvergence` | Equal-budget union bound over a finite time horizon and finite hypothesis class |
| `finiteTimeClassTwoSidedUniformDeviationUnionBound_cardInv` | `UniformConvergence` | Finite-horizon absolute-deviation shell over all `(time, hypothesis)` pairs |
| `finiteTimeClassUnionBound_timeBudget` | `UniformConvergence` | Finite time budgets whose sum is `≤ δ`, with each time split across hypotheses |
| `finiteTimeClassTwoSidedUniformDeviationUnionBound_timeBudget` | `UniformConvergence` | Finite-horizon absolute-deviation shell with a supplied time-budget sequence |
| `finiteTimeClassTwoSidedUniformDeviationUnionBound_timeBudget_threshold` | `UniformConvergence` | Finite-horizon absolute-deviation shell with a threshold depending on `(time, hypothesis)` |
| `finiteDyadicTimeBudget` | `UniformConvergence` | Standard dyadic time-budget schedule `δ * 2^(-1-t)` |
| `finiteDyadicTimeBudget_sum_fin_le` | `UniformConvergence` | Every finite prefix of the dyadic time-budget schedule sums to at most `δ` |
| `finiteDyadicTimeBudget_tsum_le` | `UniformConvergence` | The full natural-time dyadic schedule has total budget at most `δ` |
| `countableTimeClassUnionBound_timeBudget` | `UniformConvergence` | Countable-time finite-class union shell with a supplied summable time-budget sequence |
| `countableTimeClassUnionBound_dyadicBudget` | `UniformConvergence` | Countable-time finite-class union shell using the standard dyadic schedule |
| `countableTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold` | `UniformConvergence` | Countable-time dyadic absolute-deviation shell with time-varying thresholds |
| `countableTimeClass_iUnion_eq_exists` | `UniformConvergence` | Rewrites a countable time-class indexed union as an existential event |
| `countableTimeClass_not_forall_lt_eq_exists_ge` | `UniformConvergence` | Rewrites failure of an all-times/all-hypotheses strict bound as an existential crossing event |
| `finiteTimeClassUnionBound_dyadicBudget` | `UniformConvergence` | Finite-prefix time-class union shell using the standard dyadic schedule |
| `finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget` | `UniformConvergence` | Finite-prefix absolute-deviation shell using the standard dyadic schedule |
| `finiteTimeClassTwoSidedUniformDeviationUnionBound_dyadicBudget_threshold` | `UniformConvergence` | Finite-prefix dyadic absolute-deviation shell with time-varying thresholds |
| `finiteTimeClassTwoSidedUnionBoundFromOneSidedTails_dyadicBudget` | `UniformConvergence` | Finite-prefix dyadic shell from one-sided upper and lower pointwise tails |
| `empiricalAverageUpperHoeffdingTail` | `UniformConvergence` | Named `ENNReal` upper-tail budget produced by the fixed-hypothesis Hoeffding wrapper |
| `empiricalAverageLowerHoeffdingTail` | `UniformConvergence` | Named `ENNReal` lower-tail budget produced by the fixed-hypothesis Hoeffding wrapper |
| `finiteTimeClassEmpiricalAverageDeviationFromHoeffding_dyadicBudget` | `UniformConvergence` | Finite-prefix dyadic finite-class deviation bound from bounded independent empirical-average losses |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_dyadicBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper for bounded independent empirical-average losses |
| `empiricalAverageUpperHoeffdingTail_eq_lower` | `UniformConvergence` | Normalizes the upper-tail Hoeffding range expression to the lower-tail expression |
| `empiricalAverageTwoSidedHoeffdingTail` | `UniformConvergence` | Combined two-sided empirical-average Hoeffding budget |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_twoSidedTailBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using one combined two-sided Hoeffding budget |
| `empiricalAverageUniformRangeTwoSidedHoeffdingTail` | `UniformConvergence` | Uniform-range two-sided empirical-average Hoeffding budget with one denominator proxy |
| `empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail` | `UniformConvergence` | Algebraic bridge from the concrete finite sum of squared half-ranges to the uniform range proxy |
| `empiricalAverageRangeSum_le_card_mul_uniformRange` | `UniformConvergence` | Finite-sum range envelope from a pointwise uniform range-width bound |
| `empiricalAverageRangeSum_pos_of_exists_range_pos` | `UniformConvergence` | Positive finite-sum denominator certificate from one sampled coordinate with positive range |
| `empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound` | `UniformConvergence` | Two-sided Hoeffding tail bridge from a pointwise range-width bound and closed-form proxy |
| `empiricalAverageTwoSidedHoeffdingTail_le_uniformRangeTwoSidedHoeffdingTail_of_rangeBound_of_exists_range_pos` | `UniformConvergence` | Two-sided Hoeffding tail bridge using pointwise range width and an explicit nondegenerate sample coordinate |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using one uniform range proxy and dyadic time budgets |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget_of_rangeBound` | `UniformConvergence` | Shared-sample finite-prefix wrapper with pointwise uniform range width and one closed-form proxy |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_uniformRangeBudget_of_rangeBound_of_exists_range_pos` | `UniformConvergence` | Shared-sample finite-prefix wrapper with pointwise uniform range width and nondegenerate sample-coordinate certificates |
| `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail` | `UniformConvergence` | Displayed two-sided Hoeffding budget `2 * exp(-2 * sampleSize * ε^2 / R^2)` |
| `empiricalAverageUniformRangeTwoSidedHoeffdingTail_eq_sampleSizeTail` | `UniformConvergence` | Algebraic identification between the range-proxy budget and the sample-size display |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize` | `UniformConvergence` | Shared-sample finite-prefix wrapper using the displayed sample-size Hoeffding budget |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_threshold` | `UniformConvergence` | Shared-sample finite-prefix wrapper using a displayed sample-size Hoeffding budget and time-varying thresholds |
| `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_logBudget` | `UniformConvergence` | Real log-budget condition implies the displayed Hoeffding tail fits a target budget |
| `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_explicitRadius` | `UniformConvergence` | Unit-range displayed Hoeffding tail is bounded at the inverted square-root confidence radius |
| `empiricalAverageUniformRangeTwoSidedHoeffdingSampleSizeTail_le_of_sampleSize_ge` | `UniformConvergence` | Explicit sample-size lower bound implies the displayed Hoeffding tail fits a target budget |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_from_logBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using real log budgets below the dyadic ENNReal budget split |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_ge` | `UniformConvergence` | Shared-sample finite-prefix wrapper using explicit sample-size lower bounds and real budgets |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_sampleSize_dyadicRealBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using explicit sample-size lower bounds and the concrete dyadic real budget `δ * 2^(-1-t) / card(H)` |
| `finiteDyadicRealBudget_classBudget_ofReal` | `UniformConvergence` | Concrete real dyadic class budget maps exactly to the `ENNReal` dyadic time/class split |
| `empiricalAverageUniformRangeSampleSize_ge_of_sqrtBudget_le` | `UniformConvergence` | Algebraic bridge from a square-root radius condition to the displayed sample-size lower bound |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_epsilonOfSampleSize_dyadicRealBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using a radius-style condition and the concrete dyadic real budget |
| `finiteDyadicRealBudget_horizon_le_time` | `UniformConvergence` | Finite-horizon dyadic real-budget monotonicity: the horizon budget is no larger than any prefix time budget |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_horizonUniformRadius_dyadicRealBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using one horizon-level radius condition |
| `finiteDyadicRealBudget_horizon_logBudget_eq_closedForm` | `UniformConvergence` | Closed-form rewrite of the finite-horizon dyadic log-budget term |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonRadius_dyadicRealBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using a closed-form horizon/class/budget radius |
| `finiteTimeClassSharedSampleEmpiricalAverageDeviationFromHoeffding_closedFormHorizonSampleSize_dyadicRealBudget` | `UniformConvergence` | Shared-sample finite-prefix wrapper using a closed-form horizon/class/budget sample-size condition |
| `finitePrefixFiniteClassDeviationFromHoeffding_closedForm` | `UniformConvergence` | Route-facing finite-prefix finite-class Hoeffding deviation theorem with the closed-form sample-size condition |
| `finitePrefixFiniteClassDeviationFromHoeffding_closedForm_cardSample` | `UniformConvergence` | Route-facing finite-prefix finite-class Hoeffding theorem with denominator written directly as `(s.card : ℝ)` |
| `finitePrefixFiniteClassDeviationFromHoeffding_closedForm_unitRange` | `UniformConvergence` | Route-facing unit-range finite-prefix finite-class Hoeffding theorem with compact `log(card/time/budget) / (2 * ε^2)` sample-size condition |
| `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_radius` | `UniformConvergence` | Route-facing unit-range finite-prefix finite-class Hoeffding theorem in confidence-radius form |
| `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius` | `UniformConvergence` | Route-facing unit-range finite-prefix finite-class Hoeffding theorem with the confidence radius written directly in the deviation event |
| `finitePrefixFiniteClassDeviationFromHoeffding_unitRange_explicitRadius_nonemptySample` | `UniformConvergence` | Route-facing explicit-radius theorem with radius positivity discharged by nonempty sample and strict finite-prefix budget assumptions |
| `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius` | `UniformConvergence` | Route-facing explicit-radius theorem for losses bounded in `[0,1]`, removing caller-supplied lower and upper range functions and discharging the negative-integral identity internally |
| `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius` | `UniformConvergence` | Finite-prefix time-varying dyadic-radius event from supplied pointwise tails and checked dyadic budget conversion |
| `finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding` | `UniformConvergence` | Finite-prefix time-varying dyadic-radius theorem for `[0,1]` losses with the pointwise tails discharged from Hoeffding |
| `zeroOneDyadicFiniteClassConfidenceRadius` | `UniformConvergence` | Named dyadic confidence radius for `[0,1]` finite-class empirical-average deviations |
| `zeroOneDyadicFiniteClassConfidenceRadius_le_of_sampleSize_ge` | `UniformConvergence` | Sample-size lower bound implies the named dyadic confidence radius is at most a target `ε` |
| `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_fromHoeffding` | `UniformConvergence` | Countable-time finite-class Hoeffding theorem for `[0,1]` losses with dyadic per-time radii |
| `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_timeVaryingRadius_exists_fromHoeffding` | `UniformConvergence` | Existential-event version of the countable-time finite-class Hoeffding theorem |
| `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_namedRadius_exists_fromHoeffding` | `UniformConvergence` | Existential-event anytime theorem using the named dyadic confidence radius |
| `finiteClassConfidenceSequenceFailureEvent` | `UniformConvergence` | Named failure event for the `[0,1]` finite-class dyadic confidence sequence |
| `FiniteClassConfidenceSequence` | `UniformConvergence` | Bundled assumptions for the `[0,1]` finite-class dyadic confidence sequence |
| `anytimeFiniteClassDeviationFromHoeffding_zeroOneRange_confidenceSequence_fromHoeffding` | `UniformConvergence` | Confidence-sequence failure-probability theorem for all natural times and finite hypotheses |
| `FiniteClassConfidenceSequence.failure_probability_le` | `UniformConvergence` | Bundled API theorem bounding the named confidence-sequence failure event |

## Rademacher and VC spine

| Theorem | Module | Bound |
|---|---|---|
| `expected_genGap_le_two_expected_empiricalRademacherComplexity` | `Rademacher.Symmetrization` | `E[genGap] <= 2 * E[Rad]` |
| `genGap_tail_bound_azuma_explicit` | `Azuma.GenGapTail` | `P(genGap - E[genGap] >= ε) <= exp(-ε² n / (8B²))` |
| `hasBoundedDifferences_tail_sharp` | `Azuma.GenGapTail` | `P(f - E[f] >= ε) <= exp(-2ε² / sum_k c_k²)` |
| `genGap_tail_bound_sharp_explicit` | `Azuma.GenGapTail` | `P(genGap - E[genGap] >= ε) <= exp(-ε² n / (2B²))` |
| `mcdiarmid_of_hasBoundedDifferences_sharp` | `Concentration.SharpMcDiarmid` | Public wrapper for the sharp product bounded-differences tail |
| `mcdiarmid_of_hasBoundedDifferences_sharp_lower` | `Concentration.SharpMcDiarmid` | Lower-tail wrapper obtained from the upper tail applied to `-f` |
| `mcdiarmid_twoSided_of_hasBoundedDifferences_sharp` | `Concentration.SharpMcDiarmid` | Two-sided homogeneous product bounded-differences tail `P(\|f - E[f]\| >= ε) <= 2 exp(-2ε² / sum_k c_k²)` |
| `mcdiarmid_of_hasBoundedDifferences_sharp_hetero` | `Concentration.HeterogeneousMcDiarmid` | Heterogeneous-law product upper tail with the sharp McDiarmid exponent |
| `mcdiarmid_of_hasBoundedDifferences_sharp_hetero_lower` | `Concentration.HeterogeneousMcDiarmid` | Heterogeneous-law product lower tail with the sharp McDiarmid exponent |
| `mcdiarmid_twoSided_of_hasBoundedDifferences_sharp_hetero` | `Concentration.HeterogeneousMcDiarmid` | Two-sided heterogeneous-law product tail `P(\|f - E[f]\| >= ε) <= 2 exp(-2ε² / sum_k c_k²)` |
| `mcdiarmid_of_hasBoundedDifferences_sharp_of_hetero` | `Concentration.HeterogeneousMcDiarmid` | Homogeneous recovery from the heterogeneous product theorem by taking a constant law family |
| `massart_finite_class` | `Rademacher.Massart` | `Rad(H,S) <= B * sqrt(2 * log card(H) / n)` |
| `genGap_highProb_rademacher` | `Rademacher.HighProbability` | `P(genGap >= 2 * E[Rad] + ε) <= exp(-ε² n / (2B²))` |
| `genGap_highProb_finiteClass` | `Rademacher.FiniteClassHighProb` | Massart plus sharp high-probability Rademacher |
| `uniformDeviation_highProb_finiteClass` | `Rademacher.UniformDeviation` | Two-sided finite-class uniform deviation with sharp one-sided tails |
| `sauerShelah_polynomial_bound` | `VC.SauerShelah` | `sum_{k<=d} C(n,k) <= (en/d)^d` |
| `empiricalRademacherComplexity_le_massart_effective` | `VC.Rademacher` | Effective-class Massart bound |
| `vcRademacher_pointwise` | `VC.SampleComplexity` | `Rad <= B * sqrt(2d * log(en/d) / n)` |
| `genGap_highProb_vcClass` | `VC.SampleComplexity` | VC-style one-sided genGap tail with sharp exponent |
| `uniformDeviation_highProb_vcClass` | `VC.SampleComplexity` | VC-style two-sided uniform deviation with sharp one-sided tails |
| `vc_erm_excessRisk_tail` | `VC.SampleComplexity` | VC-style ERM excess-risk tail with sharp concentration term |
| `vc_erm_sample_complexity` | `VC.SampleComplexity` | Closed-form VC ERM sample-complexity theorem with explicit `72 * B^2` constant |
| `effectiveClass_zeroOneLoss_card_eq_binaryClassTrace` | `VC.BinaryVCBridge` | Effective 0-1 loss patterns equal binary traces |
| `effectiveClass_zeroOneLoss_card_le_sauerShelah` | `VC.BinaryVCBridge` | Binary VC Sauer-Shelah corollary |

## Contraction and linear predictors

| Theorem | Module | Bound |
|---|---|---|
| `one_step_contraction` | `Rademacher.Contraction` | One coordinate replacement step for the finite contraction proof |
| `contraction_1lip` | `Rademacher.Contraction` | Finite-sample scalar contraction for 1-Lipschitz transforms |
| `contraction_empirical` | `Rademacher.Contraction` | Empirical Rademacher wrapper for 1-Lipschitz transforms |
| `empiricalRademacherComplexity_contraction_lipschitz` | `Rademacher.Contraction` | `Rad_S(φ ∘ F) <= L * Rad_S(F)` for finite scalar classes |
| `linearPredictor_rademacher_finiteDim` | `Rademacher.LinearPredictor` | `Rad <= R * n⁻¹ * sqrt(sum k, ||z k||²)` |
| `linearPredictor_rademacher_uniform_finiteDim` | `Rademacher.LinearPredictor` | `||z k|| <= B` implies `Rad <= R * B / sqrt n` |

## Covering and finite chaining

| Theorem | Module | Bound |
|---|---|---|
| `rademacher_covering_bound` | `Covering.Rademacher` | `Rad(F) <= ε + Rad(N_ε)` |
| `rademacher_covering_massart` | `Covering.Rademacher` | Covering plus Massart |
| `rademacher_two_step_chaining` | `Covering.DudleyChaining` | Two-scale finite chaining bound |
| `finite_expectedSup_le_of_mgf_log` | `Covering.FiniteSubGaussianChaining` | MGF control gives finite expected-sup entropy budget |
| `finite_expectedSup_le_of_subGaussian_mgf_sqrt` | `Covering.FiniteSubGaussianChaining` | Optimized finite sub-Gaussian max bound |
| `finite_chaining_expectation_bound` | `Covering.FiniteSubGaussianChaining` | Finite multiscale chaining decomposition in expectation |
| `finite_projected_chaining_expectation_bound` | `Covering.FiniteSubGaussianChaining` | Finite projected-supremum chaining without an identity terminal projection |
| `finite_chaining_expectation_bound_of_radius_sqrt` | `Covering.FiniteSubGaussianChaining` | Radius-bounded finite chaining with square-root entropy budgets |
| `finite_chaining_expectation_bound_of_net_sequence_pairs_sqrt` | `Covering.FiniteSubGaussianChaining` | Projection-pair entropy version for finite net sequences |
| `finite_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt` | `Covering.FiniteSubGaussianChaining` | Covering-number version for finite net sequences |
| `finite_projected_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt` | `Covering.FiniteSubGaussianChaining` | Projected finite-net chaining bound with covering-number entropy budgets |
| `FiniteNet.ProjectedIndex` | `Covering.FiniteSubGaussianChaining` | Finite image of a net projection, used to avoid a finite ambient index assumption |
| `finite_projectedNet_chaining_expectation_bound_of_net_sequence_coveringNumbers_sqrt` | `Covering.FiniteSubGaussianChaining` | Projected finite-net-image chaining bound without `[Fintype T]` |
| `FiniteDyadicDudleyInstance` | `Covering.FiniteSubGaussianChaining` | Packaged reusable finite dyadic Dudley instance: net sequence, coarse budget, variance positivity, and coarse projected-supremum bound |
| `FiniteDyadicDudleyInstance.SupremumAdapter` | `Covering.FiniteSubGaussianChaining` | Optional supplied-supremum adapter to a terminal projected finite-net supremum plus explicit terminal error |
| `FiniteDyadicDudleyInstance.projected_dudley_bound` | `Covering.FiniteSubGaussianChaining` | Projected finite-net Dudley bound from a packaged finite dyadic Dudley instance |
| `FiniteDyadicDudleyInstance.suppliedSup_dudley_bound` | `Covering.FiniteSubGaussianChaining` | Supplied-supremum finite Dudley bound from a packaged instance and adapter |
| `finite_dudley_entropy_sum_projection_pairs` | `Covering.FiniteSubGaussianChaining` | Finite Dudley-style entropy sum over projection-pair families |
| `finite_dudley_entropy_sum_coveringNumbers` | `Covering.FiniteSubGaussianChaining` | Finite Dudley-style entropy sum with covering-number products |
| `finite_dudley_entropy_sum_projection_pairs_geometric_radius` | `Covering.FiniteSubGaussianChaining` | Dyadic/geometric radius schedule for projection pairs |
| `finite_dudley_entropy_sum_coveringNumbers_geometric_radius` | `Covering.FiniteSubGaussianChaining` | Dyadic/geometric radius schedule for covering numbers |
| `finite_dudley_entropy_sum_projection_pairs_geometric_entropy_budget` | `Covering.FiniteSubGaussianChaining` | Per-scale entropy-budget wrapper for projection pairs |
| `finite_dudley_entropy_sum_coveringNumbers_geometric_entropy_budget` | `Covering.FiniteSubGaussianChaining` | Per-scale entropy-budget wrapper for covering numbers |
| `finite_dudley_entropy_sum_projection_pairs_geometric_uniform_entropy` | `Covering.FiniteSubGaussianChaining` | Uniform entropy cap collapses the dyadic sum to a `2 * radiusScale` budget for projection pairs |
| `finite_dudley_entropy_sum_coveringNumbers_geometric_uniform_entropy` | `Covering.FiniteSubGaussianChaining` | Uniform entropy cap collapses the dyadic covering-number sum to a `2 * radiusScale` budget |
| `finite_dudley_entropy_sum_projection_pairs_geometric_annulus_budget` | `Covering.FiniteSubGaussianChaining` | Finite dyadic annulus-budget bridge for projection pairs |
| `finite_dudley_entropy_sum_coveringNumbers_geometric_annulus_budget` | `Covering.FiniteSubGaussianChaining` | Finite dyadic annulus-budget bridge for covering numbers |
| `finite_dudley_entropy_sum_projection_pairs_geometric_integral_budget` | `Covering.FiniteSubGaussianChaining` | Finite dyadic entropy-integral budget for projection pairs |
| `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget` | `Covering.FiniteSubGaussianChaining` | Finite dyadic entropy-integral budget for covering numbers |
| `finiteDyadicEntropyAtRadiusUpperSum` | `Covering.FiniteSubGaussianChaining` | Finite dyadic entropy-at-radius upper sum sampled at lower annulus endpoints |
| `finiteDyadicEntropyIntegralBudget_one_const` | `Covering.FiniteSubGaussianChaining` | One-step dyadic entropy budget for a constant entropy envelope |
| `finiteDyadicEntropyIntegralBudget_le_entropyAtRadiusUpperSum` | `Covering.FiniteSubGaussianChaining` | Finite dyadic budget comparison to an entropy-at-radius upper sum |
| `finitePrefixSupEnvelope_const` | `Covering.FiniteSubGaussianChaining` | Constant scale budgets remain constant under the finite prefix-sup envelope |
| `finitePrefixSupEnvelope_eq_self_of_monotone` | `Covering.FiniteSubGaussianChaining` | Monotone scale budgets equal their finite prefix-sup envelope |
| `finite_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope` | `Covering.FiniteSubGaussianChaining` | Finite covering-count wrapper with a monotone prefix-sup entropy envelope |
| `finite_projected_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope` | `Covering.FiniteSubGaussianChaining` | Projected finite Dudley wrapper with a monotone prefix-sup entropy envelope |
| `finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_integral_budget_prefix_envelope` | `Covering.FiniteSubGaussianChaining` | Projected finite-net-image Dudley wrapper without `[Fintype T]` |
| `finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_integral_comparison` | `Covering.FiniteSubGaussianChaining` | Projected finite-net Dudley wrapper compared to a supplied finite entropy-at-radius integral budget |
| `shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral` | `Covering.FiniteSubGaussianChaining` | Shifted finite dyadic annulus integrals compose into one truncated interval integral |
| `finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral` | `Covering.FiniteSubGaussianChaining` | Finite entropy-at-radius upper sum dominated by a single truncated interval integral |
| `finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison` | `Covering.FiniteSubGaussianChaining` | Projected finite-net Dudley wrapper with a truncated interval-integral entropy budget |
| `finiteExpectation_supFunctional_le_projected_add_terminalError` | `Covering.FiniteSubGaussianChaining` | Finite expectation adapter from a supplied supremum functional to a projected finite-supremum surrogate |
| `finiteSup_skeleton_le_projectedSup_add_terminalError` | `Covering.FiniteSubGaussianChaining` | Finite skeleton supremum controlled by terminal projected finite-net supremum plus explicit error |
| `finiteExpectation_supFunctional_le_projected_add_skeleton_terminalError` | `Covering.FiniteSubGaussianChaining` | Expected supplied supremum controlled through explicit finite-skeleton and terminal-projection errors |
| `terminalApprox_of_pathwise_modulus` | `Covering.FiniteSubGaussianChaining` | Terminal net radius plus pathwise modulus discharges the terminal-projection approximation hypothesis |
| `terminalApprox_of_pathwise_modulus_radiusBound` | `Covering.FiniteSubGaussianChaining` | Radius-bound variant of terminal pathwise-modulus approximation |
| `finiteSup_le_skeletonSup_add_of_pointwise_approx` | `Covering.FiniteSubGaussianChaining` | Finite ambient supremum controlled by a finite skeleton under pointwise approximation |
| `supFunctional_le_skeletonSup_add_of_witnessed_pointwise_approx` | `Covering.FiniteSubGaussianChaining` | Supplied supremum functional controlled by an approximate witness and finite skeleton selector |
| `finite_supFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison` | `Covering.FiniteSubGaussianChaining` | Boundary-layer finite Dudley wrapper for a supplied supremum functional plus terminal error |
| `finite_separableSupFunctional_dudley_entropy_sum_coveringNumbers_geometric_entropy_truncatedIntervalIntegral_comparison` | `Covering.FiniteSubGaussianChaining` | Boundary-layer finite Dudley wrapper with explicit finite-skeleton and terminal-projection hypotheses |
| `finiteMetricCoverOfTotallyBoundedUniv` | `Covering.TotalBoundedDudley` | Totally bounded metric spaces admit finite covers at every positive real radius |
| `finiteNetOfTotallyBoundedUniv` | `Covering.TotalBoundedDudley` | Extracts the repo's bundled finite-net record from total boundedness |
| `dyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le` | `Covering.TotalBoundedDudley` | Dyadic total-bounded net schedule satisfies the adjacent-radius budget used by finite chaining |
| `dyadicChainingFiniteNetSequenceOfTotallyBounded` | `Covering.TotalBoundedDudley` | Packages the total-bounded dyadic net schedule as a `FiniteDyadicNetSequence` under global projection-pair hypotheses |
| `finiteDyadicDudleyInstanceOfTotallyBounded` | `Covering.TotalBoundedDudley` | Packages the total-bounded dyadic net schedule as a `FiniteDyadicDudleyInstance` when global coarse-budget and projection-pair hypotheses are available |
| `finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers` | `Covering.TotalBoundedDudley` | Total-bounded dyadic wrapper over the terminal projected finite-net image, without `[Fintype T]` |
| `finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_integral_comparison` | `Covering.TotalBoundedDudley` | Total-bounded projected finite-net wrapper compared to a supplied finite entropy-at-radius integral budget |
| `finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison` | `Covering.TotalBoundedDudley` | Total-bounded projected finite-net wrapper with one truncated interval-integral entropy budget |
| `finite_supFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison` | `Covering.TotalBoundedDudley` | Total-bounded boundary wrapper for a supplied supremum functional under explicit terminal approximation |
| `finite_separableSupFunctional_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison` | `Covering.TotalBoundedDudley` | Total-bounded boundary wrapper with explicit finite-skeleton/dense-net and terminal-projection assumptions |
| `finite_witnessedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison` | `Covering.TotalBoundedDudley` | Total-bounded Dudley boundary wrapper using approximate witnesses, finite skeleton selectors, and pathwise modulus |
| `EpsilonizedSupremumBoundaryChoice` | `Covering.TotalBoundedDudley` | Finite skeleton and terminal-scale certificate for an epsilonized Dudley boundary step |
| `finite_epsilonizedSup_modulus_dudley_totalBounded_dyadic_entropy_truncatedIntervalIntegral_comparison` | `Covering.TotalBoundedDudley` | For every positive error budget, a finite skeleton/terminal-scale certificate yields a Dudley bound with `+ eta` |
| `skeletonApprox_of_finiteCover_pathwiseModulus` | `Covering.TotalBoundedDudley` | Finite-cover radius plus pathwise modulus gives the finite-skeleton approximation hypothesis |
| `FiniteCoverSupremumBoundaryChoice` | `Covering.TotalBoundedDudley` | Finite-cover/pathwise-modulus certificate for the epsilonized Dudley boundary step |
| `finite_epsilonizedSup_dudley_totalBounded_of_finiteCoverSupremumBoundaryChoice` | `Covering.TotalBoundedDudley` | Epsilonized total-bounded Dudley wrapper from finite-cover and pathwise-modulus certificates |
| `finite_projected_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers` | `Covering.TotalBoundedDudley` | Total-bounded dyadic wrapper for the terminal projected supremum, without an identity terminal net |
| `finite_dudley_entropy_sum_totalBounded_dyadic_coveringNumbers` | `Covering.TotalBoundedDudley` | Finite-terminal total-bounded dyadic wrapper composed with the finite Dudley entropy-budget theorem |
| `totalBoundedCoveringNumberAtRadius` | `Covering.TotalBoundedDudleyCovering` | Half-open real-radius selected-cover-count staircase for the total-bounded dyadic net schedule |
| `totalBoundedCoveringNumberAtRadius_dyadic` | `Covering.TotalBoundedDudleyCovering` | The staircase samples the monotone prefix envelope of selected adjacent dyadic cover-count products at dyadic radii |
| `totalBoundedCoveringNumberAtRadiusENat_ne_top` | `Covering.TotalBoundedDudleyCovering` | The selected-cover-count staircase has a finite `ℕ∞` surface |
| `totalBoundedCoveringEntropyAtRadius_guarded` | `Covering.TotalBoundedDudleyCovering` | The induced entropy staircase satisfies the guarded closed-annulus condition |
| `totalBoundedCoveringEntropy_dominates_dyadicEnvelope_sample` | `Covering.TotalBoundedDudleyCovering` | Dyadic samples dominate the finite entropy prefix envelope used by total-bounded finite wrappers |
| `unitInterval_totalBoundedCoveringNumber_sample_positive` | `Covering.TotalBoundedDudleyCovering` | Concrete non-vacuity witness for the generic selected-cover-count surface on the unit interval |
| `minimalMetricCoveringNumber` | `Covering.TotalBoundedMinimalCovering` | Genuine minimal finite metric covering number for a nonempty totally bounded metric index space |
| `minimalMetricCoveringNumber_spec` | `Covering.TotalBoundedMinimalCovering` | The genuine minimal covering number is realized by a finite metric cover |
| `minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe` | `Covering.TotalBoundedMinimalCovering` | Any finite metric cover with at most `n` centers bounds the genuine minimal covering number by `n` |
| `minimalMetricCoveringNumber_pos` | `Covering.TotalBoundedMinimalCovering` | Nonempty totally bounded spaces have positive genuine minimal covering number at positive radius |
| `minimalMetricCoverOfTotallyBoundedUniv` | `Covering.TotalBoundedMinimalCovering` | Chooses a cardinal-minimal finite metric cover from the genuine minimal covering-number witness |
| `minimalMetricCoverOfTotallyBoundedUniv_card_eq` | `Covering.TotalBoundedMinimalCovering` | The chosen finite metric cover has cardinality exactly equal to the genuine minimal covering number |
| `minimalMetricCoverOfTotallyBoundedUniv_card_minimal` | `Covering.TotalBoundedMinimalCovering` | Every finite metric cover has at least as many centers as the chosen minimal cover |
| `minimalFiniteNetOfTotallyBoundedUniv_coveringNumber_eq` | `Covering.TotalBoundedMinimalCovering` | The bundled finite net built from the minimal cover has covering count equal to the genuine minimal covering number |
| `minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_coveringNumber_eq` | `Covering.TotalBoundedMinimalCovering` | The dyadic minimal-net schedule has genuine minimal covering count at each sampled radius |
| `minimalMetricCoveringNumber_le_dyadicSelectedCoveringNumber` | `Covering.TotalBoundedMinimalCovering` | The genuine minimal covering number is bounded by each selected dyadic finite-net count |
| `minimalMetricCoveringNumber_le_totalBoundedDyadicCoverCountEnvelope` | `Covering.TotalBoundedMinimalCovering` | The selected dyadic envelope dominates the genuine minimal covering number at sampled dyadic net radii |
| `unitInterval_minimalMetricCoveringNumber_sample_positive` | `Covering.TotalBoundedMinimalCovering` | Concrete non-vacuity witness for the genuine minimal covering number on the unit interval |
| `unitInterval_minimalMetricCoverOfTotallyBoundedUniv_sample_card_positive` | `Covering.TotalBoundedMinimalCovering` | Concrete non-vacuity witness for the chosen minimal finite cover on the unit interval |
| `totalBoundedSelectedCoverCount_dyadicProfileBound_of_boundaryChoice` | `Covering.TotalBoundedDudleySelectedCapstone` | Boundary certificates give the guarded dyadic upper-sum input for the selected-cover-count entropy profile |
| `continuous_dudley_entropy_integral_iSup_totalBounded_selectedCoverCountEnvelope_not_minimalCoveringNumber` | `Covering.TotalBoundedDudleySelectedCapstone` | Generic totally bounded continuous Dudley capstone with the selected-cover-count envelope integrand, not genuine minimal covering number |
| `unitInterval_totalBoundedSelectedCoverCountEnvelope_sample_positive` | `Covering.TotalBoundedDudleySelectedCapstone` | Unit-interval non-vacuity witness for the selected-cover-count envelope surface |
| `minimalDyadicChainingCoverCount_eq_minimalMetricCoveringNumber_mul` | `Covering.TotalBoundedDudleyMinimalCapstone` | Adjacent cardinal-minimal dyadic cover count equals the product of genuine minimal covering numbers at the sampled radii |
| `minimalDyadicCoverCountEntropyAtRadius_guarded` | `Covering.TotalBoundedDudleyMinimalCapstone` | Cardinal-minimal dyadic adjacent-product entropy staircase satisfies the guarded closed-annulus condition |
| `finite_projectedNet_dudley_entropy_sum_totalBounded_minimalDyadic_entropy_integral_comparison_nonempty` | `Covering.TotalBoundedDudleyMinimalCapstone` | Projected finite-chain Dudley wrapper threaded through the cardinal-minimal dyadic net schedule |
| `totalBoundedMinimalDyadicCoverCount_dyadicProfileBound_of_boundaryChoice` | `Covering.TotalBoundedDudleyMinimalCapstone` | Minimal-schedule boundary certificates give the guarded dyadic upper-sum input |
| `continuous_dudley_entropy_integral_iSup_totalBounded_minimalDyadicCoverCountEnvelope` | `Covering.TotalBoundedDudleyMinimalCapstone` | Generic totally bounded continuous Dudley capstone with the cardinal-minimal dyadic adjacent-product envelope |
| `unitInterval_minimalDyadicCoverCountEnvelope_sample_positive` | `Covering.TotalBoundedDudleyMinimalCapstone` | Unit-interval non-vacuity witness for the cardinal-minimal dyadic cover-count envelope |
| `minimalMetricCoveringNumber_antitone` | `Covering.TotalBoundedDudleyMinimalShift` | Genuine minimal covering numbers are antitone in the positive radius |
| `minimalDyadicChainingCoverCount_le_next_minimalMetricCoveringNumber_sq` | `Covering.TotalBoundedDudleyMinimalShift` | Adjacent cardinal-minimal dyadic cover products are bounded by the next smaller-radius minimal covering number squared |
| `minimalDyadicChainingCoverCount_entropy_le_sqrt_two_mul_next_minimalMetricCoveringEntropy` | `Covering.TotalBoundedDudleyMinimalShift` | Adjacent-product entropy is bounded by `sqrt 2` times one shifted minimal-cover entropy |
| `minimalDyadicChainingCoverCountEntropy_dominates_shiftedMinimalEntropy_sample` | `Covering.TotalBoundedDudleyMinimalShift` | The shifted one-radius minimal-cover entropy dominates the finite prefix-envelope sample |
| `finiteDyadicEntropyAtRadiusUpperSum_shifted_div_four_le_eight_mul_full_integral` | `Covering.TotalBoundedDudleyMinimalShift` | Finite shifted dyadic upper sums are bounded by the pure entropy integral with explicit shift constants |
| `continuous_dudley_entropy_integral_iSup_totalBounded_minimalMetricCoveringNumber_shifted` | `Covering.TotalBoundedDudleyMinimalShift` | Generic totally bounded continuous Dudley capstone with pure genuine minimal-cover entropy in the conclusion, paid by shifted boundary certificates and constants |
| `unitInterval_shiftedMinimalMetricCoveringEntropy_sample_nonneg` | `Covering.TotalBoundedDudleyMinimalShift` | Unit-interval non-vacuity witness for the shifted minimal-cover entropy profile |

## Two-point Dudley example

| Declaration | Module | Role |
|---|---|---|
| `TwoPoint` | `Covering.TwoPointDudley` | The two-point discrete metric index type |
| `twoPointDist_nonneg` | `Covering.TwoPointDudley` | The two-point discrete metric is nonnegative |
| `twoPointDist_symm` | `Covering.TwoPointDudley` | The two-point discrete metric is symmetric |
| `twoPointDist_triangle` | `Covering.TwoPointDudley` | The two-point discrete metric satisfies the triangle inequality |
| `twoPoint_rademacher_mgf_bound` | `Covering.TwoPointDudley` | One-coordinate Rademacher process increments satisfy the sub-Gaussian MGF bound |
| `twoPointRademacherProcess` | `Covering.TwoPointDudley` | The two-point Rademacher process packaged as a finite sub-Gaussian process |
| `twoPointDyadicNet` | `Covering.TwoPointDudley` | Full two-point finite net with dyadic positive radius |
| `twoPointDyadicNet_radius_geometric` | `Covering.TwoPointDudley` | Adjacent two-point dyadic radii satisfy the geometric chaining budget |
| `twoPointDyadicNet_pair_card_gt_one` | `Covering.TwoPointDudley` | Adjacent two-point projection-pair families are nontrivial |
| `twoPointDyadicNet_coverCount_le` | `Covering.TwoPointDudley` | Adjacent two-point covering-number products are bounded by the constant cover-count envelope |
| `twoPointDyadicNetSequence` | `Covering.TwoPointDudley` | A second concrete `FiniteDyadicNetSequence` instantiation, independent of `[0,1]` |
| `twoPointDudleyInstance` | `Covering.TwoPointDudley` | Packaged finite dyadic Dudley instance for the two-point Rademacher process |
| `twoPointRademacher_projected_dudley_m_bound` | `Covering.TwoPointDudley` | Arbitrary finite-horizon projected Dudley bound routed through the packaged finite dyadic Dudley API |
| `twoPointRademacherSup_le_projectedSup` | `Covering.TwoPointDudley` | Terminal projected-net adapter for the two-point supplied supremum |
| `twoPointRademacherSupAdapter` | `Covering.TwoPointDudley` | Supplied-supremum adapter for the two-point packaged Dudley instance |
| `twoPointRademacherSup_dudley_m_bound` | `Covering.TwoPointDudley` | Supplied-supremum finite Dudley bound routed through the packaged finite dyadic Dudley API |

## Finite discrete Dudley family

| Declaration | Module | Role |
|---|---|---|
| `finDiscreteDist` | `Covering.FiniteDiscreteDudley` | Discrete metric on `Fin n` |
| `finDiscreteDist_nonneg` | `Covering.FiniteDiscreteDudley` | The finite discrete metric is nonnegative |
| `finDiscreteDist_symm` | `Covering.FiniteDiscreteDudley` | The finite discrete metric is symmetric |
| `finDiscreteDist_triangle` | `Covering.FiniteDiscreteDudley` | The finite discrete metric satisfies the triangle inequality |
| `finDiscreteRademacherValue` | `Covering.FiniteDiscreteDudley` | One-coordinate Rademacher process embedded in the finite discrete family |
| `finDiscrete_rademacher_mgf_bound` | `Covering.FiniteDiscreteDudley` | Embedded Rademacher process increments satisfy the sub-Gaussian MGF bound |
| `finDiscreteRademacherProcess` | `Covering.FiniteDiscreteDudley` | The embedded Rademacher process packaged as a finite sub-Gaussian process over `Fin n` |
| `finDiscreteDyadicNet` | `Covering.FiniteDiscreteDudley` | Full finite net on `Fin n` at every dyadic scale |
| `finDiscreteDyadicCoverCount` | `Covering.FiniteDiscreteDudley` | Explicit adjacent-scale cover-count envelope `n * n` |
| `finDiscreteDyadicNet_dist` | `Covering.FiniteDiscreteDudley` | Finite discrete nets use the process metric |
| `finDiscreteDyadicNet_coveringNumber` | `Covering.FiniteDiscreteDudley` | The full finite discrete net has covering number `n` |
| `finDiscreteDyadicNet_coverCount_le` | `Covering.FiniteDiscreteDudley` | Adjacent finite-discrete covering-number products are bounded by the `n * n` envelope |
| `finDiscreteDyadicNetSequence` | `Covering.FiniteDiscreteDudley` | General `FiniteDyadicNetSequence` instance for `Fin n` with `[Fact (2 ≤ n)]` |
| `finDiscreteDudleyInstance` | `Covering.FiniteDiscreteDudley` | Packaged finite dyadic Dudley instance for the `Fin n` embedded Rademacher process |
| `finDiscreteRademacher_projected_dudley_m_bound` | `Covering.FiniteDiscreteDudley` | Arbitrary finite-horizon projected Dudley bound for the embedded Rademacher process routed through the packaged finite dyadic Dudley API |
| `finDiscreteRademacherSup` | `Covering.FiniteDiscreteDudley` | Supremum functional for the embedded Rademacher process over `Fin n` |
| `finDiscreteRademacherSup_true` | `Covering.FiniteDiscreteDudley` | The supplied supremum is nontrivial: it equals `1` on the positive Rademacher outcome |
| `finDiscreteRademacherSup_le_projectedSup` | `Covering.FiniteDiscreteDudley` | Terminal projected-net adapter for the finite-discrete supplied supremum |
| `finDiscreteRademacherSupAdapter` | `Covering.FiniteDiscreteDudley` | Supplied-supremum adapter for the finite-discrete packaged Dudley instance |
| `finDiscreteRademacherSup_dudley_m_bound` | `Covering.FiniteDiscreteDudley` | Supplied-supremum finite Dudley bound for the embedded Rademacher process routed through the packaged finite dyadic Dudley API |

## Unit-interval Dudley example

| Declaration | Module | Role |
|---|---|---|
| `UnitInterval` | `Covering.UnitIntervalDudley` | The closed interval `[0,1]` as a metric index type |
| `unitInterval_totallyBounded_univ` | `Covering.UnitIntervalDudley` | The unit interval is totally bounded |
| `unitIntervalFiniteNet_covers` | `Covering.UnitIntervalDudley` | Total-bounded finite net covers the unit interval at a supplied radius |
| `unitIntervalDyadicFiniteNet_covers` | `Covering.UnitIntervalDudley` | Dyadic total-bounded finite net covers the unit interval at the dyadic chaining radius |
| `unitIntervalDyadicGridCenter_leftEndpoint` | `Covering.UnitIntervalDudley` | The reusable dyadic grid center map contains the left endpoint |
| `unitIntervalDyadicGridCenter_rightEndpoint` | `Covering.UnitIntervalDudley` | The reusable dyadic grid center map contains the right endpoint |
| `unitIntervalDyadicGrid_card` | `Covering.UnitIntervalDudley` | Level-`k` dyadic grid has cardinality `2^k + 1` |
| `unitIntervalDyadicGridPairCoverCount_zero` | `Covering.UnitIntervalDudley` | The first adjacent dyadic grid pair count is `15` |
| `unitIntervalDyadicGridFloorProject` | `Covering.UnitIntervalDudley` | Floor projection from `[0,1]` to the level-`k` dyadic grid |
| `unitIntervalDyadicGridFloorProject_dist_le` | `Covering.UnitIntervalDudley` | Floor-projected dyadic grid covers `[0,1]` at spacing radius `1 / 2^k` |
| `unitIntervalDyadicGridNet_covers` | `Covering.UnitIntervalDudley` | Generic dyadic finite net covers `[0,1]` at spacing radius `1 / 2^k` |
| `unitIntervalDyadicGridNet_coveringNumber` | `Covering.UnitIntervalDudley` | Generic dyadic finite net has `2^k + 1` centers |
| `unitIntervalDyadicGridNet_coveringNumber_one` | `Covering.UnitIntervalDudley` | Level-`1` generic dyadic finite net has `3` centers |
| `unitIntervalDyadicGridNet_coveringNumber_two` | `Covering.UnitIntervalDudley` | Level-`2` generic dyadic finite net has `5` centers |
| `unitIntervalDyadicGridNet_coveringNumberPair_zero` | `Covering.UnitIntervalDudley` | Level-`1` and level-`2` generic dyadic finite-net covering-number product is the first dyadic pair count |
| `unitIntervalDyadicGridRoundProject` | `Covering.UnitIntervalDudley` | Rounded nearest-grid projection from `[0,1]` to the level-`k` dyadic grid |
| `unitIntervalDyadicGridRoundProject_zero` | `Covering.UnitIntervalDudley` | Rounded dyadic projection fixes the left endpoint |
| `unitIntervalDyadicGridRoundProject_one` | `Covering.UnitIntervalDudley` | Rounded dyadic projection fixes the right endpoint |
| `unitIntervalDyadicGridRoundProject_dist_le` | `Covering.UnitIntervalDudley` | Rounded dyadic grid covers `[0,1]` at half-spacing radius `1 / 2^(k+1)` |
| `unitIntervalDyadicRoundedGridNet_covers` | `Covering.UnitIntervalDudley` | Rounded generic dyadic finite net covers `[0,1]` at half-spacing radius `1 / 2^(k+1)` |
| `unitIntervalDyadicRoundedGridNet_coveringNumber` | `Covering.UnitIntervalDudley` | Rounded generic dyadic finite net has `2^k + 1` centers |
| `unitIntervalDyadicRoundedGridNet_coveringNumber_one` | `Covering.UnitIntervalDudley` | Level-`1` rounded dyadic finite net has `3` centers |
| `unitIntervalDyadicRoundedGridNet_coveringNumber_two` | `Covering.UnitIntervalDudley` | Level-`2` rounded dyadic finite net has `5` centers |
| `unitIntervalDyadicRoundedGridNet_coveringNumberPair_zero` | `Covering.UnitIntervalDudley` | Level-`1` and level-`2` rounded dyadic finite-net covering-number product is the first dyadic pair count |
| `unitIntervalRoundedDyadicGridIndex` | `Covering.UnitIntervalDudley` | Shifted rounded dyadic grid index sequence, starting at level `1` |
| `unitIntervalRoundedDyadicGridNet` | `Covering.UnitIntervalDudley` | Shifted rounded dyadic finite-net sequence for finite-scale Dudley chaining |
| `unitIntervalRoundedDyadicGridCoverCount` | `Covering.UnitIntervalDudley` | Adjacent-level covering-product envelope for the shifted rounded dyadic sequence |
| `monotone_unitIntervalRoundedDyadicGridCoverCount` | `Covering.UnitIntervalDudley` | Rounded dyadic adjacent-level cover counts are monotone in the scale |
| `monotone_unitIntervalRoundedDyadicGridEntropy` | `Covering.UnitIntervalDudley` | Rounded dyadic entropy-at-scale sequence is monotone |
| `unitIntervalRoundedDyadicGridEntropy_prefixSup` | `Covering.UnitIntervalDudley` | Prefix-sup envelope collapses for the rounded dyadic entropy sequence |
| `unitIntervalRoundedDyadicGridDudleyInstance` | `Covering.UnitIntervalDudley` | Packaged finite dyadic Dudley instance for the rounded unit-interval grid sequence |
| `unitIntervalRoundedDyadicGridNet_dist` | `Covering.UnitIntervalDudley` | Shifted rounded dyadic finite nets use the Rademacher process metric |
| `unitIntervalRoundedDyadicGridNet_radius_pos` | `Covering.UnitIntervalDudley` | Adjacent rounded dyadic radii have positive sum at every scale |
| `unitIntervalRoundedDyadicGridNet_radius_geometric` | `Covering.UnitIntervalDudley` | Adjacent rounded dyadic radii satisfy the geometric chaining radius budget |
| `unitIntervalRoundedDyadicGridNet_pair_card_gt_one` | `Covering.UnitIntervalDudley` | Adjacent rounded dyadic projection-pair family is nontrivial at every scale |
| `unitIntervalRoundedDyadicGridNet_coveringNumber_product` | `Covering.UnitIntervalDudley` | Adjacent rounded dyadic covering-number product equals the reusable cover-count envelope |
| `unitIntervalRoundedDyadicGridNet_coverCount_le` | `Covering.UnitIntervalDudley` | Adjacent rounded dyadic covering-number product is bounded by the cover-count envelope |
| `unitIntervalRoundedDyadicGridNet_radius_pos_range` | `Covering.UnitIntervalDudley` | Range wrapper for positive adjacent rounded dyadic radii over any finite horizon |
| `unitIntervalRoundedDyadicGridNet_radius_geometric_range` | `Covering.UnitIntervalDudley` | Range wrapper for the geometric radius budget over any finite horizon |
| `unitIntervalRoundedDyadicGridNet_pair_card_gt_one_range` | `Covering.UnitIntervalDudley` | Range wrapper for nontrivial adjacent projection-pair families over any finite horizon |
| `unitIntervalRoundedDyadicGridNet_coverCount_le_range` | `Covering.UnitIntervalDudley` | Range wrapper for the adjacent rounded-grid covering-product envelope over any finite horizon |
| `unitIntervalHalfMeshNet_covers` | `Covering.UnitIntervalDudley` | Explicit three-point mesh covers `[0,1]` at radius `1/4` |
| `unitIntervalHalfMeshNet_coveringNumber` | `Covering.UnitIntervalDudley` | Explicit half mesh has covering number `3` |
| `unitIntervalQuarterMeshNet_covers` | `Covering.UnitIntervalDudley` | Explicit five-point mesh covers `[0,1]` at radius `1/8` |
| `unitIntervalQuarterMeshNet_coveringNumber` | `Covering.UnitIntervalDudley` | Explicit quarter mesh has covering number `5` |
| `unitIntervalHalfQuarterPair_card_gt_one` | `Covering.UnitIntervalDudley` | Adjacent half/quarter projection-pair family is nontrivial |
| `unitIntervalHalfQuarter_coveringNumber_product` | `Covering.UnitIntervalDudley` | Half/quarter covering-number product is `15` |
| `unitIntervalHalfQuarter_coveringNumber_product_eq_dyadicGridPairCoverCount_zero` | `Covering.UnitIntervalDudley` | The half/quarter product is identified with the first adjacent dyadic grid pair count |
| `unitInterval_rademacherLinear_mgf_bound` | `Covering.UnitIntervalDudley` | Rademacher linear process increment satisfies the sub-Gaussian MGF bound |
| `unitIntervalRademacherLinearProcess_increment_mgf` | `Covering.UnitIntervalDudley` | The packaged finite sub-Gaussian process has the required increment MGF |
| `unitIntervalRademacherLinearSup_expectation` | `Covering.UnitIntervalDudley` | The supplied supremum has expectation `1/2` |
| `unitIntervalRademacherLinearSup_upper` | `Covering.UnitIntervalDudley` | The supplied supremum upper-bounds the full non-finite unit-interval family |
| `unitIntervalRademacherLinearSup_attained` | `Covering.UnitIntervalDudley` | The supplied supremum is attained at an endpoint |
| `unitIntervalRademacherLinearSup_isLeastUpperBound` | `Covering.UnitIntervalDudley` | The supplied supremum is the least upper bound over the non-finite unit-interval family |
| `unitIntervalRademacherLinearSup_isLUB_range` | `Covering.UnitIntervalDudley` | The supplied supremum is the least upper bound of the actual process range |
| `unitIntervalRademacherLinearSup_sSup_range` | `Covering.UnitIntervalDudley` | The supplied supremum equals the order supremum of the actual process range |
| `unitIntervalRademacherLinear_halfQuarter_increment_log15_bound` | `Covering.UnitIntervalDudley` | Half/quarter projection-pair increment pays the concrete `log 15` entropy term |
| `unitIntervalRademacherLinear_projectedQuarterMesh_dudley_log15_bound` | `Covering.UnitIntervalDudley` | Projected quarter-mesh supremum satisfies the finite-net Dudley bound with a `sqrt(log 15)` prefix envelope |
| `unitIntervalRademacherLinearSup_projectedQuarterMesh_dudley_log15_bound` | `Covering.UnitIntervalDudley` | The nonzero supplied supremum routes through the projected quarter-mesh Dudley bound |
| `unitIntervalRademacherLinearSup_projectedQuarterMesh_dudley_log15_bound_eval` | `Covering.UnitIntervalDudley` | The projected quarter-mesh supplied-supremum bound evaluated to `1 + sqrt 2 * sqrt(log 15)` |
| `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_log15_bound` | `Covering.UnitIntervalDudley` | Rounded generic dyadic-grid projected supremum satisfies the finite-net Dudley bound with a `sqrt(log 15)` prefix envelope |
| `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_log15_bound` | `Covering.UnitIntervalDudley` | The nonzero supplied supremum routes through the rounded generic dyadic-grid Dudley bound |
| `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_log15_bound_eval` | `Covering.UnitIntervalDudley` | The rounded-grid supplied-supremum bound evaluated to `1 + sqrt 2 * sqrt(log 15)` |
| `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m2_bound` | `Covering.UnitIntervalDudley` | Three-level rounded dyadic-grid projected supremum satisfies the finite-net Dudley bound with reusable adjacent cover counts |
| `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m2_bound` | `Covering.UnitIntervalDudley` | The nonzero supplied supremum routes through the `m = 2` rounded dyadic-grid Dudley bound |
| `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound` | `Covering.UnitIntervalDudley` | Arbitrary finite-horizon rounded dyadic-grid projected supremum Dudley bound routed through the packaged API |
| `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m_bound_prefixFree` | `Covering.UnitIntervalDudley` | Arbitrary finite-horizon projected rounded-grid Dudley bound with the prefix-sup envelope removed |
| `unitIntervalRademacherLinearSup_le_projectedRoundedDyadicGridSup` | `Covering.UnitIntervalDudley` | Endpoint adapter from the supplied supremum to any rounded dyadic projected finite supremum |
| `unitIntervalRademacherLinear_projectedRoundedDyadicGridSup_eq` | `Covering.UnitIntervalDudley` | Projected finite supremum over any rounded dyadic grid equals the supplied supremum |
| `unitIntervalRademacherLinearSupRoundedDyadicGridAdapter` | `Covering.UnitIntervalDudley` | Supplied-supremum adapter for the packaged rounded unit-interval Dudley instance |
| `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound` | `Covering.UnitIntervalDudley` | Arbitrary finite-horizon rounded dyadic-grid Dudley bound for the supplied supremum routed through the packaged API |
| `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m_bound_prefixFree` | `Covering.UnitIntervalDudley` | Arbitrary finite-horizon supplied-supremum rounded-grid Dudley bound with the prefix-sup envelope removed |
| `unitIntervalRademacherLinear_roundedDyadicGrid_dudley_m3_bound` | `Covering.UnitIntervalDudley` | Named `m = 3` projected rounded dyadic-grid Dudley corollary |
| `unitIntervalRademacherLinearSup_roundedDyadicGrid_dudley_m3_bound` | `Covering.UnitIntervalDudley` | Named `m = 3` supplied-supremum rounded dyadic-grid Dudley corollary |
| `unitIntervalRademacherLinearSup_dudley_m0_bound` | `Covering.UnitIntervalDudley` | Coarse finite-horizon `m = 0` Dudley bound for the supplied supremum |
| `unitIntervalRademacherLinearSup_dudley_m1_bound_of_entropy` | `Covering.UnitIntervalDudley` | First-scale supplied-supremum Dudley bound under an explicit entropy envelope |
| `unitIntervalRademacherLinearSup_dudley_m1_bound_constEntropy_eval` | `Covering.UnitIntervalDudley` | Constant-envelope first-scale bound evaluated to a scalar expression |
| `unitIntervalChainingPairCountEnvelope` | `Covering.ContinuousDudleyUnitIntervalCovering` | Real-radius half-open pair-count chaining envelope for `[0,1]`; not a metric covering number |
| `unitIntervalPairCountEntropy_eq_pair_count_sample` | `Covering.ContinuousDudleyUnitIntervalCovering` | The staircase entropy samples the rounded-grid adjacent pair-count product at every dyadic radius |
| `unitInterval_pairCountEntropy_nonconstant` | `Covering.ContinuousDudleyUnitIntervalCovering` | The pair-count entropy integrand is nonconstant |
| `unitInterval_pairCountEntropy_integral_positive` | `Covering.ContinuousDudleyUnitIntervalCovering` | The pair-count entropy integrand has positive interval mass |
| `continuous_dudley_oneStep_entropy_integral_iSup_unitInterval_pairCountEnvelope` | `Covering.ContinuousDudleyUnitIntervalCovering` | Guarded continuous Dudley capstone for `[0,1]` with the pair-count chaining envelope integrand |

## Stability and PAC-Bayes foundations

| Theorem | Module | Bound |
|---|---|---|
| `trainingLoss_hasBoundedDifferences` | `AlgorithmicStability` | Uniform stability gives bounded differences for training loss |
| `stability_genGap_hasBoundedDifferences` | `AlgorithmicStability` | Uniform stability gives bounded differences for the gen gap scaffold |
| `FiniteCoordinateSwapIdentity` | `AlgorithmicStability` | Finite coordinate-swap symmetry predicate for explicit sample weights |
| `finiteProductSampleWeight` | `AlgorithmicStability` | Iid finite product sample weights `∏ k, p (S k)` |
| `finiteProductSampleWeight_coordinateSwapIdentity` | `AlgorithmicStability` | Finite iid product weights satisfy the coordinate-swap identity |
| `expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap` | `AlgorithmicStability` | Uniform stability gives finite expected gap `≤ β` under a finite swap identity |
| `expectedFiniteStabilityGap_le_uniformStability_finiteProduct` | `AlgorithmicStability` | Uniform stability gives finite iid product-weight expected gap `≤ β` |
| `abs_expectedFiniteStabilityGap_le_uniformStability_of_coordinateSwap` | `AlgorithmicStability` | Uniform stability gives finite two-sided expected stability gap `≤ β` under a finite swap identity |
| `abs_expectedFiniteStabilityGap_le_uniformStability_finiteProduct` | `AlgorithmicStability` | Uniform stability gives finite iid two-sided expected stability gap `≤ β` |
| `expectedFiniteGeneralizationGap_le_uniformStability_of_coordinateSwap` | `AlgorithmicStability` | Literal finite `E[R(A(S)) - Rhat_S(A(S))] ≤ β` wrapper under a finite swap identity |
| `expectedFiniteGeneralizationGap_le_uniformStability_finiteProduct` | `AlgorithmicStability` | Literal finite iid product-weight `E[R(A(S)) - Rhat_S(A(S))] ≤ β` wrapper |
| `abs_expectedFiniteGeneralizationGap_le_uniformStability_of_coordinateSwap` | `AlgorithmicStability` | Literal finite absolute expected generalization-gap wrapper under a finite swap identity |
| `abs_expectedFiniteGeneralizationGap_le_uniformStability_finiteProduct` | `AlgorithmicStability` | Literal finite iid product-weight absolute expected generalization-gap wrapper |
| `finiteClass_loss_measurable` | `AlgorithmicStability` | Finite per-hypothesis loss measurability gives joint loss measurability |
| `boundedLoss_selectedLoss_integrable` | `AlgorithmicStability` | Bounded finite-class selected loss is integrable under `μⁿ × μ` |
| `boundedLoss_updateSelectedLoss_integrable` | `AlgorithmicStability` | Bounded coordinate-updated selected loss is integrable under `μⁿ × μ` |
| `boundedLoss_coordinateSelectedLoss_integrable` | `AlgorithmicStability` | Bounded empirical coordinate loss is integrable under `μⁿ` |
| `expectedStabilityGap_le_uniformStability_piMeasure_of_boundedLoss` | `AlgorithmicStability` | Product-measure expected gap `≤ β` with bounded-loss integrability discharged |
| `abs_expectedStabilityGap_le_uniformStability_piMeasure_of_boundedLoss` | `AlgorithmicStability` | Product-measure two-sided expected gap `≤ β` with bounded-loss integrability discharged |
| `mcdiarmid_inequality_iid_const_width` | `Stability.BousquetElisseeff` | Iid bounded-differences upper tail with the sharp McDiarmid constant |
| `bousquet_elisseeff_expectedGap_variant` | `Stability.BousquetElisseeff` | Stability high-probability bound with explicit expected-gap and measurability hypotheses |
| `bousquet_elisseeff_expectedGap_variant_of_boundedLoss` | `Stability.BousquetElisseeff` | Bounded-loss finite-class wrapper for the sharp stability high-probability theorem |
| `bousquet_elisseeff_uniform_stability_corollary` | `Stability.BousquetElisseeff` | `β = c0 / n` stability corollary for the sharp variant |
| `bousquet_elisseeff_uniform_stability_corollary_of_boundedLoss` | `Stability.BousquetElisseeff` | Bounded-loss finite-class `β = c0 / n` high-probability stability corollary |
| `exp_le_quadratic_of_le` | `Probability.BernsteinMGF` | Pointwise Bennett inequality for a centered bounded variable |
| `bennett_mgf_le_one_add` | `Probability.BernsteinMGF` | Finite Bennett MGF with the affine variance factor retained |
| `bennett_mgf` | `Probability.BernsteinMGF` | Finite centered bounded-variance Bennett MGF |
| `bennett_mgf_subgamma` | `Probability.BernsteinMGF` | Sub-Gamma denominator form of the finite Bennett MGF |
| `bernstein_tail` | `Probability.BernsteinMGF` | One-sample finite Bernstein upper-tail bound |
| `averaged_bernstein_tail` | `Probability.BernsteinMGF` | Iid product-weight Bernstein tail with the `n * eps^2` exponent |
| `BernsteinCondition` | `Rademacher.Localized` | Finite Bernstein condition: excess-loss second moment controlled by excess risk |
| `localizedEmpiricalRademacherComplexity_nonneg_of_zero` | `Rademacher.Localized` | Localized empirical Rademacher complexity is nonnegative when the class contains an identically zero excess-loss comparator |
| `localizedEmpiricalRademacherComplexity_mono` | `Rademacher.Localized` | Finite localized empirical Rademacher complexity is monotone under predicate inclusion |
| `localizedExcessRiskEmpiricalRademacherComplexity_nonneg` | `Rademacher.Localized` | Excess-risk localized empirical Rademacher complexity is nonnegative because the comparator belongs to every nonnegative radius |
| `localizedExcessRiskEmpiricalRademacherComplexity_le_secondMoment` | `Rademacher.Localized` | Bernstein embeds excess-risk localized complexity into second-moment localized complexity |
| `FixedPointUpperCertificate` | `Rademacher.Localized` | Deterministic envelope certificate: above `rStar`, the localized envelope is below the identity |
| `localizedSecondMomentEmpiricalRademacherComplexity_le_of_fixedPointCertificate` | `Rademacher.Localized` | Envelope bound plus fixed-point certificate controls second-moment localized empirical complexity by its radius |
| `localizedExcessRiskEmpiricalRademacherComplexity_le_of_bernstein_fixedPointCertificate` | `Rademacher.Localized` | Bernstein bridge plus fixed-point certificate controls excess-risk localized empirical complexity by `c * r` |
| `LocalizedDeviationCertificate` | `Rademacher.Localized` | Deterministic localized concentration-event interface for population excess risk versus empirical excess risk |
| `localizedUpperDeviation` | `Rademacher.Localized` | Finite localized supremum of population-minus-empirical excess-risk gaps |
| `localizedUpperDeviationEvent` | `Rademacher.Localized` | Sample event where the localized upper-deviation statistic is bounded |
| `localizedSampleDependentUpperDeviationEvent` | `Rademacher.Localized` | Sample-dependent localized upper-deviation event for random-threshold arguments |
| `localizedFastRateUpperDeviationEvent` | `Rademacher.Localized` | Named random-threshold event used by the finite fast-rate shell |
| `localizedPointwiseUpperDeviationBadEventMass` | `Rademacher.Localized` | Finite weighted mass of one pointwise upper-deviation bad event |
| `localizedPointwiseSampleDependentUpperDeviationBadEventMass` | `Rademacher.Localized` | Finite weighted mass of one pointwise upper-deviation bad event with a sample-dependent threshold |
| `localizedUpperDeviationBadEventMass` | `Rademacher.Localized` | Finite weighted mass outside the localized upper-deviation event |
| `localizedSampleDependentUpperDeviationBadEventMass` | `Rademacher.Localized` | Finite weighted mass outside a sample-dependent localized upper-deviation event |
| `localizedFastRateUpperDeviationBadEventMass` | `Rademacher.Localized` | Finite weighted mass outside the named fast-rate random-threshold localized event |
| `localizedPointwiseUpperDeviationExpMoment` | `Rademacher.Localized` | Finite weighted exponential moment for one localized upper-deviation gap |
| `localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment` | `Rademacher.Localized` | Shifted exponential moment for one localized upper-deviation gap with a sample-dependent threshold |
| `localizedPointwiseUpperDeviationBadEventMass_le_expMoment_div` | `Rademacher.Localized` | Pointwise Markov adapter from an exponential-moment budget to an upper-deviation bad-event mass |
| `localizedPointwiseSampleDependentUpperDeviationBadEventMass_le_shiftedExpMoment` | `Rademacher.Localized` | Pointwise sample-dependent bad-event mass controlled by its shifted exponential moment |
| `localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment_le_fixedExpMoment_div` | `Rademacher.Localized` | Sample-dependent shifted moment controlled by a fixed-threshold exponential moment under a pointwise lower bound on the random threshold |
| `localizedPointwiseSampleDependentUpperDeviationShiftedExpMoment_add_const` | `Rademacher.Localized` | Fixed slack added to a sample-dependent threshold factors out of the shifted exponential moment |
| `localizedPointwiseUpperDeviationExpMoment_finiteProduct_le_of_single` | `Rademacher.Localized` | Finite iid product MGF bridge for one localized upper-deviation gap from a one-coordinate MGF budget |
| `localizedOneCoordinateDeviationMGF_le_of_excessLoss_mem_Icc_neg_one_one` | `Rademacher.Localized` | Bounded excess losses in `[-1,1]` supply the localized one-coordinate MGF budget |
| `localizedUpperDeviationBadEventMass_le_sum_pointwise` | `Rademacher.Localized` | Finite weighted union bound: localized upper-deviation bad-event mass is controlled by pointwise localized bad-event masses |
| `localizedSampleDependentUpperDeviationBadEventMass_le_sum_pointwise` | `Rademacher.Localized` | Sample-dependent localized upper-deviation bad-event mass is controlled by pointwise sample-dependent bad-event masses |
| `localizedUpperDeviationBadEventMass_le_sum_tails` | `Rademacher.Localized` | Localized bad-event mass controlled by supplied pointwise tail budgets |
| `localizedSampleDependentUpperDeviationBadEventMass_le_sum_tails` | `Rademacher.Localized` | Sample-dependent localized bad-event mass controlled by supplied pointwise tail budgets |
| `localizedUpperDeviationBadEventMass_le_sum_expMoment_div` | `Rademacher.Localized` | Localized bad-event mass controlled by summed pointwise exponential-moment budgets |
| `localizedSampleDependentUpperDeviationBadEventMass_le_sum_shiftedExpMoment` | `Rademacher.Localized` | Sample-dependent localized bad-event mass controlled by summed shifted exponential-moment budgets |
| `localizedFastRateUpperDeviationBadEventMass_le_sum_shiftedExpMoment` | `Rademacher.Localized` | Named fast-rate bad-event mass controlled by shifted exponential-moment budgets |
| `localizedFastRatePointwiseShiftedExpMoment_le_centered_div` | `Rademacher.Localized` | Algebraic interface: factors the fixed slack out of the shifted moment. Conservative-only (per-hypothesis centered moment ≤ fixed moment); names the whole-supremum obligation, does not discharge it |
| `localizedFastRateUpperDeviationBadEventMass_le_sum_centeredShiftedExpMoment_div` | `Rademacher.Localized` | Algebraic interface: bad-event mass via summed centered moments and a fixed-slack denominator. Conservative-only union bound; not a non-conservative concentration result |
| `localizedFastRatePointwiseShiftedExpMoment_finiteProduct_le_boundedExcess` | `Rademacher.Localized` | Bounded-excess finite-product shifted-moment budget for one hypothesis in the named fast-rate random-threshold event |
| `localizedUpperDeviationBadEventMass_finiteProduct_le_sum_boundedExcess` | `Rademacher.Localized` | Iid product-weight localized bad-event mass bound under pointwise `[-1,1]` excess-loss assumptions |
| `localizedUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess` | `Rademacher.Localized` | Delta-form iid product-weight localized concentration bound under pointwise `[-1,1]` excess-loss assumptions |
| `localizedUpperDeviationBadEventMass_le_delta` | `Rademacher.Localized` | Delta-form finite localized concentration adapter from supplied pointwise tail budgets |
| `localizedSampleDependentUpperDeviationBadEventMass_le_fixed` | `Rademacher.Localized` | Sample-dependent bad-event mass is controlled by a fixed-threshold bad-event mass when the random threshold is pointwise larger |
| `localizedFastRateUpperDeviationBadEventMass_le_fixed_epsilon` | `Rademacher.Localized` | Named fast-rate bad-event mass is controlled by the fixed-`ε` bad-event mass using nonnegativity of the empirical localized complexity |
| `localizedFastRateUpperDeviationBadEventMass_finiteProduct_le_delta_boundedExcess` | `Rademacher.Localized` | Conservative finite product-mass bound for the named fast-rate event by reduction to the fixed-threshold bounded-excess theorem |
| `localizedDeviationCertificate_of_mem_upperDeviationEvent` | `Rademacher.Localized` | Event membership constructs the deterministic localized deviation certificate |
| `finiteExcessRisk_le_of_localizedDeviation_empirical_nonpos` | `Rademacher.Localized` | Localized deviation plus nonpositive empirical excess risk controls population excess risk by the deviation slack |
| `finiteExcessRisk_le_of_localizedUpperDeviationEvent_empirical_nonpos` | `Rademacher.Localized` | Fixed-threshold localized upper-deviation event payoff for empirical competitors |
| `localizedFiniteClassHighConfidence_empirical_nonpos_boundedExcess` | `Rademacher.Localized` | Fixed-threshold finite high-confidence localized statement combining bounded-excess bad-event mass with the empirical-competitor payoff |
| `centeredSecondMoment_le_of_bernstein_localized` | `Rademacher.Localized` | Variance proxy for the centered excess-loss deviation is bounded by `c * r` on the localized class |
| `localizedFiniteClassBernsteinHighConfidence_empirical_nonpos` | `Rademacher.Localized` | Finite localized Bernstein high-confidence theorem with bad-event mass bounded by the averaged Bernstein tail and fixed-threshold payoff |
| `finiteExcessRisk_le_of_localizedSampleDependentUpperDeviationEvent_empirical_nonpos` | `Rademacher.Localized` | Sample-dependent localized upper-deviation event payoff for empirical competitors |
| `localizedSampleDependentHighConfidence_empirical_nonpos` | `Rademacher.Localized` | Supplied-mass high-confidence adapter for sample-dependent localized upper-deviation events |
| `localizedSampleDependentHighConfidence_empirical_nonpos_of_shiftedExpMoment` | `Rademacher.Localized` | Sample-dependent high-confidence adapter from shifted exponential-moment budgets |
| `finiteExcessRisk_le_of_localizedDeviation_bernstein_fixedPoint` | `Rademacher.Localized` | Localized deviation plus Bernstein/fixed-point control gives a finite fast-rate shell |
| `finiteExcessRisk_le_of_localizedUpperDeviationEvent_bernstein_fixedPoint` | `Rademacher.Localized` | Event-facing finite fast-rate shell, reducing the remaining localized task to proving the upper-deviation event |
| `finiteExcessRisk_le_of_localizedFastRateUpperDeviationEvent_bernstein_fixedPoint` | `Rademacher.Localized` | Fast-rate shell stated through the named sample-dependent upper-deviation event |
| `localizedFastRateHighConfidence_bernstein_fixedPoint_of_shiftedExpMoment` | `Rademacher.Localized` | Assumption-facing high-confidence finite fast-rate wrapper from shifted exponential-moment budgets |
| `localizedFastRateHighConfidence_bernstein_fixedPoint_of_centeredShiftedExpMoment` | `Rademacher.Localized` | Assumption-facing high-confidence wrapper from supplied centered shifted-moment budgets. Interface only — the budgets it consumes are conservative-only per hypothesis |
| `localizedFastRateHighConfidence_bernstein_fixedPoint_boundedExcess` | `Rademacher.Localized` | Conservative finite fast-rate high-confidence wrapper pairing the bounded-excess bad-event mass with the Bernstein/fixed-point payoff |
| `klDiv_nonneg` | `PACBayesKL` | Finite KL divergence is nonnegative under full support |
| `donsker_varadhan` | `PACBayesKL` | `sum ρ_i f_i <= KL(ρ||π) + log(sum π_i exp(f_i))` |
| `continuous_donsker_varadhan` | `PACBayes.ContinuousChangeOfMeasure` | Measure-theoretic Donsker-Varadhan bound from Radon-Nikodym tilting |
| `continuous_catoni_changeOfMeasure_bound` | `PACBayes.ContinuousChangeOfMeasure` | Continuous fixed-`lambda` Catoni change-of-measure bound from a prior log-MGF certificate |
| `continuousPriorPosterior_certificate_derived` | `PACBayes.ContinuousPriorPosterior` | Continuous prior/posterior certificate with the PAC gate derived by change of measure |
| `pacbayes_changeOfMeasure` | `PACBayesMcAllester` | Rescaled finite Donsker-Varadhan change-of-measure inequality |
| `pacbayes_mcallester_deterministic` | `PACBayesMcAllester` | Deterministic PAC-Bayes posterior bound from a prior log-MGF certificate |
| `pacbayes_mcallester_subGaussian` | `PACBayesMcAllester` | Fixed-`λ` sub-Gaussian deterministic PAC-Bayes bound |
| `pacbayes_mcallester_sqrt` | `PACBayesMcAllester` | Deterministic sqrt-form bound under a uniform-in-`λ` MGF certificate |
| `finiteEmpiricalRisk` | `PACBayesFiniteProductMGF` | Finite empirical risk for a real-valued loss |
| `finiteProduct_mgf_empiricalRiskDeviation_eq_pow` | `PACBayesFiniteProductMGF` | Exact iid product factorization of `E exp(lam * (R_i - Rhat_i))` |
| `finiteProduct_mgf_empiricalRiskDeviation_le_of_single` | `PACBayesFiniteProductMGF` | Single-coordinate MGF budget lifts to the finite sample-average MGF |
| `finitePriorAveraged_mgf_empiricalRiskDeviation_le` | `PACBayesFiniteProductMGF` | Prior-averaged finite iid empirical-risk-deviation MGF bound |
| `oneCoordinate_boundedLoss_mgf` | `PACBayesBoundedLoss` | `[0,1]` bounded-loss one-coordinate MGF instantiation |
| `sampleAverage_boundedLoss_mgf` | `PACBayesBoundedLoss` | Finite sample-average bounded-loss MGF bound |
| `priorAveraged_boundedLoss_mgf` | `PACBayesBoundedLoss` | Prior-averaged bounded-loss MGF bound |
| `priorAveraged_boundedLoss_mgf_badEventMass_le_delta` | `PACBayesBoundedLoss` | Finite Markov bad-event bound for the prior MGF |
| `posteriorRisk_bound_of_priorDeviationMGF_le` | `PACBayesBoundedLoss` | Deterministic posterior-risk adapter from a prior MGF certificate |
| `finiteCatoni_badEventMass_le_delta` | `PACBayesBoundedLoss` | Finite `[0,1]` Catoni-style PAC-Bayes posterior-risk bad-event bound |
| `catoni_fixedLambda_budget_eq_sqrt` | `PACBayesBoundedLoss` | Fixed-λ Catoni penalty optimized to a square-root budget |
| `posteriorRisk_bound_of_priorDeviationMGF_le_complexity_sqrt` | `PACBayesBoundedLoss` | Deterministic fixed-budget McAllester-style posterior-risk adapter |
| `finiteMcAllesterBoundedComplexity_badEventMass_le_delta` | `PACBayesBoundedLoss` | Finite `[0,1]` fixed-budget McAllester-style bad-event bound |
| `finiteMcAllesterGridPeeling_badEventMass_le_delta` | `PACBayesBoundedLoss` | Finite-grid McAllester peeling bound with allocated confidence mass |
| `finiteMcAllesterGridOptimized_badEventMass_le_delta` | `PACBayesBoundedLoss` | Posterior-dependent finite-grid McAllester wrapper under an explicit bucket certificate |
| `pac_bayes_generalization` | `PACBayesBoundedLoss` | Closed PAC-Bayes good-event theorem: with product-sample mass at least `1 - delta`, every posterior satisfies the Catoni-form risk bound |
| `indicatorPopulationRisk_mem_Icc` | `PACBayes.IndicatorVariance` | Population risk of an arbitrary Boolean indicator under a finite PMF lies in `[0,1]` |
| `indicatorDeviation_centered` | `PACBayes.IndicatorVariance` | The population-centered indicator loss has exactly zero finite-PMF mean |
| `indicatorDeviation_secondMoment_eq` | `PACBayes.IndicatorVariance` | Exact finite-PMF variance identity `R * (1 - R)` for arbitrary Boolean indicator predicates |
| `finiteProductSampleWeight_isPMF` | `PACBayes.FiniteProductBernstein` | Finite i.i.d. product weights package as a PMF on the sample space |
| `indicator_oneCoordinateDeviationMGF_le` | `PACBayes.FiniteProductBernstein` | One-coordinate indicator sub-Gamma MGF using exact hypothesis-specific variance |
| `indicator_product_mgf_le` | `PACBayes.FiniteProductBernstein` | Tensorized finite-product MGF with exact `R * (1 - R)` Bernstein budget |
| `indicator_product_normalizedMGF_le_one` | `PACBayes.FiniteProductBernstein` | Hypothesis-specific normalized product MGF at fixed `0 < lambda < 3n` |
| `indicatorBernstein_normalization_eq_budget` | `PACBayes.IndicatorBernsteinMoment` | Exact identification of the product-MGF budget with scale `1/(3n)` and variance proxy `R * (1 - R) / n` |
| `indicator_expectedPriorBernsteinExpMoment_le_one` | `PACBayes.IndicatorBernsteinMoment` | Prior-averaged normalized indicator Bernstein moment under the finite i.i.d. product law |
| `indicatorFinitePACBayesBernsteinBadSamples` | `PACBayes.IndicatorBernsteinConfidence` | Samples on which some finite posterior violates the explicit fixed-tilt indicator Bernstein inequality |
| `indicator_posteriorGeneralizationGap_le_of_not_mem` | `PACBayes.IndicatorBernsteinConfidence` | Every finite posterior satisfies the explicit indicator Bernstein inequality outside the specialized bad set |
| `indicator_finitePACBayesBernstein_fixedLambda_badEventMass_le_delta` | `PACBayes.IndicatorBernsteinConfidence` | End-to-end finite i.i.d. indicator PAC-Bayes Bernstein bad-event mass bound, simultaneous over all finite posteriors |
| `indicatorBernsteinVarianceProxy_le_risk_div` | `PACBayes.IndicatorBernsteinLowRisk` | Pointwise Bernoulli self-bound `R_i(1 - R_i)/n <= R_i/n` for positive sample size |
| `posteriorIndicatorBernsteinVarianceProxy_le_risk_div` | `PACBayes.IndicatorBernsteinLowRisk` | Posterior-average self-bound `V_rho <= R_rho/n` |
| `indicator_posteriorRisk_le_lowRisk_of_not_mem` | `PACBayes.IndicatorBernsteinLowRisk` | General fixed-tilt observable risk inequality for `0 < lambda < 6n/5`, with exact rearranged coefficients |
| `indicator_posteriorRisk_le_twoThirds_of_not_mem` | `PACBayes.IndicatorBernsteinLowRisk` | At `lambda = 2n/3`, every posterior outside the parent bad set satisfies `R_rho <= (7/4) Rhat_rho + (21/(8n))(KL + log(1/delta))` |
| `indicator_posteriorRisk_le_min_one_twoThirds_of_not_mem` | `PACBayes.IndicatorBernsteinLowRisk` | Public certificate form truncating the observable low-risk bound by the universal upper bound one |
| `indicator_finitePACBayesBernstein_twoThirds_badEventMass_le_delta` | `PACBayes.IndicatorBernsteinLowRisk` | Product-law mass bound for the shared fixed-tilt exceptional set at `lambda = 2n/3` |
| `indicatorFinitePACBayesBernsteinWeightedCatalogBadSamples` | `PACBayes.IndicatorBernsteinTiltCatalog` | Single exceptional set formed by the finite union of fixed indicator-Bernstein tilt events with budgets `delta * weight j` |
| `indicator_mem_weightedCatalog_iff` | `PACBayes.IndicatorBernsteinTiltCatalog` | Membership in the weighted catalog event is equivalent to membership in at least one entrywise bad set |
| `indicator_not_mem_weightedCatalog_iff` | `PACBayes.IndicatorBernsteinTiltCatalog` | A sample is outside the catalog event exactly when it is outside every entrywise bad set |
| `indicatorFixedTiltBadSamples_subset_weightedCatalog` | `PACBayes.IndicatorBernsteinTiltCatalog` | Every entrywise indicator-Bernstein exceptional set is contained in the catalog union |
| `indicator_posteriorGeneralizationGap_le_weightedCatalog_of_not_mem` | `PACBayes.IndicatorBernsteinTiltCatalog` | On one good event, every posterior satisfies every fixed tilt in the weighted finite catalog |
| `indicator_finitePACBayesBernstein_weightedCatalog_badEventMass_le_delta` | `PACBayes.IndicatorBernsteinTiltCatalog` | Finite weighted union bound giving catalog exceptional mass at most `delta` when positive weights sum to at most one |
| `indicator_posteriorRisk_le_weightedLowRiskCatalog_of_not_mem` | `PACBayes.IndicatorBernsteinTiltCatalog` | Observable low-risk bound for every entry of the weighted finite catalog |
| `indicator_posteriorRisk_le_weightedLowRiskCatalog_selected_of_not_mem` | `PACBayes.IndicatorBernsteinTiltCatalog` | Valid post-sample and posterior-dependent selection from the fixed finite weighted tilt catalog |
| `posteriorMarginVarianceProxy` | `PACBayesBernstein` | Posterior average of a supplied per-hypothesis margin-variance proxy |
| `priorBernsteinExpMoment` | `PACBayesBernstein` | Normalized Bernstein prior exponential moment with variance and scale terms |
| `posteriorGeneralizationGap_le_bernstein_of_priorBernsteinExpMoment_le` | `PACBayesBernstein` | Deterministic fixed-sample PAC-Bayes Bernstein adapter from a prior-moment certificate |
| `finitePACBayesBernstein_fixedLambda_badEventMass_le_delta` | `PACBayesBernstein` | Finite fixed-`lambda` PAC-Bayes Bernstein bad-event bound |
| `finitePACBayesBernsteinPenalty_badEventMass_le_delta` | `PACBayesBernstein` | Posterior-dependent finite Bernstein bad-event wrapper under complexity and penalty certificates |
| `finitePACBayesBernsteinMargin_badEventMass_le_delta` | `PACBayesBernstein` | Finite supplied margin-proxy wrapper with `sqrt(2 * Vρ * Cρ) + scale * Cρ` penalty form |

## Finite empirical variance and fixed-parameter empirical-Bernstein risk

| Declaration | Module | Role |
|---|---|---|
| `finitePopulationVariance` | `PACBayes.FiniteEmpiricalVariance` | Per-hypothesis population loss variance under a finite weight function |
| `finiteEmpiricalVariance` | `PACBayes.FiniteEmpiricalVariance` | Per-hypothesis Bessel-corrected empirical loss variance |
| `orderedOffDiagonalSquaredDifference` | `PACBayes.FiniteEmpiricalVariance` | Ordered sum of squared differences across distinct sample indices |
| `finitePairwiseEmpiricalVariance` | `PACBayes.FiniteEmpiricalVariance` | Normalized second-order pair-statistic form of empirical variance |

| Theorem | Module | Role |
|---|---|---|
| `finitePopulationVariance_nonneg` | `PACBayes.FiniteEmpiricalVariance` | Population loss variance is nonnegative under a finite PMF |
| `finitePopulationVariance_eq_secondMoment_sub_riskSq` | `PACBayes.FiniteEmpiricalVariance` | Identifies population loss variance with the second moment minus squared risk |
| `finitePopulationRisk_mem_Icc_of_bounded` | `PACBayes.FiniteEmpiricalVariance` | Places the population risk of a finite `[0,1]` loss in `[0,1]` |
| `finitePopulationVariance_le_quarter` | `PACBayes.FiniteEmpiricalVariance` | Gives the universal `1/4` population-variance bound for finite `[0,1]` losses |
| `finiteEmpiricalVariance_nonneg` | `PACBayes.FiniteEmpiricalVariance` | Bessel-corrected empirical loss variance is nonnegative for sample size at least two |
| `orderedOffDiagonalSquaredDifference_eq_two_mul_card_mul_centeredSum` | `PACBayes.FiniteEmpiricalVariance` | Equates the ordered off-diagonal square-difference sum with twice the sample size times the centered sum of squares |
| `finiteEmpiricalVariance_eq_pairwise` | `PACBayes.FiniteEmpiricalVariance` | Exact second-order pair-statistic representation of Bessel empirical variance |
| `orderedOffDiagonalSquaredDifference_le` | `PACBayes.FiniteEmpiricalVariance` | Bounds the ordered pair numerator for samples in `[0,1]` |
| `finiteEmpiricalVariance_le_card_div_pred_mul_empiricalRisk` | `PACBayes.FiniteEmpiricalVariance` | Source-facing self-bound `V_n <= n/(n-1) * Rhat_n` for `[0,1]` losses |
| `finiteEmpiricalVariance_le_half` | `PACBayes.FiniteEmpiricalVariance` | Universal `1/2` bound for Bessel empirical variance of a finite `[0,1]` sample |
| `finiteProductSampleWeight_pairExpectation` | `PACBayes.FiniteEmpiricalVariance` | Two distinct coordinates of the finite IID product sample have the product marginal |
| `finitePairVarianceKernelExpectation_eq_populationVariance` | `PACBayes.FiniteEmpiricalVariance` | The independent-pair half squared-difference kernel has expectation equal to population variance |
| `finiteProductSampleWeight_pairSquaredDifferenceExpectation_eq` | `PACBayes.FiniteEmpiricalVariance` | Expected squared loss difference across two distinct IID coordinates is twice the population variance |
| `finiteEmpiricalVariance_unbiased_finiteProduct` | `PACBayes.FiniteEmpiricalVariance` | End-to-end finite-IID unbiasedness of the per-hypothesis Bessel empirical loss variance |
| `average_perm_pairCatalog_eq_sampleVarianceBessel` | `PACBayes.FiniteEmpiricalVarianceMatching` | Averaging any fixed nonempty catalog of distinct coordinate pairs over all permutations recovers Bessel sample variance |
| `finitePairBlock_factorization` | `PACBayes.FiniteEmpiricalVarianceMatching` | Factors the finite-product expectation of a product over disjoint pair blocks into independent two-coordinate expectations |
| `average_perm_finiteCanonicalPairMean_eq_sampleVarianceBessel` | `PACBayes.FiniteEmpiricalVarianceMatching` | Identifies the permutation average of the canonical random-matching statistic with Bessel sample variance |
| `finiteEmpiricalVariance_lowerTailMGF_randomMatching` | `PACBayes.FiniteEmpiricalVarianceMGF` | Random-matching and finite-Jensen lower-tail MGF bound, with the exact disjoint-pair count in its coefficient |
| `finiteEmpiricalVariance_lowerTailMGF_tolstikhinSeldin` | `PACBayes.FiniteEmpiricalVarianceMGF` | All-`n >= 2` source-normalized finite-IID empirical-variance MGF inequality |
| `finiteEmpiricalVariance_normalizedLowerTailMGF_le_one` | `PACBayes.FiniteEmpiricalVarianceMGF` | Moves the deterministic variance penalty inside the exponential to obtain the normalized moment used by change of measure |
| `finiteEmpiricalVariance_expectedPriorBernsteinExpMoment_le_one` | `PACBayes.FiniteEmpiricalVariancePACBayes` | Averages the normalized per-hypothesis empirical-variance moment under a finite prior |
| `finiteEmpiricalVariancePACBayes_badEventMass_le_delta` | `PACBayes.FiniteEmpiricalVariancePACBayes` | Bounds one fixed-sample, fixed-tilt exceptional set by `delta`; the event is shared by every finite posterior |
| `posteriorPopulationVariance_le_empiricalVariance_of_not_mem` | `PACBayes.FiniteEmpiricalVariancePACBayes` | Outside the shared event, bounds the posterior average of per-hypothesis population variances by the corresponding empirical average and KL-confidence penalty |
| `boundedLoss_oneCoordinateDeviationMGF_le` | `PACBayes.FiniteBoundedLossBernstein` | One-coordinate population-variance Bernstein MGF for arbitrary finite `[0,1]` losses |
| `boundedLoss_product_normalizedMGF_le_one` | `PACBayes.FiniteBoundedLossBernstein` | Normalized finite-IID population-risk deviation MGF with exact `1 - lambda/(3n)` denominator |
| `finiteBoundedLossBernstein_badEventMass_le_delta` | `PACBayes.FiniteBoundedLossBernstein` | Bounds the separate fixed-`lambda` population-risk bad event by its declared risk budget |
| `boundedLoss_posteriorRisk_le_populationVariance_of_not_mem` | `PACBayes.FiniteBoundedLossBernstein` | Outside the risk event, bounds every posterior risk gap by KL complexity and posterior-averaged population variance |
| `finiteEmpiricalBernsteinRisk_badEventMass_le` | `PACBayes.FiniteEmpiricalBernsteinRisk` | Bounds the union of variance and risk bad events by `deltaVariance + deltaRisk` without independence |
| `posteriorRisk_le_empiricalRisk_add_empiricalVariance_of_not_mem` | `PACBayes.FiniteEmpiricalBernsteinRisk` | Final fixed-parameter observable empirical-Bernstein risk bound simultaneous over every finite posterior |
| `finiteWeightedUnionBound_sum_le_of_exists_mem` | `Probability.FiniteUnionBound` | Plain-sum finite weighted union bound stated through an existential membership cover, avoiding decidable-instance reconciliation |
| `finiteEmpiricalVarianceWeightedCatalogBadSamples` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | Finite union of empirical-variance bad sets with separately weighted variance budgets |
| `finiteEmpiricalVariance_mem_weightedCatalog_iff` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | Membership in the variance catalog is equivalent to membership in one fixed-tilt event |
| `finiteEmpiricalVariance_not_mem_weightedCatalog_iff` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | A sample is outside the variance catalog exactly when it is outside every fixed-tilt event |
| `finiteEmpiricalVarianceFixedTiltBadSamples_subset_weightedCatalog` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | Every fixed empirical-variance tilt event is contained in the catalog event |
| `finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | Weighted union bound for the finite empirical-variance tilt catalog |
| `finiteEmpiricalVariance_posteriorGap_le_weightedCatalog_of_not_mem` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | Unrearranged posterior-uniform variance gap bound for every catalog entry |
| `posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_of_not_mem` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | Rearranged observable variance certificate for every catalog entry and posterior |
| `posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem` | `PACBayes.FiniteEmpiricalVarianceTiltCatalog` | Valid sample- and posterior-dependent selection from the finite variance-tilt catalog |
| `finiteBoundedLossBernsteinWeightedCatalogBadSamples` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | Finite union of population-risk bad sets with separately weighted risk budgets |
| `finiteBoundedLossBernstein_mem_weightedCatalog_iff` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | Membership in the risk catalog is equivalent to membership in one fixed-lambda event |
| `finiteBoundedLossBernstein_not_mem_weightedCatalog_iff` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | A sample is outside the risk catalog exactly when it is outside every fixed-lambda event |
| `finiteEmpiricalBernsteinRiskWeightedCatalogBadSamples` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | One exceptional set joining the variance and risk catalogs |
| `finiteBoundedLossBernstein_weightedCatalog_badEventMass_le_delta` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | Weighted union bound for the finite population-risk tilt catalog |
| `finiteEmpiricalBernsteinRisk_weightedCatalog_badEventMass_le` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | Combined catalog mass bound `deltaVariance + deltaRisk` without a Cartesian-pair confidence charge |
| `posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_of_not_mem` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | Observable risk bound simultaneous over every pair of predeclared variance and risk tilts |
| `posteriorRisk_le_empiricalRisk_add_empiricalVariance_weightedCatalog_selected_of_not_mem` | `PACBayes.FiniteEmpiricalBernsteinRiskCatalog` | Valid sample- and posterior-dependent selection from separate finite variance and risk catalogs |

## Finite exponential tilting

| Declaration | Module | Role |
|---|---|---|
| `finiteExponentialTiltNormalizer` | `PACBayes.FiniteExponentialTilt` | Finite partition sum for an arbitrary exponential score under a base weight function |
| `finiteExponentialTiltPMF` | `PACBayes.FiniteExponentialTilt` | Base weight function reweighted by an exponential score and divided by its partition sum |
| `boundedLossTiltScore` | `PACBayes.FiniteBoundedLossExponentialTilt` | Lower-tail score `-t * ell i z` for a finite bounded loss |
| `finiteBoundedLossTiltNormalizer` | `PACBayes.FiniteBoundedLossExponentialTilt` | Partition sum for the specialized lower-tail bounded-loss tilt |
| `finiteBoundedLossTiltPMF` | `PACBayes.FiniteBoundedLossExponentialTilt` | Finite PMF obtained by reweighting with `exp (-t * ell i z)` |
| `finiteJointMeanVarianceKappa` | `PACBayes.FiniteJointMeanVarianceMGF` | Linear-minus-quadratic variance coefficient in the fixed-sample joint mean/Bessel-variance exponential moment |
| `finiteJointMeanVarianceScore` | `PACBayes.FiniteJointMeanVariancePACBayes` | Per-hypothesis normalized fixed-sample joint mean/empirical-variance score |
| `finiteJointMeanVariancePriorMoment` | `PACBayes.FiniteJointMeanVariancePACBayes` | Prior moment of the joint score at one sample and one catalog pair |
| `finiteJointMeanVarianceMasterMixture` | `PACBayes.FiniteJointMeanVariancePACBayes` | Prior-and-catalog master mixture over the weighted per-entry prior score moments |
| `finiteJointMeanVarianceCatalogBadSamples` | `PACBayes.FiniteJointMeanVariancePACBayes` | Single catalog bad-sample set thresholding the master mixture at `1 / delta` |

| Theorem | Module | Role |
|---|---|---|
| `finiteExponentialTiltNormalizer_pos` | `PACBayes.FiniteExponentialTilt` | The finite exponential-tilt normalizer is positive under any PMF, without a full-support assumption |
| `finiteExponentialTiltPMF_isPMF` | `PACBayes.FiniteExponentialTilt` | Normalizing an exponential tilt of a finite PMF produces another PMF |
| `finiteExponentialTiltPMF_mul_normalizer` | `PACBayes.FiniteExponentialTilt` | Pointwise cancellation recovers the unnormalized exponential weight |
| `finiteExponentialTilt_changeOfMeasure` | `PACBayes.FiniteExponentialTilt` | Exact one-coordinate finite change-of-measure identity for arbitrary observables |
| `finiteProductSampleWeight_mul_exp_sum_eq` | `PACBayes.FiniteExponentialTiltProduct` | Pointwise identity relating the base product weight, the summed exponential score, and the tilted product weight |
| `finiteProductExponentialTilt_changeOfMeasure` | `PACBayes.FiniteExponentialTiltProduct` | Exact finite-product exponential change-of-measure identity for arbitrary sample functionals |
| `finiteBoundedLossTiltPMF_isPMF` | `PACBayes.FiniteBoundedLossExponentialTilt` | The specialized lower-tail bounded-loss tilt is a PMF without a full-support assumption |
| `finiteBoundedLossTilt_changeOfMeasure` | `PACBayes.FiniteBoundedLossExponentialTilt` | One-coordinate lower-tail loss change of measure, specialized from the generic identity |
| `finiteBoundedLossTiltProduct_changeOfMeasure` | `PACBayes.FiniteBoundedLossExponentialTilt` | Finite-product lower-tail loss change of measure, specialized from the generic identity |
| `finiteBoundedLossTiltNormalizer_le_one` | `PACBayes.FiniteBoundedLossExponentialTilt` | The partition sum of a nonnegative bounded-loss lower-tail tilt is at most one |
| `finiteBoundedLossTilt_exp_neg_mul_le` | `PACBayes.FiniteBoundedLossExponentialTilt` | Pointwise density comparison `exp (-t) * p z <= q_t z` for losses in `[0,1]` |
| `finiteWeightedSquaredError_eq_populationVariance_add_sq` | `PACBayes.FiniteBoundedLossExponentialTilt` | Exact finite-PMF squared-error decomposition around an arbitrary center |
| `finitePopulationVariance_le_weightedSquaredError` | `PACBayes.FiniteBoundedLossExponentialTilt` | Population risk minimizes the finite-PMF weighted squared error |
| `finitePopulationVariance_mul_exp_neg_le_tilted` | `PACBayes.FiniteBoundedLossExponentialTilt` | Tilted population variance is at least `exp (-t)` times the base population variance |
| `finiteBoundedLoss_centeredBennettNormalizer_le` | `PACBayes.FiniteBoundedLossExponentialTilt` | Retained-affine-factor Bennett bound for the centered lower-tail loss score |
| `finiteJointMeanVarianceKappa_nonneg_of_eta_mul_card_le` | `PACBayes.FiniteJointMeanVarianceMGF` | Nonnegativity of the joint variance coefficient on the exact range `eta * n <= 2 * (n - 1)` |
| `finiteBoundedLossTilt_negativeEmpiricalVarianceMGF_le` | `PACBayes.FiniteJointMeanVarianceMGF` | Negative Bessel empirical-variance moment bound under the lower-tail tilted finite PMF |
| `finiteJointMeanVarianceMGF_le` | `PACBayes.FiniteJointMeanVarianceMGF` | Unnormalized fixed-sample joint lower-tail mean and Bessel empirical-variance exponential-moment bound |
| `finiteJointMeanVariance_normalizedMGF_le_one` | `PACBayes.FiniteJointMeanVarianceMGF` | Normalized fixed-sample joint score has finite-product expectation at most one |
| `finiteJointMeanVariance_priorMoment_expectation_le_one` | `PACBayes.FiniteJointMeanVariancePACBayes` | Prior score moment has finite-product expectation at most one |
| `finiteJointMeanVariance_masterMixture_expectation_le_one` | `PACBayes.FiniteJointMeanVariancePACBayes` | Master mixture expectation is at most the total catalog weight, hence at most one |
| `finiteJointMeanVariance_catalogBadSamples_mass_le_delta` | `PACBayes.FiniteJointMeanVariancePACBayes` | The single catalog bad set has product-law mass at most `delta` |
| `finiteJointMeanVariance_priorMoment_le_of_not_mem` | `PACBayes.FiniteJointMeanVariancePACBayes` | Outside the one event, each entry keeps its prior moment at most `1 / (delta * w c)` |
| `finiteJointMeanVariance_posteriorScore_le_of_not_mem` | `PACBayes.FiniteJointMeanVariancePACBayes` | One-KL Donsker-Varadhan score bound for every posterior and entry on the good event |
| `finiteJointMeanVariance_posteriorGap_le_of_not_mem` | `PACBayes.FiniteJointMeanVariancePACBayes` | Raw retained-variance posterior inequality with the Bennett log at the posterior-averaged variance |
| `finiteJointMeanVariance_posteriorGap_div_le_of_not_mem` | `PACBayes.FiniteJointMeanVariancePACBayes` | Division form of the retained-variance inequality for a strictly positive mean tilt |
| `finiteJointMeanVariance_posteriorGap_le_selected_of_not_mem` | `PACBayes.FiniteJointMeanVariancePACBayes` | Selector endpoint: the catalog entry may depend on the sample and the posterior |
| `finiteJointMeanVariance_posteriorGap_div_le_selected_of_not_mem` | `PACBayes.FiniteJointMeanVariancePACBayes` | Division form of the selector endpoint for all-positive mean tilts |

## Conditional sub-Gamma extractor

| Theorem | Module | Role |
|---|---|---|
| `bennett_taylor_bound` | `Concentration.SubGamma.BennettBound` | Pointwise Bennett Taylor bound for bounded increments in the regime `b * λ < 3` |
| `integrable_exp_mul_of_bounded` | `Concentration.SubGamma.BoundedExpIntegrable` | Bounded real increments have integrable exponential tilts under a finite measure |
| `condExp_mul_bounded_left` | `Concentration.SubGamma.CondExpProduct` | Pulls a bounded measurable factor through conditional expectation under the stated integrability hypotheses |
| `condJensen_real` | `Concentration.SubGamma.CondJensen` | Conditional Jensen inequality for real-valued conditional expectations |
| `cond_markov_of_nonneg` | `Concentration.SubGamma.CondMarkov` | Conditional Markov-style inequality for nonnegative real functions |
| `condExp_sq_eq_condVar_of_centered` | `Concentration.SubGamma.CondVarianceFromSquare` | Under conditional centering, the conditional second moment is the conditional variance proxy |
| `condSubGammaMGF_of_bounded_centered_condVariance` | `Concentration.SubGamma.Extractor` | Boundedness, conditional centering, and a conditional second-moment proxy imply a conditional sub-Gamma MGF bound |

## Anytime-valid confidence sequences

| Theorem | Module | Role |
|---|---|---|
| `condExp_mixture_swap` | `AnytimeValid.MixtureCS` | Conditional-expectation swap for the mixture exponential process |
| `mixture_is_supermartingale` | `AnytimeValid.MixtureCS` | Mixture of sub-Gamma exponential processes is a nonnegative supermartingale |
| `atTop_time_uniform_confidence_sequence_subGamma_mixture` | `AnytimeValid.MixtureCS` | Time-uniform mixture confidence sequence from the sub-Gamma exponential supermartingale |
| `subGamma_stitched_boundary_supermartingale` | `AnytimeValid.OptimizedLambdaCS` | Stitched-over-`λ` sub-Gamma exponential process is a nonnegative supermartingale |
| `stitched_atTop_crossing_bound` | `AnytimeValid.OptimizedLambdaCS` | Ville crossing bound for the stitched sub-Gamma boundary |
| `optimized_lambda_confidence_sequence_subGamma` | `AnytimeValid.OptimizedLambdaCS` | Optimized-`λ` sub-Gamma confidence sequence with the stitched boundary |
| `subGammaLogLogWidth_loglog_rate` | `AnytimeValid.OptimizedLambdaCS` | Stitched boundary half-width grows at the iterated-logarithm rate |
| `subGammaLogLogWidth_eq_boundary_optTilt` | `AnytimeValid.OptimizedLambdaCS` | The closed-form log-log width equals the sub-Gamma boundary at the per-time optimal tilt |
| `optimized_lambda_two_sided_confidence_sequence` | `AnytimeValid.OptimizedLambdaCS` | Two-sided optimized-`λ` iterated-log confidence sequence via the deterministic stitching bridge and the `X`/`-X` transfer |
| `optimized_lambda_two_sided_closed_form_pointwise` | `AnytimeValid.OptimizedLambdaCS` | Closed-form pointwise interval-width form of the two-sided optimized-`λ` confidence sequence |
| `fixedGrid_logLog_bridge_forces_exact_boundary` | `AnytimeValid.OptimizedLambdaCS` | Obstruction: a fixed finite-grid all-time closed-form bridge forces the grid to attain the exact per-time optimal boundary |
| `eProcess_typeI_control` | `AnytimeValid.EProcess` | Safe-testing Type-I control: an e-process rejection event has mass at most the level `α` over the Ville maximal inequality |
| `eProcess_product_of_supermartingale` | `AnytimeValid.EProcess` | Product of nonnegative supermartingale factors with unit start is an e-process |
| `eProcess_optionalContinuation` | `AnytimeValid.EProcess` | Optional continuation: the stopped value of an e-process keeps integral at most one |
| `bettingWealth_supermartingale` | `AnytimeValid.BettingCS` | Betting wealth from predictable bets under the conditional-mean null is a nonnegative supermartingale |
| `betting_time_uniform_confidence_sequence` | `AnytimeValid.BettingCS` | Countable-time Ville confidence sequence for the betting wealth e-process |
| `betting_confidence_sequence_of_condMean` | `AnytimeValid.BettingCS` | End-to-end betting confidence sequence for a bounded mean from predictable bets and the conditional-mean null |
| `literalDyadicEpochWeight_not_summable` | `AnytimeValid.DyadicEpochCS` | Obstruction: the literal harmonic dyadic-epoch weights are not summable, ruling out the naive all-`n` epoch mixture |
| `pSeriesDyadicEpochWeight_summable` | `AnytimeValid.DyadicEpochCS` | The redirected p-series dyadic-epoch weights are summable, recovering a finite epoch-capital budget |
| `pSeriesDyadicEpochWeight_zero_unitPenalty` | `AnytimeValid.DyadicEpochCS` | The concrete unit-capital stitching penalty for the first p-series epoch is `log 2` |
| `countableWeightedSupermartingale_tsum` | `AnytimeValid.DyadicEpochCS` | Weighted countable sums of real supermartingales are supermartingales under the domination hypothesis, the countable analogue of `supermartingale_finset_sum` |
| `dyadicEpochMixture_supermartingale` | `AnytimeValid.DyadicEpochCS` | The p-series dyadic-epoch mixture of stitched sub-Gamma exponential processes is a nonnegative supermartingale |
| `subGammaLogLogWidth_add_stitchingPenalty` | `AnytimeValid.DyadicEpochCS` | The all-`n` dyadic-epoch boundary is the log-log width plus the explicit per-epoch stitching penalty |
| `dyadic_epoch_confidence_sequence_subGamma` | `AnytimeValid.DyadicEpochCS` | One-sided all-`n` dyadic-epoch sub-Gamma confidence sequence with the explicit grid budget |
| `dyadic_epoch_two_sided_confidence_sequence` | `AnytimeValid.DyadicEpochCS` | Two-sided all-`n` dyadic-epoch confidence sequence via the `X`/`-X` transfer and the explicit stitching penalty |

## Time-uniform PAC-Bayes

| Declaration | Module | Role |
|---|---|---|
| `scorePriorMixtureProcess` | `PACBayes.TimeUniformScorePACBayes` | Finite prior-weighted mixture of exponentiated hypothesis scores |
| `timeUniformScorePACBayesAnyPosteriorFailure` | `PACBayes.TimeUniformScorePACBayes` | Common failure event existentially quantifying over every natural time and finite posterior PMF |

| Theorem | Module | Role |
|---|---|---|
| `pacBayesPriorMixture_supermartingale` | `PACBayes.TimeUniformPACBayes` | Prior mixture of per-hypothesis fixed-tilt exponential processes is a nonnegative supermartingale |
| `timeUniformPACBayes_crossing_bound` | `PACBayes.TimeUniformPACBayes` | Ville crossing bound for the prior-mixture process over all times |
| `timeUniformPACBayes_bound` | `PACBayes.TimeUniformPACBayes` | Process-level time-uniform PAC-Bayes bound: with probability at least `1 - δ`, the posterior running mean of the abstract martingale-difference process stays under the `cgf`/KL/`log(1/δ)` boundary for every `n ≥ 1` |
| `scorePriorMixture_eProcess` | `PACBayes.TimeUniformScorePACBayes` | A full-support finite prior mixture of exponentiated score e-processes is an e-process |
| `timeUniformScorePACBayesAnyPosteriorFailure_subset_crossing` | `PACBayes.TimeUniformScorePACBayes` | Any all-time/all-posterior score failure forces the common prior-mixture e-process to cross `1 / δ` |
| `timeUniformScorePACBayes_allPosteriors_bound` | `PACBayes.TimeUniformScorePACBayes` | Generic finite-hypothesis compiler: one Ville event controls every time and every posterior through pathwise Donsker--Varadhan |
| `posteriorTarget_le_of_not_mem_timeUniformScorePACBayesFailure` | `PACBayes.TimeUniformScorePACBayes` | Outside the common failure event, a deterministic pointwise regret term transfers the posterior score bound to a posterior target |
| `timeUniformIIDPACBayes_allPosteriors_bound` | `PACBayes.TimeUniformIID` | End-to-end finite-class i.i.d. bounded-loss theorem, simultaneous over all posterior PMFs at every positive sample time |
| `timeUniformIIDPACBayes_grid_allPosteriors_bound` | `PACBayes.TimeUniformIIDGrid` | Finite-class i.i.d. theorem with a fixed finite grid of data-dependent tilt choices, simultaneous over all posterior PMFs |
| `timeUniformContinuousPACBayes_bound` | `PACBayes.TimeUniformContinuousPACBayes` | Process-level time-uniform PAC-Bayes theorem on an arbitrary measurable hypothesis space for a fixed prior and posterior |
| `sphericalGaussianMeasure_klDiv_toReal_eq` | `PACBayes.GaussianMeasureKL` | Measure-theoretic KL between finite-dimensional spherical Gaussian laws equals its explicit closed form |
| `timeUniformSphericalGaussianPACBayes_bound` | `PACBayes.TimeUniformGaussianPACBayes` | Process-level time-uniform PAC-Bayes theorem specialized to a fixed finite-dimensional spherical-Gaussian prior/posterior pair |
| `timeUniformIIDGaussianPACBayes_bound` | `PACBayes.IIDContinuousGaussian` | End-to-end i.i.d. bounded-loss theorem over a continuous finite-dimensional hypothesis space with explicit spherical-Gaussian KL |
| `fairBoolGaussianPACBayesFailure_mass_ge_twoPowNegHundred` | `PACBayes.IIDContinuousGaussian` | Explicit positive-mass witness: the first-100-true cylinder has probability `2⁻¹⁰⁰` and lies inside the worked Gaussian PAC-Bayes failure event |
| `fairBoolThreshold_endToEnd_certificate` | `PACBayes.IIDContinuousGaussian` | Stochastic fair-Bernoulli product-stream instance with a checked nonconstant Gaussian-threshold loss, exact population risk `1/2`, evaluated penalty `54/275`, and a positive-probability failure cylinder, without a tightness claim |
| `timeUniformIIDGaussianPACBayes_grid_bound` | `PACBayes.IIDContinuousGaussianGrid` | Simultaneous time-uniform i.i.d. bound for a finite catalog of fixed spherical-Gaussian posterior/tilt pairs, with entrywise confidence budgets summed explicitly |
| `timeUniformIIDGaussianPACBayes_selected_bound` | `PACBayes.IIDContinuousGaussianGrid` | Data-dependent selector corollary for an arbitrary choice from the fixed finite Gaussian posterior/tilt catalog |
| `fairBoolThreshold_twoGaussianGrid_certificate` | `PACBayes.IIDContinuousGaussianGrid` | Stochastic two-entry certificate for `N(0,1)` at tilt `1/2` and `N(1,1)` at tilt `1/4`, with total failure budget `exp(-1)` |
| `fairBoolThreshold_twoGaussianSelected_certificate` | `PACBayes.IIDContinuousGaussianGrid` | The worked two-entry fair-Bernoulli catalog remains valid for every sample-dependent Boolean selector |

## Finite Markov prequential risk

| Theorem | Module | Role |
|---|---|---|
| `pathSquaredLoss_condExp` | `StochasticDynamics.MarkovRisk` | Derives the next-step squared-loss conditional expectation from the finite transition PMF and its Ionescu--Tulcea path law |
| `markovRiskInnovation_condExp_eq_zero` | `StochasticDynamics.MarkovRisk` | Centers observed loss minus transition-row conditional risk under the generated filtration |
| `markovRiskInnovation_condSecondMoment_le_one` | `StochasticDynamics.MarkovRisk` | Conservative unit conditional-second-moment bound retained as a simple compatibility lemma |
| `markovRiskInnovation_condSecondMoment_le_one_fourth` | `StochasticDynamics.MarkovRisk` | Sharp universal `1/4` conditional-second-moment bound for the centered `[0,1]` one-step loss |
| `runningMean_markovRiskInnovation` | `StochasticDynamics.MarkovRisk` | Identifies the innovation mean with observed prequential risk minus average conditional risk |
| `markovPrequentialRiskExceptionalEvent_mass_le_delta` | `StochasticDynamics.MarkovRisk` | Gives one measurable all-time finite-grid exceptional event with probability at most `delta` |
| `averageConditionalRisk_lt_empiricalPrequentialRisk_add_boundary_of_not_mem` | `StochasticDynamics.MarkovRisk` | Bounds average conditional risk by observed prequential loss plus the declared sub-Gamma boundary outside that event |
| `runningMean_markovRiskShortfall` | `StochasticDynamics.MarkovPACBayes` | Reorients the Markov innovation as conditional risk minus observed loss, the sign required for an upper-risk certificate |
| `posteriorAverage_runningMean_markovRiskShortfall` | `StochasticDynamics.MarkovPACBayes` | Identifies the posterior-averaged shortfall with posterior conditional risk minus posterior empirical prequential risk |
| `markovRiskShortfall_incrementAdapted` | `StochasticDynamics.MarkovPACBayes` | Preserves increment adaptedness under the risk-shortfall sign change |
| `measurable_markovRiskShortfall` | `StochasticDynamics.MarkovPACBayes` | Establishes measurability of every catalog member's risk-shortfall increment |
| `integrable_markovRiskShortfall` | `StochasticDynamics.MarkovPACBayes` | Establishes integrability under the actual finite Markov path law |
| `abs_markovRiskShortfall_le_one` | `StochasticDynamics.MarkovPACBayes` | Supplies the uniform absolute bound for `[0,1]` squared losses |
| `markovRiskShortfall_condExp_eq_zero` | `StochasticDynamics.MarkovPACBayes` | Derives conditional centering of the risk shortfall from the Markov path-law identity |
| `markovRiskShortfall_condSecondMoment_le_one_fourth` | `StochasticDynamics.MarkovPACBayes` | Transfers the sharp universal `1/4` conditional-second-moment proxy to the risk shortfall |
| `markovPACBayesAnyPosteriorUpperFailure_subset_processFailure` | `StochasticDynamics.MarkovPACBayes` | Embeds the risk-facing posterior failure event into the generic time-uniform PAC-Bayes process failure event |
| `markovPACBayes_allPosteriors_bound` | `StochasticDynamics.MarkovPACBayes` | Controls the raw all-time, all-posterior Markov failure set in outer probability at fixed tilt |
| `markovPACBayesExceptionalEvent_measurable` | `StochasticDynamics.MarkovPACBayes` | Proves measurability of the hull used for the public confidence event |
| `markovPACBayesRawFailure_subset_exceptionalEvent` | `StochasticDynamics.MarkovPACBayes` | Shows that the measurable hull contains every raw posterior-existential violation |
| `markovPACBayesExceptionalEvent_mass_le_delta` | `StochasticDynamics.MarkovPACBayes` | Gives one measurable exceptional event of ordinary probability at most `delta` |
| `markovPosteriorAverageConditionalRisk_lt_of_not_mem` | `StochasticDynamics.MarkovPACBayes` | Outside the common event, controls every posterior and every positive time by empirical prequential risk plus KL and the sub-Gamma boundary |
| `subGammaCgf_oneFourth_one_div` | `StochasticDynamics.MarkovPACBayes` | Rewrites the `1/4`-variance sub-Gamma contribution as `lambda / (8 * (1 - lambda / 3))` |
| `markovPACBayes_prequentialRisk_certificate` | `StochasticDynamics.MarkovPACBayes` | Publication-facing finite-catalog theorem with a measurable common event, all-time and all-posterior validity, and explicit KL penalty |

## Named tail-probability corollaries

| Theorem | Module | Role |
|---|---|---|
| `chernoff_tail` | `Concentration.NamedTails` | Generic two-sided sub-Gaussian tail `P(abs X ≥ t) ≤ 2 exp(-t²/(2c))` from an MGF bound |
| `subGaussianMGF_tail_twoSided` | `Concentration.NamedTails` | Centered two-sided sub-Gaussian tail `P(abs (X - E X) ≥ t) ≤ 2 exp(-t²/(2c))` |
| `hoeffding_mean_tail_twoSided` | `Concentration.NamedTails` | Two-sided Hoeffding tail for the sample mean `P(abs (X̄ - E X̄) ≥ t) ≤ 2 exp(-2 n t²/(b-a)²)` |
| `bernstein_tail` | `Concentration.NamedTails` | Two-sided Bernstein tail `P(abs X ≥ ε) ≤ 2 exp(-ε²/(2(v + bε/3)))` for a finite distribution |
| `bennett_tail` | `Concentration.NamedTails` | Two-sided Bennett / sub-Gamma tail at a chosen `λ` for a finite distribution |

## Distribution bridges and sample statistics

| Theorem | Module | Role |
|---|---|---|
| `bernoulliPMF` | `Statistics.Bernoulli` | Bernoulli(p) probability mass function on `Bool` |
| `bernoulliMean_eq` | `Statistics.Bernoulli` | Bernoulli mean equals `p` |
| `bernoulliVariance_eq` | `Statistics.Bernoulli` | Bernoulli variance equals `p(1 - p)` |
| `bernoulli_bernstein_tail` | `Statistics.Bernoulli` | Two-sided Bernstein tail specialized to Bernoulli(p) |
| `sampleMean` | `Statistics.SampleStatistics` | Sample mean `(1/n) ∑ x i` of a finite sample |
| `sampleVariance` | `Statistics.SampleStatistics` | Population-form sample variance `(1/n) ∑ (x i - x̄)²` |
| `sampleVariance_nonneg` | `Statistics.SampleStatistics` | Sample variance is nonnegative |
| `sampleVariance_eq_secondMoment_sub_meanSq` | `Statistics.SampleStatistics` | Variance decomposition `Var = E[X²] - x̄²` |
| `sampleMean_hoeffding_tail` | `Statistics.SampleStatistics` | Two-sided Hoeffding tail for the named sample mean |

## Classical estimation

| Theorem | Module | Role |
|---|---|---|
| `weightedExpectation` | `Statistics.ClassicalEstimation` | Finite weighted expectation `∑ w x · X x`, the population-mean primitive |
| `weightedExpectation_linear` | `Statistics.ClassicalEstimation` | Linearity of the weighted expectation in the estimator |
| `sampleMean_unbiased_finite` | `Statistics.ClassicalEstimation` | Sample mean is unbiased for the finite population mean |
| `sampleVarianceBessel` | `Statistics.ClassicalEstimation` | Bessel-corrected sample variance `(1/(n-1)) ∑ (x i - x̄)²` |
| `sampleVarianceBessel_unbiased_finite` | `Statistics.ClassicalEstimation` | Bessel-corrected sample variance is unbiased for the finite-population variance |
| `bernoulliScoreAtSampleMean_eq_zero` | `Statistics.ClassicalEstimation` | Bernoulli log-likelihood score vanishes at the sample-mean MLE |
| `bernoulliLogLikelihood_global_argmax_from_count` | `Statistics.ClassicalEstimation` | Sample mean is the global Bernoulli log-likelihood maximizer |
| `gaussianKnownVarianceLogLikelihood_mle` | `Statistics.ClassicalEstimation` | Sample mean is the known-variance Gaussian MLE |
| `horvitzThompson_design_unbiased` | `Statistics.ClassicalEstimation` | Horvitz-Thompson estimator is design-unbiased for the finite-population total |
| `bootstrapMean_eq_sampleMean` | `Statistics.ClassicalEstimation` | Bootstrap-resample mean equals the sample mean |

## Fisher information and Cramér-Rao

| Theorem | Module | Role |
|---|---|---|
| `weightedVariance` | `Statistics.FisherInformation` | Finite weighted variance of an estimator under a weight vector |
| `weightedCovariance` | `Statistics.FisherInformation` | Finite weighted covariance of two functions |
| `scoreFunction` | `Statistics.FisherInformation` | Score `∂_θ log p(x; θ)` as `pmfDeriv / pmf` |
| `fisherInformation` | `Statistics.FisherInformation` | Fisher information as the weighted variance of the score |
| `score_mean_zero_of_finite_regular` | `Statistics.FisherInformation` | Score has zero mean under regularity (`∑ p' = 0`) |
| `covariance_score_eq_deriv_mean` | `Statistics.FisherInformation` | Estimator-score covariance equals the derivative of the estimator mean |
| `covariance_cauchy_schwarz` | `Statistics.FisherInformation` | Weighted Cauchy-Schwarz: `Cov² ≤ Var · Var` |
| `cramerRao_unbiased` | `Statistics.CramerRao` | Cramér-Rao lower bound `1 / I(θ) ≤ Var(T)` for an unbiased estimator |
| `bernoulliFisherInformation` | `Statistics.CramerRao` | Bernoulli Fisher information `1 / (p(1-p))` |
| `bernoulliHalfFisherInformation` | `Statistics.CramerRao` | Concrete witness: `I(1/2) = 4` |
| `bernoulliHalfCramerRaoWitness` | `Statistics.CramerRao` | Concrete witness: identity estimator attains variance `1/4 = 1 / I(1/2)` |

## Finite exponential families

| Declaration | Module | Role |
|---|---|---|
| `finitePartition` | `Statistics.ExponentialFamily` | Finite exponential-family partition sum `Z(theta)` |
| `finiteLogPartition` | `Statistics.ExponentialFamily` | Log-partition function `A(theta) = log Z(theta)` |
| `finiteExponentialPMF` | `Statistics.ExponentialFamily` | Natural-parameter finite exponential-family probability mass |
| `finiteExponentialPMFDeriv` | `Statistics.ExponentialFamily` | Natural-parameter derivative of the finite exponential-family mass |
| `finitePartition_pos` | `Statistics.ExponentialFamily` | Positive base weights give positive finite partition sum |
| `finiteExponentialPMF_sum_one` | `Statistics.ExponentialFamily` | Normalized exponential-family masses sum to one |
| `finiteExponentialPMF_pos` | `Statistics.ExponentialFamily` | Positive base weights give positive normalized masses |
| `finitePartition_hasDerivAt` | `Statistics.ExponentialFamily` | Termwise derivative of the finite partition sum |
| `finiteExponentialFamily_mean_eq_logPartition_deriv` | `Statistics.ExponentialFamily` | Finite exponential-family mean equals the log-partition derivative numerator divided by `Z(theta)` |
| `finiteLogPartition_hasDerivAt` | `Statistics.ExponentialFamily` | Log-partition derivative identity `A'(theta) = E_theta[T]` |
| `finiteLogPartition_hasDerivAt_of_positiveBase` | `Statistics.ExponentialFamily` | Positive-base wrapper for `A'(theta) = E_theta[T]` |
| `finiteExponentialPMF_hasDerivAt` | `Statistics.ExponentialFamily` | Derivative of the normalized finite exponential-family mass |
| `finiteMean_hasDerivAt` | `Statistics.ExponentialFamily` | Differentiating the finite mean gives a centered second moment |
| `finiteMean_deriv_eq_variance` | `Statistics.ExponentialFamily` | Centered second-moment derivative equals finite weighted variance |
| `finiteLogPartition_hasSecondDerivAt` | `Statistics.ExponentialFamily` | Log-partition curvature identity `A''(theta) = Var_theta(T)` |
| `finiteLogPartition_hasSecondDerivAt_of_positiveBase` | `Statistics.ExponentialFamily` | Positive-base wrapper for `A''(theta) = Var_theta(T)` |
| `finiteExponentialFamily_variance_eq_logPartition_secondDeriv` | `Statistics.ExponentialFamily` | Finite exponential-family variance equals log-partition second derivative |
| `finiteExponentialFamily_score_eq_centered` | `Statistics.ExponentialFamily` | Natural-parameter score equals the centered sufficient statistic |
| `finiteExponentialFamily_fisherInformation_eq_variance` | `Statistics.ExponentialFamily` | Natural-parameter Fisher information equals finite variance |
| `finiteExponentialFamily_logPartition_secondDeriv_eq_fisherInformation` | `Statistics.ExponentialFamily` | Direct bridge `I(theta) = A''(theta)` |
| `bernoulliNaturalBase` | `Statistics.ExponentialFamily` | Bernoulli natural-family base weights on `Bool` |
| `bernoulliNaturalStatistic` | `Statistics.ExponentialFamily` | Bernoulli natural sufficient statistic `1{true}` |
| `bernoulliNatural_partition` | `Statistics.ExponentialFamily` | Bernoulli natural partition sum is `1 + exp(theta)` |
| `bernoulliNatural_logPartition_zero` | `Statistics.ExponentialFamily` | Bernoulli natural log-partition at `theta = 0` is `log 2` |
| `bernoulliNatural_mean_zero` | `Statistics.ExponentialFamily` | Bernoulli natural mean at `theta = 0` is `1/2` |
| `bernoulliNatural_logPartition_deriv_zero` | `Statistics.ExponentialFamily` | Bernoulli natural `A'(0) = 1/2` |
| `bernoulliNatural_pmf_zero` | `Statistics.ExponentialFamily` | Both Bernoulli natural atoms have mass `1/2` at `theta = 0` |
| `bernoulliNatural_variance_zero` | `Statistics.ExponentialFamily` | Bernoulli natural variance at `theta = 0` is `1/4` |
| `bernoulliNatural_logPartition_secondDeriv_zero` | `Statistics.ExponentialFamily` | Bernoulli natural `A''(0) = 1/4` |
| `bernoulliNatural_fisher_zero` | `Statistics.ExponentialFamily` | Bernoulli natural Fisher information at `theta = 0` is `1/4` |
| `bernoulliNatural_fisher_eq_variance_zero` | `Statistics.ExponentialFamily` | Bernoulli natural Fisher information equals variance at `theta = 0` |
| `bernoulliNatural_witness` | `Statistics.ExponentialFamily` | Concrete Bernoulli witness with mean `1/2`, variance `1/4`, and Fisher information `1/4` |

## Glivenko-Cantelli

| Theorem | Module | Role |
|---|---|---|
| `lowerRayIndicator` | `GlivenkoCantelli` | Closed lower-ray indicator `1{x ≤ z}` as the empirical-CDF integrand |
| `strictLowerRayIndicator` | `GlivenkoCantelli` | Open lower-ray indicator `1{x < z}`, the atom-safe upper bracket |
| `empiricalCDF` | `GlivenkoCantelli` | Empirical CDF as the lower-ray indicator-class empirical average |
| `empiricalCDFUniformDeviation` | `GlivenkoCantelli` | Uniform empirical-CDF deviation `sup_x abs(F_n(x) - F(x))` |
| `IsGCClass` | `GlivenkoCantelli` | Glivenko-Cantelli class predicate: a.s. uniform-deviation convergence to zero |
| `lowerRayGC_iff_classicalGlivenkoCantelli` | `GlivenkoCantelli` | The classical empirical-CDF GC statement is exactly the lower-ray indicator-class GC statement |
| `empiricalCDF_eq_lowerRayEmpiricalAverage` | `GlivenkoCantelli` | Empirical CDF equals the lower-ray indicator empirical average |
| `integral_lowerRayIndicator_comp_eq_cdf` | `GlivenkoCantelli` | Population lower-ray mass equals the CDF of the pushed-forward law |
| `lowerRayBracketing_uniformDeviation_bound` | `GlivenkoCantelli` | Deterministic finite-grid bracketing bound on the uniform empirical-CDF deviation |
| `finiteLowerRayBracketingGrid` | `GlivenkoCantelli` | Finite grid of bracket points that controls every threshold at a chosen mesh |
| `lowerRayPointwiseStrongLaw` | `GlivenkoCantelli` | Pointwise empirical-CDF strong law at a fixed threshold from the mathlib strong law |
| `strictLowerRayPointwiseStrongLaw` | `GlivenkoCantelli` | Open-upper-bracket pointwise strong law, the atom-safe companion |
| `classicalGlivenkoCantelli_of_pointwise_lowerRay` | `GlivenkoCantelli` | Uniform a.s. GC from pointwise convergence on closed and strict lower rays |
| `classicalGlivenkoCantelli_iid` | `GlivenkoCantelli` | Classical Glivenko-Cantelli for i.i.d. real samples: empirical CDF converges uniformly a.s. to the population CDF |
| `vcHoeffdingBridge_for_gcClass` | `GlivenkoCantelli` | Wraps the GC class into the finite-class VC/Hoeffding empirical-process surface |
| `rademacherERMBridge_for_gcClass` | `GlivenkoCantelli` | Wraps the GC class into the Rademacher ERM generalization surface |
| `vcPacBayesHybridBridge_for_gcClass` | `GlivenkoCantelli` | Wraps the GC class into the VC/PAC-Bayes hybrid surface |
| `bernoulliThreeZerosOneOne_uniformDeviation_le_quarter` | `GlivenkoCantelli` | Concrete non-vacuity witness: explicit four-sample uniform empirical-CDF deviation `≤ 1/4` |

## Partial dependency view for the original finite-class spine

```mermaid
flowchart BT
    defs["Risk / ERM / GhostSample"]
    rad["Empirical Rademacher"]
    sym["Symmetrization"]
    azuma["Azuma tail"]
    massart["Massart"]
    vc["Sauer-Shelah + binary VC bridge"]
    erm["VC ERM excess-risk tail"]
    contraction["Finite contraction"]
    linear["Linear predictors"]
    finite_chain["Finite sub-Gaussian chaining"]
    finite_dudley["Finite Dudley entropy budgets"]
    stability["Finite iid stability adapter"]

    defs --> rad --> sym --> erm
    azuma --> erm
    massart --> erm
    vc --> erm
    rad --> contraction
    rad --> linear
    finite_chain --> finite_dudley
    defs --> stability
```
