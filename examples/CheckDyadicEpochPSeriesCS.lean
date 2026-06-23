/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.DyadicEpochCS

/-!
# P-series dyadic-epoch CS checker

This checker starts the redirected dyadic-epoch route: replace the impossible
literal harmonic epoch weights by summable p-series weights.
-/

open FormalSLT.AnytimeValid

#check pSeriesDyadicEpochWeight
#check pSeriesDyadicEpochWeight_summable
#check pSeriesDyadicEpochWeight_nonneg
#check pSeriesDyadicEpochWeight_zero
#check pSeriesDyadicEpochWeight_zero_unitPenalty
#check countableWeightedSupermartingale_tsum
#check dyadicEpochGridBudget
#check dyadicEpochExtraStitchingPenalty
#check subGammaWidthAtBudget
#check subGammaLogLogWidthStitchingPenalty
#check subGammaLogLogWidth_add_stitchingPenalty
#check dyadicEpochMixture_supermartingale
#check dyadic_epoch_confidence_sequence_subGamma
#check dyadic_epoch_two_sided_confidence_sequence
#print axioms pSeriesDyadicEpochWeight_summable
#print axioms pSeriesDyadicEpochWeight_zero_unitPenalty
#print axioms countableWeightedSupermartingale_tsum
#print axioms subGammaLogLogWidth_add_stitchingPenalty
#print axioms dyadic_epoch_two_sided_confidence_sequence

example : pSeriesDyadicEpochWeight 0 = 1 / 2 :=
  pSeriesDyadicEpochWeight_zero

example : Real.log (1 / pSeriesDyadicEpochWeight 0) = Real.log 2 :=
  pSeriesDyadicEpochWeight_zero_unitPenalty
