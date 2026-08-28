import FormalSLT.AnytimeValid.CountableSleepingPredictableBettingPosterior

/-!
# Countable sleeping-strategy posterior receipt

This checker records the finite full-support compression, its exact wealth
moment, the operational posterior identity, and the KL strategy-selection
inequality. The concrete zero-time case also checks that the compressed prior
is usable without supplying any data or strategy witness.
-/

open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL

example : IsFullSupportPMF (sleepingActiveDyadicPrior 0) :=
  sleepingActiveDyadicPrior_isFullSupportPMF 0

#check sleepingActiveDyadicPrior_isFullSupportPMF
#check liftSleepingActivePosterior_isPMF
#check klDiv_liftSleepingActivePosterior
#check sleepingActivePriorMoment_eq_countableSleepingMixtureWealth
#check countableSleepingMasterPosterior_isPMF
#check countableSleepingMasterBet_eq_posteriorAverage
#check countableSleepingStrategyPosterior_logWealth_le
#check countableSleepingStrategyPosterior_logWealth_le_explicit

#print axioms sleepingActiveDyadicPrior_isFullSupportPMF
#print axioms liftSleepingActivePosterior_isPMF
#print axioms klDiv_liftSleepingActivePosterior
#print axioms sleepingActivePriorMoment_eq_countableSleepingMixtureWealth
#print axioms countableSleepingMasterPosterior_isPMF
#print axioms countableSleepingMasterBet_eq_posteriorAverage
#print axioms countableSleepingStrategyPosterior_logWealth_le
#print axioms countableSleepingStrategyPosterior_logWealth_le_explicit
