/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformIID

/-!
Public audit for the i.i.d. bounded-loss, time-uniform PAC-Bayes theorem.
-/

open FormalSLT.PACBayes.TimeUniformIID

#check @iidLossGap_runningMean
#check @posteriorAverage_iidLossGap_runningMean
#check @timeUniformIIDPACBayesAnyPosteriorUpperFailure_subset_processFailure
#check @timeUniformIIDPACBayes_allPosteriors_bound

#print axioms iidLossGap_runningMean
#print axioms posteriorAverage_iidLossGap_runningMean
#print axioms timeUniformIIDPACBayesAnyPosteriorUpperFailure_subset_processFailure
#print axioms timeUniformIIDPACBayes_allPosteriors_bound
