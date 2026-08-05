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
#check @iidLoss_integrable
#check @iidLossPopulationRisk_mem_Icc
#check @iidLossGap_measurable
#check @abs_iidLossGap_le_one
#check @iidLossGap_integrable
#check @iidLossGap_incrementAdapted
#check @iidLossGap_condExp_eq_zero
#check @iidLossGap_condExp_sq_le_one
#check @timeUniformIIDPACBayesAnyPosteriorUpperFailure_subset_processFailure
#check @timeUniformIIDPACBayes_allPosteriors_bound

#print axioms iidLossGap_runningMean
#print axioms posteriorAverage_iidLossGap_runningMean
#print axioms iidLoss_integrable
#print axioms iidLossPopulationRisk_mem_Icc
#print axioms iidLossGap_measurable
#print axioms abs_iidLossGap_le_one
#print axioms iidLossGap_integrable
#print axioms iidLossGap_incrementAdapted
#print axioms iidLossGap_condExp_eq_zero
#print axioms iidLossGap_condExp_sq_le_one
#print axioms timeUniformIIDPACBayesAnyPosteriorUpperFailure_subset_processFailure
#print axioms timeUniformIIDPACBayes_allPosteriors_bound
