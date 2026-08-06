import FormalSLT.PACBayes.IIDContinuousGaussianGrid

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes
open FormalSLT.PACBayes.IIDContinuousGaussian
open FormalSLT.PACBayes.IIDContinuousGaussianGrid

#check timeUniformIIDGaussianPACBayesGridUpperFailure
#check timeUniformIIDGaussianPACBayesSelectedUpperFailure
#check mem_timeUniformIIDGaussianPACBayesSelectedUpperFailure_iff
#check timeUniformIIDGaussianPACBayesUpperFailure_subset_grid
#check timeUniformIIDGaussianPACBayesSelectedUpperFailure_subset_grid
#check timeUniformIIDGaussianPACBayes_grid_bound
#check timeUniformIIDGaussianPACBayes_grid_bound_of_sum_le
#check timeUniformIIDGaussianPACBayes_selected_bound
#check timeUniformIIDGaussianPACBayes_selected_bound_of_sum_le
#check twoGaussianDeltaCatalog_sum
#check fairBoolThreshold_twoGaussianGrid_certificate
#check fairBoolThreshold_twoGaussianSelected_certificate

example :
    ∑ j : Bool, twoGaussianDeltaCatalog j = Real.exp (-1) :=
  twoGaussianDeltaCatalog_sum

def firstObservationSelector : FairBoolStream → Bool := fun omega => omega 0

example :
    fairBoolStreamLaw.real
        (timeUniformIIDGaussianPACBayesSelectedUpperFailure
          fairBoolLaw standardGaussianPrior twoGaussianPosteriorCatalog
          gaussianThresholdBoolLoss fairBoolCoordinateSample
          twoGaussianTiltCatalog twoGaussianDeltaCatalog firstObservationSelector) ≤
      Real.exp (-1) :=
  fairBoolThreshold_twoGaussianSelected_certificate firstObservationSelector

#print axioms timeUniformIIDGaussianPACBayes_grid_bound
#print axioms mem_timeUniformIIDGaussianPACBayesSelectedUpperFailure_iff
#print axioms timeUniformIIDGaussianPACBayesUpperFailure_subset_grid
#print axioms timeUniformIIDGaussianPACBayesSelectedUpperFailure_subset_grid
#print axioms timeUniformIIDGaussianPACBayes_grid_bound_of_sum_le
#print axioms timeUniformIIDGaussianPACBayes_selected_bound
#print axioms timeUniformIIDGaussianPACBayes_selected_bound_of_sum_le
#print axioms twoGaussianDeltaCatalog_sum
#print axioms fairBoolThreshold_twoGaussianGrid_certificate
#print axioms fairBoolThreshold_twoGaussianSelected_certificate
