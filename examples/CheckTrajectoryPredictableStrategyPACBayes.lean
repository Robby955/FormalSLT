import FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
import FormalSLT.StochasticDynamics.TrajectoryPredictableStrategyPACBayes

/-!
# Joint model--strategy predictable PAC-Bayes checker

The public endpoint permits a path- and time-dependent joint posterior over a
finite model catalog and a finite catalog of predeclared predictable
strategies.  Its complexity term is KL against the product prior.  The
strategies remain predictable: post-data selection does not authorize a tilt
to inspect the current observation.  A constant-tilt catalog with a factorized
selected posterior also yields an ordinary monitored conditional-risk bound,
with model and strategy selection charged by separate KL terms.  More
generally, a catalog of history-dependent predictable strategies shared across
models yields ordinary risk when each model's one-step conditional risk is
constant.
-/

open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
open FormalSLT.StochasticDynamics

namespace FormalSLT.Examples.CheckTrajectoryPredictableStrategyPACBayes

noncomputable section

/-- Uniform full-support prior on either Boolean catalog. -/
def uniformBoolPrior (_ : Bool) : ℝ := (1 : ℝ) / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  constructor
  · constructor <;> simp [uniformBoolPrior]
  · intro i
    simp [uniformBoolPrior]

/-- The model and strategy priors combine into a full-support prior on pairs. -/
example :
    IsFullSupportPMF
      (modelStrategyProductPrior uniformBoolPrior uniformBoolPrior :
        Bool × Bool → ℝ) :=
  modelStrategyProductPrior_isFullSupportPMF
    uniformBoolPrior_isFullSupportPMF uniformBoolPrior_isFullSupportPMF

#check modelStrategyProductPrior_isFullSupportPMF
#check dirac_modelStrategyProductPrior_klDiv_eq
#check klDiv_modelStrategyProductPrior
#check exists_forwardPredictableStrategyPACBayes_event
#check exists_forwardPredictableStrategyPACBayes_normalized_event
#check exists_forwardPredictableStrategyPACBayes_normalized_selected_event
#check exists_forwardPredictableStrategyPACBayes_factorized_normalized_selected_event
#check exists_trajectoryPredictableStrategyPACBayes_selected_event
#check exists_trajectoryPredictableStrategyPACBayes_normalized_selected_event
#check constantTrajectoryTiltCatalog
#check sharedTrajectoryStrategyCatalog
#check trajectoryPredictableStrategyPosteriorTotalWeight_constant_factorized
#check trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk_constant_factorized
#check trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk_constant_factorized
#check exists_trajectoryPredictableStrategyPACBayes_constant_factorized_ordinaryRisk_selected_event
#check exists_trajectoryPredictableStrategyPACBayes_shared_constantConditionalRisk_factorized_ordinaryRisk_event

#print axioms modelStrategyProductPrior_isFullSupportPMF
#print axioms dirac_modelStrategyProductPrior_klDiv_eq
#print axioms klDiv_modelStrategyProductPrior
#print axioms exists_forwardPredictableStrategyPACBayes_event
#print axioms exists_forwardPredictableStrategyPACBayes_normalized_event
#print axioms exists_forwardPredictableStrategyPACBayes_normalized_selected_event
#print axioms exists_forwardPredictableStrategyPACBayes_factorized_normalized_selected_event
#print axioms exists_trajectoryPredictableStrategyPACBayes_selected_event
#print axioms exists_trajectoryPredictableStrategyPACBayes_normalized_selected_event
#print axioms exists_trajectoryPredictableStrategyPACBayes_shared_constantConditionalRisk_factorized_ordinaryRisk_event
#print axioms trajectoryPredictableStrategyPosteriorTotalWeight_constant_factorized
#print axioms trajectoryPredictableStrategyPosteriorNormalizedConditionalRisk_constant_factorized
#print axioms trajectoryPredictableStrategyPosteriorNormalizedEmpiricalRisk_constant_factorized
#print axioms exists_trajectoryPredictableStrategyPACBayes_constant_factorized_ordinaryRisk_selected_event

end

end FormalSLT.Examples.CheckTrajectoryPredictableStrategyPACBayes
