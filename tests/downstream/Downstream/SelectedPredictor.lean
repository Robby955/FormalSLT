import FormalSLT.StochasticDynamics

/-!
# Selecting a predictor after monitoring two loss streams

At each reporting time, choose the predictor with the lower observed mean
loss. Both predictors are declared before monitoring begins. The bound is on
the chosen predictor's average one-step conditional risk over the same prefix.
-/

open ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayes.StabilityBridge FormalSLT.StochasticDynamics

namespace Downstream.SelectedPredictor

/-- Ties go to the predictor indexed by `false`. -/
noncomputable def lowerLossModel {Z : Type*} (score : Bool → TrajectoryScore Z)
    (x : ℕ → Z) (n : ℕ) : Bool :=
  decide (trajectoryEmpiricalPrequentialRisk (score true) n x <
    trajectoryEmpiricalPrequentialRisk (score false) n x)

/-- One event covers every positive reporting time. The point posterior at
the selected model pays exactly `log 2` against the uniform two-model prior. -/
theorem selectedRiskBound {Z : Type*}
    [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → Z) Z)
    [∀ n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Bool → TrajectoryScore Z)
    (hscore : ∀ i n u y, score i n u y ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ good : Set (ℕ → Z), (trajectoryMeasure K x0).real goodᶜ ≤ δ ∧
      ∀ x ∈ good, ∀ n : ℕ, 0 < n →
        let selected := score (lowerLossModel score x n)
        trajectoryAverageConditionalRisk K selected n x <
          trajectoryEmpiricalPrequentialRisk selected n x +
            (Real.log 2 + Real.log (1 / δ) + forwardEmpiricalBernsteinPsi (1 / 2) *
              forwardPredictableQuadratic (fun k ↦ observedTrajectoryScore selected k x) n) /
              ((1 / 2 : ℝ) * n) := by
  obtain ⟨good, hmass, hbound⟩ :=
    exists_trajectoryHalfTiltPACBayes_ordinaryRisk_selected_event K x0 hscore
      (finiteUniformRealPMF_isFullSupport Bool) hδ
      (fun x n ↦ diracPosterior (lowerLossModel score x n))
      (fun x n ↦ diracPosterior_isPMF (lowerLossModel score x n))
  refine ⟨good, hmass, ?_⟩
  intro x hx n hn
  simpa [trajectoryPosteriorAverageConditionalRisk, trajectoryPosteriorEmpiricalPrequentialRisk,
    trajectoryPosteriorForwardPredictorQuadraticVariation, pacBayesPosteriorAverage_dirac,
    klDiv_dirac_finiteUniformRealPMF, forwardPredictableQuadratic, forwardPredictorProcess]
    using hbound x hx n hn

end Downstream.SelectedPredictor
