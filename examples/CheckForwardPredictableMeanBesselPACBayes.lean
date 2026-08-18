import FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes

/-!
# Predictable-mean forward-Bessel PAC-Bayes checks

This receipt records the finite-hypothesis endpoint with a distinct
past-measurable conditional-mean process for each hypothesis. One outer-mass
event is simultaneous over time, posterior, and the declared finite tilt
catalog. No IID or trajectory specialization is used.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL

noncomputable section

namespace FormalSLT.Examples.CheckForwardPredictableMeanBesselPACBayes

open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes

/-- The boundary exposes KL, the declared atom cost, and the posterior average
of the per-hypothesis hybrid-Bessel penalties literally. -/
theorem predictableMean_boundary_definition_receipt
    {ι κ Ω : Type*} [Fintype ι]
    (prior : ι → ℝ) (weight : κ → ℝ) (lam : κ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ)
    (delta : ℝ) (j : κ) (n : ℕ) (ω : Ω) :
    forwardPredictableMeanBesselPACBayesBoundary
        prior weight lam X posterior delta j n ω =
      (klDiv posterior prior + Real.log (1 / (delta * weight j)) +
          forwardEmpiricalBernsteinPsi (lam j) *
            forwardPosteriorHybridBesselPenalty posterior X n ω) /
        ((n : ℝ) * lam j) := by
  rfl

/-- Focused receipt for the nonstationary bounded finite-hypothesis model. -/
theorem predictableMean_boundedFiniteHypothesis_event_receipt
    {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X mean : ι → ℕ → Ω → ℝ} {lam : κ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hmean_adapted : ∀ i, StronglyAdapted ℱ (mean i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] mean i k) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ j : κ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              posteriorAverage posterior
                  (fun i ↦ forwardPrefixMean (fun k ↦ mean i k ω) n) <
                posteriorAverage posterior
                    (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
                  forwardPredictableMeanBesselPACBayesBoundary
                    prior weight lam X posterior delta j n ω :=
  exists_forwardPredictableMeanBesselPACBayes_event
    hprior hweight hdelta hlam hlam1 hX_adapted hmean_adapted hX_unit hmean

#check forwardPosteriorHybridBesselPenalty
#check forwardPredictableMeanBesselPACBayesScore
#check posteriorAverage_forwardPredictableMeanBesselPACBayesScore
#check forwardPredictableMeanBesselPACBayesMasterProcess
#check forwardPredictableMeanBesselPACBayesMasterProcess_eProcess_of_bounded
#check forwardPredictableMeanBesselPACBayesBoundary
#check forwardPredictableMeanBesselPACBayesExceptionalEvent
#check forwardPredictableMeanBesselPACBayesExceptionalEvent_mass_le_delta
#check forwardPredictableMeanBesselPACBayes_boundaryFailure_mem_exceptionalEvent
#check forwardPredictableMeanBesselPACBayes_allPosteriors_of_not_mem
#check forwardPredictableMeanBesselPACBayes_selected_of_not_mem
#check exists_forwardPredictableMeanBesselPACBayes_event
#check predictableMean_boundary_definition_receipt
#check predictableMean_boundedFiniteHypothesis_event_receipt

#print axioms posteriorAverage_forwardPredictableMeanBesselPACBayesScore
#print axioms forwardPredictableMeanBesselPACBayesMasterProcess_eProcess_of_bounded
#print axioms forwardPredictableMeanBesselPACBayesExceptionalEvent_mass_le_delta
#print axioms forwardPredictableMeanBesselPACBayes_boundaryFailure_mem_exceptionalEvent
#print axioms forwardPredictableMeanBesselPACBayes_allPosteriors_of_not_mem
#print axioms forwardPredictableMeanBesselPACBayes_selected_of_not_mem
#print axioms exists_forwardPredictableMeanBesselPACBayes_event
#print axioms predictableMean_boundary_definition_receipt
#print axioms predictableMean_boundedFiniteHypothesis_event_receipt

end FormalSLT.Examples.CheckForwardPredictableMeanBesselPACBayes
