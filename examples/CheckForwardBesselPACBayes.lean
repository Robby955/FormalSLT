import FormalSLT.PACBayes.ForwardBesselPACBayes

/-!
# Forward hybrid-Bessel PAC-Bayes checks

This focused receipt checks the exact nested-mixture boundary and the generic
finite-hypothesis capstone.  The master process mixes the actual lower-tail
predictable-residual e-processes.  The hybrid Bessel term appears only as a
pointwise lower envelope inside the displayed boundary.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators

noncomputable section

namespace FormalSLT.Examples.CheckForwardBesselPACBayes

open FormalSLT.PACBayes.ForwardBesselPACBayes

/-- The public boundary exposes the posterior-average hybrid penalty and both
complexity costs literally. -/
theorem boundary_definition_receipt
    {ι κ Ω : Type*} [Fintype ι]
    (prior : ι → ℝ) (weight : κ → ℝ) (lam : κ → ℝ)
    (X : ι → ℕ → Ω → ℝ) (posterior : ι → ℝ)
    (delta : ℝ) (j : κ) (n : ℕ) (ω : Ω) :
    forwardBesselPACBayesBoundary
        prior weight lam X posterior delta j n ω =
      (klDiv posterior prior + Real.log (1 / (delta * weight j)) +
          forwardEmpiricalBernsteinPsi (lam j) *
            forwardPosteriorHybridBesselPenalty posterior X n ω) /
        ((n : ℝ) * lam j) := by
  rfl

/-- Focused receipt for the bounded finite-hypothesis model.  One event is
simultaneous over every time `n >= 2`, posterior PMF, and predeclared tilt. -/
theorem boundedFiniteHypothesis_event_receipt
    {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : κ → ℝ} (hweight : IsFullSupportPMF weight)
    {X : ι → ℕ → Ω → ℝ} {mean : ι → ℝ} {lam : κ → ℝ}
    {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : ∀ i, IncrementAdapted ℱ (X i))
    (hX_unit : ∀ i k ω, 0 ≤ X i k ω ∧ X i k ω ≤ 1)
    (hmean : ∀ i k, μ[X i k | ℱ k] =ᵐ[μ] fun _ ↦ mean i) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ j : κ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              posteriorAverage posterior mean <
                posteriorAverage posterior
                    (fun i ↦ forwardPrefixMean (fun k ↦ X i k ω) n) +
                  forwardBesselPACBayesBoundary
                    prior weight lam X posterior delta j n ω :=
  exists_forwardBesselPACBayes_event
    hprior hweight hdelta hlam hlam1 hX_adapted hX_unit hmean

#check forwardPosteriorHybridBesselPenalty
#check forwardBesselPACBayesScore
#check posteriorAverage_forwardBesselPACBayesScore
#check forwardBesselPACBayesMasterProcess
#check forwardBesselPACBayesMasterProcess_eProcess_of_bounded
#check forwardBesselPACBayesBoundary
#check forwardBesselPACBayesExceptionalEvent
#check forwardBesselPACBayesExceptionalEvent_mass_le_delta
#check forwardBesselPACBayes_boundaryFailure_mem_exceptionalEvent
#check forwardBesselPACBayes_allPosteriors_of_not_mem
#check forwardBesselPACBayes_selected_of_not_mem
#check exists_forwardBesselPACBayes_event
#check boundary_definition_receipt
#check boundedFiniteHypothesis_event_receipt

#print axioms posteriorAverage_forwardBesselPACBayesScore
#print axioms forwardBesselPACBayesMasterProcess_eProcess_of_bounded
#print axioms forwardBesselPACBayesExceptionalEvent_mass_le_delta
#print axioms forwardBesselPACBayes_boundaryFailure_mem_exceptionalEvent
#print axioms forwardBesselPACBayes_allPosteriors_of_not_mem
#print axioms forwardBesselPACBayes_selected_of_not_mem
#print axioms exists_forwardBesselPACBayes_event
#print axioms boundary_definition_receipt
#print axioms boundedFiniteHypothesis_event_receipt

end FormalSLT.Examples.CheckForwardBesselPACBayes
