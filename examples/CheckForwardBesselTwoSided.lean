import FormalSLT.AnytimeValid.ForwardBesselProcess

/-!
# Two-sided forward hybrid-Bessel confidence-sequence check

This focused checker exercises the missing upper-tail endpoint and the actual
two-tail union step.  Both tails use
`forwardEmpiricalBernsteinBesselBoundary` with budget `delta / 2`, so their
observable path penalty is literally the same `forwardHybridBesselPenalty`.
-/

open FormalSLT.AnytimeValid
open MeasureTheory ProbabilityTheory

noncomputable section

namespace FormalSLT.Examples.CheckForwardBesselTwoSided

/-- Reduced bounded-model receipt for the fixed-tilt two-sided confidence
sequence. -/
theorem boundedModel_allTimeTwoSidedBessel_receipt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          |mean - forwardPrefixMean (fun k ↦ X k ω) n| <
            forwardEmpiricalBernsteinBesselBoundary
              X lam (delta / 2) n ω :=
  exists_forwardEmpiricalBernsteinTwoSidedBessel_event
    hδ hlam hlam1 hX_adapted hX_unit hmean

#check sum_sub_mean_eq_mul_sub_forwardPrefixMean
#check forwardHybridBesselPenalty_one_sub
#check forwardEmpiricalBernsteinProcess_atTop_crossing_mass_le_delta
#check forwardEmpiricalBernsteinUpperBesselFailure
#check forwardEmpiricalBernsteinUpperBesselFailure_subset_crossing
#check forwardEmpiricalBernsteinUpperBesselFailure_mass_le_delta
#check forwardEmpiricalBernsteinTwoSidedBesselFailure
#check forwardEmpiricalBernsteinTwoSidedBesselFailure_subset_tail_union
#check forwardEmpiricalBernsteinTwoSidedBesselFailure_mass_le_delta
#check exists_forwardEmpiricalBernsteinTwoSidedBessel_event
#check boundedModel_allTimeTwoSidedBessel_receipt

#print axioms sum_sub_mean_eq_mul_sub_forwardPrefixMean
#print axioms forwardHybridBesselPenalty_one_sub
#print axioms forwardEmpiricalBernsteinProcess_atTop_crossing_mass_le_delta
#print axioms forwardEmpiricalBernsteinUpperBesselFailure_subset_crossing
#print axioms forwardEmpiricalBernsteinUpperBesselFailure_mass_le_delta
#print axioms forwardEmpiricalBernsteinTwoSidedBesselFailure_subset_tail_union
#print axioms forwardEmpiricalBernsteinTwoSidedBesselFailure_mass_le_delta
#print axioms exists_forwardEmpiricalBernsteinTwoSidedBessel_event
#print axioms boundedModel_allTimeTwoSidedBessel_receipt

end FormalSLT.Examples.CheckForwardBesselTwoSided
