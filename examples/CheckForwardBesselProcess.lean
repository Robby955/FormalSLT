import FormalSLT.AnytimeValid.ForwardBesselProcess

/-!
# Forward hybrid-Bessel process checks

This focused receipt checks the deterministic Welford bridge, the honest
e-process interface, and the sharp two-observation Boolean witness.  The path
`(false,true)`, encoded as `(0,1)`, is an atom of the fair two-Bool product
model.  On that path coefficient `1` fails, while coefficient `3/2` is attained
exactly.
-/

open FormalSLT.AnytimeValid
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace FormalSLT.Examples.CheckForwardBesselProcess

/-- The Boolean path `(false,true)`, encoded by losses `(0,1)`. -/
def falseTrueSample : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 1

theorem falseTrue_predictableQuadratic :
    forwardPredictableQuadratic falseTrueSample 2 = (5 : ℝ) / 4 := by
  norm_num [falseTrueSample, forwardPredictableQuadratic_two]

theorem falseTrue_besselQ :
    forwardBesselQ falseTrueSample 2 = (1 : ℝ) / 2 := by
  norm_num [falseTrueSample, forwardBesselQ_two]

/-- Coefficient `1` is strictly too small on the fair-Bool path. -/
theorem falseTrue_coefficient_one_fails :
    (1 : ℝ) / 2 + forwardBesselQ falseTrueSample 2 <
      forwardPredictableQuadratic falseTrueSample 2 := by
  rw [falseTrue_predictableQuadratic, falseTrue_besselQ]
  norm_num

/-- The repaired coefficient `3/2` is exact on the same path. -/
theorem falseTrue_three_halves_exact :
    forwardPredictableQuadratic falseTrueSample 2 =
      (1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ falseTrueSample 2 := by
  rw [falseTrue_predictableQuadratic, falseTrue_besselQ]
  norm_num

/-- At the sharp two-step witness, both branches of the hybrid envelope agree
with the predictable penalty. -/
theorem falseTrue_hybrid_exact :
    forwardHybridBesselPenalty falseTrueSample 2 = (5 : ℝ) / 4 := by
  norm_num [forwardHybridBesselPenalty, falseTrue_besselQ, harmonic]

/-- The public fixed-tilt boundary uses the hybrid penalty literally. -/
theorem fixedTilt_hybridBoundary_definition_receipt
    {Ω : Type*} (X : ℕ → Ω → ℝ) (lam delta : ℝ) (n : ℕ) (ω : Ω) :
    forwardEmpiricalBernsteinBesselBoundary X lam delta n ω =
      (forwardEmpiricalBernsteinPsi lam *
          forwardHybridBesselPenalty (fun k ↦ X k ω) n +
        Real.log (1 / delta)) / ((n : ℝ) * lam) := by
  rfl

/-- The catalog boundary keeps the exact atom-weight penalty while using the
same hybrid deterministic envelope. -/
theorem catalog_hybridBoundary_definition_receipt
    {κ Ω : Type*} (weight : κ → ℝ) (lam : κ → ℝ)
    (X : ℕ → Ω → ℝ) (delta : ℝ) (j : κ) (n : ℕ) (ω : Ω) :
    forwardEmpiricalBernsteinTiltCatalogBoundary
        weight lam X delta j n ω =
      (forwardEmpiricalBernsteinPsi (lam j) *
          forwardHybridBesselPenalty (fun k ↦ X k ω) n +
        Real.log (1 / (delta * weight j))) / ((n : ℝ) * lam j) := by
  rfl

/-- A concrete endpoint of the scalar one-step inequality. -/
theorem half_tilt_minus_one_scalar_check :
    Real.exp
        ((1 : ℝ) / 2 * (-1) -
          forwardEmpiricalBernsteinPsi ((1 : ℝ) / 2) * (-1) ^ 2) ≤
      1 + (1 : ℝ) / 2 * (-1) := by
  exact exp_forwardEmpiricalBernstein_le_one_add (by norm_num) (by norm_num) (by norm_num)

/-- Focused receipt for the reduced bounded-model interface: the caller only
supplies increment adaptedness, the `[0,1]` observation range, and the
conditional mean. -/
theorem boundedModel_eProcess_receipt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean) :
    EProcess μ ℱ (forwardEmpiricalBernsteinProcess X mean lam) :=
  forwardEmpiricalBernsteinProcess_eProcess_of_bounded
    hlam0 hlam1 hX_adapted hX_unit hmean

/-- The complementary process is the checked positive-tilt route for the
lower tail `mean - X`; this does not assert that its Bessel envelope is an
e-process. -/
theorem boundedModel_lowerTail_eProcess_receipt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean) :
    EProcess μ ℱ (forwardEmpiricalBernsteinLowerProcess X mean lam) :=
  forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded
    hlam0 hlam1 hX_adapted hX_unit hmean

/-- Focused all-time receipt for the explicit fixed-tilt hybrid-Bessel
boundary. -/
theorem boundedModel_allTimeLowerBessel_receipt
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
          mean < forwardPrefixMean (fun k ↦ X k ω) n +
            forwardEmpiricalBernsteinBesselBoundary X lam delta n ω :=
  exists_forwardEmpiricalBernsteinLowerBessel_event
    hδ hlam hlam1 hX_adapted hX_unit hmean

/-- Focused receipt for one full-support finite tilt catalog with hybrid-Bessel
penalties.  The selector may use both the realized path and the current time,
while the catalog and weights remain predeclared. -/
theorem boundedModel_allTimeLowerBesselTiltCatalog_selected_receipt
    {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {weight : κ → ℝ} {lam : κ → ℝ}
    {X : ℕ → Ω → ℝ} {mean delta : ℝ}
    (hδ : 0 < delta)
    (hweight_pos : ∀ j, 0 < weight j)
    (hweight_sum_one : ∑ j : κ, weight j = 1)
    (hlam : ∀ j, 0 < lam j) (hlam1 : ∀ j, lam j < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean)
    (select : Ω → ℕ → κ) :
    ∃ goodEvent : Set Ω,
      μ.real goodEventᶜ ≤ delta ∧
        ∀ ω ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          mean < forwardPrefixMean (fun k ↦ X k ω) n +
            forwardEmpiricalBernsteinTiltCatalogBoundary
              weight lam X delta (select ω n) n ω :=
  exists_forwardEmpiricalBernsteinLowerTiltCatalog_selected_event
    hδ hweight_pos hweight_sum_one hlam hlam1
    hX_adapted hX_unit hmean select

#check forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
#check forwardBesselQ_succ
#check forwardPredictableQuadratic_le_half_add_three_halves_besselQ
#check forwardPredictableQuadratic_abel_welford
#check forwardBesselQ_le_quarter_card
#check forwardPredictableQuadratic_le_harmonic_bessel
#check forwardHybridBesselPenalty
#check forwardPredictableQuadratic_le_hybrid_bessel
#check fixedTilt_hybridBoundary_definition_receipt
#check catalog_hybridBoundary_definition_receipt
#check forwardBessel_coefficient_one_bool_obstruction
#check exp_forwardEmpiricalBernstein_le_one_add
#check forwardEmpiricalBernsteinFactor_condExp_le_one
#check forwardEmpiricalBernsteinProcess_supermartingale
#check forwardEmpiricalBernsteinProcess_eProcess
#check stronglyAdapted_forwardPredictorProcess_of_incrementAdapted
#check stronglyAdapted_forwardEmpiricalBernsteinProcess_of_incrementAdapted
#check integrable_forwardEmpiricalBernsteinProcess_of_bounded
#check integrable_forwardEmpiricalBernsteinFactor_of_bounded
#check forwardEmpiricalBernsteinProcess_eProcess_of_bounded
#check forwardPredictor_one_sub
#check forwardPredictableQuadratic_one_sub
#check forwardBesselQ_one_sub
#check forwardEmpiricalBernsteinLowerProcess_eq
#check forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#check forwardEmpiricalBernsteinLowerProcess_atTop_crossing_mass_le_delta
#check forwardEmpiricalBernsteinLowerBesselEnvelope_le_lowerProcess
#check forwardEmpiricalBernsteinLowerBesselFailure_subset_crossing
#check forwardEmpiricalBernsteinLowerBesselFailure_mass_le_delta
#check exists_forwardEmpiricalBernsteinLowerBessel_event
#check finiteWeightedProcess_eProcess
#check forwardEmpiricalBernsteinLowerTiltMixtureProcess_eProcess_of_bounded
#check forwardEmpiricalBernsteinLowerTiltMixtureProcess_atTop_crossing_mass_le_delta
#check forwardEmpiricalBernsteinTiltCatalogBoundary
#check forwardEmpiricalBernsteinTiltCatalogBoundary_eq
#check forwardEmpiricalBernsteinLowerTiltCatalogFailure_subset_mixture_crossing
#check forwardEmpiricalBernsteinLowerTiltCatalogFailure_mass_le_delta
#check forwardEmpiricalBernsteinLowerTiltCatalog_all_of_not_mem
#check forwardEmpiricalBernsteinLowerTiltCatalog_selected_of_not_mem
#check exists_forwardEmpiricalBernsteinLowerTiltCatalog_event
#check exists_forwardEmpiricalBernsteinLowerTiltCatalog_selected_event
#check forwardEmpiricalBernsteinBesselEnvelope_certified
#check forwardPlugIn_eProcess_of_condExp_step
#check forwardBesselExponentialEnvelope_le_forwardPlugIn
#check forwardBesselEnvelope_certified_by_eProcess
#check forwardPredictorProcess_one_sub
#check incrementAdapted_one_sub
#check forwardPredictorProcess_mem_Icc_of_mem_Icc
#check sum_mean_sub_eq_mul_sub_forwardPrefixMean
#check forwardEmpiricalBernsteinProcess_le_of_mem_Icc
#check forwardEmpiricalBernsteinFactor_le_of_mem_Icc

#print axioms forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
#print axioms forwardBesselQ_succ
#print axioms forwardPredictableQuadratic_le_half_add_three_halves_besselQ
#print axioms forwardPredictableQuadratic_abel_welford
#print axioms forwardBesselQ_le_quarter_card
#print axioms forwardPredictableQuadratic_le_harmonic_bessel
#print axioms forwardPredictableQuadratic_le_hybrid_bessel
#print axioms fixedTilt_hybridBoundary_definition_receipt
#print axioms catalog_hybridBoundary_definition_receipt
#print axioms forwardBessel_coefficient_one_bool_obstruction
#print axioms exp_forwardEmpiricalBernstein_le_one_add
#print axioms forwardEmpiricalBernsteinFactor_condExp_le_one
#print axioms forwardEmpiricalBernsteinProcess_supermartingale
#print axioms forwardEmpiricalBernsteinProcess_eProcess
#print axioms forwardEmpiricalBernsteinProcess_eProcess_of_bounded
#print axioms forwardPredictableQuadratic_one_sub
#print axioms forwardBesselQ_one_sub
#print axioms forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#print axioms forwardEmpiricalBernsteinLowerProcess_atTop_crossing_mass_le_delta
#print axioms forwardEmpiricalBernsteinLowerBesselEnvelope_le_lowerProcess
#print axioms forwardEmpiricalBernsteinLowerBesselFailure_subset_crossing
#print axioms forwardEmpiricalBernsteinLowerBesselFailure_mass_le_delta
#print axioms exists_forwardEmpiricalBernsteinLowerBessel_event
#print axioms finiteWeightedProcess_eProcess
#print axioms forwardEmpiricalBernsteinLowerTiltMixtureProcess_eProcess_of_bounded
#print axioms forwardEmpiricalBernsteinLowerTiltMixtureProcess_atTop_crossing_mass_le_delta
#print axioms forwardEmpiricalBernsteinTiltCatalogBoundary_eq
#print axioms forwardEmpiricalBernsteinLowerTiltCatalogFailure_subset_mixture_crossing
#print axioms forwardEmpiricalBernsteinLowerTiltCatalogFailure_mass_le_delta
#print axioms forwardEmpiricalBernsteinLowerTiltCatalog_all_of_not_mem
#print axioms forwardEmpiricalBernsteinLowerTiltCatalog_selected_of_not_mem
#print axioms exists_forwardEmpiricalBernsteinLowerTiltCatalog_event
#print axioms exists_forwardEmpiricalBernsteinLowerTiltCatalog_selected_event
#print axioms forwardEmpiricalBernsteinBesselEnvelope_certified
#print axioms forwardPlugIn_eProcess_of_condExp_step
#print axioms forwardBesselEnvelope_certified_by_eProcess
#print axioms forwardPredictorProcess_one_sub
#print axioms incrementAdapted_one_sub
#print axioms forwardPredictorProcess_mem_Icc_of_mem_Icc
#print axioms sum_mean_sub_eq_mul_sub_forwardPrefixMean
#print axioms forwardEmpiricalBernsteinProcess_le_of_mem_Icc
#print axioms forwardEmpiricalBernsteinFactor_le_of_mem_Icc
#print axioms falseTrue_coefficient_one_fails
#print axioms falseTrue_three_halves_exact
#print axioms falseTrue_hybrid_exact
#print axioms half_tilt_minus_one_scalar_check
#print axioms boundedModel_eProcess_receipt
#print axioms boundedModel_lowerTail_eProcess_receipt
#print axioms boundedModel_allTimeLowerBessel_receipt
#print axioms boundedModel_allTimeLowerBesselTiltCatalog_selected_receipt

end FormalSLT.Examples.CheckForwardBesselProcess
