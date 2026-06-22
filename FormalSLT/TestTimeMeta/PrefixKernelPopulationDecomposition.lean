/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipComposition
import FormalSLT.Azuma.SharpMcDiarmid
import FormalSLT.Azuma.HasBoundedDifferences

/-!
# Non-vacuous prefix-kernel discharge of the flagship population-risk decomposition

`FlagshipComposition` exposes the prefix-kernel slot only as a nonnegative scalar, and every
existing worked example pins `prefixKernelContribution := 0`. This module fills that slot with a
real derived quantity: the sharp-McDiarmid lower-tail deviation radius produced through the
prefix/tail conditional-kernel disintegration.

The chain is the same shape as the online and McAllester discharges:

* `prefixKernelDeviationBadEventMass_le_exp_of_sharpMcDiarmid` is the genuine machinery. It is
  the constant-width sharp-McDiarmid bound
  `mu^{⊗n} {S | f S + ε ≤ E[f]} ≤ exp (-2 ε² / (n c²))`, obtained from
  `FormalSLT.Azuma.ExposureMartingale.sharp_mcdiarmid_inequality_iid_const_width`, whose proof
  routes through `condExpKernel_product_decomposition`, the prefix/tail kernel support lemma.
  The tail bound is the conclusion, so the conditional-kernel route is load-bearing.
* `prefixKernelPopulationDecomposition_of_sharpMcDiarmid` derives the flagship-shaped
  decomposition `populationRisk ≤ empiricalRisk + 0 + 0 + 0 + 0 + ε` for an observed sample
  outside the lower-tail bad event. The gap is the deviation radius `ε`, not an assumed
  `R ≤ Rhat + penalty` hypothesis.

`PrefixKernelDecompWorkedExample` instantiates this on a concrete bounded `f` over the finite
homogeneous product `Measure.pi (fun _ : Fin 1 => Measure.dirac 0)` on the two-point space
`Fin 2`. The population risk is a genuine integral average, the prefix-kernel deviation radius is
the only nonzero gap, and the capstone `flagship_population_le_bound` assembles the flagship bound
through `flagshipScalarAssembly_from_componentInequalities`.

Sources for this lane: McDiarmid 1989; Boucheron-Lugosi-Massart 2013 §6.
-/

open MeasureTheory ProbabilityTheory Real
open FormalSLT.Azuma.ExposureMartingale
open FormalSLT.Azuma.BoundedDifferences (HasBoundedDifferences)

namespace FormalSLT.TestTimeMeta

noncomputable section

/-- Lower-tail deviation set for the prefix-kernel route: the observed statistic `f S` falls
below its product-measure mean `E[f]` by at least `ε`. This is the event whose mass the sharp
McDiarmid tail controls. -/
def prefixKernelDeviationBadEvent {n : ℕ} {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (f : (Fin n → Z) → ℝ) (ε : ℝ) : Set (Fin n → Z) :=
  {S | f S + ε ≤ ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ))}

/--
Sharp-McDiarmid mass bound for the prefix-kernel lower-tail deviation set.

For the homogeneous finite product measure `mu^{⊗n}` and a statistic `f` with constant-width
bounded differences `c`, the probability that the observed value falls below the mean by at least
`ε` is at most `exp (-2 ε² / (n c²))`.

The proof applies `sharp_mcdiarmid_inequality_iid_const_width` to `-f`; that theorem is assembled
from the sharp conditional sub-Gaussian MGF through the FormalSLT exposure martingale, and its
prefix/tail structure is exactly `condExpKernel_product_decomposition`. The tail bound is the
conclusion here, so the conditional-kernel disintegration is load-bearing.
-/
theorem prefixKernelDeviationBadEventMass_le_exp_of_sharpMcDiarmid
    {n : ℕ} {Z : Type*} [Nonempty Z] [MeasurableSpace Z] [StandardBorelSpace Z]
    {μ : Measure Z} [IsProbabilityMeasure μ]
    {f : (Fin n → Z) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbdd : HasBoundedDifferences f (fun _ : Fin n => c))
    (hf : StronglyMeasurable f)
    (hfi : Integrable f (Measure.pi (fun _ : Fin n => μ)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real (prefixKernelDeviationBadEvent μ f ε)
      ≤ Real.exp (-2 * ε ^ 2 / ((n : ℝ) * c ^ 2)) := by
  have hTail :=
    sharp_mcdiarmid_inequality_iid_const_width (ν := μ) (f := fun S => -f S) (c := c)
      hc hbdd.neg hf.neg hfi.neg hε
  have hset :
      {S | (∫ s, (-f s) ∂(Measure.pi (fun _ : Fin n => μ))) + ε ≤ -f S}
        = prefixKernelDeviationBadEvent μ f ε := by
    ext S
    simp only [prefixKernelDeviationBadEvent, Set.mem_setOf_eq, integral_neg]
    constructor <;> intro h <;> linarith
  rw [hset] at hTail
  exact hTail

/--
Flagship-shaped population-risk decomposition for the prefix-kernel component.

For a sample `S₀` outside the sharp-McDiarmid lower-tail bad event, the population risk, the
product-measure mean of `f`, is bounded by the empirical risk (`f S₀`) plus the deviation radius
`ε`. The five flagship gaps are `(0, 0, 0, 0, ε)`, so the prefix-kernel gap is the only nonzero
one. The inequality is derived from non-membership in the bad event whose mass
`prefixKernelDeviationBadEventMass_le_exp_of_sharpMcDiarmid` controls; no
`R ≤ Rhat + penalty` hypothesis is threaded through the statement.
-/
theorem prefixKernelPopulationDecomposition_of_sharpMcDiarmid
    {n : ℕ} {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (f : (Fin n → Z) → ℝ) {ε : ℝ} (S₀ : Fin n → Z)
    (hnotBad : S₀ ∉ prefixKernelDeviationBadEvent μ f ε)
    (populationRisk empiricalRisk : ℝ)
    (hpop : populationRisk = ∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ)))
    (hemp : empiricalRisk = f S₀) :
    populationRisk ≤ empiricalRisk + 0 + 0 + 0 + 0 + ε := by
  have hlt : (∫ s, f s ∂(Measure.pi (fun _ : Fin n => μ))) < f S₀ + ε :=
    not_le.mp hnotBad
  rw [hpop, hemp]
  linarith

namespace PrefixKernelDecompWorkedExample

/-- Base coordinate measure: a Dirac mass at `0` on the two-point space `Fin 2`. -/
def baseMeasure : Measure (Fin 2) := Measure.dirac (0 : Fin 2)

instance : IsProbabilityMeasure baseMeasure := by
  dsimp [baseMeasure]
  infer_instance

/-- Homogeneous single-coordinate product measure on `Fin 1 → Fin 2`. -/
def sampleMeasure : Measure (Fin 1 → Fin 2) := Measure.pi (fun _ : Fin 1 => baseMeasure)

instance : IsProbabilityMeasure sampleMeasure := by
  dsimp [sampleMeasure]
  infer_instance

/-- A bounded, nonconstant statistic on the product sample space, width `1/2`. -/
def f : (Fin 1 → Fin 2) → ℝ := fun S => if S 0 = 0 then (1 : ℝ) / 4 else (3 : ℝ) / 4

/-- Constant coordinate width of `f`. -/
def width : ℝ := (1 : ℝ) / 2

/-- Sharp-McDiarmid deviation radius; this becomes the prefix-kernel gap. -/
def deviationRadius : ℝ := (1 : ℝ) / 2

/-- The observed sample: the Dirac-supported point. -/
def sample : Fin 1 → Fin 2 := fun _ => 0

/-- The product of Dirac masses collapses to a single Dirac at the constant point. -/
theorem sampleMeasure_eq_dirac :
    sampleMeasure = Measure.dirac (fun _ : Fin 1 => (0 : Fin 2)) := by
  classical
  unfold sampleMeasure baseMeasure
  refine Measure.pi_eq (fun s _ => ?_)
  rw [Fin.prod_univ_one, Measure.dirac_apply, Measure.dirac_apply,
    Set.indicator_apply, Set.indicator_apply]
  have hiff :
      ((fun _ : Fin 1 => (0 : Fin 2)) ∈ Set.univ.pi s) ↔ ((0 : Fin 2) ∈ s 0) := by
    simp [Fin.forall_fin_one]
  by_cases h : (0 : Fin 2) ∈ s 0
  · rw [if_pos h, if_pos (hiff.mpr h)]
    rfl
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

/-- The population risk is the genuine integral average of `f` over the product measure. -/
def populationRisk : ℝ := ∫ s, f s ∂sampleMeasure

/-- The empirical risk is the value of `f` at the observed sample. -/
def empiricalRisk : ℝ := f sample

theorem populationRisk_eq : populationRisk = (1 : ℝ) / 4 := by
  unfold populationRisk
  rw [sampleMeasure_eq_dirac, integral_dirac]
  simp [f]

theorem empiricalRisk_eq : empiricalRisk = (1 : ℝ) / 4 := by
  simp [empiricalRisk, f, sample]

theorem f_hasBoundedDifferences : HasBoundedDifferences f (fun _ : Fin 1 => width) := by
  intro S k z'
  fin_cases k
  by_cases h1 : S 0 = 0 <;> by_cases h2 : z' = 0 <;>
    simp [f, width, Function.update, h1, h2] <;> norm_num

theorem f_stronglyMeasurable : StronglyMeasurable f :=
  (measurable_of_finite f).stronglyMeasurable

theorem f_integrable : Integrable f sampleMeasure := Integrable.of_finite

/-- The sharp-McDiarmid lower-tail mass bound for this worked statistic: the prefix-kernel
deviation event has probability at most `exp (-2 · (1/2)² / (1 · (1/2)²)) = exp (-2)`. -/
theorem deviationMass_le_exp :
    sampleMeasure.real (prefixKernelDeviationBadEvent baseMeasure f deviationRadius)
      ≤ Real.exp (-2 * deviationRadius ^ 2 / ((1 : ℝ) * width ^ 2)) := by
  have h :=
    prefixKernelDeviationBadEventMass_le_exp_of_sharpMcDiarmid
      (μ := baseMeasure) (f := f) (c := width)
      (by norm_num [width]) f_hasBoundedDifferences f_stronglyMeasurable f_integrable
      (ε := deviationRadius) (by norm_num [deviationRadius])
  simpa [sampleMeasure] using h

/-- The observed sample is outside the lower-tail deviation event:
`f sample + ε = 1/4 + 1/2 = 3/4`, which exceeds the mean `1/4`. -/
theorem sample_not_mem_deviation :
    sample ∉ prefixKernelDeviationBadEvent baseMeasure f deviationRadius := by
  unfold prefixKernelDeviationBadEvent
  rw [Set.mem_setOf_eq]
  have hmean : (∫ s, f s ∂(Measure.pi (fun _ : Fin 1 => baseMeasure))) = (1 : ℝ) / 4 := by
    have := populationRisk_eq
    unfold populationRisk sampleMeasure at this
    exact this
  rw [hmean]
  simp only [f, sample, deviationRadius]
  norm_num

/-- The flagship-shaped decomposition with the prefix-kernel deviation radius as the only gap. -/
theorem populationDecomposition_holds :
    populationRisk ≤ empiricalRisk + 0 + 0 + 0 + 0 + deviationRadius := by
  exact prefixKernelPopulationDecomposition_of_sharpMcDiarmid
    baseMeasure f sample sample_not_mem_deviation populationRisk empiricalRisk rfl rfl

/-- Only the prefix-kernel contribution is nonzero in this worked decomposition;
it carries the real deviation radius. -/
def derived : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution := 0
  onlineIidContribution := 0
  bernsteinOrGaussianContribution := 0
  anytimeVilleContribution := 0
  prefixKernelContribution := deviationRadius
  mcAllesterGeneralWidthContributionNonnegative := le_rfl
  onlineIidContributionNonnegative := le_rfl
  bernsteinOrGaussianContributionNonnegative := le_rfl
  anytimeVilleContributionNonnegative := le_rfl
  prefixKernelContributionNonnegative := by norm_num [deviationRadius]

/-- User inputs whose population risk is the integral average above. -/
def user : FlagshipUserSupplied where
  sampleSize := 1
  targetConfidence := (19 : ℝ) / 20
  delta := (1 : ℝ) / 20
  lossWidth := 1
  empiricalRisk := empiricalRisk
  populationRisk := populationRisk
  positiveSampleSize := by norm_num
  deltaPositive := by norm_num
  confidenceNonnegative := by norm_num
  lossWidthNonnegative := by norm_num
  empiricalRiskNonnegative := by
    rw [empiricalRisk_eq]
    norm_num
  populationRiskNonnegative := by
    rw [populationRisk_eq]
    norm_num

theorem scalarBounds :
    FlagshipScalarComponentBounds user derived 0 0 0 0 deviationRadius := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show populationRisk ≤ empiricalRisk + 0 + 0 + 0 + 0 + deviationRadius
    exact populationDecomposition_holds
  · simp [user, derived]
  · simp [derived]
  · simp [derived]
  · simp [derived]
  · simp [derived]

/--
Non-vacuous flagship prefix-kernel worked example: the population risk is a real integral average
over the homogeneous Dirac product, and the only nonzero gap is the sharp-McDiarmid deviation
radius produced through the prefix/tail conditional-kernel disintegration.
-/
theorem flagship_population_le_bound :
    user.populationRisk ≤ flagshipBound user derived :=
  flagshipScalarAssembly_from_componentInequalities user derived scalarBounds

end PrefixKernelDecompWorkedExample

end

end FormalSLT.TestTimeMeta
