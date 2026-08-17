/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.TimeUniformContinuousPACBayes
import FormalSLT.PACBayes.FiniteJointMeanVarianceReverse

/-!
# Continuous-posterior reverse mean--variance PAC-Bayes

This module replaces the finite hypothesis sum in the reverse-epoch joint
mean/Bessel-variance process by an integral over an arbitrary measurable
hypothesis space.  It proves the prior integral is a submartingale from the
checked per-hypothesis reverse processes and explicit Fubini obligations.  It
then combines Doob's maximal inequality with the fixed-hypothesis endpoint MGF
and continuous Donsker--Varadhan change of measure.

The observation space and reverse horizon remain finite.  The product
integrability hypotheses are analytic measurability obligations; no prior MGF
or concentration bound is assumed.
-/

namespace FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse

open Finset BigOperators MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
open FormalSLT.PACBayes.FiniteJointMeanVarianceReverse
open FormalSLT.PACBayes.TimeUniformContinuous

noncomputable section

variable {Θ Z : Type*} [MeasurableSpace Θ] [MeasurableSpace Z]

/-- Prior integral of the reverse joint mean--variance exponential process. -/
def continuousReverseJointMeanVarianceEpochPriorMixture [Fintype Z]
    (prior : Measure Θ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ) (t eta : ℝ) :
    ℕ → (Fin N → Z) → ℝ :=
  continuousPriorMixtureProcess prior
    (fun θ ↦ reverseJointMeanVarianceEpochExponentialProcess
      N hN m p ell t eta θ)

omit [MeasurableSpace Z] in
theorem continuousReverseJointMeanVarianceEpochPriorMixture_nonneg
    [Fintype Z] (prior : Measure Θ)
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ) (t eta : ℝ) :
    0 ≤ continuousReverseJointMeanVarianceEpochPriorMixture
      prior N hN m p ell t eta := by
  intro k x
  exact integral_nonneg fun θ ↦
    reverseJointMeanVarianceEpochExponentialProcess_nonneg
      N hN m p ell t eta θ k x

/--
The continuous prior integral is a reverse-time submartingale.

The per-hypothesis submartingale is discharged by the checked reverse
mean/Bessel construction.  The remaining assumptions are exactly the joint
and restricted-product integrability and adaptedness obligations needed to
pass the conditional-expectation inequality through the prior integral.
-/
theorem continuousReverseJointMeanVarianceEpochPriorMixture_submartingale
    [Fintype Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ) (t eta : ℝ)
    (h_adapted_mix :
      StronglyAdapted (reverseBesselFiltration (Z := Z) N)
        (continuousReverseJointMeanVarianceEpochPriorMixture
          prior N hN m p ell t eta))
    (h_integrable_mix : ∀ k,
      Integrable
        (continuousReverseJointMeanVarianceEpochPriorMixture
          prior N hN m p ell t eta k)
        (Measure.pi (fun _ : Fin N ↦ mu)))
    (hM_int_next : ∀ k,
      Integrable
        (fun q : Θ × (Fin N → Z) ↦
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta q.1 (k + 1) q.2)
        (prior.prod (Measure.pi (fun _ : Fin N ↦ mu))))
    (hM_int_next_restrict : ∀ k, ∀ {s : Set (Fin N → Z)},
      MeasurableSet s →
      Measure.pi (fun _ : Fin N ↦ mu) s < ⊤ →
        Integrable
          (fun q : (Fin N → Z) × Θ ↦
            reverseJointMeanVarianceEpochExponentialProcess
              N hN m p ell t eta q.2 (k + 1) q.1)
          (((Measure.pi (fun _ : Fin N ↦ mu)).restrict s).prod prior))
    (hM_int_current : ∀ k,
      Integrable
        (fun q : (Fin N → Z) × Θ ↦
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta q.2 k q.1)
        ((Measure.pi (fun _ : Fin N ↦ mu)).prod prior))
    (hM_int_current_restrict : ∀ k, ∀ {s : Set (Fin N → Z)},
      MeasurableSet s →
      Measure.pi (fun _ : Fin N ↦ mu) s < ⊤ →
        Integrable
          (fun q : (Fin N → Z) × Θ ↦
            reverseJointMeanVarianceEpochExponentialProcess
              N hN m p ell t eta q.2 k q.1)
          (((Measure.pi (fun _ : Fin N ↦ mu)).restrict s).prod prior)) :
    Submartingale
      (continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  let μN : Measure (Fin N → Z) := Measure.pi (fun _ : Fin N ↦ mu)
  let M : Θ → ℕ → (Fin N → Z) → ℝ := fun θ ↦
    reverseJointMeanVarianceEpochExponentialProcess
      N hN m p ell t eta θ
  have hfixed : ∀ᵐ θ ∂prior,
      Submartingale (M θ) (reverseBesselFiltration (Z := Z) N) μN := by
    exact Filter.Eventually.of_forall fun θ ↦
      reverseJointMeanVarianceEpochExponentialProcess_submartingale
        mu N hN m p ell t eta θ
  change Submartingale (continuousPriorMixtureProcess prior M)
    (reverseBesselFiltration (Z := Z) N) μN
  exact continuousPriorMixture_submartingale
    h_adapted_mix h_integrable_mix hM_int_next hM_int_next_restrict
    hM_int_current hM_int_current_restrict hfixed

/-- A real-valued function on a product with finite discrete right factor is
strongly measurable when all left sections are strongly measurable. -/
theorem stronglyMeasurable_uncurry_of_finite_right
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype β] [MeasurableSingletonClass β]
    (f : α → β → ℝ)
    (hf : ∀ b, StronglyMeasurable (fun a ↦ f a b)) :
    StronglyMeasurable (fun q : α × β ↦ f q.1 q.2) := by
  classical
  have heq : (fun q : α × β ↦ f q.1 q.2) =
      ∑ b : β, fun q ↦ if q.2 = b then f q.1 b else 0 := by
    funext q
    simp
  rw [heq]
  exact Finset.stronglyMeasurable_sum Finset.univ fun b _ ↦
    StronglyMeasurable.ite
      (measurable_snd (measurableSet_singleton b))
      ((hf b).comp_measurable measurable_fst) stronglyMeasurable_const

omit [MeasurableSpace Z] in
/-- Population risk is measurable in a continuous hypothesis parameter when
every loss coordinate is measurable. -/
theorem stronglyMeasurable_finitePopulationRisk_parameter
    [Fintype Z] (p : Z → ℝ) (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z)) :
    StronglyMeasurable (fun θ ↦ finitePopulationRisk p ell θ) := by
  unfold finitePopulationRisk
  have hsum := Finset.stronglyMeasurable_sum Finset.univ fun z _ ↦
    (hell_meas z).const_mul (p z)
  have heq : (fun θ ↦ ∑ z : Z, p z * ell θ z) =
      ∑ z : Z, fun θ ↦ p z * ell θ z := by
    funext θ
    simp
  rw [heq]
  exact hsum

omit [MeasurableSpace Z] in
/-- Finite-sample empirical risk is measurable in a continuous hypothesis
parameter when every loss coordinate is measurable. -/
theorem stronglyMeasurable_finiteEmpiricalRisk_parameter
    [Fintype Z] {n : ℕ} (ell : Θ → Z → ℝ) (S : Fin n → Z)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z)) :
    StronglyMeasurable (fun θ ↦ finiteEmpiricalRisk ell θ S) := by
  unfold finiteEmpiricalRisk
  have hsum := Finset.stronglyMeasurable_sum Finset.univ fun k _ ↦
    hell_meas (S k)
  have heq : (fun θ ↦ (n : ℝ)⁻¹ * ∑ k : Fin n, ell θ (S k)) =
      fun θ ↦ (n : ℝ)⁻¹ * (∑ k : Fin n, fun θ ↦ ell θ (S k)) θ := by
    funext θ
    simp
  rw [heq]
  exact hsum.const_mul (n : ℝ)⁻¹

omit [MeasurableSpace Z] in
/-- Bessel empirical variance is measurable in a continuous hypothesis
parameter when every loss coordinate is measurable. -/
theorem stronglyMeasurable_finiteEmpiricalVariance_parameter
    [Fintype Z] {n : ℕ} (ell : Θ → Z → ℝ) (S : Fin n → Z)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z)) :
    StronglyMeasurable (fun θ ↦ finiteEmpiricalVariance ell θ S) := by
  have hsampleMean : StronglyMeasurable
      (fun θ ↦ FormalSLT.Statistics.sampleMean (fun k ↦ ell θ (S k))) := by
    unfold FormalSLT.Statistics.sampleMean
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun k _ ↦
      hell_meas (S k)
    have heq :
        (fun θ ↦ (∑ k : Fin n, ell θ (S k)) / (n : ℝ)) =
          fun θ ↦ (∑ k : Fin n, fun θ ↦ ell θ (S k)) θ * (n : ℝ)⁻¹ := by
      funext θ
      simp [div_eq_mul_inv]
    rw [heq]
    exact hsum.mul_const (n : ℝ)⁻¹
  unfold finiteEmpiricalVariance
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
  have hsum := Finset.stronglyMeasurable_sum Finset.univ fun k _ ↦
    ((hell_meas (S k)).sub hsampleMean).pow 2
  have heq :
      (fun θ ↦
        (∑ k : Fin n,
          (ell θ (S k) - FormalSLT.Statistics.sampleMean
            (fun j ↦ ell θ (S j))) ^ 2) / ((n : ℝ) - 1)) =
      fun θ ↦
        (∑ k : Fin n, fun θ ↦
          (ell θ (S k) - FormalSLT.Statistics.sampleMean
            (fun j ↦ ell θ (S j))) ^ 2) θ * ((n : ℝ) - 1)⁻¹ := by
    funext θ
    simp [div_eq_mul_inv]
  rw [heq]
  exact hsum.mul_const (((n : ℝ) - 1)⁻¹)

/-- Integrating a family of prefix-permutation-invariant functions preserves
measurability for the prefix-exchangeable sigma algebra.  Finiteness of the
path space supplies ambient measurability; no measurability in the parameter
is needed for this invariance argument. -/
theorem measurable_prefixExchangeable_integral_of_invariant
    [Fintype Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) {N u : ℕ}
    (f : Θ → (Fin N → Z) → ℝ)
    (hf : ∀ θ x (σ : Equiv.Perm (Fin N)),
      (∀ j : Fin N, u ≤ j.1 → σ j = j) →
        f θ (samplePermutation σ x) = f θ x) :
    Measurable[prefixExchangeableSpace (Z := Z) N u]
      (fun x ↦ ∫ θ, f θ x ∂prior) := by
  intro s hs
  rw [measurableSet_prefixExchangeableSpace_iff]
  refine ⟨(measurable_of_finite (fun x ↦ ∫ θ, f θ x ∂prior)) hs, fun σ ↦ ?_⟩
  ext x
  simp only [Set.mem_preimage]
  have hint : (∫ θ, f θ (samplePermutation (σ : Equiv.Perm (Fin N)) x) ∂prior) =
      ∫ θ, f θ x ∂prior := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ ↦
      hf θ x (σ : Equiv.Perm (Fin N)) σ.property
  rw [hint]

/-- The continuous prior mixture is adapted to the coarse reverse
exchangeable filtration.  The proof uses pointwise permutation invariance of
the checked reverse score before integrating over the hypothesis parameter. -/
theorem continuousReverseJointMeanVarianceEpochPriorMixture_stronglyAdapted
    [Fintype Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ) (t eta : ℝ) :
    StronglyAdapted (reverseBesselFiltration (Z := Z) N)
      (continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta) := by
  intro k
  change StronglyMeasurable[
    prefixExchangeableSpace (Z := Z) N (reverseBesselPrefixSize N k)]
    (fun x ↦ ∫ θ,
      reverseJointMeanVarianceEpochExponentialProcess
        N hN m p ell t eta θ k x ∂prior)
  exact (measurable_prefixExchangeable_integral_of_invariant
    prior
    (fun θ x ↦ reverseJointMeanVarianceEpochExponentialProcess
      N hN m p ell t eta θ k x)
    (fun θ x σ hσ ↦
      reverseJointMeanVarianceEpochExponentialProcess_samplePermutation
        N hN m p ell t eta θ k x σ hσ)).stronglyMeasurable

/-- The continuous reverse prior mixture is a submartingale once only the
Fubini integrability obligations are supplied; adaptedness is derived from
prefix-permutation invariance. -/
theorem continuousReverseJointMeanVarianceEpochPriorMixture_submartingale_of_integrable
    [Fintype Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ) (t eta : ℝ)
    (h_integrable_mix : ∀ k,
      Integrable
        (continuousReverseJointMeanVarianceEpochPriorMixture
          prior N hN m p ell t eta k)
        (Measure.pi (fun _ : Fin N ↦ mu)))
    (hM_int_next : ∀ k,
      Integrable
        (fun q : Θ × (Fin N → Z) ↦
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta q.1 (k + 1) q.2)
        (prior.prod (Measure.pi (fun _ : Fin N ↦ mu))))
    (hM_int_next_restrict : ∀ k, ∀ {s : Set (Fin N → Z)},
      MeasurableSet s →
      Measure.pi (fun _ : Fin N ↦ mu) s < ⊤ →
        Integrable
          (fun q : (Fin N → Z) × Θ ↦
            reverseJointMeanVarianceEpochExponentialProcess
              N hN m p ell t eta q.2 (k + 1) q.1)
          (((Measure.pi (fun _ : Fin N ↦ mu)).restrict s).prod prior))
    (hM_int_current : ∀ k,
      Integrable
        (fun q : (Fin N → Z) × Θ ↦
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta q.2 k q.1)
        ((Measure.pi (fun _ : Fin N ↦ mu)).prod prior))
    (hM_int_current_restrict : ∀ k, ∀ {s : Set (Fin N → Z)},
      MeasurableSet s →
      Measure.pi (fun _ : Fin N ↦ mu) s < ⊤ →
        Integrable
          (fun q : (Fin N → Z) × Θ ↦
            reverseJointMeanVarianceEpochExponentialProcess
              N hN m p ell t eta q.2 k q.1)
          (((Measure.pi (fun _ : Fin N ↦ mu)).restrict s).prod prior)) :
    Submartingale
      (continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  exact continuousReverseJointMeanVarianceEpochPriorMixture_submartingale
    prior mu N hN m p ell t eta
    (continuousReverseJointMeanVarianceEpochPriorMixture_stronglyAdapted
      prior N hN m p ell t eta)
    h_integrable_mix hM_int_next hM_int_next_restrict
    hM_int_current hM_int_current_restrict

omit [MeasurableSpace Z] in
/-- The fixed-sample joint score is measurable in an arbitrary hypothesis
parameter whenever every loss coordinate is measurable in that parameter. -/
theorem stronglyMeasurable_finiteJointMeanVarianceScore_parameter
    [Fintype Z] {n : ℕ}
    (p : Z → ℝ) (ell : Θ → Z → ℝ) (t eta : ℝ)
    (S : Fin n → Z)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z)) :
    StronglyMeasurable
      (fun θ ↦ finiteJointMeanVarianceScore n p ell t eta θ S) := by
  have hrisk : StronglyMeasurable
      (fun θ ↦ finitePopulationRisk p ell θ) := by
    unfold finitePopulationRisk
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun z _ ↦
      (hell_meas z).const_mul (p z)
    have heq : (fun θ ↦ ∑ z : Z, p z * ell θ z) =
        ∑ z : Z, fun θ ↦ p z * ell θ z := by
      funext θ
      simp
    rw [heq]
    exact hsum
  have hempiricalRisk : StronglyMeasurable
      (fun θ ↦ finiteEmpiricalRisk ell θ S) := by
    unfold finiteEmpiricalRisk
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun k _ ↦
      hell_meas (S k)
    have heq : (fun θ ↦ (n : ℝ)⁻¹ * ∑ k : Fin n, ell θ (S k)) =
        fun θ ↦ (n : ℝ)⁻¹ * (∑ k : Fin n, fun θ ↦ ell θ (S k)) θ := by
      funext θ
      simp
    rw [heq]
    exact hsum.const_mul (n : ℝ)⁻¹
  have hpopulationVariance : StronglyMeasurable
      (fun θ ↦ finitePopulationVariance p ell θ) := by
    unfold finitePopulationVariance
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun z _ ↦
      (((hell_meas z).sub hrisk).pow 2).const_mul (p z)
    have heq :
        (fun θ ↦ ∑ z : Z, p z * (ell θ z - finitePopulationRisk p ell θ) ^ 2) =
          ∑ z : Z, fun θ ↦ p z * (ell θ z - finitePopulationRisk p ell θ) ^ 2 := by
      funext θ
      simp
    rw [heq]
    exact hsum
  have hsampleMean : StronglyMeasurable
      (fun θ ↦ FormalSLT.Statistics.sampleMean (fun k ↦ ell θ (S k))) := by
    unfold FormalSLT.Statistics.sampleMean
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun k _ ↦
      hell_meas (S k)
    have heq :
        (fun θ ↦ (∑ k : Fin n, ell θ (S k)) / (n : ℝ)) =
          fun θ ↦ (∑ k : Fin n, fun θ ↦ ell θ (S k)) θ * (n : ℝ)⁻¹ := by
      funext θ
      simp [div_eq_mul_inv]
    rw [heq]
    exact hsum.mul_const (n : ℝ)⁻¹
  have hempiricalVariance : StronglyMeasurable
      (fun θ ↦ finiteEmpiricalVariance ell θ S) := by
    unfold finiteEmpiricalVariance
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun k _ ↦
      ((hell_meas (S k)).sub hsampleMean).pow 2
    have heq :
        (fun θ ↦
          (∑ k : Fin n,
            (ell θ (S k) - FormalSLT.Statistics.sampleMean
              (fun j ↦ ell θ (S j))) ^ 2) / ((n : ℝ) - 1)) =
        fun θ ↦
          (∑ k : Fin n, fun θ ↦
            (ell θ (S k) - FormalSLT.Statistics.sampleMean
              (fun j ↦ ell θ (S j))) ^ 2) θ * ((n : ℝ) - 1)⁻¹ := by
      funext θ
      simp [div_eq_mul_inv]
    rw [heq]
    exact hsum.mul_const (((n : ℝ) - 1)⁻¹)
  have hlogArg : StronglyMeasurable
      (fun θ ↦ 1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) :=
    stronglyMeasurable_const.add
      (hpopulationVariance.const_mul (Real.exp t - 1 - t))
  have hlog : StronglyMeasurable
      (fun θ ↦ Real.log
        (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ)) :=
    (Real.measurable_log.comp hlogArg.measurable).stronglyMeasurable
  unfold finiteJointMeanVarianceScore
  exact (((hrisk.sub hempiricalRisk).const_mul (t * (n : ℝ))).sub
      (hempiricalVariance.const_mul (eta * (n : ℝ)))).sub
        (hlog.const_mul (n : ℝ)) |>.add
          (hpopulationVariance.const_mul
            (Real.exp (-t) * finiteJointMeanVarianceKappa n eta))

omit [MeasurableSpace Z] in
/-- At every reverse time, the joint mean--Bessel score is strongly
measurable in an arbitrary hypothesis parameter when each loss coordinate is
strongly measurable in that parameter. -/
theorem stronglyMeasurable_reverseJointMeanVarianceEpochScore_parameter
    [Fintype Z]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ) (t eta : ℝ)
    (k : ℕ) (x : Fin N → Z)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z)) :
    StronglyMeasurable
      (fun θ ↦ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x) := by
  have hrisk : StronglyMeasurable
      (fun θ ↦ finitePopulationRisk p ell θ) := by
    unfold finitePopulationRisk
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun z _ ↦
      (hell_meas z).const_mul (p z)
    have heq : (fun θ ↦ ∑ z : Z, p z * ell θ z) =
        ∑ z : Z, fun θ ↦ p z * ell θ z := by
      funext θ
      simp
    rw [heq]
    exact hsum
  have hpopulationVariance : StronglyMeasurable
      (fun θ ↦ finitePopulationVariance p ell θ) := by
    unfold finitePopulationVariance
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun z _ ↦
      (((hell_meas z).sub hrisk).pow 2).const_mul (p z)
    have heq :
        (fun θ ↦ ∑ z : Z,
          p z * (ell θ z - finitePopulationRisk p ell θ) ^ 2) =
        ∑ z : Z, fun θ ↦
          p z * (ell θ z - finitePopulationRisk p ell θ) ^ 2 := by
      funext θ
      simp
    rw [heq]
    exact hsum
  have hmean : StronglyMeasurable
      (fun θ ↦ reverseMeanProcess N hN (ell θ) k x) := by
    unfold reverseMeanProcess prefixSampleMean FormalSLT.Statistics.sampleMean
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun j _ ↦
      hell_meas (samplePrefix (reverseBesselPrefixSize_le hN k) x j)
    have heq :
        (fun θ ↦
          (∑ j : Fin (reverseBesselPrefixSize N k),
            ell θ (samplePrefix (reverseBesselPrefixSize_le hN k) x j)) /
              (reverseBesselPrefixSize N k : ℝ)) =
        fun θ ↦
          (∑ j : Fin (reverseBesselPrefixSize N k), fun θ ↦
            ell θ (samplePrefix (reverseBesselPrefixSize_le hN k) x j)) θ *
              (reverseBesselPrefixSize N k : ℝ)⁻¹ := by
      funext θ
      simp [div_eq_mul_inv]
    rw [heq]
    exact hsum.mul_const (reverseBesselPrefixSize N k : ℝ)⁻¹
  have hvariance : StronglyMeasurable
      (fun θ ↦ reverseBesselProcess N hN (ell θ) k x) := by
    unfold reverseBesselProcess prefixBesselVariance
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
    have hsampleMean : StronglyMeasurable
        (fun θ ↦ FormalSLT.Statistics.sampleMean
          (fun j : Fin (reverseBesselPrefixSize N k) ↦
            ell θ (samplePrefix (reverseBesselPrefixSize_le hN k) x j))) := by
      simpa [reverseMeanProcess, prefixSampleMean] using hmean
    have hsum := Finset.stronglyMeasurable_sum Finset.univ fun j _ ↦
      ((hell_meas
        (samplePrefix (reverseBesselPrefixSize_le hN k) x j)).sub
          hsampleMean).pow 2
    have heq :
        (fun θ ↦
          (∑ j : Fin (reverseBesselPrefixSize N k),
            (ell θ (samplePrefix (reverseBesselPrefixSize_le hN k) x j) -
              FormalSLT.Statistics.sampleMean
                (fun r : Fin (reverseBesselPrefixSize N k) ↦
                  ell θ
                    (samplePrefix (reverseBesselPrefixSize_le hN k) x r))) ^ 2) /
            ((reverseBesselPrefixSize N k : ℝ) - 1)) =
        fun θ ↦
          (∑ j : Fin (reverseBesselPrefixSize N k), fun θ ↦
            (ell θ (samplePrefix (reverseBesselPrefixSize_le hN k) x j) -
              FormalSLT.Statistics.sampleMean
                (fun r : Fin (reverseBesselPrefixSize N k) ↦
                  ell θ
                    (samplePrefix (reverseBesselPrefixSize_le hN k) x r))) ^ 2) θ *
            ((reverseBesselPrefixSize N k : ℝ) - 1)⁻¹ := by
      funext θ
      simp [div_eq_mul_inv]
    rw [heq]
    exact hsum.mul_const (((reverseBesselPrefixSize N k : ℝ) - 1)⁻¹)
  have hlogArg : StronglyMeasurable
      (fun θ ↦ 1 +
        (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) :=
    stronglyMeasurable_const.add
      (hpopulationVariance.const_mul (Real.exp t - 1 - t))
  have hlog : StronglyMeasurable
      (fun θ ↦ Real.log
        (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ)) :=
    (Real.measurable_log.comp hlogArg.measurable).stronglyMeasurable
  unfold reverseJointMeanVarianceEpochScore
  exact (((hrisk.sub hmean).const_mul (t * (m : ℝ))).sub
      (hvariance.const_mul (eta * (m : ℝ)))).sub
        (hlog.const_mul (m : ℝ)) |>.add
          (hpopulationVariance.const_mul
            (Real.exp (-t) * finiteJointMeanVarianceKappa m eta))

omit [MeasurableSpace Θ] [MeasurableSpace Z] in
/-- A bounded loss gives a reverse-time-uniform upper bound on the joint
score.  In particular, the bound does not grow with the horizon or reverse
time. -/
theorem reverseJointMeanVarianceEpochScore_le_of_bounded
    [Fintype Z]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ) (t eta : ℝ)
    (θ : Θ) (k : ℕ) (x : Fin N → Z)
    (hell : ∀ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta) :
    reverseJointMeanVarianceEpochScore N hN m p ell t eta θ k x ≤
      t * (m : ℝ) +
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4 := by
  have hR := finitePopulationRisk_mem_Icc_of_bounded p hp ell θ hell
  have hVnonneg := finitePopulationVariance_nonneg p hp ell θ
  have hVquarter := finitePopulationVariance_le_quarter p hp ell θ hell
  have hmean_nonneg : 0 ≤ reverseMeanProcess N hN (ell θ) k x := by
    unfold reverseMeanProcess prefixSampleMean FormalSLT.Statistics.sampleMean
    exact div_nonneg
      (Finset.sum_nonneg fun j _ ↦
        (hell (samplePrefix (reverseBesselPrefixSize_le hN k) x j)).1)
      (Nat.cast_nonneg _)
  have hvariance_nonneg :
      0 ≤ reverseBesselProcess N hN (ell θ) k x := by
    unfold reverseBesselProcess prefixBesselVariance
    exact FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel_nonneg
      (reverseBesselPrefixSize_two_le N k) _
  have hpsi : 0 ≤ Real.exp t - 1 - t := by
    linarith [Real.add_one_le_exp t]
  have hlog_nonneg :
      0 ≤ Real.log
        (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) := by
    exact Real.log_nonneg (by nlinarith [mul_nonneg hpsi hVnonneg])
  have hmeanTerm :
      t * (m : ℝ) *
          (finitePopulationRisk p ell θ -
            reverseMeanProcess N hN (ell θ) k x) ≤
        t * (m : ℝ) := by
    have hcoef : 0 ≤ t * (m : ℝ) :=
      mul_nonneg ht (Nat.cast_nonneg m)
    have hdiff :
        finitePopulationRisk p ell θ -
            reverseMeanProcess N hN (ell θ) k x ≤ 1 := by
      linarith [hR.2, hmean_nonneg]
    simpa using mul_le_mul_of_nonneg_left hdiff hcoef
  have hcorrection :
      Real.exp (-t) * finiteJointMeanVarianceKappa m eta *
          finitePopulationVariance p ell θ ≤
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4 := by
    have hcoef : 0 ≤ Real.exp (-t) * finiteJointMeanVarianceKappa m eta :=
      mul_nonneg (Real.exp_pos _).le hkappa
    nlinarith
  unfold reverseJointMeanVarianceEpochScore
  nlinarith [mul_nonneg (mul_nonneg heta (Nat.cast_nonneg m))
      hvariance_nonneg,
    mul_nonneg (Nat.cast_nonneg m) hlog_nonneg]

omit [MeasurableSpace Θ] [MeasurableSpace Z] in
/-- A two-sided, reverse-time-uniform bound for the continuous-hypothesis
joint score.  This supplies posterior score integrability without assuming it
as a PAC-Bayes interface. -/
theorem abs_reverseJointMeanVarianceEpochScore_le_of_bounded
    [Fintype Z]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ) (t eta : ℝ)
    (θ : Θ) (k : ℕ) (x : Fin N → Z)
    (hell : ∀ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta) :
    |reverseJointMeanVarianceEpochScore N hN m p ell t eta θ k x| ≤
      t * (m : ℝ) + eta * (m : ℝ) / 2 +
        (m : ℝ) * (Real.exp t - 1 - t) / 4 +
          Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4 := by
  have hR := finitePopulationRisk_mem_Icc_of_bounded p hp ell θ hell
  have hVnonneg := finitePopulationVariance_nonneg p hp ell θ
  have hVquarter := finitePopulationVariance_le_quarter p hp ell θ hell
  have hmean := reverseMeanProcess_mem_Icc_of_bounded
    N hN (ell θ) hell k x
  have hVhat_nonneg :
      0 ≤ reverseBesselProcess N hN (ell θ) k x := by
    unfold reverseBesselProcess prefixBesselVariance
    exact FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel_nonneg
      (reverseBesselPrefixSize_two_le N k) _
  have hVhat_half :
      reverseBesselProcess N hN (ell θ) k x ≤ (1 : ℝ) / 2 := by
    unfold reverseBesselProcess
    rw [prefixBesselVariance_eq_finiteEmpiricalVariance
      (reverseBesselPrefixSize_le hN k) ell θ x]
    exact finiteEmpiricalVariance_le_half
      (reverseBesselPrefixSize_two_le N k) ell θ
      (samplePrefix (reverseBesselPrefixSize_le hN k) x)
      (fun j ↦ hell (samplePrefix (reverseBesselPrefixSize_le hN k) x j))
  have hpsi : 0 ≤ Real.exp t - 1 - t := by
    linarith [Real.add_one_le_exp t]
  have hlog_nonneg :
      0 ≤ Real.log
        (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) := by
    exact Real.log_nonneg (by nlinarith [mul_nonneg hpsi hVnonneg])
  have hlog_upper :
      Real.log
          (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) ≤
        (Real.exp t - 1 - t) / 4 := by
    have harg_pos :
        0 < 1 +
          (Real.exp t - 1 - t) * finitePopulationVariance p ell θ := by
      nlinarith [mul_nonneg hpsi hVnonneg]
    have hlog_sub := Real.log_le_sub_one_of_pos harg_pos
    have hmul := mul_le_mul_of_nonneg_left hVquarter hpsi
    nlinarith
  have hcoef : 0 ≤ t * (m : ℝ) :=
    mul_nonneg ht (Nat.cast_nonneg m)
  have hgap_lower :
      -(1 : ℝ) ≤ finitePopulationRisk p ell θ -
        reverseMeanProcess N hN (ell θ) k x := by
    linarith [hR.1, hmean.2]
  have hmean_lower := mul_le_mul_of_nonneg_left hgap_lower hcoef
  have hmean_lower' :
      -(t * (m : ℝ)) ≤ t * (m : ℝ) *
        (finitePopulationRisk p ell θ -
          reverseMeanProcess N hN (ell θ) k x) := by
    nlinarith [hmean_lower]
  have hvariance_upper := mul_le_mul_of_nonneg_left hVhat_half
    (mul_nonneg heta (Nat.cast_nonneg m))
  have hvariance_upper' :
      eta * (m : ℝ) * reverseBesselProcess N hN (ell θ) k x ≤
        eta * (m : ℝ) / 2 := by
    nlinarith [hvariance_upper]
  have hlogTerm_upper := mul_le_mul_of_nonneg_left hlog_upper
    (Nat.cast_nonneg m)
  have hlogTerm_upper' :
      (m : ℝ) * Real.log
          (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) ≤
        (m : ℝ) * (Real.exp t - 1 - t) / 4 := by
    nlinarith [hlogTerm_upper]
  have hcorrection_nonneg :
      0 ≤ Real.exp (-t) * finiteJointMeanVarianceKappa m eta *
        finitePopulationVariance p ell θ :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hkappa) hVnonneg
  have hcorrection_bound_nonneg :
      0 ≤ Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4 := by
    positivity
  have hlower :
      -(t * (m : ℝ) + eta * (m : ℝ) / 2 +
          (m : ℝ) * (Real.exp t - 1 - t) / 4 +
            Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4) ≤
        reverseJointMeanVarianceEpochScore N hN m p ell t eta θ k x := by
    unfold reverseJointMeanVarianceEpochScore
    nlinarith
  have hupper := reverseJointMeanVarianceEpochScore_le_of_bounded
    N hN m p hp ell t eta θ k x hell ht heta hkappa
  rw [abs_le]
  constructor
  · exact hlower
  · have hvarianceTerm_nonneg :
        0 ≤ eta * (m : ℝ) / 2 := by positivity
    have hlogTerm_nonneg :
        0 ≤ (m : ℝ) * (Real.exp t - 1 - t) / 4 := by positivity
    nlinarith

omit [MeasurableSpace Z] in
/-- The reverse score is integrable under every probability posterior when
the loss is measurable and bounded. -/
theorem reverseJointMeanVarianceEpochScore_integrable_of_measurable_bounded
    [Fintype Z]
    (posterior : Measure Θ) [IsProbabilityMeasure posterior]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : ℝ) (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (k : ℕ) (x : Fin N → Z) :
    Integrable
      (fun θ ↦ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x) posterior := by
  refine Integrable.of_bound
    (stronglyMeasurable_reverseJointMeanVarianceEpochScore_parameter
      N hN m p ell t eta k x hell_meas).aestronglyMeasurable
    (t * (m : ℝ) + eta * (m : ℝ) / 2 +
      (m : ℝ) * (Real.exp t - 1 - t) / 4 +
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4) ?_
  exact Filter.Eventually.of_forall fun θ ↦ by
    simpa [Real.norm_eq_abs] using
      (abs_reverseJointMeanVarianceEpochScore_le_of_bounded
        N hN m p hp ell t eta θ k x (hell θ) ht heta hkappa)

omit [MeasurableSpace Z] in
/-- The exponential reverse score is integrable under every probability
prior when the loss is measurable and bounded. -/
theorem reverseJointMeanVarianceEpochExponential_integrable_of_measurable_bounded
    [Fintype Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : ℝ) (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (k : ℕ) (x : Fin N → Z) :
    Integrable
      (fun θ ↦ Real.exp (reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x)) prior := by
  have hscore := stronglyMeasurable_reverseJointMeanVarianceEpochScore_parameter
    N hN m p ell t eta k x hell_meas
  refine Integrable.of_bound
    (Real.continuous_exp.comp_stronglyMeasurable hscore).aestronglyMeasurable
    (Real.exp (t * (m : ℝ) +
      Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4)) ?_
  exact Filter.Eventually.of_forall fun θ ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr
      (reverseJointMeanVarianceEpochScore_le_of_bounded
        N hN m p hp ell t eta θ k x (hell θ) ht heta hkappa)

/-- Measurable bounded losses make the reverse exponential score integrable
over an arbitrary finite path law and probability prior, at every reverse
time. -/
theorem reverseJointMeanVarianceEpochExponentialProcess_integrable_prod
    [Fintype Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (nu : Measure (Fin N → Z)) [IsFiniteMeasure nu]
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : ℝ) (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (k : ℕ) :
    Integrable
      (fun q : Θ × (Fin N → Z) ↦
        reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta q.1 k q.2)
      (prior.prod nu) := by
  have hscore_joint : StronglyMeasurable
      (fun q : Θ × (Fin N → Z) ↦
        reverseJointMeanVarianceEpochScore
          N hN m p ell t eta q.1 k q.2) :=
    stronglyMeasurable_uncurry_of_finite_right
      (fun θ x ↦ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x)
      (fun x ↦ stronglyMeasurable_reverseJointMeanVarianceEpochScore_parameter
        N hN m p ell t eta k x hell_meas)
  have hexp_joint : StronglyMeasurable
      (fun q : Θ × (Fin N → Z) ↦
        reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta q.1 k q.2) := by
    unfold reverseJointMeanVarianceEpochExponentialProcess
    exact Real.continuous_exp.comp_stronglyMeasurable hscore_joint
  refine Integrable.of_bound hexp_joint.aestronglyMeasurable
    (Real.exp (t * (m : ℝ) +
      Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4)) ?_
  exact Filter.Eventually.of_forall fun q ↦ by
    unfold reverseJointMeanVarianceEpochExponentialProcess
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr
      (reverseJointMeanVarianceEpochScore_le_of_bounded
        N hN m p hp ell t eta q.1 k q.2 (hell q.1) ht heta hkappa)

/-- For measurable `[0,1]` losses, the continuous-prior reverse exponential
mixture is a genuine submartingale.  Both adaptedness and every Fubini
integrability obligation are derived rather than supplied as interfaces. -/
theorem continuousReverseJointMeanVarianceEpochPriorMixture_submartingale_of_measurable_bounded
    [Fintype Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (t eta : ℝ) (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta) :
    Submartingale
      (continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  let muN : Measure (Fin N → Z) := Measure.pi (fun _ : Fin N ↦ mu)
  haveI : IsProbabilityMeasure muN := by
    dsimp [muN]
    infer_instance
  have hprod (k : ℕ) : Integrable
      (fun q : Θ × (Fin N → Z) ↦
        reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta q.1 k q.2)
      (prior.prod muN) :=
    reverseJointMeanVarianceEpochExponentialProcess_integrable_prod
      prior N hN m muN p hp ell hell_meas hell t eta ht heta hkappa k
  have hmix (k : ℕ) : Integrable
      (continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta k) muN :=
    Integrable.of_finite
  have hcurrent (k : ℕ) : Integrable
      (fun q : (Fin N → Z) × Θ ↦
        reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta q.2 k q.1)
      (muN.prod prior) := by
    simpa [Function.comp_def] using (hprod k).swap
  have hrestrict (k : ℕ) {s : Set (Fin N → Z)} : Integrable
      (fun q : (Fin N → Z) × Θ ↦
        reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta q.2 k q.1)
      ((muN.restrict s).prod prior) :=
    (hcurrent k).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  change Submartingale
    (continuousReverseJointMeanVarianceEpochPriorMixture
      prior N hN m p ell t eta)
    (reverseBesselFiltration (Z := Z) N) muN
  exact continuousReverseJointMeanVarianceEpochPriorMixture_submartingale_of_integrable
    prior mu N hN m p ell t eta hmix
    (fun k ↦ hprod (k + 1))
    (fun k _s _hs _hfinite ↦ hrestrict (k + 1))
    hcurrent
    (fun k _s _hs _hfinite ↦ hrestrict k)

omit [MeasurableSpace Θ] [MeasurableSpace Z] in
/-- A bounded loss gives a uniform upper bound on the fixed-sample joint
score.  This bound is sufficient to integrate its exponential under any
probability prior. -/
theorem finiteJointMeanVarianceScore_le_of_bounded
    [Fintype Z] {n : ℕ} (hn : 2 ≤ n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ) (t eta : ℝ) (θ : Θ) (S : Fin n → Z)
    (hell : ∀ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa n eta) :
    finiteJointMeanVarianceScore n p ell t eta θ S ≤
      t * (n : ℝ) +
        Real.exp (-t) * finiteJointMeanVarianceKappa n eta / 4 := by
  have hR := finitePopulationRisk_mem_Icc_of_bounded p hp ell θ hell
  have hVnonneg := finitePopulationVariance_nonneg p hp ell θ
  have hVquarter := finitePopulationVariance_le_quarter p hp ell θ hell
  have hRhat_nonneg : 0 ≤ finiteEmpiricalRisk ell θ S := by
    unfold finiteEmpiricalRisk
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun k _ ↦ (hell (S k)).1)
  have hVhat_nonneg := finiteEmpiricalVariance_nonneg hn ell θ S
  have hpsi : 0 ≤ Real.exp t - 1 - t := by
    linarith [Real.add_one_le_exp t]
  have hlog_nonneg :
      0 ≤ Real.log
        (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) := by
    exact Real.log_nonneg (by nlinarith [mul_nonneg hpsi hVnonneg])
  have hmeanTerm :
      t * (n : ℝ) *
          (finitePopulationRisk p ell θ - finiteEmpiricalRisk ell θ S) ≤
        t * (n : ℝ) := by
    have hcoef : 0 ≤ t * (n : ℝ) := mul_nonneg ht (Nat.cast_nonneg n)
    have hdiff :
        finitePopulationRisk p ell θ - finiteEmpiricalRisk ell θ S ≤ 1 := by
      linarith [hR.2, hRhat_nonneg]
    simpa using mul_le_mul_of_nonneg_left hdiff hcoef
  have hcorrection :
      Real.exp (-t) * finiteJointMeanVarianceKappa n eta *
          finitePopulationVariance p ell θ ≤
        Real.exp (-t) * finiteJointMeanVarianceKappa n eta / 4 := by
    have hcoef : 0 ≤ Real.exp (-t) * finiteJointMeanVarianceKappa n eta :=
      mul_nonneg (Real.exp_pos _).le hkappa
    nlinarith
  unfold finiteJointMeanVarianceScore
  nlinarith [mul_nonneg (mul_nonneg heta (Nat.cast_nonneg n)) hVhat_nonneg,
    mul_nonneg (Nat.cast_nonneg n) hlog_nonneg]

/-- Joint measurability and `[0,1]` boundedness discharge the endpoint product
integrability needed to mix the checked fixed-hypothesis MGF over a continuous
prior. -/
theorem continuousReverseJointMeanVarianceEpoch_endpoint_integrable
    [Fintype Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {t eta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta) :
    Integrable
      (fun q : Θ × (Fin N → Z) ↦
        reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta q.1 (N - m) q.2)
      (prior.prod
        (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure))) := by
  let f : Θ → (Fin N → Z) → ℝ := fun θ x ↦
    finiteJointMeanVarianceScore m p ell t eta θ (samplePrefix hm.2 x)
  have hf_section (x : Fin N → Z) :
      StronglyMeasurable (fun θ ↦ f θ x) := by
    exact stronglyMeasurable_finiteJointMeanVarianceScore_parameter
      p ell t eta (samplePrefix hm.2 x) hell_meas
  have hf_joint : StronglyMeasurable
      (fun q : Θ × (Fin N → Z) ↦ f q.1 q.2) :=
    stronglyMeasurable_uncurry_of_finite_right f hf_section
  have hexp_joint : StronglyMeasurable
      (fun q : Θ × (Fin N → Z) ↦ Real.exp (f q.1 q.2)) :=
    Real.continuous_exp.comp_stronglyMeasurable hf_joint
  have hfixed : Integrable
      (fun q : Θ × (Fin N → Z) ↦ Real.exp (f q.1 q.2))
      (prior.prod
        (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure))) := by
    refine Integrable.of_bound hexp_joint.aestronglyMeasurable
      (Real.exp (t * (m : ℝ) +
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta / 4)) ?_
    exact Filter.Eventually.of_forall fun q ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr
        (finiteJointMeanVarianceScore_le_of_bounded hm.1 p hp ell t eta
          q.1 (samplePrefix hm.2 q.2) (hell q.1) ht heta hkappa)
  have heq :
      (fun q : Θ × (Fin N → Z) ↦
        reverseJointMeanVarianceEpochExponentialProcess
          N hN m p ell t eta q.1 (N - m) q.2) =
      fun q ↦ Real.exp (f q.1 q.2) := by
    funext q
    unfold reverseJointMeanVarianceEpochExponentialProcess f
    rw [reverseJointMeanVarianceEpochScore_endpoint hN hm]
  rw [heq]
  exact hfixed

/-- The endpoint expectation of the continuous prior mixture is at most one. -/
theorem continuousReverseJointMeanVarianceEpochPriorMixture_endpoint_integral_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {t eta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hM_endpoint :
      Integrable
        (fun q : Θ × (Fin N → Z) ↦
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta q.1 (N - m) q.2)
        (prior.prod
          (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)))) :
    (∫ x, continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta (N - m) x
      ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 := by
  let μN : Measure (Fin N → Z) :=
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
  let M : Θ → (Fin N → Z) → ℝ := fun θ x ↦
    reverseJointMeanVarianceEpochExponentialProcess
      N hN m p ell t eta θ (N - m) x
  have hcomponent (θ : Θ) : (∫ x, M θ x ∂μN) ≤ 1 := by
    exact reverseJointMeanVarianceEpoch_endpoint_integral_le_one
      hN hm p hp ell θ (hell θ) ht heta hkappa
  calc
    (∫ x, continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta (N - m) x ∂μN) =
        ∫ θ, ∫ x, M θ x ∂μN ∂prior := by
          simpa [continuousReverseJointMeanVarianceEpochPriorMixture,
            continuousPriorMixtureProcess, M] using
            (integral_integral_swap (μ := prior) (ν := μN)
              (f := M) hM_endpoint).symm
    _ ≤ ∫ _θ : Θ, (1 : ℝ) ∂prior := by
      exact integral_mono hM_endpoint.integral_prod_left
        (integrable_const 1) hcomponent
    _ = 1 := by simp

/-- Prior-mixture crossing event for one continuous-hypothesis reverse epoch. -/
def continuousReverseJointMeanVarianceEpochBadPaths [Fintype Z]
    (prior : Measure Θ) (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : Θ → Z → ℝ)
    (t eta delta : ℝ) : Set (Fin N → Z) :=
  {x | delta⁻¹ ≤
    (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta k x)}

/-- Doob's maximal inequality and the checked endpoint MGF control the
continuous prior-mixture crossing event. -/
theorem continuousReverseJointMeanVarianceEpochPriorMixture_maximal_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {t eta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hsub : Submartingale
      (continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)))
    (hM_endpoint :
      Integrable
        (fun q : Θ × (Fin N → Z) ↦
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta q.1 (N - m) q.2)
        (prior.prod
          (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure))))
    (epsilon : ℝ≥0) :
    epsilon * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | (epsilon : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ continuousReverseJointMeanVarianceEpochPriorMixture
              prior N hN m p ell t eta k x)} ≤ 1 := by
  let μN := Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
  let M := continuousReverseJointMeanVarianceEpochPriorMixture
    prior N hN m p ell t eta
  have hnonneg : 0 ≤ M :=
    continuousReverseJointMeanVarianceEpochPriorMixture_nonneg
      prior N hN m p ell t eta
  have hdoob := MeasureTheory.maximal_ineq hsub hnonneg
    (ε := epsilon) (N - m)
  have hsetIntegral :
      ∫ x in {x | (epsilon : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ M k x)}, M (N - m) x ∂μN ≤
        ∫ x, M (N - m) x ∂μN :=
    setIntegral_le_integral (hsub.integrable (N - m))
      (Filter.Eventually.of_forall (fun x ↦ hnonneg (N - m) x))
  have hend : (∫ x, M (N - m) x ∂μN) ≤ 1 :=
    continuousReverseJointMeanVarianceEpochPriorMixture_endpoint_integral_le_one
      prior N m hN hm p hp ell hell ht heta hkappa hM_endpoint
  calc
    epsilon * μN {x | (epsilon : ℝ) ≤
        (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ M k x)} ≤
      ENNReal.ofReal
        (∫ x in {x | (epsilon : ℝ) ≤
            (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
              (fun k ↦ M k x)}, M (N - m) x ∂μN) := hdoob
    _ ≤ ENNReal.ofReal (∫ x, M (N - m) x ∂μN) :=
      ENNReal.ofReal_le_ofReal hsetIntegral
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hend
    _ = 1 := by norm_num

/-- The continuous-prior reverse-epoch crossing event has mass at most
`delta`.  Its endpoint moment bound is derived by Fubini from the checked
fixed-hypothesis MGF. -/
theorem continuousReverseJointMeanVarianceEpochBadPaths_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {t eta delta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hdelta : 0 < delta)
    (hsub : Submartingale
      (continuousReverseJointMeanVarianceEpochPriorMixture
        prior N hN m p ell t eta)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)))
    (hM_endpoint :
      Integrable
        (fun q : Θ × (Fin N → Z) ↦
          reverseJointMeanVarianceEpochExponentialProcess
            N hN m p ell t eta q.1 (N - m) q.2)
        (prior.prod
          (Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)))) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousReverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell t eta delta) ≤ ENNReal.ofReal delta := by
  let epsilon : ℝ≥0 := ⟨delta⁻¹, inv_nonneg.mpr hdelta.le⟩
  let d : ℝ≥0∞ := ENNReal.ofReal delta
  have hscaled :=
    continuousReverseJointMeanVarianceEpochPriorMixture_maximal_le_one
      prior N m hN hm p hp ell hell ht heta hkappa hsub hM_endpoint epsilon
  have hepsilonReal : (epsilon : ℝ) = delta⁻¹ := rfl
  have hepsilon : (epsilon : ℝ≥0∞) = d⁻¹ := by
    calc
      (epsilon : ℝ≥0∞) = ENNReal.ofReal delta⁻¹ := by
        symm
        exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hdelta.le)
      _ = d⁻¹ := by rw [ENNReal.ofReal_inv_of_pos hdelta]
  have hscaled' : d⁻¹ *
      Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousReverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell t eta delta) ≤ 1 := by
    rw [hepsilon] at hscaled
    rw [hepsilonReal] at hscaled
    simpa [continuousReverseJointMeanVarianceEpochBadPaths] using hscaled
  have hd0 : d ≠ 0 := by
    simpa [d] using ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hdtop : d ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousReverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell t eta delta) =
      d * (d⁻¹ * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousReverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell t eta delta)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, one_mul]
    _ ≤ d * 1 := mul_le_mul_right hscaled' d
    _ = ENNReal.ofReal delta := by simp [d]

/-- Measurable bounded losses alone discharge both the reverse
submartingale and endpoint Fubini obligations in the continuous-prior epoch
crossing bound. -/
theorem continuousReverseJointMeanVarianceEpochBadPaths_mass_le_delta_of_measurable_bounded
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {t eta delta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        (continuousReverseJointMeanVarianceEpochBadPaths
          prior N hN m p ell t eta delta) ≤ ENNReal.ofReal delta := by
  have hsub :=
    continuousReverseJointMeanVarianceEpochPriorMixture_submartingale_of_measurable_bounded
      prior hp.toPMF.toMeasure N hN m p hp ell hell_meas hell
      t eta ht heta hkappa
  have hendpoint :=
    continuousReverseJointMeanVarianceEpoch_endpoint_integrable
      prior N m hN hm p hp ell hell_meas hell ht heta hkappa
  exact continuousReverseJointMeanVarianceEpochBadPaths_mass_le_delta
    prior N m hN hm p hp ell hell ht heta hkappa hdelta hsub hendpoint

omit [MeasurableSpace Z] in
/-- Outside the prior-mixture crossing event, an arbitrary absolutely
continuous posterior satisfies the reverse score inequality with one
measure-theoretic KL term. -/
theorem continuousReverseJointMeanVarianceEpoch_posteriorScore_lt_of_not_mem
    [Fintype Z]
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (N m : ℕ) (hN : 2 ≤ N) (p : Z → ℝ)
    (ell : Θ → Z → ℝ) {t eta delta : ℝ}
    (hdelta : 0 < delta)
    (x : Fin N → Z)
    (hx : x ∉ continuousReverseJointMeanVarianceEpochBadPaths
      prior N hN m p ell t eta delta)
    (k : ℕ) (hk : k ≤ N - m)
    (hexp_int : Integrable
      (fun θ ↦ Real.exp
        (reverseJointMeanVarianceEpochScore
          N hN m p ell t eta θ k x)) prior)
    (hscore_int : Integrable
      (fun θ ↦ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x) posterior)
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x ∂posterior) <
      (InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta) := by
  let M := continuousReverseJointMeanVarianceEpochPriorMixture
    prior N hN m p ell t eta
  have hk_mem : k ∈ Finset.range (N - m + 1) := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  have hM_lt : M k x < 1 / delta := by
    have hnot : ¬ delta⁻¹ ≤
        (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
          (fun j ↦ M j x) := by
      simpa [continuousReverseJointMeanVarianceEpochBadPaths, M] using hx
    have hsup_lt :
        (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
          (fun j ↦ M j x) < delta⁻¹ := lt_of_not_ge hnot
    have hle := Finset.le_sup' (fun j ↦ M j x) hk_mem
    simpa only [one_div] using hle.trans_lt hsup_lt
  have hM_pos : 0 < M k x := by
    simpa [M, continuousReverseJointMeanVarianceEpochPriorMixture,
      continuousPriorMixtureProcess,
      reverseJointMeanVarianceEpochExponentialProcess] using
      integral_exp_pos hexp_int
  have hinv_pos : 0 < (1 : ℝ) / delta := one_div_pos.mpr hdelta
  have hlog_lt : Real.log (M k x) < Real.log (1 / delta) :=
    Real.strictMonoOn_log hM_pos hinv_pos hM_lt
  have hdv :=
    ContinuousChangeOfMeasure.continuous_donsker_varadhan
      posterior prior hposteriorPrior
      (fun θ ↦ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x)
      hexp_int hscore_int hllr
  have hdv' :
      (∫ θ, reverseJointMeanVarianceEpochScore
          N hN m p ell t eta θ k x ∂posterior) ≤
        (InformationTheory.klDiv posterior prior).toReal + Real.log (M k x) := by
    simpa [M, continuousReverseJointMeanVarianceEpochPriorMixture,
      continuousPriorMixtureProcess,
      reverseJointMeanVarianceEpochExponentialProcess] using hdv
  linarith

omit [MeasurableSpace Z] in
/-- Outside the derived continuous-prior crossing event, measurable bounded
losses discharge both exponential-prior and posterior-score integrability.
The only remaining analytic posterior condition is integrability of the
log-likelihood ratio itself. -/
theorem continuousReverseJointMeanVarianceEpoch_posteriorScore_lt_of_not_mem_of_measurable_bounded
    [Fintype Z]
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (N m : ℕ) (hN : 2 ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {t eta delta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hdelta : 0 < delta)
    (x : Fin N → Z)
    (hx : x ∉ continuousReverseJointMeanVarianceEpochBadPaths
      prior N hN m p ell t eta delta)
    (k : ℕ) (hk : k ≤ N - m)
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ k x ∂posterior) <
      (InformationTheory.klDiv posterior prior).toReal +
        Real.log (1 / delta) := by
  exact continuousReverseJointMeanVarianceEpoch_posteriorScore_lt_of_not_mem
    prior posterior hposteriorPrior N m hN p ell hdelta x hx k hk
    (reverseJointMeanVarianceEpochExponential_integrable_of_measurable_bounded
      prior N hN m p hp ell hell_meas hell t eta ht heta hkappa k x)
    (reverseJointMeanVarianceEpochScore_integrable_of_measurable_bounded
      posterior N hN m p hp ell hell_meas hell t eta ht heta hkappa k x)
    hllr

omit [MeasurableSpace Z] in
/-- **Continuous-hypothesis reverse-epoch empirical-Bernstein PAC-Bayes.**

Outside the posterior-independent crossing event, every prefix size `s` in
`[m, N]` and every probability posterior absolutely continuous with respect
to the prior whose log-likelihood ratio is posterior-integrable satisfy a
population-risk bound with posterior-averaged empirical risk,
posterior-averaged Bessel empirical variance, and one measure-theoretic
KL/confidence term.  The posterior may therefore be chosen after observing the
horizon sample.

This is a single-epoch, fixed-tilt theorem over a finite observation space.  It
does not select a tilt, stitch epochs, optimize to a square-root boundary, or
claim a continuous observation space.  The balance condition is the explicit
zero-residual condition that absorbs the retained population-variance term. -/
theorem continuousReverseJointMeanVarianceEpoch_posteriorRisk_prefix_lt_of_not_mem_of_measurable_bounded
    [Fintype Z]
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (N m s : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m)
    (hms : m ≤ s) (hsN : s ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {t eta delta : ℝ} (ht : 0 < t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta)
    (hbalance :
      (m : ℝ) * (Real.exp t - 1 - t) ≤
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta)
    (hdelta : 0 < delta)
    (x : Fin N → Z)
    (hx : x ∉ continuousReverseJointMeanVarianceEpochBadPaths
      prior N hN m p ell t eta delta)
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (samplePrefix hsN x) ∂posterior) +
        ((InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta)) / (t * (m : ℝ)) +
        (eta / t) *
          (∫ θ, finiteEmpiricalVariance ell θ (samplePrefix hsN x)
            ∂posterior) := by
  have hs_two : 2 ≤ s := hm.trans hms
  have hk : N - s ≤ N - m := Nat.sub_le_sub_left hms N
  have hscore :=
    continuousReverseJointMeanVarianceEpoch_posteriorScore_lt_of_not_mem_of_measurable_bounded
      prior posterior hposteriorPrior N m hN p hp ell hell_meas hell
      ht.le heta hkappa hdelta x hx (N - s) hk hllr
  let empiricalRisk : Θ → ℝ := fun θ ↦
    finiteEmpiricalRisk ell θ (samplePrefix hsN x)
  let empiricalVariance : Θ → ℝ := fun θ ↦
    finiteEmpiricalVariance ell θ (samplePrefix hsN x)
  let base : Θ → ℝ := fun θ ↦
    t * (m : ℝ) * (finitePopulationRisk p ell θ - empiricalRisk θ) -
      eta * (m : ℝ) * empiricalVariance θ
  have hrisk_int : Integrable (fun θ ↦ finitePopulationRisk p ell θ) posterior := by
    refine Integrable.of_bound
      (stronglyMeasurable_finitePopulationRisk_parameter
        p ell hell_meas).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun θ ↦ by
      have hR := finitePopulationRisk_mem_Icc_of_bounded p hp ell θ (hell θ)
      rw [Real.norm_eq_abs, abs_of_nonneg hR.1]
      exact hR.2
  have hempirical_mem (θ : Θ) : empiricalRisk θ ∈ Set.Icc (0 : ℝ) 1 := by
    have hmean := reverseMeanProcess_mem_Icc_of_bounded
      N hN (ell θ) (hell θ) (N - s) x
    rw [reverseMeanProcess_sub_eq_prefix hN hs_two hsN,
      prefixSampleMean_eq_finiteEmpiricalRisk] at hmean
    exact hmean
  have hempirical_int : Integrable empiricalRisk posterior := by
    refine Integrable.of_bound
      (stronglyMeasurable_finiteEmpiricalRisk_parameter
        ell (samplePrefix hsN x) hell_meas).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun θ ↦ by
      have hRhat := hempirical_mem θ
      rw [Real.norm_eq_abs, abs_of_nonneg hRhat.1]
      exact hRhat.2
  have hvariance_nonneg (θ : Θ) : 0 ≤ empiricalVariance θ :=
    finiteEmpiricalVariance_nonneg hs_two ell θ (samplePrefix hsN x)
  have hvariance_int : Integrable empiricalVariance posterior := by
    refine Integrable.of_bound
      (stronglyMeasurable_finiteEmpiricalVariance_parameter
        ell (samplePrefix hsN x) hell_meas).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun θ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hvariance_nonneg θ)]
      have hhalf := finiteEmpiricalVariance_le_half
        hs_two ell θ (samplePrefix hsN x)
        (fun j ↦ hell θ (samplePrefix hsN x j))
      linarith
  have hbase_int : Integrable base posterior := by
    dsimp [base]
    exact ((hrisk_int.sub hempirical_int).const_mul (t * (m : ℝ))).sub
      (hvariance_int.const_mul (eta * (m : ℝ)))
  have hscore_int : Integrable
      (fun θ ↦ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ (N - s) x) posterior :=
    reverseJointMeanVarianceEpochScore_integrable_of_measurable_bounded
      posterior N hN m p hp ell hell_meas hell t eta ht.le heta hkappa
        (N - s) x
  have hpoint (θ : Θ) :
      base θ ≤ reverseJointMeanVarianceEpochScore
        N hN m p ell t eta θ (N - s) x := by
    have hresidual :
        (m : ℝ) * Real.log
            (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell θ) -
          Real.exp (-t) * finiteJointMeanVarianceKappa m eta *
            finitePopulationVariance p ell θ ≤ 0 :=
      finiteJointMeanVariance_logResidual_nonpos_of_balance
        (finitePopulationVariance_nonneg p hp ell θ) hbalance
    rw [reverseJointMeanVarianceEpochScore_sub_eq_prefix
      hN hs_two hsN m p ell t eta θ x]
    dsimp only [base, empiricalRisk, empiricalVariance]
    linarith
  have hbase_le :
      (∫ θ, base θ ∂posterior) ≤
        ∫ θ, reverseJointMeanVarianceEpochScore
          N hN m p ell t eta θ (N - s) x ∂posterior :=
    integral_mono hbase_int hscore_int hpoint
  have hbase_lt :
      (∫ θ, base θ ∂posterior) <
        (InformationTheory.klDiv posterior prior).toReal +
          Real.log (1 / delta) := hbase_le.trans_lt hscore
  have hbase_identity :
      (∫ θ, base θ ∂posterior) =
        t * (m : ℝ) *
            ((∫ θ, finitePopulationRisk p ell θ ∂posterior) -
              ∫ θ, empiricalRisk θ ∂posterior) -
          eta * (m : ℝ) *
            (∫ θ, empiricalVariance θ ∂posterior) := by
    dsimp [base]
    rw [integral_sub]
    · rw [integral_const_mul, integral_sub hrisk_int hempirical_int,
        integral_const_mul]
    · exact (hrisk_int.sub hempirical_int).const_mul (t * (m : ℝ))
    · exact hvariance_int.const_mul (eta * (m : ℝ))
  rw [hbase_identity] at hbase_lt
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hden : 0 < t * (m : ℝ) := mul_pos ht hmR
  have hgap :
      (∫ θ, finitePopulationRisk p ell θ ∂posterior) -
          (∫ θ, empiricalRisk θ ∂posterior) <
        ((InformationTheory.klDiv posterior prior).toReal +
            Real.log (1 / delta) +
          eta * (m : ℝ) *
            (∫ θ, empiricalVariance θ ∂posterior)) /
          (t * (m : ℝ)) := by
    rw [lt_div_iff₀ hden]
    linarith
  have hsplit :
      ((InformationTheory.klDiv posterior prior).toReal +
            Real.log (1 / delta) +
          eta * (m : ℝ) *
            (∫ θ, empiricalVariance θ ∂posterior)) /
          (t * (m : ℝ)) =
        ((InformationTheory.klDiv posterior prior).toReal +
            Real.log (1 / delta)) / (t * (m : ℝ)) +
          (eta / t) * (∫ θ, empiricalVariance θ ∂posterior) := by
    field_simp [ne_of_gt ht, ne_of_gt hmR]
  rw [hsplit] at hgap
  dsimp only [empiricalRisk, empiricalVariance] at hgap ⊢
  linarith

end

end FormalSLT.PACBayes.ContinuousJointMeanVarianceReverse
