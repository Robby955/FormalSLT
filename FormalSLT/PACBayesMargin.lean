/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesBernstein
import FormalSLT.PACBayesFiniteProductMGF
import FormalSLT.Probability.BernsteinMGF

/-!
# Finite PAC-Bayes classifier-margin adapter

This module specializes the finite PAC-Bayes Bernstein shell to classifier
margin losses on a finite data domain.

The supplied-certificate adapter remains available for arbitrary normalized
Bernstein prior-moment certificates. For iid finite classifier-margin losses,
this file also derives that certificate internally from the finite product law
and the Bennett/sub-Gamma MGF layer.

## Main declarations

* `classifierMarginLoss` — thresholded margin loss in `{0,1}`.
* `classifierMarginPopulationRisk` and `classifierMarginEmpiricalRisk` —
  concrete finite risk functions for margin loss.
* `classifierMarginVarianceProxy` — the margin-risk proxy used by the
  Bernstein shell.
* `expectedPriorBernsteinExpMoment_classifierMargin_iid_le_one` — iid finite
  classifier-margin losses discharge the normalized Bernstein prior-moment
  certificate.
* `finitePACBayesClassifierMarginBernstein_iid_badEventMass_le_delta` — the
  end-to-end finite iid PAC-Bayes Bernstein theorem for classifier-margin
  losses and a fixed admissible `lambda`.
-/

namespace FormalSLT.PACBayesMargin

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayesBernstein
open FormalSLT.Probability.BernsteinMGF

noncomputable section

variable {ι Z : Type*}

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Classifier margin losses -/

/-- Encode a Boolean label as `+1` for `true` and `-1` for `false`. -/
def signedBool (y : Bool) : ℝ :=
  if y then 1 else -1

/-- Signed margin of hypothesis `i` on example `z`. -/
def classifierMargin
    (score : ι → Z → ℝ) (label : Z → Bool) (i : ι) (z : Z) : ℝ :=
  signedBool (label z) * score i z

/--
Thresholded classifier margin loss.

The loss is `1` when the signed margin is at most `threshold`, and `0`
otherwise. For `threshold = 0`, this is the usual error-or-no-positive-margin
indicator for real-valued scores with Boolean labels.
-/
def classifierMarginLoss
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (i : ι) (z : Z) : ℝ :=
  if classifierMargin score label i z ≤ threshold then 1 else 0

/-- Classifier margin loss is always in `[0,1]`. -/
lemma classifierMarginLoss_mem_Icc_zero_one
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (i : ι) (z : Z) :
    classifierMarginLoss threshold score label i z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold classifierMarginLoss
  by_cases h : classifierMargin score label i z ≤ threshold
  · simp [h]
  · simp [h]

/-- Finite population risk of a thresholded classifier margin loss. -/
def classifierMarginPopulationRisk [Fintype Z]
    (p : Z → ℝ) (threshold : ℝ)
    (score : ι → Z → ℝ) (label : Z → Bool) (i : ι) : ℝ :=
  finitePopulationRisk p (classifierMarginLoss threshold score label) i

/-- Finite empirical risk of a thresholded classifier margin loss. -/
def classifierMarginEmpiricalRisk {n : ℕ}
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (i : ι) (S : Fin n → Z) : ℝ :=
  finiteEmpiricalRisk (classifierMarginLoss threshold score label) i S

/-- Sample-indexed empirical-risk function for the PAC-Bayes Bernstein shell. -/
def classifierMarginEmpiricalRiskFn {n : ℕ}
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (S : Fin n → Z) (i : ι) : ℝ :=
  classifierMarginEmpiricalRisk threshold score label i S

/--
Concrete margin-risk variance proxy.

For an indicator margin loss, the second moment equals the population risk, so
this is the natural Bernstein variance proxy exposed to the PAC-Bayes layer.
The equality is kept as a definition here; deriving the normalized prior MGF
from this proxy is a separate concentration step.
-/
def classifierMarginVarianceProxy [Fintype Z]
    (p : Z → ℝ) (threshold : ℝ)
    (score : ι → Z → ℝ) (label : Z → Bool) (i : ι) : ℝ :=
  classifierMarginPopulationRisk p threshold score label i

/-- The margin variance proxy is definitionally the margin population risk. -/
lemma classifierMarginVarianceProxy_eq_populationRisk [Fintype Z]
    (p : Z → ℝ) (threshold : ℝ)
    (score : ι → Z → ℝ) (label : Z → Bool) (i : ι) :
    classifierMarginVarianceProxy p threshold score label i =
      classifierMarginPopulationRisk p threshold score label i := rfl

/-- Sample-average variance proxy for iid classifier-margin empirical risks. -/
def classifierMarginSampleVarianceProxy {n : ℕ} [Fintype Z]
    (p : Z → ℝ) (threshold : ℝ)
    (score : ι → Z → ℝ) (label : Z → Bool) (i : ι) : ℝ :=
  classifierMarginVarianceProxy p threshold score label i / (n : ℝ)

/-- Posterior-averaged classifier-margin variance proxy. -/
def posteriorClassifierMarginVarianceProxy [Fintype Z] [Fintype ι]
    (ρ : ι → ℝ) (p : Z → ℝ) (threshold : ℝ)
    (score : ι → Z → ℝ) (label : Z → Bool) : ℝ :=
  posteriorMarginVarianceProxy ρ
    (classifierMarginVarianceProxy p threshold score label)

/-- Posterior-averaged iid sample classifier-margin variance proxy. -/
def posteriorClassifierMarginSampleVarianceProxy {n : ℕ} [Fintype Z] [Fintype ι]
    (ρ : ι → ℝ) (p : Z → ℝ) (threshold : ℝ)
    (score : ι → Z → ℝ) (label : Z → Bool) : ℝ :=
  posteriorMarginVarianceProxy ρ
    (classifierMarginSampleVarianceProxy (n := n) p threshold score label)

lemma classifierMarginPopulationRisk_mem_Icc_zero_one [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool) (i : ι) :
    classifierMarginPopulationRisk p threshold score label i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold classifierMarginPopulationRisk finitePopulationRisk
    exact Finset.sum_nonneg
      (fun z _hz =>
        mul_nonneg (hp.nonneg z)
          (classifierMarginLoss_mem_Icc_zero_one threshold score label i z).1)
  · unfold classifierMarginPopulationRisk finitePopulationRisk
    calc
      (∑ z : Z, p z * classifierMarginLoss threshold score label i z)
          ≤ ∑ z : Z, p z * 1 := by
            apply Finset.sum_le_sum
            intro z _hz
            exact mul_le_mul_of_nonneg_left
              (classifierMarginLoss_mem_Icc_zero_one threshold score label i z).2
              (hp.nonneg z)
      _ = 1 := by simp [hp.sum_one]

lemma classifierMarginLoss_sq
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (i : ι) (z : Z) :
    classifierMarginLoss threshold score label i z ^ 2 =
      classifierMarginLoss threshold score label i z := by
  unfold classifierMarginLoss
  by_cases h : classifierMargin score label i z ≤ threshold
  · simp [h]
  · simp [h]

lemma classifierMarginVariance_le_risk [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool) (i : ι) :
    (∑ z : Z,
        p z *
          (classifierMarginPopulationRisk p threshold score label i -
            classifierMarginLoss threshold score label i z) ^ 2)
      ≤ classifierMarginVarianceProxy p threshold score label i := by
  classical
  let R := classifierMarginPopulationRisk p threshold score label i
  let loss : Z → ℝ := classifierMarginLoss threshold score label i
  have hsum_loss : (∑ z : Z, p z * loss z) = R := by
    simp [R, loss, classifierMarginPopulationRisk, finitePopulationRisk]
  have hsum_loss_sq : (∑ z : Z, p z * loss z ^ 2) = R := by
    calc
      (∑ z : Z, p z * loss z ^ 2)
          = ∑ z : Z, p z * loss z := by
              apply Finset.sum_congr rfl
              intro z _hz
              rw [classifierMarginLoss_sq]
      _ = R := hsum_loss
  have hvariance_eq :
      (∑ z : Z, p z * (R - loss z) ^ 2) = R - R ^ 2 := by
    calc
      (∑ z : Z, p z * (R - loss z) ^ 2)
          =
        ∑ z : Z, (p z * R ^ 2 - 2 * R * (p z * loss z) +
          p z * loss z ^ 2) := by
            apply Finset.sum_congr rfl
            intro z _hz
            ring
      _ =
        (∑ z : Z, p z * R ^ 2) -
          (∑ z : Z, 2 * R * (p z * loss z)) +
          ∑ z : Z, p z * loss z ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ =
        (∑ z : Z, p z * R ^ 2) -
          2 * R * (∑ z : Z, p z * loss z) +
          ∑ z : Z, p z * loss z ^ 2 := by
            congr 2
            rw [Finset.mul_sum]
      _ =
        R ^ 2 * (∑ z : Z, p z) -
          2 * R * (∑ z : Z, p z * loss z) +
          ∑ z : Z, p z * loss z ^ 2 := by
            congr 2
            calc
              (∑ z : Z, p z * R ^ 2)
                  = ∑ z : Z, R ^ 2 * p z := by
                      apply Finset.sum_congr rfl
                      intro z _hz
                      ring
              _ = R ^ 2 * (∑ z : Z, p z) := by
                      rw [Finset.mul_sum]
      _ = R - R ^ 2 := by
            rw [hp.sum_one, hsum_loss, hsum_loss_sq]
            ring
  have hR_nonneg : 0 ≤ R :=
    (classifierMarginPopulationRisk_mem_Icc_zero_one
      p hp threshold score label i).1
  calc
    (∑ z : Z,
        p z *
          (classifierMarginPopulationRisk p threshold score label i -
            classifierMarginLoss threshold score label i z) ^ 2)
        = ∑ z : Z, p z * (R - loss z) ^ 2 := by
            simp [R, loss]
    _ = R - R ^ 2 := hvariance_eq
    _ ≤ R := by nlinarith [sq_nonneg R]
    _ = classifierMarginVarianceProxy p threshold score label i := by
            simp [classifierMarginVarianceProxy, R]

theorem oneCoordinate_classifierMarginLoss_mgf_subgamma
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (i : ι) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambda_bound : lambda * (n : ℝ)⁻¹ < 3) :
    oneCoordinateDeviationMGF (n := n) p
        (classifierMarginLoss threshold score label) i lambda
      ≤
    Real.exp
      ((lambda * (n : ℝ)⁻¹) ^ 2 *
          classifierMarginVarianceProxy p threshold score label i /
        (2 * (1 - (lambda * (n : ℝ)⁻¹) / 3))) := by
  classical
  let R := classifierMarginPopulationRisk p threshold score label i
  let loss : Z → ℝ := classifierMarginLoss threshold score label i
  have hcenter : (∑ z : Z, p z * (R - loss z)) = 0 := by
    have hexp :
        (∑ z : Z, p z * (R - loss z))
          = R * (∑ z : Z, p z) - ∑ z : Z, p z * loss z := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun z _hz => by ring)
    rw [hexp, hp.sum_one]
    simp [R, loss, classifierMarginPopulationRisk, finitePopulationRisk]
  have hbound : ∀ z : Z, R - loss z ≤ 1 := by
    intro z
    have hR_le :
        R ≤ 1 :=
      (classifierMarginPopulationRisk_mem_Icc_zero_one
        p hp threshold score label i).2
    have hloss_nonneg :
        0 ≤ loss z :=
      (classifierMarginLoss_mem_Icc_zero_one threshold score label i z).1
    linarith
  have hvar :
      (∑ z : Z, p z * (R - loss z) ^ 2)
        ≤ classifierMarginVarianceProxy p threshold score label i := by
    simpa [R, loss] using
      (classifierMarginVariance_le_risk p hp threshold score label i)
  have h :=
    bennett_mgf_subgamma p (fun z : Z => R - loss z)
      (b := 1)
      (v := classifierMarginVarianceProxy p threshold score label i)
      (lam := lambda * (n : ℝ)⁻¹)
      (by norm_num) (by positivity) (by simpa using hlambda_bound)
      hp.nonneg hp.sum_one hcenter hbound hvar
  simpa [oneCoordinateDeviationMGF, R, loss, classifierMarginPopulationRisk] using h

theorem finiteProduct_classifierMarginLoss_mgf_subgamma
    {n : ℕ} [Fintype Z] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (i : ι) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambda_bound : lambda * (n : ℝ)⁻¹ < 3) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp
            (lambda *
              (classifierMarginPopulationRisk p threshold score label i -
                classifierMarginEmpiricalRisk threshold score label i S)))
      ≤
    Real.exp
      (lambda ^ 2 *
          classifierMarginSampleVarianceProxy (n := n) p threshold score label i /
        (2 * (1 - (3 * (n : ℝ))⁻¹ * lambda))) := by
  classical
  let singleBudget : ℝ :=
    (lambda * (n : ℝ)⁻¹) ^ 2 *
        classifierMarginVarianceProxy p threshold score label i /
      (2 * (1 - (lambda * (n : ℝ)⁻¹) / 3))
  have hsingle :
      oneCoordinateDeviationMGF (n := n) p
          (classifierMarginLoss threshold score label) i lambda ≤
        Real.exp singleBudget := by
    simpa [singleBudget] using
      (oneCoordinate_classifierMarginLoss_mgf_subgamma
        (n := n) hn p hp threshold score label i lambda hlambda hlambda_bound)
  have hprod :=
    finiteProduct_mgf_empiricalRiskDeviation_le_exp_of_single
      (ι := ι) (Z := Z) hn p hp
      (classifierMarginLoss threshold score label) i lambda singleBudget hsingle
  refine hprod.trans_eq ?_
  congr 1
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hden₁ : 2 * (1 - (lambda * (n : ℝ)⁻¹) / 3) ≠ 0 := by
    have hpos : 0 < 1 - (lambda * (n : ℝ)⁻¹) / 3 := by linarith
    nlinarith
  have hden₂ : 2 * (1 - (3 * (n : ℝ))⁻¹ * lambda) ≠ 0 := by
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlt : lambda < 3 * (n : ℝ) := by
      rw [← div_lt_iff₀ hn_pos]
      simpa [div_eq_mul_inv] using hlambda_bound
    have hpos : 0 < 1 - (3 * (n : ℝ))⁻¹ * lambda := by
      rw [sub_pos]
      rw [inv_mul_lt_iff₀ (by positivity : 0 < 3 * (n : ℝ))]
      nlinarith
    nlinarith
  simp [singleBudget, classifierMarginSampleVarianceProxy]
  field_simp [hn_ne, hden₁, hden₂]

theorem expectedPriorBernsteinExpMoment_classifierMargin_iid_le_one
    {n : ℕ} [Fintype Z] [Fintype ι]
    (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    {π : ι → ℝ} (hπ : IsPMF π)
    (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambda_bound : lambda * (n : ℝ)⁻¹ < 3)
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool) :
    expectedPriorBernsteinExpMoment
        (finiteProductSampleWeight (n := n) p) π lambda ((3 * (n : ℝ))⁻¹)
        (classifierMarginPopulationRisk p threshold score label)
        (classifierMarginEmpiricalRiskFn threshold score label)
        (classifierMarginSampleVarianceProxy (n := n) p threshold score label)
      ≤ 1 := by
  classical
  apply expectedPriorBernsteinExpMoment_le_one_of_mgf_bound hπ
  intro i
  simpa [classifierMarginEmpiricalRiskFn] using
    (finiteProduct_classifierMarginLoss_mgf_subgamma
      (n := n) hn p hp threshold score label i lambda hlambda hlambda_bound)

/-! ### Product sample law -/

/-- Finite iid product sample weights form a PMF when the base mass is a PMF. -/
theorem finiteProductSampleWeight_isPMF
    {n : ℕ} [Fintype Z] {p : Z → ℝ} (hp : IsPMF p) :
    IsPMF (finiteProductSampleWeight (n := n) p) where
  nonneg := by
    intro S
    unfold finiteProductSampleWeight
    exact Finset.prod_nonneg (fun k _hk => hp.nonneg (S k))
  sum_one := by
    unfold finiteProductSampleWeight
    calc
      (∑ S : Fin n → Z, ∏ k : Fin n, p (S k))
          = ∏ _k : Fin n, ∑ z : Z, p z := by
            exact (Fintype.prod_sum (f := fun _k : Fin n => p)).symm
      _ = 1 := by simp [hp.sum_one]

/-! ### PAC-Bayes Bernstein specialization -/

/-- Bad samples for the concrete classifier-margin PAC-Bayes Bernstein event. -/
def finitePACBayesClassifierMarginBernsteinBadSamples
    {n : ℕ} [Fintype Z] [Fintype ι]
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (p : Z → ℝ) (posteriorPenalty : (ι → ℝ) → ℝ) :
    Finset (Fin n → Z) :=
  finitePACBayesBernsteinPenaltyBadSamples
    (classifierMarginPopulationRisk p threshold score label)
    (classifierMarginEmpiricalRiskFn threshold score label)
    posteriorPenalty

/--
Finite PAC-Bayes Bernstein theorem specialized to classifier margin losses.

The theorem states that, under the same explicit finite-parameter certificates
as `finitePACBayesBernsteinMargin_badEventMass_le_delta`, the iid sample mass
of classifier-margin bad samples is at most `delta`.
-/
theorem finitePACBayesClassifierMarginBernstein_badEventMass_le_delta
    {n : ℕ} [Fintype Z] [Fintype ι] [Nonempty ι]
    (p : Z → ℝ) (hp : IsPMF p)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (lambda scale delta : ℝ)
    (hlambda : 0 < lambda) (hscale : scale * lambda < 1)
    (hdelta : 0 < delta)
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (complexityOf : (ι → ℝ) → ℝ)
    (hcomplexity :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        klDiv ρ π + Real.log (1 / delta) ≤ complexityOf ρ)
    (hpenalty :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        complexityOf ρ / lambda +
            lambda *
                posteriorClassifierMarginVarianceProxy ρ p threshold score label /
              (2 * (1 - scale * lambda))
          ≤
        Real.sqrt
            (2 * posteriorClassifierMarginVarianceProxy ρ p threshold score label *
              complexityOf ρ) +
          scale * complexityOf ρ)
    (hExpected :
      expectedPriorBernsteinExpMoment
        (finiteProductSampleWeight (n := n) p) π lambda scale
        (classifierMarginPopulationRisk p threshold score label)
        (classifierMarginEmpiricalRiskFn threshold score label)
        (classifierMarginVarianceProxy p threshold score label) ≤ 1) :
    (∑ S ∈
        finitePACBayesClassifierMarginBernsteinBadSamples
          (n := n) threshold score label p
          (fun ρ =>
            Real.sqrt
                (2 * posteriorClassifierMarginVarianceProxy ρ p threshold score label *
                  complexityOf ρ) +
              scale * complexityOf ρ),
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  simpa [finitePACBayesClassifierMarginBernsteinBadSamples,
    posteriorClassifierMarginVarianceProxy]
    using
      (finitePACBayesBernsteinMargin_badEventMass_le_delta
        (Ω := Fin n → Z) (ι := ι)
        (ν := finiteProductSampleWeight (n := n) p)
        (hν := finiteProductSampleWeight_isPMF (n := n) hp)
        (π := π) hπ lambda scale delta hlambda hscale hdelta
        (classifierMarginPopulationRisk p threshold score label)
        (classifierMarginEmpiricalRiskFn threshold score label)
        (classifierMarginVarianceProxy p threshold score label)
        complexityOf hcomplexity hpenalty hExpected)

/--
Finite iid PAC-Bayes Bernstein theorem for classifier-margin losses.

This version derives the normalized Bernstein prior-moment certificate from the
iid product sample law and the finite Bennett/sub-Gamma bound for thresholded
margin losses. The variance proxy is scaled by the sample size.
-/
theorem finitePACBayesClassifierMarginBernstein_iid_badEventMass_le_delta
    {n : ℕ} [Fintype Z] [Fintype ι] [Nonempty ι]
    (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    {π : ι → ℝ} (hπ : IsFullSupportPMF π)
    (lambda delta : ℝ)
    (hlambda : 0 < lambda)
    (hlambda_bound : lambda * (n : ℝ)⁻¹ < 3)
    (hdelta : 0 < delta)
    (threshold : ℝ) (score : ι → Z → ℝ) (label : Z → Bool)
    (complexityOf : (ι → ℝ) → ℝ)
    (hcomplexity :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        klDiv ρ π + Real.log (1 / delta) ≤ complexityOf ρ)
    (hpenalty :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        complexityOf ρ / lambda +
            lambda *
                posteriorClassifierMarginSampleVarianceProxy
                  (n := n) ρ p threshold score label /
              (2 * (1 - (3 * (n : ℝ))⁻¹ * lambda))
          ≤
        Real.sqrt
            (2 *
              posteriorClassifierMarginSampleVarianceProxy
                (n := n) ρ p threshold score label *
              complexityOf ρ) +
          (3 * (n : ℝ))⁻¹ * complexityOf ρ) :
    (∑ S ∈
        finitePACBayesClassifierMarginBernsteinBadSamples
          (n := n) threshold score label p
          (fun ρ =>
            Real.sqrt
                (2 *
                  posteriorClassifierMarginSampleVarianceProxy
                    (n := n) ρ p threshold score label *
                  complexityOf ρ) +
              (3 * (n : ℝ))⁻¹ * complexityOf ρ),
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  have hExpected :
      expectedPriorBernsteinExpMoment
        (finiteProductSampleWeight (n := n) p) π lambda ((3 * (n : ℝ))⁻¹)
        (classifierMarginPopulationRisk p threshold score label)
        (classifierMarginEmpiricalRiskFn threshold score label)
        (classifierMarginSampleVarianceProxy (n := n) p threshold score label) ≤ 1 := by
    exact
      expectedPriorBernsteinExpMoment_classifierMargin_iid_le_one
        (n := n) hn p hp hπ.toIsPMF lambda hlambda.le hlambda_bound
        threshold score label
  have hscale : (3 * (n : ℝ))⁻¹ * lambda < 1 := by
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlt : lambda < 3 * (n : ℝ) := by
      rw [← div_lt_iff₀ hn_pos]
      simpa [div_eq_mul_inv] using hlambda_bound
    rw [inv_mul_lt_iff₀ (by positivity : 0 < 3 * (n : ℝ))]
    nlinarith
  simpa [finitePACBayesClassifierMarginBernsteinBadSamples,
    posteriorClassifierMarginSampleVarianceProxy]
    using
      (finitePACBayesBernsteinMargin_badEventMass_le_delta
        (Ω := Fin n → Z) (ι := ι)
        (ν := finiteProductSampleWeight (n := n) p)
        (hν := finiteProductSampleWeight_isPMF (n := n) hp)
        (π := π) hπ lambda ((3 * (n : ℝ))⁻¹) delta hlambda
        hscale hdelta
        (classifierMarginPopulationRisk p threshold score label)
        (classifierMarginEmpiricalRiskFn threshold score label)
        (classifierMarginSampleVarianceProxy (n := n) p threshold score label)
        complexityOf hcomplexity hpenalty hExpected)

end

end FormalSLT.PACBayesMargin
