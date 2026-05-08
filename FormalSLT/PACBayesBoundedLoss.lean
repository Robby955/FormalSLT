/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesFiniteProductMGF
import FormalSLT.Probability.Concentration
import FormalSLT.Probability.FiniteUnionBound
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite bounded-loss PAC-Bayes MGF and confidence layer

This module continues the finite PAC-Bayes path for scalar bounded losses.
It instantiates the one-coordinate MGF budget for `[0,1]` losses, lifts it
through the finite iid product bridge, and proves the finite Markov/confidence
event that feeds a Catoni-style posterior-risk statement.
It also derives a finite McAllester-style square-root corollary for a fixed
posterior-complexity budget.

Scope:
* finite data domain;
* finite hypothesis index;
* finite prior and posterior distributions;
* scalar losses in `[0,1]`;
* positive `lambda` and confidence parameter `delta`;
* fixed complexity budget for the square-root corollary;
* no infinite hypothesis spaces or arbitrary measurable posterior kernels.
-/

namespace FormalSLT.PACBayesBoundedLoss

open Finset Real BigOperators
open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι Z Ω : Type*}

/-! ### PMF bridge for finite real mass functions -/

/-- Convert a finite real-valued PMF into mathlib's `PMF` type. -/
private noncomputable def pmfOfReal [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) : PMF Z :=
  PMF.ofFintype (fun z => ENNReal.ofReal (p z)) (by
    rw [← ENNReal.ofReal_one, ← hp.sum_one]
    exact Eq.symm (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := p) (fun z _hz => hp.nonneg z)))

private lemma integral_pmfOfReal_eq_sum [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (p : Z → ℝ) (hp : IsPMF p) (f : Z → ℝ) :
    (∫ z, f z ∂(pmfOfReal p hp).toMeasure) = ∑ z, p z * f z := by
  rw [PMF.integral_eq_sum]
  simp [pmfOfReal, hp.nonneg, smul_eq_mul]

private lemma finiteProductSampleWeight_nonneg {n : ℕ} [Fintype Z]
    {p : Z → ℝ} (hp : IsPMF p) :
    ∀ S : Fin n → Z, 0 ≤ finiteProductSampleWeight p S := by
  intro S
  unfold finiteProductSampleWeight
  exact Finset.prod_nonneg (fun k _hk => hp.nonneg (S k))

/-! ### Finite risks averaged over a posterior -/

/-- Posterior average over a finite hypothesis class. -/
def posteriorAverage [Fintype ι] (ρ : ι → ℝ) (g : ι → ℝ) : ℝ :=
  ∑ i, ρ i * g i

/-- Posterior population risk for the finite bounded-loss PAC-Bayes layer. -/
def posteriorPopulationRisk [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (ℓ : ι → Z → ℝ) (ρ : ι → ℝ) : ℝ :=
  posteriorAverage ρ (fun i => finitePopulationRisk p ℓ i)

/-- Posterior empirical risk for the finite bounded-loss PAC-Bayes layer. -/
def posteriorEmpiricalRisk {n : ℕ} [Fintype ι]
    (ℓ : ι → Z → ℝ) (ρ : ι → ℝ) (S : Fin n → Z) : ℝ :=
  posteriorAverage ρ (fun i => finiteEmpiricalRisk ℓ i S)

/-- Prior exponential deviation moment at a fixed finite sample. -/
def priorDeviationMGF {n : ℕ} [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (prior : ι → ℝ) (ℓ : ι → Z → ℝ) (lam : ℝ)
    (S : Fin n → Z) : ℝ :=
  ∑ i : ι,
    prior i * Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))

lemma priorDeviationMGF_nonneg {n : ℕ} [Fintype Z] [Fintype ι]
    (p : Z → ℝ) {prior : ι → ℝ} (hprior : IsPMF prior)
    (ℓ : ι → Z → ℝ) (lam : ℝ) (S : Fin n → Z) :
    0 ≤ priorDeviationMGF p prior ℓ lam S := by
  unfold priorDeviationMGF
  exact Finset.sum_nonneg
    (fun i _hi => mul_nonneg (hprior.nonneg i) (le_of_lt (Real.exp_pos _)))

/-! ### Bounded-loss one-coordinate MGF -/

private lemma finitePopulationRisk_mem_Icc_zero_one [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓi : Z → ℝ)
    (hℓ : ∀ z : Z, 0 ≤ ℓi z ∧ ℓi z ≤ 1) :
    finitePopulationRisk p (fun _ : Unit => ℓi) () ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold finitePopulationRisk
    exact Finset.sum_nonneg
      (fun z _hz => mul_nonneg (hp.nonneg z) (hℓ z).1)
  · unfold finitePopulationRisk
    calc
      (∑ z : Z, p z * ℓi z) ≤ ∑ z : Z, p z * 1 := by
        apply Finset.sum_le_sum
        intro z _hz
        exact mul_le_mul_of_nonneg_left (hℓ z).2 (hp.nonneg z)
      _ = 1 := by
        simp [hp.sum_one]

private lemma finitePopulationRisk_i_mem_Icc_zero_one [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (ℓ : ι → Z → ℝ) (i : ι)
    (hℓ : ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    finitePopulationRisk p ℓ i ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [finitePopulationRisk] using
    finitePopulationRisk_mem_Icc_zero_one p hp (ℓ i) hℓ

/--
One-coordinate bounded-loss MGF instantiation.

For a fixed finite hypothesis `i` and `[0,1]` loss, the centered one-sample
deviation `R_i - ℓ_i(z)` has Hoeffding MGF budget `exp(t² / 8)`. With
`t = lam / n`, this supplies the one-coordinate hypothesis required by the
finite iid product bridge.
-/
theorem oneCoordinate_boundedLoss_mgf
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι) (lam : ℝ)
    (hℓ : ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    oneCoordinateDeviationMGF (n := n) p ℓ i lam ≤
      Real.exp (lam ^ 2 / (8 * (n : ℝ) ^ 2)) := by
  classical
  let μ := (pmfOfReal p hp).toMeasure
  let R := finitePopulationRisk p ℓ i
  let X : Z → ℝ := fun z => R - ℓ i z
  haveI : IsProbabilityMeasure μ := PMF.toMeasure.isProbabilityMeasure (pmfOfReal p hp)
  have hmeas : AEMeasurable X μ :=
    (measurable_of_countable X).aemeasurable
  have hbound : ∀ᵐ z ∂μ, X z ∈ Set.Icc (R - 1) R := by
    exact Filter.Eventually.of_forall (fun z => by
      dsimp [X]
      constructor
      · linarith [(hℓ z).2]
      · linarith [(hℓ z).1])
  have hmean : (∫ z, X z ∂μ) = 0 := by
    dsimp [μ, X, R]
    rw [integral_pmfOfReal_eq_sum p hp]
    unfold finitePopulationRisk
    calc
      (∑ z : Z, p z * ((∑ x : Z, p x * ℓ i x) - ℓ i z))
          =
        (∑ z : Z, p z * (∑ x : Z, p x * ℓ i x)) -
          ∑ z : Z, p z * ℓ i z := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun z _hz => ?_)
            ring
      _ =
        (∑ x : Z, p x * ℓ i x) * (∑ z : Z, p z) -
          ∑ z : Z, p z * ℓ i z := by
            congr 1
            calc
              (∑ z : Z, p z * (∑ x : Z, p x * ℓ i x))
                  = ∑ z : Z, (∑ x : Z, p x * ℓ i x) * p z := by
                    refine Finset.sum_congr rfl (fun z _hz => ?_)
                    ring
              _ = (∑ x : Z, p x * ℓ i x) * (∑ z : Z, p z) := by
                    rw [Finset.mul_sum]
      _ = 0 := by
        rw [hp.sum_one]
        ring
  have hsubG :
      HasSubgaussianMGF X ((‖R - (R - 1)‖₊ / 2) ^ 2) μ :=
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hmeas hbound hmean
  have hmgf := hsubG.mgf_le (lam * (n : ℝ)⁻¹)
  have hmgf_eq :
      ProbabilityTheory.mgf X μ (lam * (n : ℝ)⁻¹) =
        oneCoordinateDeviationMGF (n := n) p ℓ i lam := by
    dsimp [ProbabilityTheory.mgf, oneCoordinateDeviationMGF, μ, X, R]
    rw [integral_pmfOfReal_eq_sum p hp]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmgf' :
      oneCoordinateDeviationMGF (n := n) p ℓ i lam ≤
        Real.exp ((2 ^ 2 : ℝ)⁻¹ * (lam * (n : ℝ)⁻¹) ^ 2 / 2) := by
    simpa [hmgf_eq] using hmgf
  have hparam :
      (2 ^ 2 : ℝ)⁻¹ * (lam * (n : ℝ)⁻¹) ^ 2 / 2 =
        lam ^ 2 / (8 * (n : ℝ) ^ 2) := by
    field_simp [hn_ne]
    ring_nf
  simpa [hparam] using hmgf'

/-! ### Product and prior-averaged bounded-loss MGFs -/

/-- Finite sample-average bounded-loss MGF via the product bridge. -/
theorem sampleAverage_boundedLoss_mgf
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (ℓ : ι → Z → ℝ) (i : ι) (lam : ℝ)
    (hℓ : ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S *
          Real.exp (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S))) ≤
      Real.exp (lam ^ 2 / (8 * (n : ℝ))) := by
  have hsingle :
      oneCoordinateDeviationMGF (n := n) p ℓ i lam ≤
        Real.exp (lam ^ 2 * (1 / 4 : ℝ) / (2 * (n : ℝ) ^ 2)) := by
    have h := oneCoordinate_boundedLoss_mgf hn p hp ℓ i lam hℓ
    convert h using 1
    ring_nf
  have h :=
    finiteProduct_mgf_empiricalRiskDeviation_le_of_single
      (ι := ι) (Z := Z) hn p hp ℓ i lam (1 / 4 : ℝ) hsingle
  convert h using 1
  ring_nf

/-- Finite prior-averaged bounded-loss MGF via the product bridge. -/
theorem priorAveraged_boundedLoss_mgf
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsPMF prior)
    (ℓ : ι → Z → ℝ) (lam : ℝ)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S : Fin n → Z,
        finiteProductSampleWeight p S * priorDeviationMGF p prior ℓ lam S) ≤
      Real.exp (lam ^ 2 / (8 * (n : ℝ))) := by
  have hsingle :
      ∀ i : ι,
        oneCoordinateDeviationMGF (n := n) p ℓ i lam ≤
          Real.exp (lam ^ 2 * (1 / 4 : ℝ) / (2 * (n : ℝ) ^ 2)) := by
    intro i
    have h := oneCoordinate_boundedLoss_mgf hn p hp ℓ i lam (hℓ i)
    convert h using 1
    ring_nf
  have h :=
    finitePriorAveraged_mgf_empiricalRiskDeviation_le
      (ι := ι) (Z := Z) hn p hp prior hprior ℓ lam (1 / 4 : ℝ) hsingle
  have h' :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S * priorDeviationMGF p prior ℓ lam S) ≤
        Real.exp (lam ^ 2 * (1 / 4 : ℝ) / (2 * (n : ℝ))) := by
    simpa [priorDeviationMGF] using h
  convert h' using 1
  ring_nf

/-! ### Finite Markov confidence event -/

/-- Finite Markov confidence event for the prior-averaged bounded-loss MGF. -/
theorem priorAveraged_boundedLoss_mgf_badEventMass_le_delta
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsPMF prior)
    (ℓ : ι → Z → ℝ) (lam delta : ℝ)
    (hdelta : 0 < delta)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        Real.exp (lam ^ 2 / (8 * (n : ℝ))) / delta ≤
          priorDeviationMGF p prior ℓ lam S),
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  set C := Real.exp (lam ^ 2 / (8 * (n : ℝ))) with hCdef
  have hCpos : 0 < C := by
    simpa [hCdef] using Real.exp_pos (lam ^ 2 / (8 * (n : ℝ)))
  have hthreshold : 0 < C / delta := div_pos hCpos hdelta
  have hmarkov :=
    FormalSLT.Probability.Concentration.markovInequalityFiniteWeighted_proof
      (ι := Fin n → Z)
      (s := (Finset.univ : Finset (Fin n → Z)))
      (w := fun S : Fin n → Z => finiteProductSampleWeight p S)
      (x := fun S : Fin n → Z => priorDeviationMGF p prior ℓ lam S)
      (t := C / delta)
      (fun S : Fin n → Z => finiteProductSampleWeight_nonneg (n := n) hp S)
      (fun S : Fin n → Z => priorDeviationMGF_nonneg (n := n) p hprior ℓ lam S)
      hthreshold
  unfold FormalSLT.Probability.Concentration.upperTailMass
    FormalSLT.Probability.Concentration.weightedMean at hmarkov
  have hmgf :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S * priorDeviationMGF p prior ℓ lam S) ≤ C := by
    simpa [C, hCdef] using
      priorAveraged_boundedLoss_mgf hn p hp prior hprior ℓ lam hℓ
  have hdiv :
      (∑ S : Fin n → Z,
          finiteProductSampleWeight p S * priorDeviationMGF p prior ℓ lam S) / (C / delta)
        ≤ C / (C / delta) :=
    div_le_div_of_nonneg_right hmgf (le_of_lt hthreshold)
  have hCdiv : C / (C / delta) = delta := by
    field_simp [ne_of_gt hCpos, ne_of_gt hdelta]
  simpa [C, hCdef] using hmarkov.trans (hdiv.trans_eq hCdiv)

/-! ### Deterministic posterior-risk adapter and final bad-event theorem -/

/--
Posterior-risk bound from a finite prior-deviation MGF confidence certificate.

This is deterministic for a fixed sample `S`: if the prior exponential moment
at that sample is at most `exp(λ²/(8n))/δ`, then every finite posterior `ρ`
satisfies the Catoni-style risk inequality.
-/
theorem posteriorRisk_bound_of_priorDeviationMGF_le
    {n : ℕ} [Fintype Z] [Fintype ι] [Nonempty ι]
    (hn : 0 < n)
    (p : Z → ℝ)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ρ : ι → ℝ) (hρ : IsPMF ρ)
    (ℓ : ι → Z → ℝ) (S : Fin n → Z)
    {lam delta : ℝ} (hlam : 0 < lam) (hdelta : 0 < delta)
    (hconf :
      priorDeviationMGF p prior ℓ lam S ≤
        Real.exp (lam ^ 2 / (8 * (n : ℝ))) / delta) :
    posteriorPopulationRisk p ℓ ρ ≤
      posteriorEmpiricalRisk ℓ ρ S +
        (klDiv ρ prior + Real.log (1 / delta)) / lam +
        lam / (8 * (n : ℝ)) := by
  classical
  let riskFn : ι → ℝ := fun i => finitePopulationRisk p ℓ i
  let empiricalRiskFn : ι → ℝ := fun i => finiteEmpiricalRisk ℓ i S
  have hprior_pos : 0 < priorDeviationMGF p prior ℓ lam S := by
    unfold priorDeviationMGF
    apply Finset.sum_pos
    · intro i _hi
      exact mul_pos (hprior.pos i) (Real.exp_pos _)
    · exact Finset.univ_nonempty
  have hthreshold_pos :
      0 < Real.exp (lam ^ 2 / (8 * (n : ℝ))) / delta :=
    div_pos (Real.exp_pos _) hdelta
  have hlog :
      Real.log (priorDeviationMGF p prior ℓ lam S) ≤
        lam ^ 2 / (8 * (n : ℝ)) + Real.log (1 / delta) := by
    calc
      Real.log (priorDeviationMGF p prior ℓ lam S)
          ≤ Real.log (Real.exp (lam ^ 2 / (8 * (n : ℝ))) / delta) :=
            Real.log_le_log hprior_pos hconf
      _ = lam ^ 2 / (8 * (n : ℝ)) + Real.log (1 / delta) := by
        rw [div_eq_mul_inv, Real.log_mul (Real.exp_pos _).ne' (inv_ne_zero hdelta.ne')]
        rw [Real.log_exp]
        congr 1
        rw [one_div]
  have hdv :=
    donsker_varadhan hρ hprior
      (fun i : ι => lam * (riskFn i - empiricalRiskFn i))
  have hlhs :
      (∑ i : ι, ρ i * (lam * (riskFn i - empiricalRiskFn i))) =
        lam * (posteriorPopulationRisk p ℓ ρ - posteriorEmpiricalRisk ℓ ρ S) := by
    unfold posteriorPopulationRisk posteriorEmpiricalRisk posteriorAverage riskFn empiricalRiskFn
    calc
      (∑ i : ι, ρ i * (lam * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)))
          = ∑ i : ι, lam * (ρ i * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S)) := by
            refine Finset.sum_congr rfl (fun i _hi => ?_)
            ring
      _ = lam * ∑ i : ι, ρ i * (finitePopulationRisk p ℓ i - finiteEmpiricalRisk ℓ i S) := by
            rw [Finset.mul_sum]
      _ = lam * ((∑ i : ι, ρ i * finitePopulationRisk p ℓ i) -
            ∑ i : ι, ρ i * finiteEmpiricalRisk ℓ i S) := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun i _hi => ?_)
            ring
  have hmoment :
      (∑ i : ι, prior i * Real.exp (lam * (riskFn i - empiricalRiskFn i))) =
        priorDeviationMGF p prior ℓ lam S := by
    unfold priorDeviationMGF riskFn empiricalRiskFn
    rfl
  have hgap_scaled :
      lam * (posteriorPopulationRisk p ℓ ρ - posteriorEmpiricalRisk ℓ ρ S) ≤
        klDiv ρ prior + (lam ^ 2 / (8 * (n : ℝ)) + Real.log (1 / delta)) := by
    rw [← hlhs]
    exact hdv.trans (by rw [hmoment]; linarith)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hgap :
      posteriorPopulationRisk p ℓ ρ - posteriorEmpiricalRisk ℓ ρ S ≤
        (klDiv ρ prior + Real.log (1 / delta)) / lam + lam / (8 * (n : ℝ)) := by
    have hgap0 :
        posteriorPopulationRisk p ℓ ρ - posteriorEmpiricalRisk ℓ ρ S ≤
          (klDiv ρ prior + (lam ^ 2 / (8 * (n : ℝ)) + Real.log (1 / delta))) / lam := by
      rw [le_div_iff₀ hlam]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hgap_scaled
    calc
      posteriorPopulationRisk p ℓ ρ - posteriorEmpiricalRisk ℓ ρ S
          ≤ (klDiv ρ prior + (lam ^ 2 / (8 * (n : ℝ)) + Real.log (1 / delta))) / lam :=
            hgap0
      _ = (klDiv ρ prior + Real.log (1 / delta)) / lam + lam / (8 * (n : ℝ)) := by
            field_simp [hlam.ne', hn_ne]
            ring
  linarith

/--
Finite Catoni-style PAC-Bayes bad-event bound for `[0,1]` losses.

Equivalently: with finite product-sample mass at least `1 - delta`, every
finite posterior `ρ` satisfies

`R(ρ) ≤ Rhat_S(ρ) + (KL(ρ‖π) + log(1/delta)) / λ + λ/(8n)`.
-/
theorem finiteCatoni_badEventMass_le_delta
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ℓ : ι → Z → ℝ) (lam delta : ℝ)
    (hlam : 0 < lam) (hdelta : 0 < delta)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S +
                (klDiv ρ prior + Real.log (1 / delta)) / lam +
                lam / (8 * (n : ℝ))),
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  set threshold := Real.exp (lam ^ 2 / (8 * (n : ℝ))) / delta with hthreshold
  have hsubset :
      (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S +
                (klDiv ρ prior + Real.log (1 / delta)) / lam +
                lam / (8 * (n : ℝ)))
        ⊆
      (Finset.univ.filter fun S : Fin n → Z =>
        threshold ≤ priorDeviationMGF p prior ℓ lam S) := by
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    rcases hS.2 with ⟨ρ, hρ, hbad⟩
    refine ⟨Finset.mem_univ S, ?_⟩
    by_contra hnot
    have hconf : priorDeviationMGF p prior ℓ lam S ≤ threshold :=
      le_of_not_ge hnot
    have hbound :=
      posteriorRisk_bound_of_priorDeviationMGF_le
        hn p prior hprior ρ hρ ℓ S hlam hdelta (by simpa [threshold, hthreshold] using hconf)
    linarith
  have hnonneg :
      ∀ x ∈ (Finset.univ.filter fun S : Fin n → Z =>
        threshold ≤ priorDeviationMGF p prior ℓ lam S),
        0 ≤ finiteProductSampleWeight p x := by
    intro S _hS
    exact finiteProductSampleWeight_nonneg hp S
  have hmass_le :
      (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S +
                (klDiv ρ prior + Real.log (1 / delta)) / lam +
                lam / (8 * (n : ℝ))),
        finiteProductSampleWeight p S)
        ≤
      ∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        threshold ≤ priorDeviationMGF p prior ℓ lam S),
        finiteProductSampleWeight p S := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro S _hS _hnot
      exact finiteProductSampleWeight_nonneg hp S)
  have hmarkov :=
    priorAveraged_boundedLoss_mgf_badEventMass_le_delta
      hn p hp prior hprior.toIsPMF ℓ lam delta hdelta hℓ
  exact hmass_le.trans (by simpa [threshold, hthreshold] using hmarkov)

/-! ### Finite McAllester-style fixed-budget corollary -/

/--
The optimizer identity behind the fixed-budget McAllester-style corollary.

For a positive complexity budget `C`, choosing
`λ = sqrt(8 * n * C)` turns the Catoni penalty
`C / λ + λ / (8n)` into `sqrt(C / (2n))`.
-/
theorem catoni_fixedLambda_budget_eq_sqrt
    {n : ℕ} (hn : 0 < n) {complexityBound : ℝ}
    (hcomplexityBound : 0 < complexityBound) :
    complexityBound / Real.sqrt (8 * (n : ℝ) * complexityBound) +
        Real.sqrt (8 * (n : ℝ) * complexityBound) / (8 * (n : ℝ)) =
      Real.sqrt (complexityBound / (2 * (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have harg_pos : 0 < 8 * (n : ℝ) * complexityBound := by positivity
  have hlam_pos : 0 < Real.sqrt (8 * (n : ℝ) * complexityBound) :=
    Real.sqrt_pos_of_pos harg_pos
  have htarget_nonneg : 0 ≤ complexityBound / (2 * (n : ℝ)) := by positivity
  have hleft_nonneg :
      0 ≤ complexityBound / Real.sqrt (8 * (n : ℝ) * complexityBound) +
        Real.sqrt (8 * (n : ℝ) * complexityBound) / (8 * (n : ℝ)) := by
    positivity
  symm
  rw [Real.sqrt_eq_iff_eq_sq htarget_nonneg hleft_nonneg]
  rw [sq]
  field_simp [hlam_pos.ne', hnR.ne']
  rw [Real.sq_sqrt (by positivity : 0 ≤ complexityBound * (n : ℝ) * 8)]
  ring

/--
Deterministic finite McAllester-style square-root posterior-risk adapter.

This is still a fixed-sample statement. If the prior-deviation MGF certificate
holds at the optimized fixed `lambda = sqrt(8nC)` and a posterior has
`KL(ρ‖π) + log(1/δ) ≤ C`, then its posterior risk is bounded by
`Rhat_S(ρ) + sqrt(C/(2n))`.
-/
theorem posteriorRisk_bound_of_priorDeviationMGF_le_complexity_sqrt
    {n : ℕ} [Fintype Z] [Fintype ι] [Nonempty ι]
    (hn : 0 < n)
    (p : Z → ℝ)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ρ : ι → ℝ) (hρ : IsPMF ρ)
    (ℓ : ι → Z → ℝ) (S : Fin n → Z)
    {complexityBound delta : ℝ}
    (hcomplexityBound : 0 < complexityBound) (hdelta : 0 < delta)
    (hcomplexity :
      klDiv ρ prior + Real.log (1 / delta) ≤ complexityBound)
    (hconf :
      priorDeviationMGF p prior ℓ
          (Real.sqrt (8 * (n : ℝ) * complexityBound)) S ≤
        Real.exp
          ((Real.sqrt (8 * (n : ℝ) * complexityBound)) ^ 2 /
            (8 * (n : ℝ))) / delta) :
    posteriorPopulationRisk p ℓ ρ ≤
      posteriorEmpiricalRisk ℓ ρ S +
        Real.sqrt (complexityBound / (2 * (n : ℝ))) := by
  have hlam :
      0 < Real.sqrt (8 * (n : ℝ) * complexityBound) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact Real.sqrt_pos_of_pos (by positivity)
  have hcatoni :=
    posteriorRisk_bound_of_priorDeviationMGF_le
      hn p prior hprior ρ hρ ℓ S hlam hdelta hconf
  have hpenalty :
      (klDiv ρ prior + Real.log (1 / delta)) /
          Real.sqrt (8 * (n : ℝ) * complexityBound) +
        Real.sqrt (8 * (n : ℝ) * complexityBound) / (8 * (n : ℝ))
        ≤ Real.sqrt (complexityBound / (2 * (n : ℝ))) := by
    calc
      (klDiv ρ prior + Real.log (1 / delta)) /
          Real.sqrt (8 * (n : ℝ) * complexityBound) +
        Real.sqrt (8 * (n : ℝ) * complexityBound) / (8 * (n : ℝ))
          ≤
        complexityBound / Real.sqrt (8 * (n : ℝ) * complexityBound) +
          Real.sqrt (8 * (n : ℝ) * complexityBound) / (8 * (n : ℝ)) := by
          exact add_le_add
            (div_le_div_of_nonneg_right hcomplexity (le_of_lt hlam))
            (le_refl _)
      _ = Real.sqrt (complexityBound / (2 * (n : ℝ))) :=
          catoni_fixedLambda_budget_eq_sqrt hn hcomplexityBound
  linarith

/--
Finite McAllester-style bounded-complexity PAC-Bayes bad-event theorem.

For a fixed positive complexity budget `C`, finite product-sample mass at most
`δ` is assigned to samples where there exists a finite posterior `ρ` with
`KL(ρ‖π) + log(1/δ) ≤ C` but
`R(ρ) > Rhat_S(ρ) + sqrt(C/(2n))`.

This is a finite, fixed-budget corollary of the fixed-`lambda` Catoni-style
theorem. The finite-grid peeling theorems below remove the single fixed-budget
restriction while staying within finite samples, finite hypothesis classes, and
finite confidence grids.
-/
theorem finiteMcAllesterBoundedComplexity_badEventMass_le_delta
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ℓ : ι → Z → ℝ) {complexityBound delta : ℝ}
    (hcomplexityBound : 0 < complexityBound) (hdelta : 0 < delta)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            klDiv ρ prior + Real.log (1 / delta) ≤ complexityBound ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S +
                Real.sqrt (complexityBound / (2 * (n : ℝ)))),
        finiteProductSampleWeight p S) ≤ delta := by
  classical
  set lam := Real.sqrt (8 * (n : ℝ) * complexityBound) with hlam_def
  set threshold := Real.exp (lam ^ 2 / (8 * (n : ℝ))) / delta with hthreshold
  have hsubset :
      (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            klDiv ρ prior + Real.log (1 / delta) ≤ complexityBound ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S +
                Real.sqrt (complexityBound / (2 * (n : ℝ))))
        ⊆
      (Finset.univ.filter fun S : Fin n → Z =>
        threshold ≤ priorDeviationMGF p prior ℓ lam S) := by
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    rcases hS.2 with ⟨ρ, hρ, hcomplexity, hbad⟩
    refine ⟨Finset.mem_univ S, ?_⟩
    by_contra hnot
    have hconf : priorDeviationMGF p prior ℓ lam S ≤ threshold :=
      le_of_not_ge hnot
    have hbound :=
      posteriorRisk_bound_of_priorDeviationMGF_le_complexity_sqrt
        hn p prior hprior ρ hρ ℓ S hcomplexityBound hdelta hcomplexity
        (by simpa [lam, hlam_def, threshold, hthreshold] using hconf)
    linarith
  have hmass_le :
      (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            klDiv ρ prior + Real.log (1 / delta) ≤ complexityBound ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S +
                Real.sqrt (complexityBound / (2 * (n : ℝ)))),
        finiteProductSampleWeight p S)
        ≤
      ∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        threshold ≤ priorDeviationMGF p prior ℓ lam S),
        finiteProductSampleWeight p S := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro S _hS _hnot
      exact finiteProductSampleWeight_nonneg hp S)
  have hmarkov :=
    priorAveraged_boundedLoss_mgf_badEventMass_le_delta
      hn p hp prior hprior.toIsPMF ℓ lam delta hdelta hℓ
  exact hmass_le.trans (by simpa [threshold, hthreshold] using hmarkov)

/-! ### Finite-grid peeling over McAllester budgets -/

/--
Samples where some posterior in one finite McAllester budget bucket violates
the corresponding square-root bound.

The bucket is parameterized by a positive complexity budget and its own
confidence allocation. Positivity is required by the theorem using this event,
not by the event definition itself.
-/
def finiteMcAllesterBucketBadSamples
    {n : ℕ} [Fintype Z] [Fintype ι]
    (p : Z → ℝ) (prior : ι → ℝ) (ℓ : ι → Z → ℝ)
    (complexityBound confidence : ℝ) : Finset (Fin n → Z) :=
  Finset.univ.filter fun S : Fin n → Z =>
    ∃ ρ : ι → ℝ,
      IsPMF ρ ∧
        klDiv ρ prior + Real.log (1 / confidence) ≤ complexityBound ∧
        posteriorPopulationRisk p ℓ ρ >
          posteriorEmpiricalRisk ℓ ρ S +
            Real.sqrt (complexityBound / (2 * (n : ℝ)))

/--
Samples where some posterior violates at least one bucket in a finite
McAllester grid.

This is a finite-grid/peeling event: each grid index supplies a complexity
budget and a confidence allocation. It is not an all-real-`lambda` confidence
statement.
-/
def finiteMcAllesterGridPeelingBadSamples
    {n : ℕ} [Fintype Z] [Fintype ι] [Fintype γ]
    (p : Z → ℝ) (prior : ι → ℝ) (ℓ : ι → Z → ℝ)
    (complexityBound confidenceOf : γ → ℝ) : Finset (Fin n → Z) :=
  Finset.univ.filter fun S : Fin n → Z =>
    ∃ g : γ, ∃ ρ : ι → ℝ,
      IsPMF ρ ∧
        klDiv ρ prior + Real.log (1 / confidenceOf g) ≤ complexityBound g ∧
        posteriorPopulationRisk p ℓ ρ >
          posteriorEmpiricalRisk ℓ ρ S +
            Real.sqrt (complexityBound g / (2 * (n : ℝ)))

/--
Finite-grid peeling McAllester-style bad-event bound for `[0,1]` losses.

For each grid index `g`, the fixed-budget McAllester theorem is applied with
budget `complexityBound g` and confidence allocation `confidenceOf g`. A finite
weighted union bound then controls the mass of samples on which any bucket
fails. This removes the single fixed-budget restriction while remaining
finite-sample, finite-class, finite-grid, and scalar-valued.
-/
theorem finiteMcAllesterGridPeeling_badEventMass_le_sum_delta
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] [Fintype γ] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ℓ : ι → Z → ℝ)
    (complexityBound confidenceOf : γ → ℝ)
    (hcomplexityBound : ∀ g : γ, 0 < complexityBound g)
    (hconfidenceOf : ∀ g : γ, 0 < confidenceOf g)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S ∈
        finiteMcAllesterGridPeelingBadSamples (n := n) p prior ℓ complexityBound confidenceOf,
        finiteProductSampleWeight (n := n) p S) ≤
      ∑ g : γ, confidenceOf g := by
  classical
  let bucketEvent : γ → Finset (Fin n → Z) := fun g =>
    finiteMcAllesterBucketBadSamples (n := n) p prior ℓ (complexityBound g) (confidenceOf g)
  let gridUnionEvent : Finset (Fin n → Z) :=
    Finset.univ.filter fun S : Fin n → Z => ∃ g : γ, S ∈ bucketEvent g
  have hsubset :
      finiteMcAllesterGridPeelingBadSamples (n := n) p prior ℓ complexityBound confidenceOf ⊆
        gridUnionEvent := by
    intro S hS
    rw [finiteMcAllesterGridPeelingBadSamples, Finset.mem_filter] at hS
    rcases hS.2 with ⟨g, ρ, hρ, hcomplexity, hbad⟩
    change S ∈ (Finset.univ.filter fun S : Fin n → Z => ∃ g : γ, S ∈ bucketEvent g)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ S, g, ?_⟩
    change S ∈ finiteMcAllesterBucketBadSamples (n := n) p prior ℓ
      (complexityBound g) (confidenceOf g)
    rw [finiteMcAllesterBucketBadSamples, Finset.mem_filter]
    exact ⟨Finset.mem_univ S, ρ, hρ, hcomplexity, hbad⟩
  have hmass_subset :
      (∑ S ∈
          finiteMcAllesterGridPeelingBadSamples (n := n) p prior ℓ complexityBound confidenceOf,
          finiteProductSampleWeight (n := n) p S) ≤
        ∑ S ∈ gridUnionEvent,
          finiteProductSampleWeight (n := n) p S := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro S _hS _hnot
      exact finiteProductSampleWeight_nonneg hp S)
  have hunion :=
    FormalSLT.Probability.FiniteUnionBound.finiteProbabilityUnionBound_proof
      (support := (Finset.univ : Finset (Fin n → Z)))
      (w := fun S : Fin n → Z => finiteProductSampleWeight (n := n) p S)
      (events := bucketEvent)
      (s := (Finset.univ : Finset γ))
      (fun S : Fin n → Z => finiteProductSampleWeight_nonneg hp S)
  have hunion_mass :
      (∑ S ∈ gridUnionEvent,
          finiteProductSampleWeight (n := n) p S) ≤
        ∑ g : γ, ∑ S ∈ bucketEvent g, finiteProductSampleWeight (n := n) p S := by
    change
      (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z => ∃ g : γ, S ∈ bucketEvent g),
          finiteProductSampleWeight (n := n) p S) ≤
        ∑ g : γ, ∑ S ∈ bucketEvent g, finiteProductSampleWeight (n := n) p S
    unfold FormalSLT.Probability.FiniteUnionBound.finiteUnionEventMass at hunion
    unfold FormalSLT.Probability.FiniteUnionBound.finiteEventMassSum at hunion
    unfold FormalSLT.Probability.FiniteUnionBound.finiteEventMass at hunion
    simp_rw [← Finset.sum_filter] at hunion
    simpa using hunion
  have hbucket :
      ∀ g : γ,
        (∑ S ∈ bucketEvent g, finiteProductSampleWeight (n := n) p S) ≤ confidenceOf g := by
    intro g
    simpa [bucketEvent, finiteMcAllesterBucketBadSamples] using
      finiteMcAllesterBoundedComplexity_badEventMass_le_delta
        (n := n) (Z := Z) (ι := ι) hn p hp prior hprior ℓ
        (hcomplexityBound g) (hconfidenceOf g) hℓ
  have hbucket_sum :
      (∑ g : γ, ∑ S ∈ bucketEvent g, finiteProductSampleWeight (n := n) p S) ≤
        ∑ g : γ, confidenceOf g := by
    exact Finset.sum_le_sum (fun g _hg => hbucket g)
  exact hmass_subset.trans (hunion_mass.trans hbucket_sum)

/--
Finite-grid peeling McAllester-style bad-event bound with an explicit total
confidence budget.
-/
theorem finiteMcAllesterGridPeeling_badEventMass_le_delta
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] [Fintype γ] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ℓ : ι → Z → ℝ)
    (complexityBound confidenceOf : γ → ℝ)
    (hcomplexityBound : ∀ g : γ, 0 < complexityBound g)
    (hconfidenceOf : ∀ g : γ, 0 < confidenceOf g)
    {delta : ℝ} (hgridConfidence : (∑ g : γ, confidenceOf g) ≤ delta)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S ∈
        finiteMcAllesterGridPeelingBadSamples (n := n) p prior ℓ complexityBound confidenceOf,
        finiteProductSampleWeight (n := n) p S) ≤ delta :=
  (finiteMcAllesterGridPeeling_badEventMass_le_sum_delta
    (n := n) (Z := Z) (ι := ι) (γ := γ)
    hn p hp prior hprior ℓ complexityBound confidenceOf
    hcomplexityBound hconfidenceOf hℓ).trans hgridConfidence

/--
Finite-grid optimized McAllester-style bad-event bound.

The user-supplied `posteriorPenalty` may depend on the posterior. The theorem
requires a finite grid certificate: every posterior PMF must be assigned to a
grid bucket whose complexity budget is large enough and whose square-root
bucket penalty is no larger than `posteriorPenalty`. Under that finite
certificate, the bad-event mass is controlled by the sum of the bucket
confidence allocations.
-/
theorem finiteMcAllesterGridOptimized_badEventMass_le_sum_delta
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] [Fintype γ] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ℓ : ι → Z → ℝ)
    (complexityBound confidenceOf : γ → ℝ)
    (posteriorPenalty : (ι → ℝ) → ℝ)
    (hcomplexityBound : ∀ g : γ, 0 < complexityBound g)
    (hconfidenceOf : ∀ g : γ, 0 < confidenceOf g)
    (hgridCovers :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        ∃ g : γ,
          klDiv ρ prior + Real.log (1 / confidenceOf g) ≤ complexityBound g ∧
          Real.sqrt (complexityBound g / (2 * (n : ℝ))) ≤ posteriorPenalty ρ)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S + posteriorPenalty ρ),
        finiteProductSampleWeight (n := n) p S) ≤
      ∑ g : γ, confidenceOf g := by
  classical
  have hsubset :
      (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S + posteriorPenalty ρ)
        ⊆
      finiteMcAllesterGridPeelingBadSamples (n := n) p prior ℓ complexityBound confidenceOf := by
    intro S hS
    rw [Finset.mem_filter] at hS
    rcases hS.2 with ⟨ρ, hρ, hbad⟩
    rcases hgridCovers ρ hρ with ⟨g, hcomplexity, hpenalty⟩
    rw [finiteMcAllesterGridPeelingBadSamples, Finset.mem_filter]
    refine ⟨Finset.mem_univ S, g, ρ, hρ, hcomplexity, ?_⟩
    linarith
  have hmass_subset :
      (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S + posteriorPenalty ρ),
        finiteProductSampleWeight (n := n) p S) ≤
      ∑ S ∈ finiteMcAllesterGridPeelingBadSamples (n := n) p prior ℓ complexityBound confidenceOf,
        finiteProductSampleWeight (n := n) p S := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro S _hS _hnot
      exact finiteProductSampleWeight_nonneg hp S)
  exact hmass_subset.trans
    (finiteMcAllesterGridPeeling_badEventMass_le_sum_delta
      (n := n) (Z := Z) (ι := ι) (γ := γ)
      hn p hp prior hprior ℓ complexityBound confidenceOf
      hcomplexityBound hconfidenceOf hℓ)

/--
Finite-grid optimized McAllester-style bad-event bound with an explicit total
confidence budget.
-/
theorem finiteMcAllesterGridOptimized_badEventMass_le_delta
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] [Fintype γ] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ℓ : ι → Z → ℝ)
    (complexityBound confidenceOf : γ → ℝ)
    (posteriorPenalty : (ι → ℝ) → ℝ)
    (hcomplexityBound : ∀ g : γ, 0 < complexityBound g)
    (hconfidenceOf : ∀ g : γ, 0 < confidenceOf g)
    (hgridCovers :
      ∀ ρ : ι → ℝ, IsPMF ρ →
        ∃ g : γ,
          klDiv ρ prior + Real.log (1 / confidenceOf g) ≤ complexityBound g ∧
          Real.sqrt (complexityBound g / (2 * (n : ℝ))) ≤ posteriorPenalty ρ)
    {delta : ℝ} (hgridConfidence : (∑ g : γ, confidenceOf g) ≤ delta)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    (∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∃ ρ : ι → ℝ,
          IsPMF ρ ∧
            posteriorPopulationRisk p ℓ ρ >
              posteriorEmpiricalRisk ℓ ρ S + posteriorPenalty ρ),
        finiteProductSampleWeight (n := n) p S) ≤ delta :=
  (finiteMcAllesterGridOptimized_badEventMass_le_sum_delta
    (n := n) (Z := Z) (ι := ι) (γ := γ)
    hn p hp prior hprior ℓ complexityBound confidenceOf posteriorPenalty
    hcomplexityBound hconfidenceOf hgridCovers hℓ).trans hgridConfidence

/-! ### Closed PAC-Bayes generalization payoff -/

/--
Total iid product sample weight equals one when the data mass function sums
to one. This is the discrete-product analogue of `(∫ 1) = 1` and complements
the bad-event bounds above into high-confidence (`≥ 1 - δ`) statements.
-/
private lemma finiteProductSampleWeight_sum_eq_one'
    {n : ℕ} [Fintype Z] {p : Z → ℝ} (hp : IsPMF p) :
    (∑ S : Fin n → Z, finiteProductSampleWeight p S) = 1 := by
  unfold finiteProductSampleWeight
  calc
    (∑ S : Fin n → Z, ∏ k : Fin n, p (S k))
        = ∏ _k : Fin n, ∑ z : Z, p z :=
          (Fintype.prod_sum (f := fun _k : Fin n => p)).symm
    _ = 1 := by simp [hp.sum_one]

/--
**Closed PAC-Bayes generalization payoff** (Catoni form, `[0,1]` losses).

For finite `[0,1]` losses on a finite hypothesis class with full-support
prior `π`, a finite data domain, and any fixed `λ > 0` and `δ ∈ (0,1]`,
the iid product-sample mass of the *good event* — every posterior `ρ` (PMF
on the hypothesis class) simultaneously satisfies

  `R(ρ) ≤ R̂_S(ρ) + (KL(ρ‖π) + log(1/δ)) / λ + λ / (8 n)`

— is at least `1 - δ`:

  `∑_{S : Fin n → Z, good_event holds} ∏_k p(S k)  ≥  1 - δ`.

This is the high-confidence form of `finiteCatoni_badEventMass_le_delta`,
obtained by complementing the bad event against the total iid product mass
`∑ ∏ p (S k) = 1`. The textbook reading is

> with probability at least `1 - δ` over the iid sample `S ~ p^{⊗ n}`,
> every posterior `ρ` satisfies `R(ρ) ≤ R̂_S(ρ) + (KL(ρ‖π) + log(1/δ))/λ +
> λ/(8 n)`.

The constants are explicit in the statement: the `log(1/δ)` term is the
Markov/confidence cost, `KL(ρ‖π)/λ` is the change-of-measure cost, and
`λ/(8 n)` is the sub-Gaussian Hoeffding penalty for `[0,1]` losses
averaged over `n` iid samples.

Source: McAllester (1999, 2003); Catoni (2007) §1.1.
-/
theorem pac_bayes_generalization
    {n : ℕ} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype ι] [Nonempty ι] (hn : 0 < n)
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : ι → ℝ) (hprior : IsFullSupportPMF prior)
    (ℓ : ι → Z → ℝ) (lam delta : ℝ)
    (hlam : 0 < lam) (hdelta : 0 < delta)
    (hℓ : ∀ i : ι, ∀ z : Z, 0 ≤ ℓ i z ∧ ℓ i z ≤ 1) :
    1 - delta ≤
      ∑ S ∈ (Finset.univ.filter fun S : Fin n → Z =>
        ∀ ρ : ι → ℝ, IsPMF ρ →
          posteriorPopulationRisk p ℓ ρ ≤
            posteriorEmpiricalRisk ℓ ρ S +
              (klDiv ρ prior + Real.log (1 / delta)) / lam +
              lam / (8 * (n : ℝ))),
        finiteProductSampleWeight p S := by
  classical
  set badPred : (Fin n → Z) → Prop := fun S =>
    ∃ ρ : ι → ℝ,
      IsPMF ρ ∧
        posteriorPopulationRisk p ℓ ρ >
          posteriorEmpiricalRisk ℓ ρ S +
            (klDiv ρ prior + Real.log (1 / delta)) / lam +
            lam / (8 * (n : ℝ)) with hbadPred_def
  set goodPred : (Fin n → Z) → Prop := fun S =>
    ∀ ρ : ι → ℝ, IsPMF ρ →
      posteriorPopulationRisk p ℓ ρ ≤
        posteriorEmpiricalRisk ℓ ρ S +
          (klDiv ρ prior + Real.log (1 / delta)) / lam +
          lam / (8 * (n : ℝ)) with hgoodPred_def
  have hcompl : ∀ S, goodPred S ↔ ¬ badPred S := by
    intro S
    refine ⟨?_, ?_⟩
    · rintro hgood ⟨ρ, hρ, hgt⟩
      exact (not_lt.mpr (hgood ρ hρ)) hgt
    · intro hnotbad ρ hρ
      by_contra hgt
      push Not at hgt
      exact hnotbad ⟨ρ, hρ, hgt⟩
  have hdisj :
      Disjoint (Finset.univ.filter badPred) (Finset.univ.filter goodPred) := by
    rw [Finset.disjoint_filter]
    intro S _hS hbad hgood
    exact ((hcompl S).mp hgood) hbad
  have hcover :
      (Finset.univ : Finset (Fin n → Z)) =
        Finset.univ.filter badPred ∪ Finset.univ.filter goodPred := by
    ext S
    refine ⟨fun _ => ?_, fun _ => Finset.mem_univ S⟩
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h : badPred S
    · exact Or.inl ⟨Finset.mem_univ S, h⟩
    · exact Or.inr ⟨Finset.mem_univ S, (hcompl S).mpr h⟩
  have htotal :
      (∑ S : Fin n → Z, finiteProductSampleWeight p S) = 1 :=
    finiteProductSampleWeight_sum_eq_one' (n := n) hp
  have hsum_split :
      (∑ S : Fin n → Z, finiteProductSampleWeight p S) =
        (∑ S ∈ Finset.univ.filter badPred, finiteProductSampleWeight p S) +
          (∑ S ∈ Finset.univ.filter goodPred, finiteProductSampleWeight p S) := by
    have hunion :=
      Finset.sum_union (s₁ := Finset.univ.filter badPred)
        (s₂ := Finset.univ.filter goodPred)
        (f := fun S => finiteProductSampleWeight p S) hdisj
    calc
      (∑ S : Fin n → Z, finiteProductSampleWeight p S)
          = ∑ S ∈ (Finset.univ : Finset (Fin n → Z)),
              finiteProductSampleWeight p S := rfl
      _ = ∑ S ∈ (Finset.univ.filter badPred ∪ Finset.univ.filter goodPred),
              finiteProductSampleWeight p S := by rw [← hcover]
      _ = (∑ S ∈ Finset.univ.filter badPred, finiteProductSampleWeight p S) +
              (∑ S ∈ Finset.univ.filter goodPred, finiteProductSampleWeight p S) :=
            hunion
  have hbad :
      (∑ S ∈ Finset.univ.filter badPred, finiteProductSampleWeight p S) ≤ delta :=
    finiteCatoni_badEventMass_le_delta
      (n := n) (Z := Z) (ι := ι) hn p hp prior hprior ℓ lam delta hlam hdelta hℓ
  linarith

end

end FormalSLT.PACBayesBoundedLoss
