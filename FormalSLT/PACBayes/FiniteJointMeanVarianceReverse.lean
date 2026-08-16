/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseExponential
import FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
import FormalSLT.PACBayes.FiniteProductMeasureBridge

/-!
# Reverse-time mean and Bessel-variance structure

This module develops the second load-bearing reverse-martingale coordinate
needed for a joint time-uniform empirical-Bernstein PAC-Bayes argument.  The
sample mean of a prefix is proved to be the conditional expectation of the
mean of the preceding prefix under the same exchangeable reverse filtration
used by Bessel variance.

The proof derives the leave-one-out mean identity and its conditional-
expectation consequence.  No martingale or conditional-MGF interface is
assumed.  The fixed-horizon joint exponential and PAC-Bayes layers are built
downstream.
-/

namespace FormalSLT.PACBayes.FiniteJointMeanVarianceReverse

open Finset BigOperators MeasureTheory
open FormalSLT.Statistics
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
open FormalSLT.PACBayes.FiniteProductMeasureBridge
open FormalSLT.Concentration.SubGamma

noncomputable section

/-- **Leave-one-out mean identity.**  The mean of `n + 1` observations is the
average of the means obtained by deleting one observation. -/
theorem sampleMean_eq_average_eraseCoordinate {n : ℕ} (hn : 0 < n)
    (x : Fin (n + 1) → ℝ) :
    sampleMean x =
      (∑ r : Fin (n + 1), sampleMean (eraseCoordinate r x)) /
        (n + 1 : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsuccR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have herase (r : Fin (n + 1)) :
      (∑ k : Fin n, x (r.succAbove k)) =
        (∑ i : Fin (n + 1), x i) - x r := by
    have h := Fin.sum_univ_succAbove x r
    linarith
  unfold sampleMean
  simp only [eraseCoordinate]
  simp_rw [herase]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num [Nat.cast_add]
  field_simp [hnR, hsuccR]
  ring

section ExchangeableMean

variable {Z : Type*} [MeasurableSpace Z]

/-- Mean of the losses in the first `t` coordinates of a horizon sample. -/
def prefixSampleMean {N t : ℕ} (ht : t ≤ N) (ell : Z → ℝ)
    (x : Fin N → Z) : ℝ :=
  sampleMean (fun k ↦ ell (samplePrefix ht x k))

omit [MeasurableSpace Z] in
theorem prefixSampleMean_eq_finiteEmpiricalRisk {N t : ℕ} (ht : t ≤ N)
    (ell : ι → Z → ℝ) (i : ι) (x : Fin N → Z) :
    prefixSampleMean ht (ell i) x =
      finiteEmpiricalRisk ell i (samplePrefix ht x) := by
  simp only [prefixSampleMean, sampleMean, finiteEmpiricalRisk, div_eq_inv_mul]

omit [MeasurableSpace Z] in
theorem prefixBesselVariance_eq_finiteEmpiricalVariance {N t : ℕ}
    (ht : t ≤ N) (ell : ι → Z → ℝ) (i : ι) (x : Fin N → Z) :
    prefixBesselVariance ht (ell i) x =
      finiteEmpiricalVariance ell i (samplePrefix ht x) := by
  rfl

/-- A prefix mean is invariant under every horizon permutation supported on
that prefix. -/
theorem prefixSampleMean_samplePermutation {N t : ℕ} (ht : t ≤ N)
    (ell : Z → ℝ) (x : Fin N → Z) (sigma : Equiv.Perm (Fin N))
    (hsigma : ∀ k : Fin N, t ≤ k.1 → sigma k = k) :
    prefixSampleMean ht ell (samplePermutation sigma x) =
      prefixSampleMean ht ell x := by
  let tau := restrictPrefixPermutation ht sigma hsigma
  let y : Fin t → ℝ := fun k ↦ ell (samplePrefix ht x k)
  have hperm : sampleMean (y ∘ tau) = sampleMean y := by
    unfold sampleMean
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp tau y]
  unfold prefixSampleMean
  rw [← hperm]
  congr 1
  funext k
  simp only [Function.comp_apply, samplePrefix, samplePermutation_apply,
    y, tau]
  rw [castLE_restrictPrefixPermutation]

/-- The prefix mean is measurable for the exchangeable reverse sigma algebra
at the same prefix size. -/
theorem measurable_prefixSampleMean [Fintype Z] [MeasurableSingletonClass Z]
    {N t : ℕ} (ht : t ≤ N) (ell : Z → ℝ) :
    Measurable[prefixExchangeableSpace (Z := Z) N t]
      (prefixSampleMean ht ell) := by
  intro s hs
  rw [measurableSet_prefixExchangeableSpace_iff]
  refine ⟨(measurable_of_finite (prefixSampleMean ht ell)) hs, fun sigma ↦ ?_⟩
  ext x
  simp only [Set.mem_preimage]
  rw [prefixSampleMean_samplePermutation ht ell x
    (sigma : Equiv.Perm (Fin N)) sigma.property]

/-- Leave-one-out mean identity inside a common horizon sample space. -/
theorem prefixSampleMean_eq_average_horizonDeletion {N n : ℕ}
    (hn : 0 < n) (h : n + 1 ≤ N) (ell : Z → ℝ) (x : Fin N → Z) :
    prefixSampleMean h ell x =
      (∑ r : Fin (n + 1),
          prefixSampleMean ((Nat.le_succ n).trans h) ell
            (samplePermutation (horizonDeletionPermutation h r) x)) /
        (n + 1 : ℝ) := by
  have hmean := sampleMean_eq_average_eraseCoordinate hn
    (fun k ↦ ell (samplePrefix h x k))
  unfold prefixSampleMean
  rw [hmean]
  congr 1
  refine Finset.sum_congr rfl (fun r _ ↦ ?_)
  rw [samplePrefix_samplePermutation_horizonDeletion h r x]
  rfl

/-- Set-integral identity for one reverse conditional-expectation step of the
prefix mean under a finite iid law. -/
theorem setIntegral_prefixSampleMean_succ_eq [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    {N n : ℕ} (hn : 0 < n) (h : n + 1 ≤ N) (ell : Z → ℝ)
    {s : Set (Fin N → Z)}
    (hs : MeasurableSet[prefixExchangeableSpace (Z := Z) N (n + 1)] s) :
    ∫ x in s, prefixSampleMean h ell x
        ∂(Measure.pi (fun _ : Fin N ↦ mu)) =
      ∫ x in s, prefixSampleMean ((Nat.le_succ n).trans h) ell x
        ∂(Measure.pi (fun _ : Fin N ↦ mu)) := by
  let muN : Measure (Fin N → Z) := Measure.pi (fun _ : Fin N ↦ mu)
  have hs' : MeasurableSet s :=
    (measurableSet_prefixExchangeableSpace_iff.mp hs).1
  have hinv (r : Fin (n + 1)) :
      samplePermutation (horizonDeletionPermutation h r) ⁻¹' s = s := by
    exact (measurableSet_prefixExchangeableSpace_iff.mp hs).2
      (horizonDeletionPrefixPermutation h r)
  have hint (r : Fin (n + 1)) :
      Integrable
        (fun x : Fin N → Z ↦
          prefixSampleMean ((Nat.le_succ n).trans h) ell
            (samplePermutation (horizonDeletionPermutation h r) x))
        (muN.restrict s) :=
    Integrable.of_finite
  calc
    ∫ x in s, prefixSampleMean h ell x ∂muN =
        ∫ x in s,
          ((∑ r : Fin (n + 1),
              prefixSampleMean ((Nat.le_succ n).trans h) ell
                (samplePermutation (horizonDeletionPermutation h r) x)) /
            (n + 1 : ℝ)) ∂muN := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (prefixSampleMean_eq_average_horizonDeletion hn h ell)
    _ = (∑ r : Fin (n + 1),
          ∫ x in s,
            prefixSampleMean ((Nat.le_succ n).trans h) ell
              (samplePermutation (horizonDeletionPermutation h r) x) ∂muN) /
          (n + 1 : ℝ) := by
            rw [integral_div]
            rw [integral_finsetSum Finset.univ (fun r _ ↦ hint r)]
    _ = (∑ _r : Fin (n + 1),
          ∫ x in s,
            prefixSampleMean ((Nat.le_succ n).trans h) ell x ∂muN) /
          (n + 1 : ℝ) := by
            apply congrArg (fun z : ℝ ↦ z / (n + 1 : ℝ))
            refine Finset.sum_congr rfl (fun r _ ↦ ?_)
            exact setIntegral_comp_samplePermutation_eq mu
              (horizonDeletionPermutation h r)
              (prefixSampleMean ((Nat.le_succ n).trans h) ell) hs' (hinv r)
    _ = ∫ x in s,
          prefixSampleMean ((Nat.le_succ n).trans h) ell x ∂muN := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            have hne : (n + 1 : ℝ) ≠ 0 := by positivity
            norm_num [Nat.cast_add]
            exact mul_div_cancel_left₀ _ hne

/-- **Load-bearing reverse conditional-expectation step for the sample
mean.**  Under a finite iid product law, the mean of the first `n + 1`
observations is the conditional expectation of the mean of the first `n`
observations given the exchangeable prefix sigma algebra. -/
theorem prefixSampleMean_ae_eq_condExp [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    {N n : ℕ} (hn : 0 < n) (h : n + 1 ≤ N) (ell : Z → ℝ) :
    prefixSampleMean h ell =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (prefixExchangeableSpace (Z := Z) N (n + 1))
        (Measure.pi (fun _ : Fin N ↦ mu))
        (prefixSampleMean ((Nat.le_succ n).trans h) ell) := by
  let muN : Measure (Fin N → Z) := Measure.pi (fun _ : Fin N ↦ mu)
  haveI : IsProbabilityMeasure muN := by
    dsimp [muN]
    infer_instance
  have hsource : Integrable
      (prefixSampleMean ((Nat.le_succ n).trans h) ell) muN :=
    Integrable.of_finite
  have hcandidate : Integrable (prefixSampleMean h ell) muN :=
    Integrable.of_finite
  have hm := prefixExchangeableSpace_le (Z := Z) N (n + 1)
  change prefixSampleMean h ell =ᵐ[muN]
    condExp (prefixExchangeableSpace (Z := Z) N (n + 1)) muN
      (prefixSampleMean ((Nat.le_succ n).trans h) ell)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hsource
    (fun _s _hs _hfinite ↦ hcandidate.integrableOn)
    (fun s hs _hfinite ↦ ?_)
    (measurable_prefixSampleMean h ell).aestronglyMeasurable
  exact setIntegral_prefixSampleMean_succ_eq mu hn h ell hs

/-! ### The reverse prefix-mean martingale -/

/-- Prefix mean along the same reverse sample-size schedule as the Bessel
variance process. -/
def reverseMeanProcess (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) :
    ℕ → (Fin N → Z) → ℝ :=
  fun k ↦ prefixSampleMean (reverseBesselPrefixSize_le hN k) ell

theorem reverseMeanProcess_stronglyAdapted [Fintype Z]
    [MeasurableSingletonClass Z] (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) :
    StronglyAdapted (reverseBesselFiltration (Z := Z) N)
      (reverseMeanProcess N hN ell) := by
  intro k
  exact (measurable_prefixSampleMean
    (reverseBesselPrefixSize_le hN k) ell).stronglyMeasurable

omit [MeasurableSpace Z] in
private theorem prefixSampleMean_eq_of_size_eq {N t u : ℕ}
    (ht : t ≤ N) (hu : u ≤ N) (ell : Z → ℝ) (htu : t = u) :
    prefixSampleMean ht ell = prefixSampleMean hu ell := by
  subst u
  rfl

omit [MeasurableSpace Z] in
/-- At reverse time `N - m`, the mean process is exactly the mean of the first
`m` observations. -/
theorem reverseMeanProcess_sub_eq_prefix {N m : ℕ} (hN : 2 ≤ N)
    (hm : 2 ≤ m) (hmN : m ≤ N) (ell : Z → ℝ) (x : Fin N → Z) :
    reverseMeanProcess N hN ell (N - m) x =
      prefixSampleMean hmN ell x := by
  unfold reverseMeanProcess
  exact congrFun (prefixSampleMean_eq_of_size_eq _ _ ell
    (reverseBesselPrefixSize_sub_eq hm hmN)) x

private theorem prefixSampleMean_ae_eq_condExp_of_succ_eq [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    {N t u : ℕ} (hu_pos : 0 < u) (ht : t ≤ N) (hu : u ≤ N)
    (ell : Z → ℝ) (hsucc : u + 1 = t) :
    prefixSampleMean ht ell =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (prefixExchangeableSpace (Z := Z) N t)
        (Measure.pi (fun _ : Fin N ↦ mu))
        (prefixSampleMean hu ell) := by
  subst t
  simpa only using prefixSampleMean_ae_eq_condExp mu hu_pos ht ell

theorem reverseMeanProcess_ae_eq_condExp_succ [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) (k : ℕ) :
    reverseMeanProcess N hN ell k =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (reverseBesselFiltration (Z := Z) N k)
        (Measure.pi (fun _ : Fin N ↦ mu))
        (reverseMeanProcess N hN ell (k + 1)) := by
  let t := reverseBesselPrefixSize N k
  let u := reverseBesselPrefixSize N (k + 1)
  have hu_two : 2 ≤ u := reverseBesselPrefixSize_two_le N (k + 1)
  have htN : t ≤ N := reverseBesselPrefixSize_le hN k
  have huN : u ≤ N := reverseBesselPrefixSize_le hN (k + 1)
  have hut : u ≤ t := reverseBesselPrefixSize_antitone N (Nat.le_succ k)
  by_cases ht : t = 2
  · have hu : u = 2 := le_antisymm (ht ▸ hut) hu_two
    have hsame :
        reverseMeanProcess N hN ell (k + 1) =
          reverseMeanProcess N hN ell k := by
      have hsize : reverseBesselPrefixSize N (k + 1) =
          reverseBesselPrefixSize N k := hu.trans ht.symm
      unfold reverseMeanProcess
      exact prefixSampleMean_eq_of_size_eq _ _ ell hsize
    rw [hsame]
    rw [condExp_of_stronglyMeasurable
      ((reverseBesselFiltration (Z := Z) N).le k)
      (reverseMeanProcess_stronglyAdapted N hN ell k)
      Integrable.of_finite]
  · have hsucc : u + 1 = t := by
      dsimp [t, u, reverseBesselPrefixSize] at *
      omega
    change prefixSampleMean htN ell =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (prefixExchangeableSpace (Z := Z) N t)
        (Measure.pi (fun _ : Fin N ↦ mu))
        (prefixSampleMean huN ell)
    exact prefixSampleMean_ae_eq_condExp_of_succ_eq mu
      (lt_of_lt_of_le (by norm_num) hu_two) htN huN ell hsucc

/-- **Finite-horizon reverse mean martingale.**  Prefix means at sizes
`N, N - 1, ..., 2`, followed by a constant tail, form a martingale under the
finite iid product law. -/
theorem reverseMeanProcess_martingale [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) :
    Martingale (reverseMeanProcess N hN ell)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  exact martingale_nat
    (reverseMeanProcess_stronglyAdapted N hN ell)
    (fun _ ↦ Integrable.of_finite)
    (reverseMeanProcess_ae_eq_condExp_succ mu N hN ell)

/-! ### The joint reverse mean--Bessel process -/

/-- Fixed-endpoint normalized joint mean/Bessel score along reverse prefix
time.  Its value at reverse time `N - m` is exactly the checked fixed-`m`
joint score. -/
def reverseJointMeanVarianceEpochScore [Fintype Z]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ)
    (i : ι) : ℕ → (Fin N → Z) → ℝ :=
  fun k x ↦
    t * (m : ℝ) *
        (finitePopulationRisk p ell i - reverseMeanProcess N hN (ell i) k x) -
      eta * (m : ℝ) * reverseBesselProcess N hN (ell i) k x -
      (m : ℝ) * Real.log
        (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell i) +
      Real.exp (-t) * finiteJointMeanVarianceKappa m eta *
        finitePopulationVariance p ell i

/-- The joint reverse score is a martingale because its two moving
coordinates, prefix mean and Bessel variance, are martingales on the same
exchangeable filtration. -/
theorem reverseJointMeanVarianceEpochScore_martingale [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ) (i : ι) :
    Martingale
      (reverseJointMeanVarianceEpochScore N hN m p ell t eta i)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  let filt := reverseBesselFiltration (Z := Z) N
  let muN := Measure.pi (fun _ : Fin N ↦ mu)
  let R := finitePopulationRisk p ell i
  let V := finitePopulationVariance p ell i
  let logPenalty := (m : ℝ) * Real.log
    (1 + (Real.exp t - 1 - t) * V)
  let varianceCorrection :=
    Real.exp (-t) * finiteJointMeanVarianceKappa m eta * V
  have hmean : Martingale (reverseMeanProcess N hN (ell i)) filt muN :=
    reverseMeanProcess_martingale mu N hN (ell i)
  have hvariance : Martingale (reverseBesselProcess N hN (ell i)) filt muN :=
    reverseBesselProcess_martingale mu N hN (ell i)
  have hR : Martingale (fun _ _ ↦ R) filt muN :=
    martingale_const filt muN R
  have hlog : Martingale (fun _ _ ↦ logPenalty) filt muN :=
    martingale_const filt muN logPenalty
  have hcorrection : Martingale (fun _ _ ↦ varianceCorrection) filt muN :=
    martingale_const filt muN varianceCorrection
  have hscore :=
    (((hR.sub hmean).smul (t * (m : ℝ))).sub
      (hvariance.smul (eta * (m : ℝ)))).sub hlog |>.add hcorrection
  change Martingale
    (reverseJointMeanVarianceEpochScore N hN m p ell t eta i) filt muN
  convert hscore using 1
  funext k x
  simp only [reverseJointMeanVarianceEpochScore, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, R, V, logPenalty, varianceCorrection]

/-- Exponential transform of the fixed joint reverse score. -/
def reverseJointMeanVarianceEpochExponentialProcess [Fintype Z]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ) (i : ι) :
    ℕ → (Fin N → Z) → ℝ :=
  fun k x ↦ Real.exp
    (reverseJointMeanVarianceEpochScore N hN m p ell t eta i k x)

/-- Conditional Jensen turns the exponential of the joint score martingale
into a nonnegative submartingale. -/
theorem reverseJointMeanVarianceEpochExponentialProcess_submartingale
    [Fintype Z] [MeasurableSingletonClass Z]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ) (i : ι) :
    Submartingale
      (reverseJointMeanVarianceEpochExponentialProcess
        N hN m p ell t eta i)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  let filt := reverseBesselFiltration (Z := Z) N
  let muN := Measure.pi (fun _ : Fin N ↦ mu)
  let score := reverseJointMeanVarianceEpochScore N hN m p ell t eta i
  have hscore : Martingale score filt muN :=
    reverseJointMeanVarianceEpochScore_martingale
      mu N hN m p ell t eta i
  have hadapted : StronglyAdapted filt
      (reverseJointMeanVarianceEpochExponentialProcess
        N hN m p ell t eta i) := by
    intro k
    exact Real.continuous_exp.comp_stronglyMeasurable
      (hscore.stronglyMeasurable k)
  refine submartingale_nat hadapted (fun _ ↦ Integrable.of_finite) ?_
  intro k
  have hjensen := condJensen_real
    (μ := muN) (m := filt k) (X := score (k + 1)) (φ := Real.exp)
    (filt.le k) convexOn_exp Real.continuous_exp.lowerSemicontinuous
    Integrable.of_finite Integrable.of_finite
  have hstep := hscore.condExp_ae_eq (Nat.le_succ k)
  filter_upwards [hjensen, hstep] with x hj hx
  change Real.exp (score k x) ≤
    condExp (filt k) muN (fun y ↦ Real.exp (score (k + 1) y)) x
  rw [← hx]
  exact hj

omit [MeasurableSpace Z] in
theorem reverseJointMeanVarianceEpochExponentialProcess_nonneg [Fintype Z]
    (N : ℕ) (hN : 2 ≤ N) (m : ℕ)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ) (i : ι) :
    0 ≤ reverseJointMeanVarianceEpochExponentialProcess
      N hN m p ell t eta i := by
  intro k x
  exact (Real.exp_pos _).le

omit [MeasurableSpace Z] in
/-- At reverse time `N - s`, the joint score is the fixed endpoint-scaled
score evaluated with the empirical mean and Bessel variance of the first `s`
observations. -/
theorem reverseJointMeanVarianceEpochScore_sub_eq_prefix [Fintype Z]
    {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s ≤ N)
    (m : ℕ) (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ)
    (i : ι) (x : Fin N → Z) :
    reverseJointMeanVarianceEpochScore N hN m p ell t eta i (N - s) x =
      t * (m : ℝ) *
          (finitePopulationRisk p ell i -
            finiteEmpiricalRisk ell i (samplePrefix hsN x)) -
        eta * (m : ℝ) *
          finiteEmpiricalVariance ell i (samplePrefix hsN x) -
        (m : ℝ) * Real.log
          (1 + (Real.exp t - 1 - t) * finitePopulationVariance p ell i) +
        Real.exp (-t) * finiteJointMeanVarianceKappa m eta *
          finitePopulationVariance p ell i := by
  unfold reverseJointMeanVarianceEpochScore
  rw [reverseMeanProcess_sub_eq_prefix hN hs hsN,
    reverseBesselProcess_sub_eq_prefix hN hs hsN,
    prefixSampleMean_eq_finiteEmpiricalRisk,
    prefixBesselVariance_eq_finiteEmpiricalVariance]

omit [MeasurableSpace Z] in
/-- At the end of the reverse epoch, the process score is exactly the existing
fixed-sample normalized joint mean/variance score on the first `m` values. -/
theorem reverseJointMeanVarianceEpochScore_endpoint [Fintype Z]
    {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (ell : ι → Z → ℝ) (t eta : ℝ)
    (i : ι) (x : Fin N → Z) :
    reverseJointMeanVarianceEpochScore N hN m p ell t eta i (N - m) x =
      finiteJointMeanVarianceScore m p ell t eta i (samplePrefix hm.2 x) := by
  rw [reverseJointMeanVarianceEpochScore_sub_eq_prefix
    hN hm.1 hm.2 m p ell t eta i x]
  rfl

/-- The endpoint expectation of the joint reverse exponential is at most one.
The proof transports the horizon endpoint to the explicit `m`-sample product
sum and invokes the checked fixed-sample joint MGF. -/
theorem reverseJointMeanVarianceEpoch_endpoint_integral_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    {N m : ℕ} (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {t eta : ℝ} (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hkappa : 0 ≤ finiteJointMeanVarianceKappa m eta) :
    (∫ x, reverseJointMeanVarianceEpochExponentialProcess
        N hN m p ell t eta i (N - m) x
      ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 := by
  have hbridge := integral_comp_samplePrefix_eq_finiteProductSum
    hm.2 hp (fun S : Fin m → Z ↦
      Real.exp (finiteJointMeanVarianceScore m p ell t eta i S))
  have hmgf := finiteJointMeanVarianceScore_expectation_le_one
    hm.1 p hp ell i hell ht heta hkappa
  change (∫ x, Real.exp
      (reverseJointMeanVarianceEpochScore N hN m p ell t eta i (N - m) x)
      ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1
  calc
    (∫ x, Real.exp
        (reverseJointMeanVarianceEpochScore N hN m p ell t eta i (N - m) x)
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) =
      ∑ S : Fin m → Z, finiteProductSampleWeight p S *
        Real.exp (finiteJointMeanVarianceScore m p ell t eta i S) := by
          rw [← hbridge]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            change Real.exp
              (reverseJointMeanVarianceEpochScore
                N hN m p ell t eta i (N - m) x) =
              Real.exp
                (finiteJointMeanVarianceScore
                  m p ell t eta i (samplePrefix hm.2 x))
            rw [reverseJointMeanVarianceEpochScore_endpoint hN hm]
    _ ≤ 1 := hmgf

end ExchangeableMean

end

end FormalSLT.PACBayes.FiniteJointMeanVarianceReverse
