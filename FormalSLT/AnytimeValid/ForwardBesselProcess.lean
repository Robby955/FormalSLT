/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.EProcess
import FormalSLT.AnytimeValid.MixtureCS
import FormalSLT.Concentration.SubGamma.CondExpProduct
import FormalSLT.Statistics.ClassicalEstimation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Forward Bessel variance bridge

This file records the deterministic algebra needed to turn the standard
predictable plug-in squared-residual penalty into an exact Bessel-variance
penalty.  For a real sequence `x`, let

* `forwardPrefixMean x n` be the mean of `x 0, ..., x (n-1)`;
* `forwardBesselQ x n` be the centered sum of squares of that prefix, hence
  `(n - 1)` times its Bessel sample variance when `n >= 2`;
* `forwardPredictableQuadratic x n` use the seed predictor `1 / 2` for the
  first observation and the preceding prefix mean thereafter.

Welford's identity gives the exact one-step increment of `forwardBesselQ`.
For observations in `[0,1]`, the first two observations cost at most `1 / 2`
and every later predictable squared residual is at most `3 / 2` times the
corresponding Welford increment.  Consequently

`forwardPredictableQuadratic x n <= 1/2 + (3/2) * forwardBesselQ x n`

for every `n >= 2`.  The coefficient `1` is false already on the two-point
Boolean sample `(0,1)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Mean of the first `n` values of a sequence.  As elsewhere in FormalSLT,
division is total; results that use this as a genuine mean state `0 < n`. -/
def forwardPrefixMean (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, x i) / (n : ℝ)

/-- The exact centered sum of squares of the first `n` observations. -/
def forwardBesselQ (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (x i - forwardPrefixMean x n) ^ 2

/-- Predict from `1/2` before the first observation and from the empirical
prefix mean thereafter. -/
def forwardPredictor (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then (1 : ℝ) / 2 else forwardPrefixMean x k

/-- Sum of squared one-step-ahead prediction residuals through time `n`. -/
def forwardPredictableQuadratic (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (x k - forwardPredictor x k) ^ 2

lemma forwardPrefixMean_eq_sampleMean (x : ℕ → ℝ) (n : ℕ) :
    forwardPrefixMean x n =
      FormalSLT.Statistics.sampleMean (fun i : Fin n ↦ x i) := by
  simp [forwardPrefixMean,
    FormalSLT.Statistics.sampleMean,
    Fin.sum_univ_eq_sum_range]

/-- `Q_n` is exactly `(n-1)` times the Bessel sample variance. -/
theorem forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
    (x : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n) :
    forwardBesselQ x n =
      ((n : ℝ) - 1) *
        FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin n ↦ x i) := by
  have hden : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  unfold forwardBesselQ
  rw [FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel]
  rw [← forwardPrefixMean_eq_sampleMean]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ (x i - forwardPrefixMean x n) ^ 2) n]
  field_simp [hden]

/-- The centered sum of squares is nonnegative. -/
lemma forwardBesselQ_nonneg (x : ℕ → ℝ) (n : ℕ) :
    0 ≤ forwardBesselQ x n := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Online mean update. -/
lemma forwardPrefixMean_succ (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardPrefixMean x (n + 1) =
      forwardPrefixMean x n +
        (x n - forwardPrefixMean x n) / ((n : ℝ) + 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnp10 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold forwardPrefixMean
  rw [Finset.sum_range_succ]
  push_cast
  field_simp [hn0, hnp10]
  ring

/-- Welford's exact one-step identity for the centered sum of squares. -/
theorem forwardBesselQ_succ (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardBesselQ x (n + 1) =
      forwardBesselQ x n +
        (n : ℝ) / ((n : ℝ) + 1) *
          (x n - forwardPrefixMean x n) ^ 2 := by
  let m : ℝ := forwardPrefixMean x n
  let m' : ℝ := forwardPrefixMean x (n + 1)
  have hdecomp :
      ∑ i ∈ Finset.range n, (x i - m') ^ 2 =
        forwardBesselQ x n + (n : ℝ) * (m - m') ^ 2 := by
    have h :=
      FormalSLT.Statistics.ClassicalEstimation.sum_sq_sub_eq_sum_sq_sub_mean_add_card
        hn (fun i : Fin n ↦ x i) m'
    have hsum (a : ℝ) :
        (∑ i : Fin n, (x i - a) ^ 2) =
          ∑ i ∈ Finset.range n, (x i - a) ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun i ↦ (x i - a) ^ 2) n
    have hprefix :
        FormalSLT.Statistics.sampleMean (fun i : Fin n ↦ x i) = m := by
      simpa [m] using (forwardPrefixMean_eq_sampleMean x n).symm
    rw [hsum m', hsum, hprefix] at h
    simpa [forwardBesselQ] using h
  have hmean : m' = m + (x n - m) / ((n : ℝ) + 1) := by
    simpa [m, m'] using forwardPrefixMean_succ x hn
  have hnp10 : (n : ℝ) + 1 ≠ 0 := by positivity
  change (∑ i ∈ Finset.range (n + 1),
      (x i - forwardPrefixMean x (n + 1)) ^ 2) = _
  rw [Finset.sum_range_succ]
  change (∑ i ∈ Finset.range n, (x i - m') ^ 2) + (x n - m') ^ 2 = _
  rw [hdecomp, hmean]
  field_simp [hnp10]
  ring

lemma forwardPredictableQuadratic_succ (x : ℕ → ℝ) (n : ℕ) :
    forwardPredictableQuadratic x (n + 1) =
      forwardPredictableQuadratic x n + (x n - forwardPredictor x n) ^ 2 := by
  simp [forwardPredictableQuadratic, Finset.sum_range_succ]

lemma forwardPredictor_eq_prefixMean (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardPredictor x n = forwardPrefixMean x n := by
  simp [forwardPredictor, hn.ne']

lemma forwardPredictableQuadratic_two (x : ℕ → ℝ) :
    forwardPredictableQuadratic x 2 =
      (x 0 - (1 : ℝ) / 2) ^ 2 + (x 1 - x 0) ^ 2 := by
  norm_num [forwardPredictableQuadratic, forwardPredictor, forwardPrefixMean,
    Finset.sum_range_succ]

lemma forwardBesselQ_two (x : ℕ → ℝ) :
    forwardBesselQ x 2 = (x 0 - x 1) ^ 2 / 2 := by
  norm_num [forwardBesselQ, forwardPrefixMean, Finset.sum_range_succ]
  ring

/-- The two-observation seed costs at most `1/2` beyond the `3/2 Q_2`
term for `[0,1]` observations. -/
lemma forwardPredictableQuadratic_two_le
    (x : ℕ → ℝ)
    (hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1) (hx1 : 0 ≤ x 1 ∧ x 1 ≤ 1) :
    forwardPredictableQuadratic x 2 ≤
      (1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ x 2 := by
  rw [forwardPredictableQuadratic_two, forwardBesselQ_two]
  have hseed : (x 0 - (1 : ℝ) / 2) ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith [mul_nonneg hx0.1 (sub_nonneg.mpr hx0.2)]
  have hdiff : (x 0 - x 1) ^ 2 ≤ (1 : ℝ) := by
    have hlo : -(1 : ℝ) ≤ x 0 - x 1 := by linarith
    have hhi : x 0 - x 1 ≤ (1 : ℝ) := by linarith
    nlinarith
  nlinarith [sq_nonneg (x 0 - x 1)]

/-- Exact-Bessel domination of the predictable plug-in quadratic penalty.

The coefficient `3/2` is forced by the first nontrivial Welford update.  From
time two onward it is preserved inductively because
`1 <= (3/2) * n/(n+1)` for every `n >= 2`. -/
theorem forwardPredictableQuadratic_le_half_add_three_halves_besselQ
    (x : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hx : ∀ i < n, 0 ≤ x i ∧ x i ≤ 1) :
    forwardPredictableQuadratic x n ≤
      (1 : ℝ) / 2 + (3 : ℝ) / 2 * forwardBesselQ x n := by
  induction n, hn using Nat.le_induction with
  | base =>
      exact forwardPredictableQuadratic_two_le x (hx 0 (by omega)) (hx 1 (by omega))
  | succ n hn ih =>
      have hnpos : 0 < n := by omega
      have ih' := ih (fun i hi ↦ hx i (by omega))
      rw [forwardPredictableQuadratic_succ, forwardBesselQ_succ x hnpos,
        forwardPredictor_eq_prefixMean x hnpos]
      have hsq : 0 ≤ (x n - forwardPrefixMean x n) ^ 2 := sq_nonneg _
      have hden : 0 < (n : ℝ) + 1 := by positivity
      have hcoef :
          (1 : ℝ) ≤ (3 : ℝ) / 2 * ((n : ℝ) / ((n : ℝ) + 1)) := by
        rw [show (3 : ℝ) / 2 * ((n : ℝ) / ((n : ℝ) + 1)) =
          (((3 : ℝ) / 2) * (n : ℝ)) / ((n : ℝ) + 1) by ring]
        rw [le_div_iff₀ hden]
        have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      have hstep :
          (x n - forwardPrefixMean x n) ^ 2 ≤
            ((3 : ℝ) / 2 * ((n : ℝ) / ((n : ℝ) + 1))) *
              (x n - forwardPrefixMean x n) ^ 2 :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hsq
      nlinarith

/-- Pointwise obstruction to replacing `3/2` by `1`: the Boolean sample
`(false,true)`, encoded as `(0,1)`, violates the proposed bound at `n = 2`. -/
theorem forwardBessel_coefficient_one_bool_obstruction :
    let x : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 1
    (1 : ℝ) / 2 + forwardBesselQ x 2 < forwardPredictableQuadratic x 2 := by
  dsimp
  norm_num [forwardPredictableQuadratic_two, forwardBesselQ_two]

/-! ### Complement invariance and the lower-tail orientation -/

/-- For a nonempty prefix, complementing `[0,1]` observations complements
their prefix mean. -/
lemma forwardPrefixMean_one_sub (x : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    forwardPrefixMean (fun k ↦ 1 - x k) n = 1 - forwardPrefixMean x n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold forwardPrefixMean
  have hsum :
      (∑ k ∈ Finset.range n, (1 - x k)) =
        (n : ℝ) - ∑ k ∈ Finset.range n, x k := by
    simp [Finset.sum_sub_distrib]
  rw [hsum]
  field_simp [hn0]

/-- The seed `1/2` and every later empirical predictor commute with
complementation. -/
theorem forwardPredictor_one_sub (x : ℕ → ℝ) (k : ℕ) :
    forwardPredictor (fun i ↦ 1 - x i) k = 1 - forwardPredictor x k := by
  by_cases hk : k = 0
  · subst k
    norm_num [forwardPredictor]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    simp only [forwardPredictor, hk, if_false]
    exact forwardPrefixMean_one_sub x hkpos

/-- Complementing the observations negates each predictable residual and
therefore leaves the accumulated squared residual penalty unchanged. -/
theorem forwardPredictableQuadratic_one_sub (x : ℕ → ℝ) (n : ℕ) :
    forwardPredictableQuadratic (fun k ↦ 1 - x k) n =
      forwardPredictableQuadratic x n := by
  unfold forwardPredictableQuadratic
  apply Finset.sum_congr rfl
  intro k _
  rw [forwardPredictor_one_sub]
  ring

/-- Exact Bessel variance is invariant under complementation. -/
theorem forwardBesselQ_one_sub (x : ℕ → ℝ) (n : ℕ) :
    forwardBesselQ (fun k ↦ 1 - x k) n = forwardBesselQ x n := by
  by_cases hn : n = 0
  · subst n
    simp [forwardBesselQ]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    unfold forwardBesselQ
    apply Finset.sum_congr rfl
    intro k _
    rw [forwardPrefixMean_one_sub x hnpos]
    ring

/-! ### Honest stochastic interface

The deterministic Bessel envelope below does not by itself preserve the
supermartingale property.  The stochastic object is the standard exponential
process with the realized predictable-residual penalty.  Once its exact
one-step conditional-expectation inequality is supplied, it is an `EProcess`;
the Bessel expression is then a pointwise lower envelope of that e-process.
This separation prevents a deterministic domination argument from being
mistaken for a supermartingale closure theorem.
-/

/-- Empirical-Bernstein log-cumulant used by the predictable plug-in process. -/
def forwardEmpiricalBernsteinPsi (lam : ℝ) : ℝ :=
  -Real.log (1 - lam) - lam

/-- Scalar empirical-Bernstein inequality.

For `0 <= lam < 1` and `z >= -1`,

`exp (lam*z - psi(lam)*z^2) <= 1 + lam*z`.

The proof checks monotonicity in the tilt.  The derivative of the logarithmic
gap is

`t^2*z^2*(z+1) / ((1-t)*(1+t*z))`,

which is nonnegative throughout `[0,lam]`. -/
theorem exp_forwardEmpiricalBernstein_le_one_add
    {lam z : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hz : -1 ≤ z) :
    Real.exp (lam * z - forwardEmpiricalBernsteinPsi lam * z ^ 2) ≤
      1 + lam * z := by
  let F : ℝ → ℝ := fun t ↦
    Real.log (1 + t * z) - t * z + forwardEmpiricalBernsteinPsi t * z ^ 2
  let dF : ℝ → ℝ := fun t ↦
    t ^ 2 * z ^ 2 * (z + 1) / ((1 - t) * (1 + t * z))
  have hpos (t : ℝ) (ht : t ∈ Set.Icc 0 lam) :
      0 < 1 - t ∧ 0 < 1 + t * z := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hlam1
    have htz : -t ≤ t * z := by
      have := mul_le_mul_of_nonneg_left hz ht0
      nlinarith
    constructor <;> nlinarith
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc 0 lam) : HasDerivAt F (dF t) t := by
    have hp := hpos t ht
    have hinner : HasDerivAt (fun s : ℝ ↦ 1 + s * z) z t := by
      have h := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const z)
      exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    have hlog : HasDerivAt (fun s : ℝ ↦ Real.log (1 + s * z))
        (z / (1 + t * z)) t :=
      hinner.log hp.2.ne'
    have honeSub : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
      have h := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    have hpsi :
        HasDerivAt forwardEmpiricalBernsteinPsi (1 / (1 - t) - 1) t := by
      unfold forwardEmpiricalBernsteinPsi
      have h := (honeSub.log hp.1.ne').neg.sub (hasDerivAt_id t)
      apply (h.congr_deriv ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)
      field_simp [hp.1.ne']
    have hraw : HasDerivAt F
        (z / (1 + t * z) - z + (1 / (1 - t) - 1) * z ^ 2) t := by
      dsimp [F]
      have h :=
        (hlog.sub ((hasDerivAt_id t).mul_const z)).add
          (hpsi.mul_const (z ^ 2))
      exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    convert hraw using 1
    dsimp [dF]
    field_simp [hp.1.ne', hp.2.ne']
    ring
  have hcont : ContinuousOn F (Set.Icc 0 lam) := by
    intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn F (Set.Icc 0 lam) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := dF)
      (convex_Icc 0 lam) hcont ?_ ?_
    · intro t ht
      exact (hderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc 0 lam := interior_subset ht
      have hp := hpos t ht'
      dsimp [dF]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg z)) (by linarith))
        (mul_nonneg hp.1.le hp.2.le)
  have hgap : 0 ≤ F lam := by
    have h := hmono
      (show 0 ∈ Set.Icc (0 : ℝ) lam by exact ⟨le_rfl, hlam0⟩)
      (show lam ∈ Set.Icc (0 : ℝ) lam by exact ⟨hlam0, le_rfl⟩) hlam0
    simpa [F, forwardEmpiricalBernsteinPsi] using h
  have hrhs : 0 < 1 + lam * z := (hpos lam ⟨hlam0, le_rfl⟩).2
  apply (Real.le_log_iff_exp_le hrhs).mp
  dsimp [F] at hgap
  linarith

/-- The empirical-Bernstein cumulant is nonnegative on its admissible tilt
range. -/
lemma forwardEmpiricalBernsteinPsi_nonneg
    {lam : ℝ} (_hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    0 ≤ forwardEmpiricalBernsteinPsi lam := by
  have hpos : 0 < 1 - lam := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  unfold forwardEmpiricalBernsteinPsi
  linarith

/-- Random predictable prefix-mean predictor induced by an observation process. -/
def forwardPredictorProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  forwardPredictor (fun i ↦ X i ω) k

/-- Process-valued form of `forwardPredictor_one_sub`. -/
theorem forwardPredictorProcess_one_sub {Ω : Type*}
    (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    forwardPredictorProcess (fun i ω ↦ 1 - X i ω) k ω =
      1 - forwardPredictorProcess X k ω := by
  exact forwardPredictor_one_sub (fun i ↦ X i ω) k

/-- The empirical prefix predictor is predictable when observations are
revealed one step after the past filtration. -/
theorem stronglyAdapted_forwardPredictorProcess_of_incrementAdapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX_adapted : IncrementAdapted ℱ X) :
    StronglyAdapted ℱ (forwardPredictorProcess X) := by
  intro k
  unfold forwardPredictorProcess forwardPredictor
  split_ifs
  · exact stronglyMeasurable_const
  · unfold forwardPrefixMean
    have hsum : StronglyMeasurable[ℱ k]
        (∑ i ∈ Finset.range k, X i) := by
      apply Finset.stronglyMeasurable_sum
      intro i hi
      rw [Finset.mem_range] at hi
      exact (hX_adapted i).mono (ℱ.mono (Nat.succ_le_of_lt hi))
    simpa only [Finset.sum_apply, div_eq_mul_inv] using
      hsum.mul_const ((k : ℝ)⁻¹)

/-- A prefix-average predictor stays in `[0,1]` when every observation does. -/
theorem forwardPredictorProcess_mem_Icc_of_mem_Icc
    {Ω : Type*} {X : ℕ → Ω → ℝ}
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1) (k : ℕ) (ω : Ω) :
    0 ≤ forwardPredictorProcess X k ω ∧
      forwardPredictorProcess X k ω ≤ 1 := by
  by_cases hk : k = 0
  · subst k
    norm_num [forwardPredictorProcess, forwardPredictor]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range k, X i ω :=
      Finset.sum_nonneg fun i _ ↦ (hX_unit i ω).1
    have hsum_le : (∑ i ∈ Finset.range k, X i ω) ≤ (k : ℝ) := by
      calc
        (∑ i ∈ Finset.range k, X i ω) ≤
            ∑ _i ∈ Finset.range k, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ (hX_unit i ω).2
        _ = (k : ℝ) := by simp
    simp only [forwardPredictorProcess, forwardPredictor, hk, if_false,
      forwardPrefixMean]
    constructor
    · exact div_nonneg hsum_nonneg hkR.le
    · exact (div_le_one hkR).2 hsum_le

/-- Complementation preserves predictable-increment adaptedness. -/
theorem incrementAdapted_one_sub
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX_adapted : IncrementAdapted ℱ X) :
    IncrementAdapted ℱ (fun k ω ↦ 1 - X k ω) := by
  intro k
  exact stronglyMeasurable_const.sub (hX_adapted k)

/-- One empirical-Bernstein plug-in factor. -/
def forwardEmpiricalBernsteinFactor {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (lam * (X k ω - mean) - forwardEmpiricalBernsteinPsi lam *
      (X k ω - forwardPredictorProcess X k ω) ^ 2)

/-- The one-step predictable plug-in factor has conditional expectation at
most one under the conditional-mean model.

The scalar empirical-Bernstein inequality gives

`factor <= exp(a) * (1 + lam * (X-p))`, `a = lam*(p-mean)`.

The predictable exponential is pulled outside the conditional expectation;
conditional centering turns the affine factor into `1-a`, and
`exp(a)*(1-a) <= 1` follows from `1-a <= exp(-a)`. -/
theorem forwardEmpiricalBernsteinFactor_condExp_le_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ} {k : ℕ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_meas : Measurable (X k)) (hX_int : Integrable (X k) μ)
    (hP_meas : StronglyMeasurable[ℱ k] (forwardPredictorProcess X k))
    (hX_unit : ∀ᵐ ω ∂μ, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hP_unit : ∀ᵐ ω ∂μ,
      0 ≤ forwardPredictorProcess X k ω ∧
        forwardPredictorProcess X k ω ≤ 1)
    (hmean : μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean) :
    μ[forwardEmpiricalBernsteinFactor X mean lam k | ℱ k]
      ≤ᵐ[μ] fun _ ↦ (1 : ℝ) := by
  let P : Ω → ℝ := forwardPredictorProcess X k
  let A : Ω → ℝ := fun ω ↦ lam * (P ω - mean)
  let Z : Ω → ℝ := fun ω ↦ Real.exp (A ω)
  let Y : Ω → ℝ := fun ω ↦ 1 + lam * (X k ω - P ω)
  let C : ℝ := Real.exp (lam * (1 + |mean|))
  have hP_global : StronglyMeasurable P := hP_meas.mono (ℱ.le k)
  have hP_bdd : ∀ᵐ ω ∂μ, |P ω| ≤ (1 : ℝ) := by
    filter_upwards [hP_unit] with ω hω
    simpa [P, abs_of_nonneg hω.1] using hω.2
  have hP_int : Integrable P μ :=
    Integrable.of_bound hP_global.aestronglyMeasurable 1 hP_bdd
  have hR_int : Integrable (fun ω ↦ X k ω - P ω) μ := hX_int.sub hP_int
  have hY_int : Integrable Y μ :=
    (integrable_const 1).add (hR_int.const_mul lam)
  have hZ_meas : StronglyMeasurable[ℱ k] Z := by
    have hA : StronglyMeasurable[ℱ k] A :=
      (hP_meas.sub stronglyMeasurable_const).const_mul lam
    exact Real.continuous_exp.comp_stronglyMeasurable hA
  have hZ_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ C := by
    filter_upwards [hP_unit] with ω hω
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    dsimp [A, C, P]
    have hmean_abs : -mean ≤ |mean| := neg_le_abs mean
    have hdiff : forwardPredictorProcess X k ω - mean ≤ 1 + |mean| := by
      linarith
    exact mul_le_mul_of_nonneg_left hdiff hlam0
  have hcomparison_int : Integrable (fun ω ↦ Z ω * Y ω) μ :=
    hY_int.bdd_mul (hZ_meas.mono (ℱ.le k)).aestronglyMeasurable hZ_bdd
  have hfactor_meas : Measurable (forwardEmpiricalBernsteinFactor X mean lam k) := by
    change Measurable (fun ω ↦ Real.exp
      (lam * (X k ω - mean) - forwardEmpiricalBernsteinPsi lam *
        (X k ω - P ω) ^ 2))
    fun_prop
  have hpoint : ∀ᵐ ω ∂μ,
      forwardEmpiricalBernsteinFactor X mean lam k ω ≤ Z ω * Y ω := by
    filter_upwards [hX_unit, hP_unit] with ω hXω hPω
    have hz : -(1 : ℝ) ≤ X k ω - P ω := by
      dsimp [P] at hPω ⊢
      linarith
    have hs := exp_forwardEmpiricalBernstein_le_one_add hlam0 hlam1 hz
    calc
      forwardEmpiricalBernsteinFactor X mean lam k ω =
          Real.exp (A ω) *
            Real.exp (lam * (X k ω - P ω) -
              forwardEmpiricalBernsteinPsi lam * (X k ω - P ω) ^ 2) := by
            rw [← Real.exp_add]
            unfold forwardEmpiricalBernsteinFactor
            dsimp [A, P]
            congr 1
            ring
      _ ≤ Real.exp (A ω) * (1 + lam * (X k ω - P ω)) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = Z ω * Y ω := rfl
  have hfactor_int : Integrable (forwardEmpiricalBernsteinFactor X mean lam k) μ := by
    refine Integrable.mono' hcomparison_int hfactor_meas.aestronglyMeasurable ?_
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (by
      unfold forwardEmpiricalBernsteinFactor
      exact Real.exp_pos _)]
    exact hω
  have hmono :
      μ[forwardEmpiricalBernsteinFactor X mean lam k | ℱ k] ≤ᵐ[μ]
        μ[fun ω ↦ Z ω * Y ω | ℱ k] :=
    condExp_mono hfactor_int hcomparison_int hpoint
  have hpull :
      μ[fun ω ↦ Z ω * Y ω | ℱ k] =ᵐ[μ]
        fun ω ↦ Z ω * (μ[Y | ℱ k]) ω :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (ℱ.le k) hZ_meas hZ_bdd hY_int
  have hP_cond : μ[P | ℱ k] = P :=
    condExp_of_stronglyMeasurable (ℱ.le k) hP_meas hP_int
  have hR_cond :
      μ[fun ω ↦ X k ω - P ω | ℱ k] =ᵐ[μ] fun ω ↦ mean - P ω := by
    have hsub := condExp_sub hX_int hP_int (ℱ k)
    filter_upwards [hsub, hmean] with ω hsubω hmeanω
    change μ[X k - P | ℱ k] ω = mean - P ω
    rw [hsubω]
    simp only [Pi.sub_apply]
    rw [hmeanω, hP_cond]
  have hY_cond : μ[Y | ℱ k] =ᵐ[μ] fun ω ↦ 1 + lam * (mean - P ω) := by
    have hadd :=
      condExp_add (integrable_const (1 : ℝ)) (hR_int.const_mul lam) (ℱ k)
    have hscale := condExp_smul (𝕜 := ℝ) (μ := μ) (m := ℱ k) lam
      (fun ω ↦ X k ω - P ω)
    have hscale' :
        μ[fun ω ↦ lam * (X k ω - P ω) | ℱ k] =ᵐ[μ]
          fun ω ↦ lam * (μ[fun ω ↦ X k ω - P ω | ℱ k]) ω := by
      filter_upwards [hscale] with ω hscaleω
      change μ[lam • (fun ω ↦ X k ω - P ω) | ℱ k] ω =
        lam * (μ[fun ω ↦ X k ω - P ω | ℱ k]) ω
      simpa only [Pi.smul_apply, smul_eq_mul] using hscaleω
    have hone : μ[(fun _ : Ω ↦ (1 : ℝ)) | ℱ k] = fun _ ↦ (1 : ℝ) :=
      condExp_const (ℱ.le k) 1
    filter_upwards [hadd, hscale', hR_cond] with ω haddω hscaleω hRω
    change μ[(fun _ : Ω ↦ (1 : ℝ)) +
      (fun ω ↦ lam * (X k ω - P ω)) | ℱ k] ω =
        1 + lam * (mean - P ω)
    rw [haddω]
    simp only [Pi.add_apply]
    rw [hone, hscaleω, hRω]
  filter_upwards [hmono, hpull, hY_cond] with ω hmonoω hpullω hYω
  refine hmonoω.trans ?_
  rw [hpullω, hYω]
  have ha : 1 - A ω ≤ Real.exp (-A ω) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-A ω)
  calc
    Z ω * (1 + lam * (mean - P ω)) = Real.exp (A ω) * (1 - A ω) := by
      dsimp [Z, A]
      congr 1
      ring
    _ ≤ Real.exp (A ω) * Real.exp (-A ω) :=
      mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Predictable-residual exponential process for observations `X` and candidate
mean `mean`.  The scalar `psi` is the one-step cumulant multiplier. -/
def forwardPlugInExponentialProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam psi : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (lam * (∑ k ∈ Finset.range n, (X k ω - mean)) -
      psi * forwardPredictableQuadratic (fun k ↦ X k ω) n)

/-- The concrete forward empirical-Bernstein process. -/
def forwardEmpiricalBernsteinProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam : ℝ) : ℕ → Ω → ℝ :=
  forwardPlugInExponentialProcess X mean lam (forwardEmpiricalBernsteinPsi lam)

/-- Positive-tilt lower-tail process, implemented by complementing `[0,1]`
observations.  If `X` has conditional mean `mean`, then `1 - X` has
conditional mean `1 - mean`. -/
def forwardEmpiricalBernsteinLowerProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam : ℝ) : ℕ → Ω → ℝ :=
  forwardEmpiricalBernsteinProcess (fun k ω ↦ 1 - X k ω) (1 - mean) lam

/-- Explicit lower-tail orientation of the complemented process.  Its
predictable quadratic penalty is exactly the original one. -/
theorem forwardEmpiricalBernsteinLowerProcess_eq {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam : ℝ) (n : ℕ) (ω : Ω) :
    forwardEmpiricalBernsteinLowerProcess X mean lam n ω =
      Real.exp
        (lam * (∑ k ∈ Finset.range n, (mean - X k ω)) -
          forwardEmpiricalBernsteinPsi lam *
            forwardPredictableQuadratic (fun k ↦ X k ω) n) := by
  unfold forwardEmpiricalBernsteinLowerProcess
  unfold forwardEmpiricalBernsteinProcess forwardPlugInExponentialProcess
  rw [forwardPredictableQuadratic_one_sub]
  congr 1
  apply congrArg (fun s : ℝ ↦ lam * s -
    forwardEmpiricalBernsteinPsi lam *
      forwardPredictableQuadratic (fun k ↦ X k ω) n)
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact multiplicative update of the generic plug-in exponential process. -/
lemma forwardPlugInExponentialProcess_succ {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam psi : ℝ) (n : ℕ) (ω : Ω) :
    forwardPlugInExponentialProcess X mean lam psi (n + 1) ω =
      forwardPlugInExponentialProcess X mean lam psi n ω *
        Real.exp
          (lam * (X n ω - mean) -
            psi * (X n ω - forwardPredictorProcess X n ω) ^ 2) := by
  unfold forwardPlugInExponentialProcess forwardPredictorProcess
  rw [Finset.sum_range_succ, forwardPredictableQuadratic_succ, ← Real.exp_add]
  congr 1
  ring

/-- Exact multiplicative update of the concrete empirical-Bernstein process. -/
lemma forwardEmpiricalBernsteinProcess_succ {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam : ℝ) (n : ℕ) (ω : Ω) :
    forwardEmpiricalBernsteinProcess X mean lam (n + 1) ω =
      forwardEmpiricalBernsteinProcess X mean lam n ω *
        forwardEmpiricalBernsteinFactor X mean lam n ω := by
  exact forwardPlugInExponentialProcess_succ
    X mean lam (forwardEmpiricalBernsteinPsi lam) n ω

/-- The forward empirical-Bernstein process is adapted under the standard
increment convention: `X k` is revealed at time `k + 1`. -/
theorem stronglyAdapted_forwardEmpiricalBernsteinProcess_of_incrementAdapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hX_adapted : IncrementAdapted ℱ X) :
    StronglyAdapted ℱ (forwardEmpiricalBernsteinProcess X mean lam) := by
  have hP_adapted : StronglyAdapted ℱ (forwardPredictorProcess X) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hX_adapted
  intro n
  have hcentered : StronglyMeasurable[ℱ n]
      (fun ω ↦ ∑ k ∈ Finset.range n, (X k ω - mean)) := by
    have hrw : (fun ω ↦ ∑ k ∈ Finset.range n, (X k ω - mean)) =
        ∑ k ∈ Finset.range n, (fun ω ↦ X k ω - mean) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro k hk
    rw [Finset.mem_range] at hk
    exact ((hX_adapted k).mono
      (ℱ.mono (Nat.succ_le_of_lt hk))).sub stronglyMeasurable_const
  have hquadratic : StronglyMeasurable[ℱ n]
      (fun ω ↦ forwardPredictableQuadratic (fun k ↦ X k ω) n) := by
    have hrw :
        (fun ω ↦ forwardPredictableQuadratic (fun k ↦ X k ω) n) =
          ∑ k ∈ Finset.range n,
            (fun ω ↦ (X k ω - forwardPredictorProcess X k ω) ^ 2) := by
      funext ω
      simp only [forwardPredictableQuadratic, forwardPredictorProcess,
        Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hXk : StronglyMeasurable[ℱ n] (X k) :=
      (hX_adapted k).mono (ℱ.mono (Nat.succ_le_of_lt hk))
    have hPk : StronglyMeasurable[ℱ n] (forwardPredictorProcess X k) :=
      (hP_adapted k).mono (ℱ.mono (le_of_lt hk))
    exact (hXk.sub hPk).pow 2
  change StronglyMeasurable[ℱ n]
    (fun ω ↦ Real.exp
      (lam * (∑ k ∈ Finset.range n, (X k ω - mean)) -
        forwardEmpiricalBernsteinPsi lam *
          forwardPredictableQuadratic (fun k ↦ X k ω) n))
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((hcentered.const_mul lam).sub
      (hquadratic.const_mul (forwardEmpiricalBernsteinPsi lam)))

/-- A uniform pointwise bound for the forward empirical-Bernstein process
under `[0,1]` observations.  The nonnegative quadratic penalty can only
decrease the exponent. -/
theorem forwardEmpiricalBernsteinProcess_le_of_mem_Icc
    {Ω : Type*} {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (n : ℕ) (ω : Ω) :
    forwardEmpiricalBernsteinProcess X mean lam n ω ≤
      Real.exp (lam * (n : ℝ) * (1 + |mean|)) := by
  unfold forwardEmpiricalBernsteinProcess forwardPlugInExponentialProcess
  apply Real.exp_le_exp.mpr
  have hsum_le :
      (∑ k ∈ Finset.range n, (X k ω - mean)) ≤
        (n : ℝ) * (1 + |mean|) := by
    calc
      (∑ k ∈ Finset.range n, (X k ω - mean)) ≤
          ∑ _k ∈ Finset.range n, (1 + |mean|) :=
        Finset.sum_le_sum fun k _ ↦ by
          have hmean : -mean ≤ |mean| := neg_le_abs mean
          linarith [(hX_unit k ω).2]
      _ = (n : ℝ) * (1 + |mean|) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htilt :
      lam * (∑ k ∈ Finset.range n, (X k ω - mean)) ≤
        lam * ((n : ℝ) * (1 + |mean|)) :=
    mul_le_mul_of_nonneg_left hsum_le hlam0
  have hpenalty : 0 ≤
      forwardEmpiricalBernsteinPsi lam *
        forwardPredictableQuadratic (fun k ↦ X k ω) n :=
    mul_nonneg (forwardEmpiricalBernsteinPsi_nonneg hlam0 hlam1)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  nlinarith

/-- A uniform pointwise bound for one plug-in factor under `[0,1]`
observations.  The squared predictor residual appears with a nonpositive
coefficient, so its range is not needed for this bound. -/
theorem forwardEmpiricalBernsteinFactor_le_of_mem_Icc
    {Ω : Type*} {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (k : ℕ) (ω : Ω) :
    forwardEmpiricalBernsteinFactor X mean lam k ω ≤
      Real.exp (lam * (1 + |mean|)) := by
  unfold forwardEmpiricalBernsteinFactor
  apply Real.exp_le_exp.mpr
  have hmean_abs : -mean ≤ |mean| := neg_le_abs mean
  have hlinear : X k ω - mean ≤ 1 + |mean| := by
    linarith [(hX_unit k ω).2]
  have htilt : lam * (X k ω - mean) ≤ lam * (1 + |mean|) :=
    mul_le_mul_of_nonneg_left hlinear hlam0
  have hpenalty : 0 ≤
      forwardEmpiricalBernsteinPsi lam *
        (X k ω - forwardPredictorProcess X k ω) ^ 2 :=
    mul_nonneg (forwardEmpiricalBernsteinPsi_nonneg hlam0 hlam1) (sq_nonneg _)
  nlinarith

/-- Bounded adapted observations make every forward empirical-Bernstein
process value integrable. -/
theorem integrable_forwardEmpiricalBernsteinProcess_of_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (n : ℕ) :
    Integrable (forwardEmpiricalBernsteinProcess X mean lam n) μ := by
  let C : ℝ := Real.exp (lam * (n : ℝ) * (1 + |mean|))
  have hadapted :=
    stronglyAdapted_forwardEmpiricalBernsteinProcess_of_incrementAdapted
      (mean := mean) (lam := lam) hX_adapted
  refine Integrable.of_bound
    ((hadapted n).mono (ℱ.le n)).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (by
      unfold forwardEmpiricalBernsteinProcess forwardPlugInExponentialProcess
      exact Real.exp_pos _)]
    exact forwardEmpiricalBernsteinProcess_le_of_mem_Icc
      hlam0 hlam1 hX_unit n ω

/-- Bounded adapted observations make every one-step plug-in factor
integrable. -/
theorem integrable_forwardEmpiricalBernsteinFactor_of_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (k : ℕ) :
    Integrable (forwardEmpiricalBernsteinFactor X mean lam k) μ := by
  have hP_adapted : StronglyAdapted ℱ (forwardPredictorProcess X) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hX_adapted
  have hX_global : StronglyMeasurable (X k) :=
    (hX_adapted k).mono (ℱ.le (k + 1))
  have hP_global : StronglyMeasurable (forwardPredictorProcess X k) :=
    (hP_adapted k).mono (ℱ.le k)
  have hfactor_meas : StronglyMeasurable
      (forwardEmpiricalBernsteinFactor X mean lam k) := by
    unfold forwardEmpiricalBernsteinFactor
    exact Real.continuous_exp.comp_stronglyMeasurable
      (((hX_global.sub stronglyMeasurable_const).const_mul lam).sub
        (((hX_global.sub hP_global).pow 2).const_mul
          (forwardEmpiricalBernsteinPsi lam)))
  refine Integrable.of_bound hfactor_meas.aestronglyMeasurable
    (Real.exp (lam * (1 + |mean|))) ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (by
      unfold forwardEmpiricalBernsteinFactor
      exact Real.exp_pos _)]
    exact forwardEmpiricalBernsteinFactor_le_of_mem_Icc
      hlam0 hlam1 hX_unit k ω

/-- The concrete forward plug-in empirical-Bernstein process is a
supermartingale.  Adaptedness, integrability, and the bounded-current-process
condition are stated explicitly; the formerly abstract one-step hypothesis is
discharged by `forwardEmpiricalBernsteinFactor_condExp_le_one`. -/
theorem forwardEmpiricalBernsteinProcess_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hP_adapted : StronglyAdapted ℱ (forwardPredictorProcess X))
    (hX_unit : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hP_unit : ∀ k, ∀ᵐ ω ∂μ,
      0 ≤ forwardPredictorProcess X k ω ∧
        forwardPredictorProcess X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean)
    (hprocess_adapted : StronglyAdapted ℱ
      (forwardEmpiricalBernsteinProcess X mean lam))
    (hprocess_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinProcess X mean lam n) μ)
    (hfactor_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinFactor X mean lam n) μ)
    (hprocess_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ,
      |forwardEmpiricalBernsteinProcess X mean lam n ω| ≤ C) :
    Supermartingale (forwardEmpiricalBernsteinProcess X mean lam) ℱ μ := by
  refine supermartingale_nat hprocess_adapted hprocess_int ?_
  intro n
  let Z : Ω → ℝ := forwardEmpiricalBernsteinProcess X mean lam n
  let Y : Ω → ℝ := forwardEmpiricalBernsteinFactor X mean lam n
  have hfact :
      forwardEmpiricalBernsteinProcess X mean lam (n + 1) =
        fun ω ↦ Z ω * Y ω := by
    funext ω
    exact forwardEmpiricalBernsteinProcess_succ X mean lam n ω
  have hZ_meas : StronglyMeasurable[ℱ n] Z := hprocess_adapted n
  obtain ⟨C, hZ_bdd⟩ := hprocess_bdd n
  have hpull :
      μ[fun ω ↦ Z ω * Y ω | ℱ n] =ᵐ[μ]
        fun ω ↦ Z ω * (μ[Y | ℱ n]) ω :=
    FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left
      (ℱ.le n) hZ_meas hZ_bdd (by simpa [Y] using hfactor_int n)
  have hstep := forwardEmpiricalBernsteinFactor_condExp_le_one
    (ℱ := ℱ) (X := X) (mean := mean) (k := n)
    hlam0 hlam1 (hX_meas n) (hX_int n) (hP_adapted n)
    (hX_unit n) (hP_unit n) (hmean n)
  rw [hfact]
  filter_upwards [hpull, hstep] with ω hpullω hstepω
  rw [hpullω]
  have hZ_nonneg : 0 ≤ Z ω := by
    dsimp [Z, forwardEmpiricalBernsteinProcess,
      forwardPlugInExponentialProcess]
    exact (Real.exp_pos _).le
  calc
    Z ω * (μ[Y | ℱ n]) ω ≤ Z ω * 1 :=
      mul_le_mul_of_nonneg_left (by simpa [Y] using hstepω) hZ_nonneg
    _ = forwardEmpiricalBernsteinProcess X mean lam n ω := by simp [Z]

/-- The concrete forward plug-in empirical-Bernstein process is an e-process. -/
theorem forwardEmpiricalBernsteinProcess_eProcess
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hP_adapted : StronglyAdapted ℱ (forwardPredictorProcess X))
    (hX_unit : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hP_unit : ∀ k, ∀ᵐ ω ∂μ,
      0 ≤ forwardPredictorProcess X k ω ∧
        forwardPredictorProcess X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean)
    (hprocess_adapted : StronglyAdapted ℱ
      (forwardEmpiricalBernsteinProcess X mean lam))
    (hprocess_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinProcess X mean lam n) μ)
    (hfactor_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinFactor X mean lam n) μ)
    (hprocess_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ,
      |forwardEmpiricalBernsteinProcess X mean lam n ω| ≤ C) :
    EProcess μ ℱ (forwardEmpiricalBernsteinProcess X mean lam) where
  nonneg := fun _ _ ↦ (Real.exp_pos _).le
  start_one := fun ω ↦ by
    simp [forwardEmpiricalBernsteinProcess, forwardPlugInExponentialProcess,
      forwardPredictableQuadratic]
  supermartingale := forwardEmpiricalBernsteinProcess_supermartingale
    hlam0 hlam1 hX_meas hX_int hP_adapted hX_unit hP_unit hmean
    hprocess_adapted hprocess_int hfactor_int hprocess_bdd

/-- **Bounded-model forward empirical-Bernstein e-process.**

Under the standard stochastic interface—`X k` is revealed at time `k + 1`,
every observation lies in `[0,1]`, and its conditional mean given `ℱ k` is
`mean`—all measurability, predictor, integrability, and finite-time boundedness
obligations of `forwardEmpiricalBernsteinProcess_eProcess` are automatic. -/
theorem forwardEmpiricalBernsteinProcess_eProcess_of_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean) :
    EProcess μ ℱ (forwardEmpiricalBernsteinProcess X mean lam) := by
  have hX_meas : ∀ k, Measurable (X k) := by
    intro k
    exact ((hX_adapted k).mono (ℱ.le (k + 1))).measurable
  have hX_int : ∀ k, Integrable (X k) μ := by
    intro k
    refine Integrable.of_bound (hX_meas k).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k ω).1]
      exact (hX_unit k ω).2
  have hP_adapted : StronglyAdapted ℱ (forwardPredictorProcess X) :=
    stronglyAdapted_forwardPredictorProcess_of_incrementAdapted hX_adapted
  have hX_unit_ae : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ X k ω ∧ X k ω ≤ 1 :=
    fun k ↦ Filter.Eventually.of_forall (hX_unit k)
  have hP_unit_ae : ∀ k, ∀ᵐ ω ∂μ,
      0 ≤ forwardPredictorProcess X k ω ∧
        forwardPredictorProcess X k ω ≤ 1 :=
    fun k ↦ Filter.Eventually.of_forall
      (forwardPredictorProcess_mem_Icc_of_mem_Icc hX_unit k)
  have hprocess_adapted : StronglyAdapted ℱ
      (forwardEmpiricalBernsteinProcess X mean lam) :=
    stronglyAdapted_forwardEmpiricalBernsteinProcess_of_incrementAdapted
      hX_adapted
  have hprocess_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinProcess X mean lam n) μ :=
    fun n ↦ integrable_forwardEmpiricalBernsteinProcess_of_bounded
      hlam0 hlam1 hX_adapted hX_unit n
  have hfactor_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinFactor X mean lam n) μ :=
    fun n ↦ integrable_forwardEmpiricalBernsteinFactor_of_bounded
      hlam0 hlam1 hX_adapted hX_unit n
  have hprocess_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ,
      |forwardEmpiricalBernsteinProcess X mean lam n ω| ≤ C := by
    intro n
    refine ⟨Real.exp (lam * (n : ℝ) * (1 + |mean|)),
      Filter.Eventually.of_forall fun ω ↦ ?_⟩
    rw [abs_of_pos (by
      unfold forwardEmpiricalBernsteinProcess forwardPlugInExponentialProcess
      exact Real.exp_pos _)]
    exact forwardEmpiricalBernsteinProcess_le_of_mem_Icc
      hlam0 hlam1 hX_unit n ω
  exact forwardEmpiricalBernsteinProcess_eProcess
    hlam0 hlam1 hX_meas hX_int hP_adapted hX_unit_ae hP_unit_ae hmean
    hprocess_adapted hprocess_int hfactor_int hprocess_bdd

/-- **Bounded-model lower-tail e-process.**

Positive tilts of `forwardEmpiricalBernsteinProcess` control upward deviations
of `X - mean`.  The process below applies the same checked theorem to `1 - X`,
thereby controlling the lower tail `mean - X`.  Complementation preserves both
the predictable squared-residual penalty and the exact Bessel variance; no
claim is made that the later Bessel lower envelope is itself an e-process. -/
theorem forwardEmpiricalBernsteinLowerProcess_eProcess_of_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_adapted : IncrementAdapted ℱ X)
    (hX_unit : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean) :
    EProcess μ ℱ (forwardEmpiricalBernsteinLowerProcess X mean lam) := by
  let Y : ℕ → Ω → ℝ := fun k ω ↦ 1 - X k ω
  have hY_adapted : IncrementAdapted ℱ Y :=
    incrementAdapted_one_sub hX_adapted
  have hY_unit : ∀ k ω, 0 ≤ Y k ω ∧ Y k ω ≤ 1 := by
    intro k ω
    dsimp [Y]
    constructor <;> linarith [((hX_unit k ω).1), ((hX_unit k ω).2)]
  have hX_int : ∀ k, Integrable (X k) μ := by
    intro k
    have hX_meas : Measurable (X k) :=
      ((hX_adapted k).mono (ℱ.le (k + 1))).measurable
    refine Integrable.of_bound hX_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k ω).1]
      exact (hX_unit k ω).2
  have hY_mean : ∀ k, μ[Y k | ℱ k] =ᵐ[μ] fun _ ↦ 1 - mean := by
    intro k
    have hsub := condExp_sub (integrable_const (1 : ℝ)) (hX_int k) (ℱ k)
    have hone : μ[(fun _ : Ω ↦ (1 : ℝ)) | ℱ k] = fun _ ↦ (1 : ℝ) :=
      condExp_const (ℱ.le k) 1
    filter_upwards [hsub, hmean k] with ω hsubω hmeanω
    change μ[(fun _ : Ω ↦ (1 : ℝ)) - X k | ℱ k] ω = 1 - mean
    rw [hsubω, hone]
    simp only [Pi.sub_apply]
    rw [hmeanω]
  exact forwardEmpiricalBernsteinProcess_eProcess_of_bounded
    (X := Y) (mean := 1 - mean) hlam0 hlam1 hY_adapted hY_unit hY_mean

/-- Exact-Bessel lower envelope of `forwardPlugInExponentialProcess`. -/
def forwardBesselExponentialEnvelope {Ω : Type*}
    (X : ℕ → Ω → ℝ) (mean lam psi : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (lam * (∑ k ∈ Finset.range n, (X k ω - mean)) -
      psi * ((1 : ℝ) / 2 + (3 : ℝ) / 2 *
        forwardBesselQ (fun k ↦ X k ω) n))

/-- Under `[0,1]` observations and a nonnegative cumulant multiplier, the
exact-Bessel expression is a pointwise lower envelope of the predictable
plug-in process. -/
theorem forwardBesselExponentialEnvelope_le_forwardPlugIn
    {Ω : Type*} (X : ℕ → Ω → ℝ) (mean lam psi : ℝ)
    {n : ℕ} (hn : 2 ≤ n) (hpsi : 0 ≤ psi) (ω : Ω)
    (hX : ∀ i < n, 0 ≤ X i ω ∧ X i ω ≤ 1) :
    forwardBesselExponentialEnvelope X mean lam psi n ω ≤
      forwardPlugInExponentialProcess X mean lam psi n ω := by
  apply Real.exp_le_exp.mpr
  have hq :=
    forwardPredictableQuadratic_le_half_add_three_halves_besselQ
      (fun k ↦ X k ω) hn hX
  have hpen := mul_le_mul_of_nonneg_left hq hpsi
  linarith

/-- End-to-end certificate for the repaired forward exact-Bessel construction:
the predictable-residual process is an e-process, and from time two onward
the explicit Bessel-variance expression is its pointwise lower envelope. -/
theorem forwardEmpiricalBernsteinBesselEnvelope_certified
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hX_meas : ∀ k, Measurable (X k))
    (hX_int : ∀ k, Integrable (X k) μ)
    (hP_adapted : StronglyAdapted ℱ (forwardPredictorProcess X))
    (hX_unit : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ X k ω ∧ X k ω ≤ 1)
    (hP_unit : ∀ k, ∀ᵐ ω ∂μ,
      0 ≤ forwardPredictorProcess X k ω ∧
        forwardPredictorProcess X k ω ≤ 1)
    (hmean : ∀ k, μ[X k | ℱ k] =ᵐ[μ] fun _ ↦ mean)
    (hprocess_adapted : StronglyAdapted ℱ
      (forwardEmpiricalBernsteinProcess X mean lam))
    (hprocess_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinProcess X mean lam n) μ)
    (hfactor_int : ∀ n,
      Integrable (forwardEmpiricalBernsteinFactor X mean lam n) μ)
    (hprocess_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ,
      |forwardEmpiricalBernsteinProcess X mean lam n ω| ≤ C)
    (hX_pointwise : ∀ n ≥ 2, ∀ ω, ∀ i < n,
      0 ≤ X i ω ∧ X i ω ≤ 1) :
    EProcess μ ℱ (forwardEmpiricalBernsteinProcess X mean lam) ∧
      ∀ n ≥ 2, ∀ ω,
        forwardBesselExponentialEnvelope X mean lam
            (forwardEmpiricalBernsteinPsi lam) n ω ≤
          forwardEmpiricalBernsteinProcess X mean lam n ω := by
  refine ⟨forwardEmpiricalBernsteinProcess_eProcess
    hlam0 hlam1 hX_meas hX_int hP_adapted hX_unit hP_unit hmean
    hprocess_adapted hprocess_int hfactor_int hprocess_bdd, ?_⟩
  intro n hn ω
  exact forwardBesselExponentialEnvelope_le_forwardPlugIn
    X mean lam (forwardEmpiricalBernsteinPsi lam) hn
      (forwardEmpiricalBernsteinPsi_nonneg hlam0 hlam1) ω
      (hX_pointwise n hn ω)

/-- The predictable-residual exponential is an e-process once its exact
conditional one-step inequality, adaptedness, and integrability obligations
have been discharged.  This is the reusable handoff point for any particular
plug-in empirical-Bernstein one-step lemma. -/
theorem forwardPlugIn_eProcess_of_condExp_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam psi : ℝ}
    (hadapted : MeasureTheory.StronglyAdapted ℱ
      (forwardPlugInExponentialProcess X mean lam psi))
    (hintegrable : ∀ n,
      MeasureTheory.Integrable (forwardPlugInExponentialProcess X mean lam psi n) μ)
    (hstep : ∀ n,
      μ[forwardPlugInExponentialProcess X mean lam psi (n + 1) | ℱ n]
        ≤ᵐ[μ] forwardPlugInExponentialProcess X mean lam psi n) :
    EProcess μ ℱ (forwardPlugInExponentialProcess X mean lam psi) where
  nonneg := fun _ _ ↦ (Real.exp_pos _).le
  start_one := fun ω ↦ by
    simp [forwardPlugInExponentialProcess, forwardPredictableQuadratic]
  supermartingale := MeasureTheory.supermartingale_nat hadapted hintegrable hstep

/-- A single checked certificate packages both the stochastic e-process and
its exact-Bessel lower envelope.  Notice that the conclusion intentionally
does not assert that the lower envelope itself is a supermartingale. -/
theorem forwardBesselEnvelope_certified_by_eProcess
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {mean lam psi : ℝ}
    (hpsi : 0 ≤ psi)
    (hadapted : MeasureTheory.StronglyAdapted ℱ
      (forwardPlugInExponentialProcess X mean lam psi))
    (hintegrable : ∀ n,
      MeasureTheory.Integrable (forwardPlugInExponentialProcess X mean lam psi n) μ)
    (hstep : ∀ n,
      μ[forwardPlugInExponentialProcess X mean lam psi (n + 1) | ℱ n]
        ≤ᵐ[μ] forwardPlugInExponentialProcess X mean lam psi n)
    (hX : ∀ n ≥ 2, ∀ ω, ∀ i < n, 0 ≤ X i ω ∧ X i ω ≤ 1) :
    EProcess μ ℱ (forwardPlugInExponentialProcess X mean lam psi) ∧
      ∀ n ≥ 2, ∀ ω,
        forwardBesselExponentialEnvelope X mean lam psi n ω ≤
          forwardPlugInExponentialProcess X mean lam psi n ω := by
  refine ⟨forwardPlugIn_eProcess_of_condExp_step hadapted hintegrable hstep, ?_⟩
  intro n hn ω
  exact forwardBesselExponentialEnvelope_le_forwardPlugIn
    X mean lam psi hn hpsi ω (hX n hn ω)

end

end FormalSLT.AnytimeValid
