/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonContraction

/-!
# Computable finite-state Dobrushin contraction

For finite probability mass functions, this module uses the probabilists'
total-variation convention

`TV(p,q) = (1/2) * sum_z |p(z) - q(z)|`.

The finite Dobrushin coefficient of a transition kernel is the maximum row
total variation.  The oscillation-duality lemma below therefore has no extra
factor two, and proves that the kernel's Markov operator contracts finite
oscillation by its computed Dobrushin coefficient.

The capstones instantiate the finite-depth Poisson stationary-risk theorem
with that coefficient.  They still require a supplied invariant PMF; no
unknown-kernel or invariant-law estimation is claimed here.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [Fintype Z] [Nonempty Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

omit [Nonempty Z] in
/-- A finite PMF's real masses sum to one. -/
lemma finitePMF_real_mass_sum (p : PMF Z) :
    ∑ z : Z, (p z).toReal = 1 := by
  have h := PMF.integral_eq_sum p (fun _ : Z ↦ (1 : ℝ))
  simpa using h.symm

/-- Probabilists' finite total variation: one half of the `L¹` row distance. -/
def finitePMFTotalVariation (p q : PMF Z) : ℝ :=
  (1 / 2 : ℝ) * ∑ z : Z, |(p z).toReal - (q z).toReal|

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma finitePMFTotalVariation_nonneg (p q : PMF Z) :
    0 ≤ finitePMFTotalVariation p q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun z _hz ↦ abs_nonneg _)

omit [Nonempty Z] in
lemma finitePMFTotalVariation_le_one (p q : PMF Z) :
    finitePMFTotalVariation p q ≤ 1 := by
  have hsum :
      (∑ z : Z, |(p z).toReal - (q z).toReal|) ≤ 2 := by
    calc
      (∑ z : Z, |(p z).toReal - (q z).toReal|) ≤
          ∑ z : Z, ((p z).toReal + (q z).toReal) := by
        apply Finset.sum_le_sum
        intro z _hz
        calc
          |(p z).toReal - (q z).toReal| ≤
              |(p z).toReal| + |(q z).toReal| := abs_sub _ _
          _ = (p z).toReal + (q z).toReal := by
            rw [abs_of_nonneg ENNReal.toReal_nonneg,
              abs_of_nonneg ENNReal.toReal_nonneg]
      _ = 2 := by
        rw [Finset.sum_add_distrib, finitePMF_real_mass_sum,
          finitePMF_real_mass_sum]
        norm_num
  unfold finitePMFTotalVariation
  nlinarith

omit [Nonempty Z] in
/-- Two finite PMFs that share the subprobability mass
`(1 - alpha) * reference` are within `alpha` in total variation. -/
theorem finitePMFTotalVariation_le_of_common_minorization
    (p q reference : PMF Z) {alpha : ℝ}
    (hp : ∀ z,
      (1 - alpha) * (reference z).toReal ≤ (p z).toReal)
    (hq : ∀ z,
      (1 - alpha) * (reference z).toReal ≤ (q z).toReal) :
    finitePMFTotalVariation p q ≤ alpha := by
  let base : Z → ℝ :=
    fun z ↦ (1 - alpha) * (reference z).toReal
  have hpointwise (z : Z) :
      |(p z).toReal - (q z).toReal| ≤
        ((p z).toReal - base z) + ((q z).toReal - base z) := by
    have hpz : 0 ≤ (p z).toReal - base z := sub_nonneg.mpr (hp z)
    have hqz : 0 ≤ (q z).toReal - base z := sub_nonneg.mpr (hq z)
    calc
      |(p z).toReal - (q z).toReal| =
          |((p z).toReal - base z) - ((q z).toReal - base z)| := by
            ring_nf
      _ ≤ |(p z).toReal - base z| + |(q z).toReal - base z| :=
        abs_sub _ _
      _ = ((p z).toReal - base z) + ((q z).toReal - base z) := by
        rw [abs_of_nonneg hpz, abs_of_nonneg hqz]
  have hbase : ∑ z : Z, base z = 1 - alpha := by
    simp only [base, ← Finset.mul_sum, finitePMF_real_mass_sum, mul_one]
  unfold finitePMFTotalVariation
  calc
    (1 / 2 : ℝ) * ∑ z : Z, |(p z).toReal - (q z).toReal| ≤
        (1 / 2 : ℝ) * ∑ z : Z,
          (((p z).toReal - base z) + ((q z).toReal - base z)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun z _hz ↦ hpointwise z) (by norm_num)
    _ = alpha := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, finitePMF_real_mass_sum,
        finitePMF_real_mass_sum, hbase]
      ring

omit [Nonempty Z] in
lemma finitePMFTotalVariation_mem_Icc (p q : PMF Z) :
    finitePMFTotalVariation p q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨finitePMFTotalVariation_nonneg p q,
    finitePMFTotalVariation_le_one p q⟩

/-- Sharp oscillation duality for finite PMFs under the `TV = L¹/2`
convention.  In particular, there is no additional factor two. -/
lemma abs_finitePMFExpectation_sub_le_totalVariation_mul_oscillation
    (p q : PMF Z) (f : Z → ℝ) :
    |(∑ z : Z, (p z).toReal * f z) -
        ∑ z : Z, (q z).toReal * f z| ≤
      finitePMFTotalVariation p q * finiteOscillation f := by
  obtain ⟨zmin, hmin⟩ := Finite.exists_min f
  obtain ⟨zmax, hmax⟩ := Finite.exists_max f
  let midpoint : ℝ := (f zmin + f zmax) / 2
  have hspan : f zmax - f zmin ≤ finiteOscillation f := by
    have h := abs_sub_le_finiteOscillation f zmin zmax
    rw [abs_of_nonneg (sub_nonneg.mpr (hmax zmin))] at h
    exact h
  have hmidpoint : ∀ z : Z,
      |f z - midpoint| ≤ finiteOscillation f / 2 := by
    intro z
    have hlo := hmin z
    have hhi := hmax z
    have hlocal : |f z - midpoint| ≤ (f zmax - f zmin) / 2 := by
      rw [abs_le]
      dsimp [midpoint]
      constructor <;> linarith
    exact hlocal.trans (div_le_div_of_nonneg_right hspan (by norm_num))
  have hmassdiff :
      ∑ z : Z, ((p z).toReal - (q z).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, finitePMF_real_mass_sum,
      finitePMF_real_mass_sum]
    norm_num
  have hcentered :
      (∑ z : Z, (p z).toReal * f z) -
          ∑ z : Z, (q z).toReal * f z =
        ∑ z : Z,
          ((p z).toReal - (q z).toReal) * (f z - midpoint) := by
    calc
      (∑ z : Z, (p z).toReal * f z) -
          ∑ z : Z, (q z).toReal * f z =
        ∑ z : Z,
          ((p z).toReal - (q z).toReal) * f z := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro z _hz
            ring
      _ = ∑ z : Z,
          (((p z).toReal - (q z).toReal) * (f z - midpoint) +
            ((p z).toReal - (q z).toReal) * midpoint) := by
            apply Finset.sum_congr rfl
            intro z _hz
            ring
      _ = (∑ z : Z,
          ((p z).toReal - (q z).toReal) * (f z - midpoint)) +
            ∑ z : Z, ((p z).toReal - (q z).toReal) * midpoint := by
              rw [Finset.sum_add_distrib]
      _ = ∑ z : Z,
          ((p z).toReal - (q z).toReal) * (f z - midpoint) := by
            rw [← Finset.sum_mul, hmassdiff, zero_mul, add_zero]
  rw [hcentered]
  calc
    |∑ z : Z,
        ((p z).toReal - (q z).toReal) * (f z - midpoint)| ≤
      ∑ z : Z,
        |((p z).toReal - (q z).toReal) * (f z - midpoint)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z : Z,
        |(p z).toReal - (q z).toReal| * |f z - midpoint| := by
          apply Finset.sum_congr rfl
          intro z _hz
          rw [abs_mul]
    _ ≤ ∑ z : Z,
        |(p z).toReal - (q z).toReal| * (finiteOscillation f / 2) := by
          apply Finset.sum_le_sum
          intro z _hz
          exact mul_le_mul_of_nonneg_left (hmidpoint z) (abs_nonneg _)
    _ = finitePMFTotalVariation p q * finiteOscillation f := by
          rw [← Finset.sum_mul]
          unfold finitePMFTotalVariation
          ring

lemma abs_pmfIntegral_sub_le_totalVariation_mul_oscillation
    (p q : PMF Z) (f : Z → ℝ) :
    |(∫ z, f z ∂p.toMeasure) - ∫ z, f z ∂q.toMeasure| ≤
      finitePMFTotalVariation p q * finiteOscillation f := by
  simpa only [PMF.integral_eq_sum, smul_eq_mul] using
    abs_finitePMFExpectation_sub_le_totalVariation_mul_oscillation p q f

/-- Maximum pairwise row total variation of a finite transition kernel. -/
def finiteDobrushinCoefficient (P : Z → PMF Z) : ℝ :=
  (Finset.univ : Finset Z).sup' Finset.univ_nonempty fun x ↦
    (Finset.univ : Finset Z).sup' Finset.univ_nonempty fun y ↦
      finitePMFTotalVariation (P x) (P y)

/-- A common row minorization bounds the finite Dobrushin coefficient. -/
theorem finiteDobrushinCoefficient_le_of_common_minorization
    (P : Z → PMF Z) (reference : PMF Z) {alpha : ℝ}
    (hminor : ∀ x z,
      (1 - alpha) * (reference z).toReal ≤ (P x z).toReal) :
    finiteDobrushinCoefficient P ≤ alpha := by
  unfold finiteDobrushinCoefficient
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro x _hx
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro y _hy
  exact finitePMFTotalVariation_le_of_common_minorization
    (P x) (P y) reference (hminor x) (hminor y)

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma finitePMFTotalVariation_le_finiteDobrushinCoefficient
    (P : Z → PMF Z) (x y : Z) :
    finitePMFTotalVariation (P x) (P y) ≤ finiteDobrushinCoefficient P := by
  unfold finiteDobrushinCoefficient
  exact (Finset.le_sup' (s := (Finset.univ : Finset Z))
    (fun y ↦ finitePMFTotalVariation (P x) (P y)) (Finset.mem_univ y)).trans
      (Finset.le_sup' (s := (Finset.univ : Finset Z))
        (fun x ↦ (Finset.univ : Finset Z).sup' Finset.univ_nonempty
          (fun y ↦ finitePMFTotalVariation (P x) (P y))) (Finset.mem_univ x))

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
lemma finiteDobrushinCoefficient_nonneg (P : Z → PMF Z) :
    0 ≤ finiteDobrushinCoefficient P := by
  let z : Z := Classical.choice inferInstance
  exact (finitePMFTotalVariation_nonneg (P z) (P z)).trans
    (finitePMFTotalVariation_le_finiteDobrushinCoefficient P z z)

lemma finiteDobrushinCoefficient_le_one (P : Z → PMF Z) :
    finiteDobrushinCoefficient P ≤ 1 := by
  unfold finiteDobrushinCoefficient
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro x _hx
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro y _hy
  exact finitePMFTotalVariation_le_one (P x) (P y)

lemma finiteDobrushinCoefficient_mem_Icc (P : Z → PMF Z) :
    finiteDobrushinCoefficient P ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨finiteDobrushinCoefficient_nonneg P,
    finiteDobrushinCoefficient_le_one P⟩

/-- The kernel's computed Dobrushin coefficient contracts finite
oscillation. -/
theorem finiteDobrushinCoefficient_isOscillationContraction
    (P : Z → PMF Z) :
    IsOscillationContraction P (finiteDobrushinCoefficient P) := by
  intro f
  apply finiteOscillation_le
  intro x y
  calc
    |markovPotentialMean P f y - markovPotentialMean P f x| ≤
        finitePMFTotalVariation (P y) (P x) * finiteOscillation f := by
          simpa only [markovPotentialMean] using
            abs_pmfIntegral_sub_le_totalVariation_mul_oscillation (P y) (P x) f
    _ ≤ finiteDobrushinCoefficient P * finiteOscillation f :=
      mul_le_mul_of_nonneg_right
        (finitePMFTotalVariation_le_finiteDobrushinCoefficient P y x)
        (finiteOscillation_nonneg f)

/-- Any upper bound on the finite Dobrushin coefficient is an oscillation
contraction factor. -/
theorem isOscillationContraction_of_finiteDobrushinCoefficient_le
    (P : Z → PMF Z) {alpha : ℝ}
    (hcoefficient : finiteDobrushinCoefficient P ≤ alpha) :
    IsOscillationContraction P alpha := by
  intro f
  calc
    finiteOscillation (markovPotentialMean P f) ≤
        finiteDobrushinCoefficient P * finiteOscillation f :=
      finiteDobrushinCoefficient_isOscillationContraction P f
    _ ≤ alpha * finiteOscillation f :=
      mul_le_mul_of_nonneg_right hcoefficient
        (finiteOscillation_nonneg f)

variable {I T : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype T] [DecidableEq T]

/-- Finite-depth stationary-risk capstone with the contraction factor
computed directly from the kernel.  `D` remains a supplied centered row-risk
oscillation envelope. -/
theorem exists_stationaryFiniteDepthDobrushinEmpiricalBernsteinPACBayes_closed_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    {D : ℝ} (hcoefficient : finiteDobrushinCoefficient P < 1)
    (hDnonneg : 0 ≤ D)
    (hD : ∀ i, finiteOscillation
      (centeredMarkovRowRisk P stationary (score i)) ≤ D)
    (m : ℕ)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : T → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : T → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : T,
          ∀ posterior : I → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient P) D m) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonClosedSpanBound
                            (finiteDobrushinCoefficient P) D m)
                          (score i)
                          (finiteDepthPoissonPotential P stationary (score i) m))
                        posterior delta j n x +
                  finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient P) D m / (n : ℝ) +
                    finiteDepthPoissonResidualBound
                      (finiteDobrushinCoefficient P) D m :=
  exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_closed_event
    P stationary hstationary x0 hscore
      (finiteDobrushinCoefficient_nonneg P) hcoefficient hDnonneg
      (finiteDobrushinCoefficient_isOscillationContraction P) hD m
      hprior hweight hdelta hlam hlam_one

/-- Unit-range convenience capstone with both the Dobrushin contraction and
the centered row-risk envelope discharged from the kernel and score range. -/
theorem exists_stationaryFiniteDepthDobrushinEmpiricalBernsteinPACBayes_unit_event
    (P : Z → PMF Z) (stationary : PMF Z)
    (hstationary : IsInvariantPMF P stationary) (x0 : Z)
    {score : I → MarkovTransitionScore Z}
    (hscore : ∀ i x y, score i x y ∈ Set.Icc (0 : ℝ) 1)
    (hcoefficient : finiteDobrushinCoefficient P < 1) (m : ℕ)
    {prior : I → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : T → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : T → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → Z),
      (markovPathMeasure P x0).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : T,
          ∀ posterior : I → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk P stationary score posterior <
                empiricalTransitionPosteriorRisk score posterior n x +
                  (1 + 2 * finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient P) 1 m) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      prior weight lam
                        (fun i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonClosedSpanBound
                            (finiteDobrushinCoefficient P) 1 m)
                          (score i)
                          (finiteDepthPoissonPotential P stationary (score i) m))
                        posterior delta j n x +
                  finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient P) 1 m / (n : ℝ) +
                    finiteDepthPoissonResidualBound
                      (finiteDobrushinCoefficient P) 1 m :=
  exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_unit_event
    P stationary hstationary x0 hscore
      (finiteDobrushinCoefficient_nonneg P) hcoefficient
      (finiteDobrushinCoefficient_isOscillationContraction P) m
      hprior hweight hdelta hlam hlam_one

end

end FormalSLT.StochasticDynamics
