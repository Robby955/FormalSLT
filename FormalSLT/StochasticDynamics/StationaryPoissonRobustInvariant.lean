/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryPoissonRobustCandidate

/-!
# Robust finite-state contraction and invariant-target uniqueness

For finite kernels `P` and `Q`, suppose every corresponding pair of rows is
within `eta` in probabilists' total variation.  The triangle inequality gives

`Dobrushin(P) <= Dobrushin(Q) + 2 * eta`.

Consequently, the checkable strict inequality
`Dobrushin(Q) + 2 * eta < 1` certifies oscillation contraction of the true
kernel `P`.  Under that certificate, any two supplied invariant PMFs of `P`
are equal, so the stationary-risk target is independent of the invariant
witness used to state it.

This is deterministic robustness infrastructure.  It neither estimates a
kernel nor proves that an invariant PMF exists.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z : Type*} [Fintype Z] [Nonempty Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Triangle inequality for probabilists' finite total variation. -/
lemma finitePMFTotalVariation_triangle (p q r : PMF Z) :
    finitePMFTotalVariation p r ≤
      finitePMFTotalVariation p q + finitePMFTotalVariation q r := by
  have hsum :
      (∑ z : Z, |(p z).toReal - (r z).toReal|) ≤
        (∑ z : Z, |(p z).toReal - (q z).toReal|) +
          ∑ z : Z, |(q z).toReal - (r z).toReal| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _hz
    calc
      |(p z).toReal - (r z).toReal| =
          |((p z).toReal - (q z).toReal) +
            ((q z).toReal - (r z).toReal)| := by ring_nf
      _ ≤ |(p z).toReal - (q z).toReal| +
          |(q z).toReal - (r z).toReal| := abs_add_le _ _
  unfold finitePMFTotalVariation
  nlinarith

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Symmetry of probabilists' finite total variation. -/
lemma finitePMFTotalVariation_comm (p q : PMF Z) :
    finitePMFTotalVariation p q = finitePMFTotalVariation q p := by
  unfold finitePMFTotalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro z _hz
  exact abs_sub_comm _ _

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Rowwise kernel error perturbs the finite Dobrushin coefficient by at most
twice the row error.  The factor two comes from comparing both endpoints of a
pair of true rows with their candidate rows. -/
theorem finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta) :
    finiteDobrushinCoefficient P ≤
      finiteDobrushinCoefficient Q + 2 * eta := by
  unfold finiteDobrushinCoefficient
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro x _hx
  refine Finset.sup'_le Finset.univ_nonempty _ ?_
  intro y _hy
  calc
    finitePMFTotalVariation (P x) (P y) ≤
        finitePMFTotalVariation (P x) (Q x) +
          finitePMFTotalVariation (Q x) (P y) :=
      finitePMFTotalVariation_triangle (P x) (Q x) (P y)
    _ ≤ finitePMFTotalVariation (P x) (Q x) +
        (finitePMFTotalVariation (Q x) (Q y) +
          finitePMFTotalVariation (Q y) (P y)) := by
      gcongr
      exact finitePMFTotalVariation_triangle (Q x) (Q y) (P y)
    _ ≤ eta + (finiteDobrushinCoefficient Q + eta) := by
      gcongr
      · exact hrowTV x
      · exact finitePMFTotalVariation_le_finiteDobrushinCoefficient Q x y
      · rw [finitePMFTotalVariation_comm]
        exact hrowTV y
    _ = finiteDobrushinCoefficient Q + 2 * eta := by ring

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- A candidate coefficient plus a uniform row-TV radius below one certifies
that the true kernel's computed coefficient is below one. -/
theorem finiteDobrushinCoefficient_lt_one_of_candidate_rowTV
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (hcertificate : finiteDobrushinCoefficient Q + 2 * eta < 1) :
    finiteDobrushinCoefficient P < 1 :=
  (finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
    P Q hrowTV).trans_lt hcertificate

/-- The candidate coefficient plus the row-TV radius is a valid oscillation
contraction factor for the true kernel. -/
theorem candidateDobrushin_add_two_mul_rowTV_isOscillationContraction
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta) :
    IsOscillationContraction P
      (finiteDobrushinCoefficient Q + 2 * eta) := by
  intro f
  calc
    finiteOscillation (markovPotentialMean P f) ≤
        finiteDobrushinCoefficient P * finiteOscillation f :=
      finiteDobrushinCoefficient_isOscillationContraction P f
    _ ≤ (finiteDobrushinCoefficient Q + 2 * eta) *
        finiteOscillation f :=
      mul_le_mul_of_nonneg_right
        (finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
          P Q hrowTV)
        (finiteOscillation_nonneg f)

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- A finite PMF pair has zero total variation exactly when the PMFs are
equal. -/
lemma finitePMFTotalVariation_eq_zero_iff (p q : PMF Z) :
    finitePMFTotalVariation p q = 0 ↔ p = q := by
  constructor
  · intro htv
    have hsum : ∑ z : Z, |(p z).toReal - (q z).toReal| = 0 := by
      unfold finitePMFTotalVariation at htv
      nlinarith
    apply PMF.ext
    intro z
    have hz : |(p z).toReal - (q z).toReal| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _hy ↦ abs_nonneg ((p y).toReal - (q y).toReal))).mp
          hsum z (Finset.mem_univ z)
    have hreal : (p z).toReal = (q z).toReal := by
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    exact (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top p z) (PMF.apply_ne_top q z)).mp hreal
  · rintro rfl
    unfold finitePMFTotalVariation
    simp

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Sign of the real mass difference of two finite PMFs. -/
private def finitePMFMassSign (p q : PMF Z) (z : Z) : ℝ :=
  if (q z).toReal ≤ (p z).toReal then 1 else -1

omit [Fintype Z] [Nonempty Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private lemma sub_mul_finitePMFMassSign (p q : PMF Z) (z : Z) :
    ((p z).toReal - (q z).toReal) * finitePMFMassSign p q z =
      |(p z).toReal - (q z).toReal| := by
  unfold finitePMFMassSign
  by_cases h : (q z).toReal ≤ (p z).toReal
  · simp [h, abs_of_nonneg (sub_nonneg.mpr h)]
  · have hle : (p z).toReal - (q z).toReal ≤ 0 := by linarith
    simp [h, abs_of_nonpos hle]

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private lemma finitePMFMassSign_oscillation_le_two (p q : PMF Z) :
    finiteOscillation (finitePMFMassSign p q) ≤ 2 := by
  apply finiteOscillation_le
  intro x y
  unfold finitePMFMassSign
  split_ifs <;> norm_num

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
private lemma finitePMFMassSign_expectation_gap (p q : PMF Z) :
    (∑ z : Z, (p z).toReal * finitePMFMassSign p q z) -
        ∑ z : Z, (q z).toReal * finitePMFMassSign p q z =
      2 * finitePMFTotalVariation p q := by
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ z : Z,
        ((p z).toReal * finitePMFMassSign p q z -
          (q z).toReal * finitePMFMassSign p q z) =
      ∑ z : Z,
        ((p z).toReal - (q z).toReal) * finitePMFMassSign p q z := by
          apply Finset.sum_congr rfl
          intro z _hz
          ring
    _ = ∑ z : Z, |(p z).toReal - (q z).toReal| := by
          apply Finset.sum_congr rfl
          intro z _hz
          exact sub_mul_finitePMFMassSign p q z
    _ = 2 * finitePMFTotalVariation p q := by
          unfold finitePMFTotalVariation
          ring

/-- A finite kernel with Dobrushin coefficient below one has at most one
invariant PMF.  This is a uniqueness theorem for supplied invariant laws; it
does not construct one. -/
theorem invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one
    (P : Z → PMF Z)
    (hcoefficient : finiteDobrushinCoefficient P < 1)
    (stationary₁ stationary₂ : PMF Z)
    (hstationary₁ : IsInvariantPMF P stationary₁)
    (hstationary₂ : IsInvariantPMF P stationary₂) :
    stationary₁ = stationary₂ := by
  let sign : Z → ℝ := finitePMFMassSign stationary₁ stationary₂
  let d : ℝ := finitePMFTotalVariation stationary₁ stationary₂
  have hsign : finiteOscillation sign ≤ 2 :=
    finitePMFMassSign_oscillation_le_two stationary₁ stationary₂
  have hinvariant₁ := markovPotentialMean_invariant
    P stationary₁ hstationary₁ sign
  have hinvariant₂ := markovPotentialMean_invariant
    P stationary₂ hstationary₂ sign
  have hgap :
      (∑ z : Z, (stationary₁ z).toReal * sign z) -
          ∑ z : Z, (stationary₂ z).toReal * sign z = 2 * d := by
    exact finitePMFMassSign_expectation_gap stationary₁ stationary₂
  have hcontract := finiteDobrushinCoefficient_isOscillationContraction P sign
  have hbound : 2 * d ≤ 2 * finiteDobrushinCoefficient P * d := by
    calc
      2 * d =
          |(∑ z : Z, (stationary₁ z).toReal * sign z) -
            ∑ z : Z, (stationary₂ z).toReal * sign z| := by
              rw [hgap, abs_of_nonneg]
              exact mul_nonneg (by norm_num)
                (finitePMFTotalVariation_nonneg stationary₁ stationary₂)
      _ =
          |(∑ z : Z, (stationary₁ z).toReal * markovPotentialMean P sign z) -
            ∑ z : Z, (stationary₂ z).toReal * markovPotentialMean P sign z| := by
              simp only [PMF.integral_eq_sum, smul_eq_mul] at hinvariant₁ hinvariant₂
              rw [hinvariant₁, hinvariant₂]
      _ ≤ d * finiteOscillation (markovPotentialMean P sign) := by
              exact abs_finitePMFExpectation_sub_le_totalVariation_mul_oscillation
                stationary₁ stationary₂ (markovPotentialMean P sign)
      _ ≤ d * (finiteDobrushinCoefficient P * finiteOscillation sign) := by
              exact mul_le_mul_of_nonneg_left hcontract
                (finitePMFTotalVariation_nonneg stationary₁ stationary₂)
      _ ≤ d * (finiteDobrushinCoefficient P * 2) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsign
                  (finiteDobrushinCoefficient_nonneg P))
                (finitePMFTotalVariation_nonneg stationary₁ stationary₂)
      _ = 2 * finiteDobrushinCoefficient P * d := by ring
  have hd : d = 0 := by
    have hdnonneg : 0 ≤ d :=
      finitePMFTotalVariation_nonneg stationary₁ stationary₂
    nlinarith
  exact (finitePMFTotalVariation_eq_zero_iff stationary₁ stationary₂).mp hd

/-- Candidate-kernel row-TV control certifies uniqueness of every supplied
true invariant PMF. -/
theorem invariantPMF_unique_of_candidate_rowTV
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (hcertificate : finiteDobrushinCoefficient Q + 2 * eta < 1)
    (stationary₁ stationary₂ : PMF Z)
    (hstationary₁ : IsInvariantPMF P stationary₁)
    (hstationary₂ : IsInvariantPMF P stationary₂) :
    stationary₁ = stationary₂ :=
  invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one P
    (finiteDobrushinCoefficient_lt_one_of_candidate_rowTV
      P Q hrowTV hcertificate)
    stationary₁ stationary₂ hstationary₁ hstationary₂

/-- Under the candidate row-TV certificate, the stationary transition-risk
target is independent of which supplied invariant witness is used. -/
theorem stationaryMarkovRisk_eq_of_candidate_rowTV
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (hcertificate : finiteDobrushinCoefficient Q + 2 * eta < 1)
    (stationary₁ stationary₂ : PMF Z)
    (hstationary₁ : IsInvariantPMF P stationary₁)
    (hstationary₂ : IsInvariantPMF P stationary₂)
    (score : MarkovTransitionScore Z) :
    stationaryMarkovRisk P stationary₁ score =
      stationaryMarkovRisk P stationary₂ score := by
  rw [invariantPMF_unique_of_candidate_rowTV P Q hrowTV hcertificate
    stationary₁ stationary₂ hstationary₁ hstationary₂]

variable {I : Type*} [Fintype I]

/-- Posterior-averaged stationary risk is likewise independent of the
supplied invariant witness. -/
theorem stationaryPosteriorMarkovRisk_eq_of_candidate_rowTV
    (P Q : Z → PMF Z) {eta : ℝ}
    (hrowTV : ∀ z, finitePMFTotalVariation (P z) (Q z) ≤ eta)
    (hcertificate : finiteDobrushinCoefficient Q + 2 * eta < 1)
    (stationary₁ stationary₂ : PMF Z)
    (hstationary₁ : IsInvariantPMF P stationary₁)
    (hstationary₂ : IsInvariantPMF P stationary₂)
    (score : I → MarkovTransitionScore Z) (posterior : I → ℝ) :
    stationaryPosteriorMarkovRisk P stationary₁ score posterior =
      stationaryPosteriorMarkovRisk P stationary₂ score posterior := by
  rw [invariantPMF_unique_of_candidate_rowTV P Q hrowTV hcertificate
    stationary₁ stationary₂ hstationary₁ hstationary₂]

end

end FormalSLT.StochasticDynamics
