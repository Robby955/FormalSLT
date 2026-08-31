/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.TrajectoryHalfTiltOrdinaryRiskPACBayes
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Compact arithmetic interface for half-tilt Brier certificates

This module separates the reusable statistical theorem from certificate-specific
exact rationals.  A generated checker supplies a finite prior and posterior,
an exact empirical Brier loss, a conservative rational upper bound on the
forward-predictor quadratic variation, and rational logarithm witnesses.  Lean
then checks the KL bound, confidence term, cumulant penalty, and final endpoint
without embedding every input row.

The row parser and independent replay checker remain outside the Lean trust
boundary and must be reported separately.  The theorem-backed claim concerns
posterior-averaged conditional Brier loss encountered on the monitored prefix.
-/

open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open scoped BigOperators

namespace FormalSLT.Applications.CompactHalfTiltBrierCertificate

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rational-friendly upper bound for `log (2^k * r)`. -/
def dyadicLogUpper (k : ℕ) (r : ℝ) : ℝ :=
  (k : ℝ) * (7 / 10 : ℝ) + (r - 1)

/-- `log 2 < 0.7` plus the tangent bound `log r ≤ r - 1` gives a
kernel-checkable logarithm ceiling requiring only an exact dyadic
factorization of the input. -/
theorem log_two_pow_mul_le_dyadicLogUpper
    (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Real.log ((2 : ℝ) ^ k * r) ≤ dyadicLogUpper k r := by
  rw [Real.log_mul (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)) hr.ne',
    Real.log_pow]
  have hlogTwo : Real.log 2 ≤ (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hpow : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * (7 / 10 : ℝ) :=
    mul_le_mul_of_nonneg_left hlogTwo (Nat.cast_nonneg k)
  have hremainder := Real.log_le_sub_one_of_pos hr
  unfold dyadicLogUpper
  linarith

omit [DecidableEq ι] in
/-- Termwise dyadic witnesses upper-bound the finite KL divergence.  Posterior
zeroes need no logarithm witness because their KL contribution is exactly
zero. -/
theorem klDiv_le_dyadicLogUpper
    {posterior prior : ι → ℝ}
    (hposterior : IsPMF posterior)
    (exponent : ι → ℕ) (remainder : ι → ℝ)
    (hfactor : ∀ i, posterior i = 0 ∨
      (0 < remainder i ∧
        posterior i / prior i = (2 : ℝ) ^ exponent i * remainder i)) :
    klDiv posterior prior ≤
      posteriorAverage posterior
        (fun i ↦ dyadicLogUpper (exponent i) (remainder i)) := by
  unfold klDiv posteriorAverage
  apply Finset.sum_le_sum
  intro i _hi
  rcases hfactor i with hzero | ⟨hremainder, hratio⟩
  · simp [hzero]
  · apply mul_le_mul_of_nonneg_left _ (hposterior.nonneg i)
    rw [hratio]
    exact log_two_pow_mul_le_dyadicLogUpper (exponent i) hremainder

/-- At half tilt, the empirical-Bernstein cumulant is below `1/5`. -/
theorem psi_half_lt_one_fifth :
    forwardEmpiricalBernsteinPsi (1 / 2 : ℝ) < 1 / 5 := by
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlogTwo : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  linarith

/-- Summary endpoint appearing in the half-tilt trajectory theorem. -/
def summaryEndpoint
    (empiricalRisk quadraticVariation : ℝ)
    (posterior prior : ι → ℝ) (delta : ℝ) (n : ℕ) : ℝ :=
  empiricalRisk +
    (klDiv posterior prior + Real.log (1 / delta) +
        forwardEmpiricalBernsteinPsi (1 / 2 : ℝ) * quadraticVariation) /
      ((1 / 2 : ℝ) * n)

omit [DecidableEq ι] in
/-- Compose kernel-checked upper bounds on KL and the confidence logarithm
with a nonnegative quadratic-variation input and rational endpoint arithmetic. -/
theorem summaryEndpoint_lt_of_bounds
    {empiricalRisk quadraticVariation klUpper logUpper bound : ℝ}
    {posterior prior : ι → ℝ} {delta : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hquadratic : 0 ≤ quadraticVariation)
    (hkl : klDiv posterior prior ≤ klUpper)
    (hlog : Real.log (1 / delta) ≤ logUpper)
    (harithmetic :
      empiricalRisk +
          (klUpper + logUpper + (1 / 5 : ℝ) * quadraticVariation) /
            ((1 / 2 : ℝ) * n) < bound) :
    summaryEndpoint empiricalRisk quadraticVariation posterior prior delta n <
      bound := by
  have hpsi :
      forwardEmpiricalBernsteinPsi (1 / 2 : ℝ) * quadraticVariation ≤
        (1 / 5 : ℝ) * quadraticVariation :=
    mul_le_mul_of_nonneg_right psi_half_lt_one_fifth.le hquadratic
  have hden : 0 < (1 / 2 : ℝ) * n :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hn)
  unfold summaryEndpoint
  apply lt_of_le_of_lt _ harithmetic
  gcongr

omit [DecidableEq ι] in
/-- Increasing the supplied quadratic variation can only increase the
half-tilt summary endpoint.  This is the bridge used when an external replay
computes a conservative fixed-denominator upper bound. -/
theorem summaryEndpoint_mono_quadraticVariation
    {empiricalRisk quadraticVariation quadraticVariationUpper : ℝ}
    {posterior prior : ι → ℝ} {delta : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hquadratic : quadraticVariation ≤ quadraticVariationUpper) :
    summaryEndpoint empiricalRisk quadraticVariation posterior prior delta n ≤
      summaryEndpoint empiricalRisk quadraticVariationUpper posterior prior delta n := by
  have hpsi :
      0 ≤ forwardEmpiricalBernsteinPsi (1 / 2 : ℝ) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have hden : 0 < (1 / 2 : ℝ) * n :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hn)
  unfold summaryEndpoint
  gcongr

omit [DecidableEq ι] in
/-- Conditional composition used by generated numerical receipts.  Coverage
comes from `exists_trajectoryHalfTiltPACBayes_ordinaryRisk_selected_event`;
this lemma does not assert that one named path belongs to its good event. -/
theorem conditionalRisk_lt_of_summary
    {conditionalRisk empiricalRisk quadraticVariation bound : ℝ}
    {posterior prior : ι → ℝ} {delta : ℝ} {n : ℕ}
    (hgood : conditionalRisk <
      summaryEndpoint empiricalRisk quadraticVariation posterior prior delta n)
    (hsummary :
      summaryEndpoint empiricalRisk quadraticVariation posterior prior delta n <
        bound) :
    conditionalRisk < bound :=
  hgood.trans hsummary

omit [DecidableEq ι] in
/-- Conditional composition with a conservative quadratic-variation upper
bound.  The external replay remains responsible for establishing
`quadraticVariation ≤ quadraticVariationUpper` from the prediction stream. -/
theorem conditionalRisk_lt_of_quadraticVariation_upper
    {conditionalRisk empiricalRisk quadraticVariation quadraticVariationUpper bound : ℝ}
    {posterior prior : ι → ℝ} {delta : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hquadratic : quadraticVariation ≤ quadraticVariationUpper)
    (hgood : conditionalRisk <
      summaryEndpoint empiricalRisk quadraticVariation posterior prior delta n)
    (hsummary :
      summaryEndpoint empiricalRisk quadraticVariationUpper posterior prior delta n <
        bound) :
    conditionalRisk < bound := by
  have hmono := summaryEndpoint_mono_quadraticVariation
    (empiricalRisk := empiricalRisk)
    (posterior := posterior) (prior := prior) (delta := delta)
    hn hquadratic
  exact (hgood.trans_le hmono).trans hsummary

end

end FormalSLT.Applications.CompactHalfTiltBrierCertificate
