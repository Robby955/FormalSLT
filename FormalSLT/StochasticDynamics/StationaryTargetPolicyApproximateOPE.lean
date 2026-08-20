/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.StationaryTargetPolicyRobustCandidate

/-!
# Approximate-Poisson stationary target-policy OPE

This module extends the supplied target-policy off-policy evaluation event from
exact Poisson potentials to fixed approximate potentials.  The raw
importance-weighted predictable mean is kept unflattened, then decomposed into
the stationary target-policy risk and the residual encountered along the
observed state path.  A pointwise residual envelope contributes exactly its
posterior average to the final upper bound.

The environment kernel, behavior propensities, target-policy catalog,
invariant PMFs, potentials, and residual envelopes are fixed inputs.  The one
outer event remains simultaneous over path, time, posterior, and the declared
finite tilt catalog, so those latter choices may be made after observing the
path.

This module does not construct finite-depth potentials, estimate or select an
environment candidate, construct invariant laws, intersect a transition-
confidence event, license a data-dependent residual envelope, provide a
full-trajectory importance-sampling identity, or prove a two-sided confidence
interval.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A ι τ : Type*}
  [Fintype Z] [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Posterior average of the approximate target-policy Poisson residuals
encountered in the first `n` current-state coordinates of a controlled path. -/
def stationaryTargetPolicyPosteriorResidualAverage
    [Fintype ι]
    (P : Z → A → PMF Z) (π : ι → MarkovTargetPolicy Z A)
    (stationary : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) (posterior : ι → ℝ)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  posteriorAverage posterior fun i ↦
    forwardPrefixMean
      (fun k ↦ approximateTargetPolicyPoissonResidual
        P (π i) (stationary i) (score i) (potential i) (x k).2) n

omit [Nonempty Z] in
/-- Posterior form of the unflattened predictable-mean identity.  The only
departure from the exact-Poisson formula is the signed residual average. -/
theorem posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean_approximate
    [Fintype ι]
    (P : Z → A → PMF Z) (π : ι → MarkovTargetPolicy Z A)
    (stationary : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) (x : ℕ → ControlledObservation Z A) :
    posteriorAverage posterior
        (fun i ↦ forwardPrefixMean
          (fun k ↦ stationaryTargetPolicyPredictableMean
            P (π i) (score i) (potential i) B C k x) n) =
      (stationaryTargetPolicyPosteriorRisk
          P π stationary score posterior +
        stationaryTargetPolicyPosteriorResidualAverage
          P π stationary score potential posterior n x + B) /
        (C * (1 + 2 * B)) := by
  have hden : C * (1 + 2 * B) ≠ 0 :=
    mul_ne_zero hC.ne' (ne_of_gt (by linarith))
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hpoint : ∀ i k,
      stationaryTargetPolicyPredictableMean
          P (π i) (score i) (potential i) B C k x =
        (stationaryTargetPolicyRisk
              P (π i) (stationary i) (score i) +
            approximateTargetPolicyPoissonResidual
              P (π i) (stationary i) (score i) (potential i) (x k).2 + B) /
          (C * (1 + 2 * B)) := by
    intro i k
    rw [stationaryTargetPolicyPredictableMean_eq_drift
      P (π i) (score i) (potential i) hB hC k x]
    unfold approximateTargetPolicyPoissonResidual targetPolicyPoissonDrift
    ring
  have hone : ∀ i,
      forwardPrefixMean
          (fun k ↦ stationaryTargetPolicyPredictableMean
            P (π i) (score i) (potential i) B C k x) n =
        (stationaryTargetPolicyRisk
              P (π i) (stationary i) (score i) +
            forwardPrefixMean
              (fun k ↦ approximateTargetPolicyPoissonResidual
                P (π i) (stationary i) (score i) (potential i) (x k).2) n + B) /
          (C * (1 + 2 * B)) := by
    intro i
    unfold forwardPrefixMean
    simp_rw [hpoint i]
    rw [← Finset.sum_div]
    simp_rw [Finset.sum_add_distrib]
    simp [Finset.sum_const, nsmul_eq_mul]
    field_simp [hden, hnreal]
  unfold stationaryTargetPolicyPosteriorRisk
    stationaryTargetPolicyPosteriorResidualAverage posteriorAverage
  simp_rw [hone, ← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (div_eq_div_iff hden hden).2
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hposterior.sum_one]
  ring

omit [Nonempty Z] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- A pointwise absolute residual envelope controls the negative encountered
residual after averaging over both time and a posterior PMF. -/
theorem neg_stationaryTargetPolicyPosteriorResidualAverage_le
    [Fintype ι]
    (P : Z → A → PMF Z) (π : ι → MarkovTargetPolicy Z A)
    (stationary : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ)
    {residualEnvelope : ι → ℝ}
    (hresidual : ∀ i z,
      |approximateTargetPolicyPoissonResidual
        P (π i) (stationary i) (score i) (potential i) z| ≤
          residualEnvelope i)
    {posterior : ι → ℝ} (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) (x : ℕ → ControlledObservation Z A) :
    -stationaryTargetPolicyPosteriorResidualAverage
        P π stationary score potential posterior n x ≤
      posteriorAverage posterior residualEnvelope := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold stationaryTargetPolicyPosteriorResidualAverage posteriorAverage
  rw [show
      -(∑ i : ι, posterior i *
          forwardPrefixMean
            (fun k ↦ approximateTargetPolicyPoissonResidual
              P (π i) (stationary i) (score i) (potential i) (x k).2) n) =
        ∑ i : ι, posterior i *
          (-forwardPrefixMean
            (fun k ↦ approximateTargetPolicyPoissonResidual
              P (π i) (stationary i) (score i) (potential i) (x k).2) n) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  apply Finset.sum_le_sum
  intro i _hi
  apply mul_le_mul_of_nonneg_left _ (hposterior.nonneg i)
  unfold forwardPrefixMean
  rw [← neg_div]
  apply (div_le_iff₀ hnreal).2
  have hsum :
      ∑ k ∈ Finset.range n,
          -approximateTargetPolicyPoissonResidual
            P (π i) (stationary i) (score i) (potential i) (x k).2 ≤
        ∑ _k ∈ Finset.range n, residualEnvelope i := by
    apply Finset.sum_le_sum
    intro k _hk
    exact (neg_le_abs _).trans (hresidual i (x k).2)
  rw [Finset.sum_neg_distrib] at hsum
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

omit [Nonempty Z] in
/-- Approximate-Poisson target-policy empirical-Bernstein PAC--Bayes OPE.

One outer event is simultaneous over every `n >= 2`, posterior PMF, and atom
of the fixed finite tilt catalog.  Relative to the exact-Poisson OPE boundary,
the theorem adds exactly the posterior average of the supplied pointwise
residual envelopes. -/
theorem exists_stationaryApproximateTargetPolicyOPE_event
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype τ] [DecidableEq τ] [Nonempty τ]
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : ι → MarkovTargetPolicy Z A) (stationary : ι → PMF Z)
    (hinvariant : ∀ i, IsInvariantPMF
      (targetPolicyKernel P (π i)) (stationary i))
    (score : ι → TargetPolicyTransitionScore Z A)
    (hscore : ∀ i z a y, score i z a y ∈ Set.Icc (0 : ℝ) 1)
    (potential : ι → Z → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hspan : ∀ i z y, |potential i y - potential i z| ≤ B)
    {residualEnvelope : ι → ℝ}
    (hresidual : ∀ i z,
      |approximateTargetPolicyPoissonResidual
        P (π i) (stationary i) (score i) (potential i) z| ≤
          residualEnvelope i)
    (hoverlap : ∀ i, ControlledPolicyOverlap
      β (markovTargetPolicyAsHistory (π i)))
    (hratio : ∀ i, ControlledPolicyRatioBound
      β (markovTargetPolicyAsHistory (π i)) C)
    {prior : ι → ℝ} (hprior : IsFullSupportPMF prior)
    {weight : τ → ℝ} (hweight : IsFullSupportPMF weight)
    {lam : τ → ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hlam : ∀ j, 0 < lam j) (hlam_one : ∀ j, lam j < 1) :
    ∃ goodEvent : Set (ℕ → ControlledObservation Z A),
      (controlledTrajectoryMeasure P β initial).real goodEventᶜ ≤ delta ∧
        ∀ x ∈ goodEvent, ∀ j : τ,
          ∀ posterior : ι → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryTargetPolicyPosteriorRisk
                  P π stationary score posterior <
                stationaryTargetPolicyOPEBoundary
                    prior weight lam β π score potential B C
                      posterior delta j n x +
                  posteriorAverage posterior residualEnvelope := by
  -- Invariance supplies the stationary interpretation.  The concentration
  -- algebra below uses the explicit residual decomposition.
  let _ := hinvariant
  have hcorrected : ∀ i n u a y,
      targetPolicyPoissonControlledScore
          (score i) (potential i) B n u a y ∈ Set.Icc (0 : ℝ) 1 := by
    intro i n u a y
    exact targetPolicyPoissonControlledScore_mem_Icc
      hB (hscore i) (hspan i) n u a y
  have hinterfaces := controlledImportanceCatalog_predictableMean_interfaces
    P β initial
      (fun i ↦ markovTargetPolicyAsHistory (π i))
      (fun i ↦ targetPolicyPoissonControlledScore
        (score i) (potential i) B)
      (fun _i ↦ C) hoverlap hratio (fun _i ↦ hC) hcorrected
  rcases hinterfaces with ⟨hXadapted, hmeanadapted, hXunit, hcond⟩
  rcases exists_forwardPredictableMeanBesselPACBayes_event
      (μ := controlledTrajectoryMeasure P β initial)
      (ℱ := Filtration.piLE
        (X := fun _ : ℕ ↦ ControlledObservation Z A))
      hprior hweight hdelta hlam hlam_one
      hXadapted hmeanadapted hXunit hcond with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior n hn
  have hnpos : 0 < n := by omega
  have hden : 0 < C * (1 + 2 * B) :=
    mul_pos hC (by linarith)
  have hbase :
      posteriorAverage posterior
          (fun i ↦ forwardPrefixMean
            (fun k ↦ stationaryTargetPolicyPredictableMean
              P (π i) (score i) (potential i) B C k x) n) <
        stationaryTargetPolicyPosteriorEmpiricalScore
            β π score potential B C posterior n x +
          forwardPredictableMeanBesselPACBayesBoundary
            prior weight lam
              (fun i ↦ controlledObservedImportanceScore β
                (markovTargetPolicyAsHistory (π i))
                (targetPolicyPoissonControlledScore
                  (score i) (potential i) B) C)
              posterior delta j n x := by
    simpa only [stationaryTargetPolicyPredictableMean,
      stationaryTargetPolicyObservedScore,
      stationaryTargetPolicyPosteriorEmpiricalScore] using
        hgood x hx j posterior hposterior n hn
  have hleft :=
    posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean_approximate
      P π stationary score potential hB hC
        posterior hposterior n hnpos x
  rw [hleft] at hbase
  have hscaled := mul_lt_mul_of_pos_left hbase hden
  have hres := neg_stationaryTargetPolicyPosteriorResidualAverage_le
    P π stationary score potential hresidual
      hposterior n hnpos x
  field_simp [ne_of_gt hden] at hscaled
  unfold stationaryTargetPolicyOPEBoundary
  change
    stationaryTargetPolicyPosteriorRisk P π stationary score posterior <
      C * (1 + 2 * B) *
        (stationaryTargetPolicyPosteriorEmpiricalScore
            β π score potential B C posterior n x +
          forwardPredictableMeanBesselPACBayesBoundary
            prior weight lam
              (fun i ↦ controlledObservedImportanceScore β
                (markovTargetPolicyAsHistory (π i))
                (targetPolicyPoissonControlledScore
                  (score i) (potential i) B) C)
              posterior delta j n x) - B +
        posteriorAverage posterior residualEnvelope
  linarith

end

end FormalSLT.StochasticDynamics
