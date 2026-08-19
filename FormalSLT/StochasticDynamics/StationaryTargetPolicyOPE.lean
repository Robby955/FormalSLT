/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ControlledTrajectory
import FormalSLT.StochasticDynamics.StationaryPoissonPACBayes

/-!
# Stationary target-policy off-policy evaluation

This file combines the controlled-trajectory importance-weighting semantics
with a supplied exact Poisson equation for a finite catalog of state-based
Markov target policies.  The behavior policy may depend on the full observed
history.  For each target policy, the caller supplies its invariant state PMF
and a bounded exact Poisson potential.  The resulting importance-weighted,
Poisson-corrected score has a constant conditional mean under the behavior
law, equal to an affine rescaling of the target policy's stationary risk.

The predictable-mean forward-Bessel PAC--Bayes theorem then gives one
outer-probability event, simultaneous over every time `n >= 2`, posterior PMF,
and atom of a finite declared tilt catalog.  The theorem assumes the
environment kernel and behavior propensities are known, uses one-step action
importance ratios only, and does not estimate invariant laws or Poisson
potentials.  It is not a full-trajectory importance-sampling theorem.
-/

open Filter Finset Function MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal NNReal Topology

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Z A ι τ : Type*}
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- A state-based Markov target policy.  Unlike `TargetPolicy`, it cannot
inspect the earlier controlled trajectory. -/
abbrev MarkovTargetPolicy (Z A : Type*) := Z → PMF A

/-- Embed a state-based target policy into the history-policy interface used
by the controlled semantic layer. -/
def markovTargetPolicyAsHistory
    (π : MarkovTargetPolicy Z A) : TargetPolicy Z A :=
  fun n u ↦ π (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2

/-- State transition kernel induced by a Markov target policy and the known
controlled environment. -/
def targetPolicyKernel
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A) (z : Z) : PMF Z :=
  (π z).bind (P z)

/-- A bounded reward/loss attached to a controlled transition. -/
abbrev TargetPolicyTransitionScore (Z A : Type*) := Z → A → Z → ℝ

/-- Target-policy one-step row risk at state `z`. -/
def targetPolicyRowRisk
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (score : TargetPolicyTransitionScore Z A) (z : Z) : ℝ :=
  ∑ a : A, (π z a).toReal *
    ∑ y : Z, (P z a y).toReal * score z a y

/-- Expected next-state potential under the target-policy kernel, written as
the action/outcome iterated sum used by the controlled path semantics. -/
def targetPolicyPotentialMean
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (potential : Z → ℝ) (z : Z) : ℝ :=
  ∑ a : A, (π z a).toReal *
    ∑ y : Z, (P z a y).toReal * potential y

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The iterated action/outcome potential mean is exactly expectation under
the induced target-policy state kernel. -/
theorem targetPolicyPotentialMean_eq_inducedKernel
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (potential : Z → ℝ) (z : Z) :
    targetPolicyPotentialMean P π potential z =
      markovPotentialMean (targetPolicyKernel P π) potential z := by
  classical
  unfold targetPolicyPotentialMean markovPotentialMean targetPolicyKernel
  rw [PMF.integral_eq_sum]
  simp only [PMF.bind_apply, tsum_fintype, smul_eq_mul]
  have hfinite : ∀ y : Z, ∀ a : A,
      π z a * P z a y ≠ (∞ : ENNReal) := by
    intro y a
    exact ENNReal.mul_ne_top ((π z).apply_ne_top a) ((P z a).apply_ne_top y)
  simp_rw [ENNReal.toReal_sum (fun a _ha ↦ hfinite _ a),
    ENNReal.toReal_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring_nf

/-- Stationary risk of a target policy under its supplied invariant state
PMF. -/
def stationaryTargetPolicyRisk
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z) (score : TargetPolicyTransitionScore Z A) : ℝ :=
  ∑ z : Z, (stationary z).toReal * targetPolicyRowRisk P π score z

/-- The supplied potential solves the target-policy Poisson equation exactly.
The invariant law is a separate explicit input to the capstone theorem. -/
def IsExactTargetPolicyPoissonSolution
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z) (score : TargetPolicyTransitionScore Z A)
    (potential : Z → ℝ) : Prop :=
  ∀ z,
    targetPolicyRowRisk P π score z +
        targetPolicyPotentialMean P π potential z - potential z =
      stationaryTargetPolicyRisk P π stationary score

/-- The target-policy Poisson correction, before action importance weighting.
It is a controlled transition score only through the current state exposed by
the final prefix coordinate. -/
def targetPolicyPoissonControlledScore
    (score : TargetPolicyTransitionScore Z A) (potential : Z → ℝ) (B : ℝ) :
    ControlledTransitionScore Z A :=
  fun n u a y ↦
    let z := (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
    (score z a y + potential y - potential z + B) / (1 + 2 * B)

/-- The normalized importance-weighted Poisson score observed under the
behavior trajectory.  Its exact formula is
`(π/β) * (score + h(next) - h(current) + B) / (C * (1 + 2B))`. -/
def stationaryTargetPolicyObservedScore
    (β : BehaviorPolicy Z A) (π : MarkovTargetPolicy Z A)
    (score : TargetPolicyTransitionScore Z A) (potential : Z → ℝ)
    (B C : ℝ) (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  controlledObservedImportanceScore β (markovTargetPolicyAsHistory π)
    (targetPolicyPoissonControlledScore score potential B) C n x

/-- The predictable target-policy conditional mean before applying the exact
Poisson identity. -/
def stationaryTargetPolicyPredictableMean
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (score : TargetPolicyTransitionScore Z A) (potential : Z → ℝ)
    (B C : ℝ) (n : ℕ) (x : ℕ → ControlledObservation Z A) : ℝ :=
  controlledTargetConditionalMean P (markovTargetPolicyAsHistory π)
    (targetPolicyPoissonControlledScore score potential B) C n x

omit [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The Poisson-corrected target transition score remains in `[0,1]`. -/
theorem targetPolicyPoissonControlledScore_mem_Icc
    {score : TargetPolicyTransitionScore Z A} {potential : Z → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hscore : ∀ z a y, score z a y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ z y, |potential y - potential z| ≤ B)
    (n : ℕ) (u : (i : Finset.Iic n) → ControlledObservation Z A)
    (a : A) (y : Z) :
    targetPolicyPoissonControlledScore score potential B n u a y ∈
      Set.Icc (0 : ℝ) 1 := by
  let z := (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  exact poissonCorrectedTransitionScore_mem_Icc
    hB (fun x y ↦ hscore x a y) hspan z y

/-- Exact target-policy conditional-mean identity.  The left side is the
quantity obtained after behavior-law importance weighting; the right side is
independent of the realized behavior history. -/
theorem stationaryTargetPolicyPredictableMean_eq
    (P : Z → A → PMF Z) (π : MarkovTargetPolicy Z A)
    (stationary : PMF Z) (score : TargetPolicyTransitionScore Z A)
    (potential : Z → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hpoisson : IsExactTargetPolicyPoissonSolution
      P π stationary score potential)
    (n : ℕ) (x : ℕ → ControlledObservation Z A) :
    stationaryTargetPolicyPredictableMean
        P π score potential B C n x =
      (stationaryTargetPolicyRisk P π stationary score + B) /
        (C * (1 + 2 * B)) := by
  classical
  let u := Preorder.frestrictLe n x
  let z := (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  have hden : 1 + 2 * B ≠ 0 := ne_of_gt (by linarith)
  have hCne : C ≠ 0 := hC.ne'
  have hπmass : ∑ a : A, ((π z a).toReal : ℝ) = 1 := by
    have hone := PMF.integral_eq_sum (π z) (fun _ : A ↦ (1 : ℝ))
    simpa [smul_eq_mul] using hone.symm
  have hPmass : ∀ a : A, ∑ y : Z, ((P z a y).toReal : ℝ) = 1 := by
    intro a
    have hone := PMF.integral_eq_sum (P z a) (fun _ : Z ↦ (1 : ℝ))
    simpa [smul_eq_mul] using hone.symm
  have hinner : ∀ a : A,
      (∑ y : Z, (P z a y).toReal *
          (score z a y + potential y - potential z + B)) =
        (∑ y : Z, (P z a y).toReal * score z a y) +
          (∑ y : Z, (P z a y).toReal * potential y) - potential z + B := by
    intro a
    simp_rw [show ∀ y : Z,
        (P z a y).toReal *
            (score z a y + potential y - potential z + B) =
          (P z a y).toReal * score z a y +
            (P z a y).toReal * potential y -
              (P z a y).toReal * potential z +
                (P z a y).toReal * B by
      intro y
      ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hPmass]
    ring
  have hnum :
      (∑ a : A, (π z a).toReal *
        ∑ y : Z, (P z a y).toReal *
          (score z a y + potential y - potential z + B)) =
        targetPolicyRowRisk P π score z +
          targetPolicyPotentialMean P π potential z - potential z + B := by
    simp_rw [hinner]
    unfold targetPolicyRowRisk targetPolicyPotentialMean
    simp_rw [show ∀ (a : A) (r p : ℝ),
        (π z a).toReal * (r + p - potential z + B) =
          (π z a).toReal * r + (π z a).toReal * p -
            (π z a).toReal * potential z + (π z a).toReal * B by
      intro a r p
      ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hπmass]
    ring
  have hscaled :
      stationaryTargetPolicyPredictableMean
          P π score potential B C n x =
        (targetPolicyRowRisk P π score z +
            targetPolicyPotentialMean P π potential z - potential z + B) /
          (C * (1 + 2 * B)) := by
    unfold stationaryTargetPolicyPredictableMean
      controlledTargetConditionalMean markovTargetPolicyAsHistory
      targetPolicyPoissonControlledScore
    simp only [u, z]
    rw [show
      (∑ a : A, (π z a).toReal *
        ∑ y : Z, (P z a y).toReal *
          ((score z a y + potential y - potential z + B) /
              (1 + 2 * B)) / C) =
        (∑ a : A, (π z a).toReal *
          ∑ y : Z, (P z a y).toReal *
            (score z a y + potential y - potential z + B)) /
          (C * (1 + 2 * B)) by
      calc
        _ = ∑ a : A, ∑ y : Z,
            ((π z a).toReal * (P z a y).toReal *
              (score z a y + potential y - potential z + B)) /
                (C * (1 + 2 * B)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          field_simp [hCne, hden]
        _ = (∑ a : A, ∑ y : Z,
            (π z a).toReal * (P z a y).toReal *
              (score z a y + potential y - potential z + B)) /
                (C * (1 + 2 * B)) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_div]
        _ = (∑ a : A, (π z a).toReal *
            ∑ y : Z, (P z a y).toReal *
              (score z a y + potential y - potential z + B)) /
                (C * (1 + 2 * B)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          ring]
    rw [hnum]
  rw [hscaled, hpoisson z]

/-- Direct conditional-expectation form of the stationary target-policy
identity under the history-dependent behavior trajectory law. -/
theorem stationaryTargetPolicyObservedScore_condExp
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (initial : ControlledObservation Z A)
    (π : MarkovTargetPolicy Z A) (stationary : PMF Z)
    (score : TargetPolicyTransitionScore Z A) (potential : Z → ℝ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hoverlap : ControlledPolicyOverlap β (markovTargetPolicyAsHistory π))
    (hratio : ControlledPolicyRatioBound
      β (markovTargetPolicyAsHistory π) C)
    (hscore : ∀ z a y, score z a y ∈ Set.Icc (0 : ℝ) 1)
    (hspan : ∀ z y, |potential y - potential z| ≤ B)
    (hpoisson : IsExactTargetPolicyPoissonSolution
      P π stationary score potential)
    (n : ℕ) :
    (controlledTrajectoryMeasure P β initial)[
        stationaryTargetPolicyObservedScore
          β π score potential B C n |
        Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
      controlledTrajectoryMeasure P β initial]
        fun _ ↦
          (stationaryTargetPolicyRisk P π stationary score + B) /
            (C * (1 + 2 * B)) := by
  have hbase := controlledObservedImportanceScore_condExp
    P β initial (markovTargetPolicyAsHistory π)
      (targetPolicyPoissonControlledScore score potential B) C
      hoverlap hratio hC
      (targetPolicyPoissonControlledScore_mem_Icc hB hscore hspan) n
  change
    (controlledTrajectoryMeasure P β initial)[
        controlledObservedImportanceScore β (markovTargetPolicyAsHistory π)
          (targetPolicyPoissonControlledScore score potential B) C n |
        Filtration.piLE
          (X := fun _ : ℕ ↦ ControlledObservation Z A) n] =ᵐ[
      controlledTrajectoryMeasure P β initial]
        fun _ ↦
          (stationaryTargetPolicyRisk P π stationary score + B) /
            (C * (1 + 2 * B))
  filter_upwards [hbase] with x hx
  rw [hx]
  exact stationaryTargetPolicyPredictableMean_eq
    P π stationary score potential hB hC hpoisson n x

/-- Posterior stationary risk across the finite target-policy catalog. -/
def stationaryTargetPolicyPosteriorRisk
    [Fintype ι]
    (P : Z → A → PMF Z) (π : ι → MarkovTargetPolicy Z A)
    (stationary : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (posterior : ι → ℝ) : ℝ :=
  posteriorAverage posterior fun i ↦
    stationaryTargetPolicyRisk P (π i) (stationary i) (score i)

/-- Posterior empirical mean of the normalized importance-weighted Poisson
scores actually observed under the behavior law. -/
def stationaryTargetPolicyPosteriorEmpiricalScore
    [Fintype ι]
    (β : BehaviorPolicy Z A) (π : ι → MarkovTargetPolicy Z A)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) (B C : ℝ)
    (posterior : ι → ℝ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) : ℝ :=
  posteriorAverage posterior fun i ↦
    forwardPrefixMean
      (fun k ↦ stationaryTargetPolicyObservedScore
        β (π i) (score i) (potential i) B C k x) n

/-- Complete target-policy OPE right-hand side for one declared tilt atom. -/
def stationaryTargetPolicyOPEBoundary
    [Fintype ι] [Fintype τ]
    (prior : ι → ℝ) (weight : τ → ℝ) (lam : τ → ℝ)
    (β : BehaviorPolicy Z A) (π : ι → MarkovTargetPolicy Z A)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) (B C : ℝ)
    (posterior : ι → ℝ) (delta : ℝ) (j : τ) (n : ℕ)
    (x : ℕ → ControlledObservation Z A) : ℝ :=
  C * (1 + 2 * B) *
      (stationaryTargetPolicyPosteriorEmpiricalScore
          β π score potential B C posterior n x +
        forwardPredictableMeanBesselPACBayesBoundary
          prior weight lam
            (fun i ↦ stationaryTargetPolicyObservedScore
              β (π i) (score i) (potential i) B C)
            posterior delta j n x) - B

/-- The posterior/time average of exact target-policy predictable means is the
affine rescaling of posterior stationary risk. -/
theorem posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean
    [Fintype ι]
    (P : Z → A → PMF Z) (π : ι → MarkovTargetPolicy Z A)
    (stationary : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hpoisson : ∀ i, IsExactTargetPolicyPoissonSolution
      P (π i) (stationary i) (score i) (potential i))
    (posterior : ι → ℝ) (hposterior : IsPMF posterior)
    (n : ℕ) (hn : 0 < n) (x : ℕ → ControlledObservation Z A) :
    posteriorAverage posterior
        (fun i ↦ forwardPrefixMean
          (fun k ↦ stationaryTargetPolicyPredictableMean
            P (π i) (score i) (potential i) B C k x) n) =
      (stationaryTargetPolicyPosteriorRisk
          P π stationary score posterior + B) /
        (C * (1 + 2 * B)) := by
  have hden : C * (1 + 2 * B) ≠ 0 := by
    exact mul_ne_zero hC.ne' (ne_of_gt (by linarith))
  have hone : ∀ i,
      forwardPrefixMean
          (fun k ↦ stationaryTargetPolicyPredictableMean
            P (π i) (score i) (potential i) B C k x) n =
        (stationaryTargetPolicyRisk
            P (π i) (stationary i) (score i) + B) /
          (C * (1 + 2 * B)) := by
    intro i
    unfold forwardPrefixMean
    simp_rw [stationaryTargetPolicyPredictableMean_eq
      P (π i) (stationary i) (score i) (potential i)
        hB hC (hpoisson i)]
    simp [hn.ne']
  unfold stationaryTargetPolicyPosteriorRisk posteriorAverage
  simp_rw [hone, ← mul_div_assoc]
  rw [← Finset.sum_div]
  apply (div_eq_div_iff hden hden).2
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hposterior.sum_one]
  ring

/-- Stationary target-policy empirical-Bernstein PAC--Bayes OPE theorem.

The supplied invariant PMFs identify the target-policy stationary risks, and
the supplied exact Poisson potentials flatten their behavior-law conditional
means.  One outer event is valid simultaneously for every `n >= 2`, every
post-data posterior PMF, and every atom of the declared finite tilt catalog;
therefore those choices may be made from the realized path after the event is
fixed. -/
theorem exists_stationaryTargetPolicyOPE_event
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
    (hpoisson : ∀ i, IsExactTargetPolicyPoissonSolution
      P (π i) (stationary i) (score i) (potential i))
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
                    posterior delta j n x := by
  have _hinvariant := hinvariant
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
    posteriorAverage_forwardPrefixMean_stationaryTargetPolicyPredictableMean
      P π stationary score potential hB hC hpoisson
        posterior hposterior n hnpos x
  rw [hleft] at hbase
  have hscaled := mul_lt_mul_of_pos_left hbase hden
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
              posterior delta j n x) - B
  linarith

omit [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- Explicit path/time/posterior/tilt specialization of the simultaneous OPE
conclusion.  This theorem introduces no selected stochastic process: it only
substitutes data-dependent choices into a bound that already holds for every
posterior, tilt atom, and time on the common event. -/
theorem stationaryTargetPolicyOPE_selected_of_simultaneous
    [Fintype ι] [Fintype τ]
    (P : Z → A → PMF Z) (β : BehaviorPolicy Z A)
    (π : ι → MarkovTargetPolicy Z A) (stationary : ι → PMF Z)
    (score : ι → TargetPolicyTransitionScore Z A)
    (potential : ι → Z → ℝ) (B C : ℝ)
    (prior : ι → ℝ) (weight : τ → ℝ) (lam : τ → ℝ) (delta : ℝ)
    (x : ℕ → ControlledObservation Z A)
    (hall : ∀ j : τ, ∀ posterior : ι → ℝ, IsPMF posterior →
      ∀ n : ℕ, 2 ≤ n →
        stationaryTargetPolicyPosteriorRisk
            P π stationary score posterior <
          stationaryTargetPolicyOPEBoundary
            prior weight lam β π score potential B C
              posterior delta j n x)
    (posterior : (ℕ → ControlledObservation Z A) → ℕ → ι → ℝ)
    (hposterior : ∀ x n, IsPMF (posterior x n))
    (select : (ℕ → ControlledObservation Z A) → ℕ → (ι → ℝ) → τ)
    (n : ℕ) (hn : 2 ≤ n) :
    stationaryTargetPolicyPosteriorRisk
        P π stationary score (posterior x n) <
      stationaryTargetPolicyOPEBoundary
        prior weight lam β π score potential B C
          (posterior x n) delta (select x n (posterior x n)) n x :=
  hall (select x n (posterior x n)) (posterior x n)
    (hposterior x n) n hn

end

end FormalSLT.StochasticDynamics
