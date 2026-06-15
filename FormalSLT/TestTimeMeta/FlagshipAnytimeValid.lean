/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipSimultaneousAssembly
import FormalSLT.TestTimeMeta.CompositionLemmas

/-!
# Anytime-valid flagship assembly

## Scope

This module keeps the q092 simultaneous flagship certificate as the fixed-horizon
base and adds an anytime-valid event controlled by Ville's maximal inequality.
The event is a finite running maximum over the sub-Gamma exponential process, so
it represents any boundary crossing up to the stated horizon.

## Assumptions

The anytime result assumes the same conditional sub-Gamma increment model used
by the fixed-horizon Ville slot: bounded increments, conditional centering,
conditional second-moment control, adaptedness, integrability, and a positive
tilt with `b * lam < 3`.

## Current boundaries

This is a finite-horizon anytime statement.  It certifies crossings up to the
chosen horizon and does not claim an infinite-time confidence sequence.  The
proof is intentionally routed through `ville_subGamma_maximal_bound`; replacing
that step by scalar nonnegativity would not prove this event-mass bound.
-/

namespace FormalSLT.TestTimeMeta

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid

noncomputable section

/--
The anytime-valid boundary event controlled by Ville.

The finite running maximum ranges over every time index `k <= horizon`.  A
single crossing at any such time is therefore a member of this event.
-/
def flagshipAnytimeUniformBoundaryEvent {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ) (horizon : ℕ) : Set Ω :=
  {ω | Real.exp (lam * (horizon : ℝ) * t)
      ≤ finiteRunningMax (subGammaExponentialProcess X sigma2 b lam) horizon ω}

/-- A time-`n` crossing with `n <= horizon` is part of the anytime event. -/
theorem flagshipAnytimeUniformBoundaryEvent_of_time_crossing
    {Ω : Type*} {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ}
    {horizon n : ℕ} {ω : Ω}
    (hn : n ≤ horizon)
    (hcross :
      Real.exp (lam * (horizon : ℝ) * t)
        ≤ subGammaExponentialProcess X sigma2 b lam n ω) :
    ω ∈ flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t horizon := by
  dsimp [flagshipAnytimeUniformBoundaryEvent, finiteRunningMax]
  exact hcross.trans
    (Finset.le_sup' (f := fun k => subGammaExponentialProcess X sigma2 b lam k ω)
      (s := Finset.range (horizon + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/--
Ville controls the mass of the anytime-valid boundary event.

This is the load-bearing step: the conclusion is about the running maximum over
all times up to `horizon`, so it needs the maximal inequality rather than a
fixed-time scalar decomposition.
-/
theorem flagshipAnytimeUniformBoundaryMass_le_from_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {horizon : ℕ}
    (hsup : Supermartingale (subGammaExponentialProcess X sigma2 b lam) ℱ μ) :
    μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t horizon)
      ≤ anytimeVilleTailContribution lam horizon t := by
  dsimp [flagshipAnytimeUniformBoundaryEvent, anytimeVilleTailContribution]
  exact ville_subGamma_maximal_bound hsup horizon t

/--
End-to-end anytime boundary mass bound from the conditional sub-Gamma increment
model.
-/
theorem flagshipAnytimeUniformBoundaryMass_le_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {horizon : ℕ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t horizon)
      ≤ anytimeVilleTailContribution lam horizon t := by
  exact flagshipAnytimeUniformBoundaryMass_le_from_supermartingale
    (nonneg_supermartingale_of_condSubGamma h_adapted h_integrable
      (condSubGamma_supermartingale_step hb hσ hlam.le hblam hX_meas hX_int
        h_adapted hbound hcenter hvar)).1

/--
q095 flagship conclusion: the existing fixed-horizon q092 certificate plus a
separate anytime-valid event-mass certificate.
-/
structure FlagshipAnytimeValidConclusion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (sigma2 b lam t : ℝ)
    (horizon : ℕ) : Prop where
  fixedHorizonFlagship : flagshipConclusion flagshipSimultaneous_certificate
  anytimeUniform :
    μ.real (flagshipAnytimeUniformBoundaryEvent X sigma2 b lam t horizon)
      ≤ anytimeVilleTailContribution lam horizon t

/--
Public q095 endpoint.  The fixed-horizon certificate is q092; the new anytime
field is proved from the increment model through Ville's maximal inequality.
-/
theorem flagshipAnytimeValid_conclusion_from_incrementModel
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam t : ℝ} {horizon : ℕ}
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    FlagshipAnytimeValidConclusion μ X sigma2 b lam t horizon := by
  refine ⟨flagshipSimultaneous_conclusion, ?_⟩
  exact flagshipAnytimeUniformBoundaryMass_le_from_incrementModel
    hb hσ hlam hblam hX_meas hX_int h_adapted h_integrable
    hbound hcenter hvar

end

end FormalSLT.TestTimeMeta
