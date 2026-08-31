/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.SingularFractionExactOptimizer
import FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes

/-!
# Exact scalar-fraction optimization for two-sided continuous PAC-Bayes bounds

The two-sided all-fractions event is established before the observed path,
posterior, reporting time, or scalar fraction is selected.  This module
therefore substitutes the exact attained minimizer of the original
singular-fraction boundary pointwise, without defining an event or stochastic
process in terms of that minimizer.

`singularFractionExactOptimalLambda` is noncomputable: it is obtained with
`Classical.choose`, and no measurable or executable optimizer is claimed.
Its use here is legitimate because it is eliminated only after the theorem
has already quantified every admissible scalar fraction.  The result is exact
only over that scalar fraction.  It is not a universal predictable-strategy
or coin-betting competitor.

The target remains the posterior-averaged conditional loss encountered on the
monitored prefix.  It is not future, population, stationary, or deployment
risk.  The exact boundary is proved no larger than the existing observable
LIL-order envelope, but no strict-improvement claim is made.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.ContinuousSingularFractionBesselPACBayes
open FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionExactOptimalPACBayes

noncomputable section

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-- Absorbing the posterior KL cost into the effective confidence identifies
the continuous PAC-Bayes boundary exactly with the original scalar
singular-fraction numerator, divided by the reporting time. -/
theorem continuousSingularFractionBesselBoundary_eq_exactNumerator_effectiveConfidence
    (prior : Measure Theta) (X : Theta → Nat → Omega → Real)
    (posterior : Measure Theta) {delta lam : Real}
    (hdelta : 0 < delta) (hlam_pos : 0 < lam)
    (hlam : lam ≤ Real.exp (-1)) (n : Nat) (omega : Omega) :
    continuousSingularFractionBesselBoundary
        prior X posterior delta lam n omega =
      singularFractionExactNumerator
          (continuousForwardPosteriorHybridBesselPenalty
            posterior X n omega)
          (continuousSingularFractionBesselEffectiveConfidence
            prior posterior delta)
          lam /
        (n : Real) := by
  let Q := continuousForwardPosteriorHybridBesselPenalty posterior X n omega
  let L := singularFractionLogScale lam
  let A := L * (L + 1)
  have hL : 1 ≤ L := by
    simpa [L] using one_le_singularFractionLogScale hlam_pos hlam
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (zero_lt_one.trans_le hL) (by linarith)
  have hlog := continuousSingularFractionBessel_log_effectiveConfidence
    prior posterior hdelta hA
  unfold continuousSingularFractionBesselBoundary
    singularFractionExactNumerator
  change
    (lam * Q + Real.exp 1 / lam *
        ((InformationTheory.klDiv posterior prior).toReal +
          Real.log (A / delta))) /
        (n : Real) =
      (lam * Q + Real.exp 1 / lam *
        Real.log
          (A / continuousSingularFractionBesselEffectiveConfidence
            prior posterior delta)) /
        (n : Real)
  rw [hlog]

/-- The exact optimized continuous PAC-Bayes radius is no larger than the
radius at any admissible scalar fraction.  This is scalar-fraction optimality
only; it does not compare against arbitrary predictable strategies. -/
theorem continuousSingularFractionExactBoundary_le_pacBayesBoundary
    (prior : Measure Theta) (X : Theta → Nat → Omega → Real)
    (posterior : Measure Theta) {delta lam : Real}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hlam_pos : 0 < lam) (hlam : lam ≤ Real.exp (-1))
    (n : Nat) (omega : Omega)
    (hQ : 0 ≤ continuousForwardPosteriorHybridBesselPenalty
      posterior X n omega) :
    singularFractionExactBoundary
          (continuousForwardPosteriorHybridBesselPenalty posterior X n omega)
          (continuousSingularFractionBesselEffectiveConfidence
            prior posterior delta) /
        (n : Real) ≤
      continuousSingularFractionBesselBoundary
        prior X posterior delta lam n omega := by
  have heffective_pos :=
    continuousSingularFractionBesselEffectiveConfidence_pos
      prior posterior hdelta
  have heffective_one :=
    continuousSingularFractionBesselEffectiveConfidence_le_one
      prior posterior hdelta hdelta_one
  rw [continuousSingularFractionBesselBoundary_eq_exactNumerator_effectiveConfidence
    prior X posterior hdelta hlam_pos hlam n omega]
  exact div_le_div_of_nonneg_right
    (singularFractionExactBoundary_le
      hQ heffective_pos heffective_one hlam_pos hlam)
    (Nat.cast_nonneg n)

/-- The attained exact scalar-fraction boundary is no larger than the existing
explicit observable LIL-order envelope.  The comparison is weak (`≤`), and
does not assert that the improvement is strict on any input. -/
theorem singularFractionExactBoundary_le_observableLIL
    {Q delta : Real} (hQ : 0 ≤ Q)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    singularFractionExactBoundary Q delta ≤
      singularFractionObservableLILBoundary Q delta := by
  let lam := singularFractionObservableTunedLambda Q delta
  have hlam_pos : 0 < lam := by
    simpa [lam] using singularFractionObservableTunedLambda_pos Q delta
  have hlam : lam ≤ Real.exp (-1) := by
    simpa [lam] using
      singularFractionObservableTunedLambda_le_exp_neg_one Q delta
  have hminimum := singularFractionExactBoundary_le
    hQ hdelta hdelta_one hlam_pos hlam
  have henvelope := singularFraction_tunedBoundary_le_observableLIL
    hQ hdelta hdelta_one
  exact hminimum.trans (by
    simpa [singularFractionExactNumerator, lam] using henvelope)

/-- Continuous-posterior specialization of exact-boundary dominance after the
posterior KL cost has been absorbed into the confidence parameter. -/
theorem continuousSingularFractionExactBoundary_le_observableLIL
    (prior posterior : Measure Theta)
    (X : Theta → Nat → Omega → Real)
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (n : Nat) (omega : Omega)
    (hQ : 0 ≤ continuousForwardPosteriorHybridBesselPenalty
      posterior X n omega) :
    singularFractionExactBoundary
        (continuousForwardPosteriorHybridBesselPenalty posterior X n omega)
        (continuousSingularFractionBesselEffectiveConfidence
          prior posterior delta) ≤
      singularFractionObservableLILBoundary
        (continuousForwardPosteriorHybridBesselPenalty posterior X n omega)
        (continuousSingularFractionBesselEffectiveConfidence
          prior posterior delta) := by
  apply singularFractionExactBoundary_le_observableLIL hQ
  · exact continuousSingularFractionBesselEffectiveConfidence_pos
      prior posterior hdelta
  · exact continuousSingularFractionBesselEffectiveConfidence_le_one
      prior posterior hdelta hdelta_one

/-- One outer-probability event controls the exact optimized two-sided
posterior-averaged conditional-minus-observed prefix gap at every reporting
time and for every eligible posterior selected from the observed path.

The exact optimizer is selected only after applying the all-fractions event;
neither the event nor either e-process depends on it.  The two tails each use
budget `delta / 2`, so the effective confidence below includes both the
posterior KL price and the two-tail `log 2` price. -/
theorem exists_continuousTwoSidedSingularFractionExactOptimalPACBayes_event
    [IsProbabilityMeasure mu]
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {X mean : Theta → Nat → Omega → Real} {delta : Real}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hX_adapted : ∀ theta, IncrementAdapted F (X theta))
    (hmean_adapted : ∀ theta, StronglyAdapted F (mean theta))
    (hX_unit : ∀ theta k omega,
      X theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean_unit : ∀ theta k omega,
      mean theta k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ theta k,
      mu[X theta k | F k] =ᵐ[mu] mean theta k)
    (hX_parameter : ∀ k omega,
      StronglyMeasurable (fun theta => X theta k omega))
    (hmean_parameter : ∀ k omega,
      StronglyMeasurable (fun theta => mean theta k omega))
    (hjoint_lower_ambient : ∀ n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (X q.2.2) (mean q.2.2) (singularFraction q.2.1) n q.1))
    (hjoint_lower_filtered : ∀ n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × (Real × Theta) =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (X q.2.2) (mean q.2.2)
              (singularFraction q.2.1) n q.1))
    (hjoint_upper_ambient : ∀ n, StronglyMeasurable
      (fun q : Omega × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (fun k omega => 1 - X q.2.2 k omega)
          (fun k omega => 1 - mean q.2.2 k omega)
          (singularFraction q.2.1) n q.1))
    (hjoint_upper_filtered : ∀ n,
      StronglyMeasurable[MeasurableSpace.prod (F n) inferInstance]
        (fun q : Omega × (Real × Theta) =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (fun k omega => 1 - X q.2.2 k omega)
            (fun k omega => 1 - mean q.2.2 k omega)
            (singularFraction q.2.1) n q.1)) :
    ∃ goodEvent : Set Omega,
      mu.real goodEventᶜ ≤ delta ∧
        ∀ omega ∈ goodEvent,
          ∀ posterior : Measure Theta,
            IsProbabilityMeasure posterior → posterior ≪ prior →
            Integrable (llr posterior prior) posterior →
            ∀ n : Nat, 2 ≤ n →
              |(∫ theta, forwardPrefixMean
                    (fun k => mean theta k omega) n ∂posterior) -
                (∫ theta, forwardPrefixMean
                    (fun k => X theta k omega) n ∂posterior)| <
                singularFractionExactBoundary
                    (continuousForwardPosteriorHybridBesselPenalty
                      posterior X n omega)
                    (continuousSingularFractionBesselEffectiveConfidence
                      prior posterior (delta / 2)) /
                  (n : Real) := by
  rcases
      exists_continuousTwoSidedSingularFractionBesselPACBayes_allFractions_event
        (mu := mu) (F := F) prior hdelta hdelta_one hX_adapted
        hmean_adapted hX_unit hmean_unit hmean hX_parameter
        hmean_parameter hjoint_lower_ambient hjoint_lower_filtered
        hjoint_upper_ambient hjoint_upper_filtered with
    ⟨goodEvent, hmass, hall⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro omega homega posterior hposterior hposterior_prior hllr n hn
  letI : IsProbabilityMeasure posterior := hposterior
  let Q := continuousForwardPosteriorHybridBesselPenalty
    posterior X n omega
  let effectiveDelta := continuousSingularFractionBesselEffectiveConfidence
    prior posterior (delta / 2)
  let lamStar := singularFractionExactOptimalLambda Q effectiveDelta
  have hdelta_half : 0 < delta / 2 := by linarith
  have hlamStar_pos : 0 < lamStar := by
    simpa [lamStar] using
      singularFractionExactOptimalLambda_pos Q effectiveDelta
  have hlamStar : lamStar ≤ Real.exp (-1) := by
    simpa [lamStar] using
      singularFractionExactOptimalLambda_le_exp_neg_one Q effectiveDelta
  have hbound := hall omega homega posterior inferInstance
    hposterior_prior hllr n hn lamStar hlamStar_pos hlamStar
  have hbridge :=
    continuousSingularFractionBesselBoundary_eq_exactNumerator_effectiveConfidence
      prior X posterior hdelta_half hlamStar_pos hlamStar n omega
  rw [hbridge] at hbound
  simpa [Q, effectiveDelta, lamStar, singularFractionExactBoundary] using hbound

end

end FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionExactOptimalPACBayes
