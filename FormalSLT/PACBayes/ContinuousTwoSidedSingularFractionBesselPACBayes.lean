/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousSingularFractionBesselPACBayes

/-!
# Two-sided continuous singular-fraction PAC-Bayes bounds

This module intersects the lower-tail singular-fraction event for a bounded
process with the corresponding event for its complement.  A single event then
controls the absolute posterior-averaged conditional-minus-observed prefix
gap at every reporting time and for every eligible posterior selected from the
observed path.  Each tail receives confidence budget `delta / 2`; the same
observable hybrid-Bessel penalty appears on both sides.

For arbitrary measurable hypothesis spaces, joint measurability of the actual
lower-process family on the path-product-fraction-product-hypothesis space
remains an explicit caller obligation for both orientations.
The conclusion concerns conditional loss encountered on the monitored prefix,
not future, population, stationary, or deployment risk.  It is LIL-order, not
a sharpness or minimax claim, and the scalar singular-fraction mixture is not a
universal competitor over arbitrary predictable strategies.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousChangeOfMeasure
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.ContinuousSingularFractionBesselPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes

noncomputable section

variable {Theta Omega : Type*} [MeasurableSpace Theta]
  {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat mOmega}

/-- Complementing every observation leaves the posterior-averaged hybrid
Bessel penalty unchanged. -/
private theorem continuousForwardPosteriorHybridBesselPenalty_one_sub
    (posterior : Measure Theta)
    (X : Theta → Nat → Omega → Real) (n : Nat) (omega : Omega) :
    continuousForwardPosteriorHybridBesselPenalty posterior
        (fun theta k omega => 1 - X theta k omega) n omega =
      continuousForwardPosteriorHybridBesselPenalty posterior X n omega := by
  unfold continuousForwardPosteriorHybridBesselPenalty
  apply integral_congr_ae
  filter_upwards [] with theta
  exact forwardHybridBesselPenalty_one_sub
    (fun k => X theta k omega) n

/-- Under a probability posterior, integrating a complemented nonempty prefix
mean complements the integrated original prefix mean. -/
private theorem integral_forwardPrefixMean_one_sub
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (x : Theta → Nat → Real) {n : Nat} (hn : 0 < n)
    (hx_meas : ∀ k, StronglyMeasurable (fun theta => x theta k))
    (hx_unit : ∀ theta k, x theta k ∈ Set.Icc (0 : Real) 1) :
    (∫ theta, forwardPrefixMean (fun k => 1 - x theta k) n ∂posterior) =
      1 - ∫ theta, forwardPrefixMean (fun k => x theta k) n ∂posterior := by
  have hx_int := integrable_forwardPrefixMean_parameter_of_unit
    posterior x hn hx_meas hx_unit
  calc
    (∫ theta, forwardPrefixMean (fun k => 1 - x theta k) n ∂posterior) =
        ∫ theta, (1 - forwardPrefixMean (fun k => x theta k) n) ∂posterior := by
          apply integral_congr_ae
          filter_upwards [] with theta
          exact forwardPrefixMean_one_sub (fun k => x theta k) hn
    _ = 1 - ∫ theta,
        forwardPrefixMean (fun k => x theta k) n ∂posterior := by
          rw [integral_sub (integrable_const 1) hx_int]
          simp

/-- Conditional expectation commutes with complementing a bounded adapted
observation. -/
private theorem condExp_one_sub_of_bounded
    [IsProbabilityMeasure mu]
    {X mean : Nat → Omega → Real}
    (hX_adapted : IncrementAdapted F X)
    (hX_unit : ∀ k omega, X k omega ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ k, mu[X k | F k] =ᵐ[mu] mean k) :
    ∀ k, mu[(fun omega => 1 - X k omega) | F k] =ᵐ[mu]
      fun omega => 1 - mean k omega := by
  intro k
  have hX_meas : Measurable (X k) :=
    ((hX_adapted k).mono (F.le (k + 1))).measurable
  have hX_int : Integrable (X k) mu := by
    refine Integrable.of_bound hX_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX_unit k omega).1]
      exact (hX_unit k omega).2
  have hsub := condExp_sub (integrable_const (1 : Real)) hX_int (F k)
  have hone : mu[(fun _ : Omega => (1 : Real)) | F k] =
      fun _ => (1 : Real) := condExp_const (F.le k) 1
  filter_upwards [hsub, hmean k] with omega hsub_omega hmean_omega
  change mu[(fun _ : Omega => (1 : Real)) - X k | F k] omega =
    1 - mean k omega
  rw [hsub_omega, hone]
  simp only [Pi.sub_apply]
  rw [hmean_omega]

/-- One outer-probability event controls the absolute posterior-averaged
conditional-minus-observed prefix gap for every path-selected posterior and
every reporting time `n >= 2`.  Each orientation receives budget `delta / 2`.

The last four assumptions state joint measurability of the actual lower
process for the original and complemented families.  Separate parameter and
path measurability is not sufficient to derive these facts on an arbitrary
measurable hypothesis space. -/
theorem exists_continuousTwoSidedSingularFractionBesselPACBayesLIL_event
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
                singularFractionObservableLILBoundary
                    (continuousForwardPosteriorHybridBesselPenalty
                      posterior X n omega)
                    (continuousSingularFractionBesselEffectiveConfidence
                      prior posterior (delta / 2)) /
                  (n : Real) := by
  have hdelta_half : 0 < delta / 2 := by linarith
  have hdelta_half_one : delta / 2 ≤ 1 := by linarith
  let Xc : Theta → Nat → Omega → Real :=
    fun theta k omega => 1 - X theta k omega
  let meanc : Theta → Nat → Omega → Real :=
    fun theta k omega => 1 - mean theta k omega
  have hXc_adapted : ∀ theta, IncrementAdapted F (Xc theta) := by
    intro theta
    exact incrementAdapted_one_sub (hX_adapted theta)
  have hmeanc_adapted : ∀ theta, StronglyAdapted F (meanc theta) := by
    intro theta k
    exact stronglyMeasurable_const.sub (hmean_adapted theta k)
  have hXc_unit : ∀ theta k omega,
      Xc theta k omega ∈ Set.Icc (0 : Real) 1 := by
    intro theta k omega
    dsimp [Xc]
    constructor <;> linarith [(hX_unit theta k omega).1,
      (hX_unit theta k omega).2]
  have hmeanc_unit : ∀ theta k omega,
      meanc theta k omega ∈ Set.Icc (0 : Real) 1 := by
    intro theta k omega
    dsimp [meanc]
    constructor <;> linarith [(hmean_unit theta k omega).1,
      (hmean_unit theta k omega).2]
  have hmeanc : ∀ theta k,
      mu[Xc theta k | F k] =ᵐ[mu] meanc theta k := by
    intro theta
    simpa [Xc, meanc] using
      condExp_one_sub_of_bounded (hX_adapted theta)
        (hX_unit theta) (hmean theta)
  have hXc_parameter : ∀ k omega,
      StronglyMeasurable (fun theta => Xc theta k omega) := by
    intro k omega
    exact stronglyMeasurable_const.sub (hX_parameter k omega)
  have hmeanc_parameter : ∀ k omega,
      StronglyMeasurable (fun theta => meanc theta k omega) := by
    intro k omega
    exact stronglyMeasurable_const.sub (hmean_parameter k omega)
  rcases exists_continuousSingularFractionBesselPACBayesLIL_event
      (mu := mu) (F := F) prior (delta := delta / 2)
      hdelta_half hdelta_half_one hX_adapted hmean_adapted
      hX_unit hmean_unit hmean hX_parameter hmean_parameter
      hjoint_lower_ambient hjoint_lower_filtered with
    ⟨lowerEvent, hlowerMass, hlower⟩
  rcases exists_continuousSingularFractionBesselPACBayesLIL_event
      (mu := mu) (F := F) prior (X := Xc) (mean := meanc)
      (delta := delta / 2) hdelta_half hdelta_half_one
      hXc_adapted hmeanc_adapted hXc_unit hmeanc_unit hmeanc
      hXc_parameter hmeanc_parameter
      (by simpa [Xc, meanc] using hjoint_upper_ambient)
      (by simpa [Xc, meanc] using hjoint_upper_filtered) with
    ⟨upperEvent, hupperMass, hupper⟩
  refine ⟨lowerEvent ∩ upperEvent, ?_, ?_⟩
  · rw [Set.compl_inter]
    calc
      mu.real (lowerEventᶜ ∪ upperEventᶜ) ≤
          mu.real lowerEventᶜ + mu.real upperEventᶜ :=
        measureReal_union_le _ _
      _ ≤ delta / 2 + delta / 2 := add_le_add hlowerMass hupperMass
      _ = delta := by ring
  · intro omega homega posterior hposterior hposterior_prior hllr n hn
    letI : IsProbabilityMeasure posterior := hposterior
    have hlowerBound := hlower omega homega.1 posterior inferInstance
      hposterior_prior hllr n hn
    have hupperBound := hupper omega homega.2 posterior inferInstance
      hposterior_prior hllr n hn
    have hnpos : 0 < n := by omega
    have hmeanComp := integral_forwardPrefixMean_one_sub posterior
      (fun theta k => mean theta k omega) hnpos
      (fun k => hmean_parameter k omega)
      (fun theta k => hmean_unit theta k omega)
    have hXComp := integral_forwardPrefixMean_one_sub posterior
      (fun theta k => X theta k omega) hnpos
      (fun k => hX_parameter k omega)
      (fun theta k => hX_unit theta k omega)
    have hpenalty := continuousForwardPosteriorHybridBesselPenalty_one_sub
      posterior X n omega
    change
      (∫ theta, forwardPrefixMean
          (fun k => 1 - mean theta k omega) n ∂posterior) <
        (∫ theta, forwardPrefixMean
          (fun k => 1 - X theta k omega) n ∂posterior) +
        singularFractionObservableLILBoundary
            (continuousForwardPosteriorHybridBesselPenalty posterior
              (fun theta k omega => 1 - X theta k omega) n omega)
            (continuousSingularFractionBesselEffectiveConfidence
              prior posterior (delta / 2)) /
          (n : Real) at hupperBound
    rw [hmeanComp, hXComp, hpenalty] at hupperBound
    rw [abs_lt]
    constructor <;> linarith

end

end FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes
