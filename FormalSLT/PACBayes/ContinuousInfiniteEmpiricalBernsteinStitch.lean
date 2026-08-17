/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousEmpiricalBernsteinReverseSqrt
import FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch

/-!
# All-sample-size continuous-posterior empirical-Bernstein PAC-Bayes bounds

This module stitches the finite-horizon continuous-posterior reverse epochs
over dyadic sample-size blocks.  The resulting event lives on one infinite iid
path, depends on the prior but not the posterior, and has mass at most `delta`.
Off that event, every sample size `n ≥ 2` and every posterior absolutely
continuous with respect to the prior with an integrable log-likelihood ratio
obey an empirical-Bernstein PAC-Bayes bound with one measure-theoretic KL term.

The observation space remains finite.  The proof is an offline reverse-epoch
stitch, not a forward e-process or an optional-stopping theorem.
-/

namespace FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch

open Finset BigOperators MeasureTheory
open Filter Topology
open scoped ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
open FormalSLT.PACBayes.FiniteEmpiricalBernsteinSqrt
open FormalSLT.PACBayes.ContinuousEmpiricalBernsteinReverseSqrt
open FormalSLT.PACBayes.InfiniteProductMeasureBridge
open FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch

noncomputable section

variable {Θ Z : Type*} [MeasurableSpace Θ] [MeasurableSpace Z]

/-- The exact measure-KL complexity paid by the selected dyadic epoch. -/
def continuousInfiniteEmpiricalBernsteinComplexity
    (n : ℕ) (delta : ℝ) (prior posterior : Measure Θ) : ℝ :=
  (InformationTheory.klDiv posterior prior).toReal +
    Real.log
      ((((Nat.log 2 n : ℕ) : ℝ) *
          (((Nat.log 2 n : ℕ) : ℝ) + 1) ^ (2 : Nat)) / delta)

theorem continuousInfiniteEmpiricalBernsteinComplexity_pos
    {n : ℕ} (hn : 2 ≤ n)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (prior posterior : Measure Θ) :
    0 < continuousInfiniteEmpiricalBernsteinComplexity
      n delta prior posterior := by
  let r : ℝ := (Nat.log 2 n : ℕ)
  have hr_nat : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hr : (1 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast hr_nat
  have hsq : (4 : ℝ) ≤ (r + 1) ^ (2 : Nat) := by
    nlinarith [sq_nonneg (r - 1)]
  have hnum : (4 : ℝ) ≤ r * (r + 1) ^ (2 : Nat) := by
    calc
      (4 : ℝ) = 1 * 4 := by norm_num
      _ ≤ r * (r + 1) ^ (2 : Nat) :=
        mul_le_mul hr hsq (by norm_num) (by linarith)
  have hratio : 1 < r * (r + 1) ^ (2 : Nat) / delta := by
    rw [lt_div_iff₀ hdelta]
    linarith
  unfold continuousInfiniteEmpiricalBernsteinComplexity
  change 0 < (InformationTheory.klDiv posterior prior).toReal +
    Real.log (r * (r + 1) ^ (2 : Nat) / delta)
  exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (Real.log_pos hratio)

/-! ## One event on the infinite iid product space -/

/-- Epoch `q`'s continuous-prior failure event at confidence
`delta * reverseDyadicEpochWeight q`. -/
def continuousReverseDyadicEpochFailure
    [Fintype Z]
    (q : ℕ) (p : Z → ℝ) (prior : Measure Θ) (ell : Θ → Z → ℝ)
    (delta : ℝ) : Set (Fin (reverseDyadicEpochHorizon q) → Z) :=
  continuousEmpiricalBernsteinReverseSqrtFailure
    (reverseDyadicEpochHorizon q) (reverseDyadicEpochHorizon_two_le q)
    (reverseDyadicEpochFloor q) p prior ell
    (reverseDyadicEpochConfidence delta q)

/-- The posterior-independent infinite-path failure event formed by pulling
every continuous-prior reverse epoch onto the same iid path. -/
def continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
    [Fintype Z]
    (p : Z → ℝ) (prior : Measure Θ) (ell : Θ → Z → ℝ)
    (delta : ℝ) : Set (ℕ → Z) :=
  ⋃ q : ℕ, natSamplePrefix (reverseDyadicEpochHorizon q) ⁻¹'
    continuousReverseDyadicEpochFailure q p prior ell delta

theorem continuousInfiniteEmpiricalBernsteinReverseSqrtFailure_measurable
    [Fintype Z] [MeasurableSingletonClass Z]
    (p : Z → ℝ) (prior : Measure Θ) (ell : Θ → Z → ℝ)
    (delta : ℝ) :
    MeasurableSet
      (continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
        p prior ell delta) := by
  unfold continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
  apply MeasurableSet.iUnion
  intro q
  exact
    (Set.toFinite
      (continuousReverseDyadicEpochFailure q p prior ell delta)).measurableSet.preimage
      (measurable_natSamplePrefix (reverseDyadicEpochHorizon q))

/-- The stitched continuous-prior infinite-path event has mass at most
`delta`. -/
theorem continuousInfiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Measure.infinitePi (fun _ : ℕ ↦ hp.toPMF.toMeasure)
        (continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
          p prior ell delta) ≤ ENNReal.ofReal delta := by
  unfold continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
  apply natPrefix_iUnion_mass_le hp.toPMF.toMeasure
    reverseDyadicEpochHorizon (reverseDyadicEpochConfidence delta)
    (fun q ↦ continuousReverseDyadicEpochFailure q p prior ell delta)
  · intro q
    exact (reverseDyadicEpochConfidence_pos hdelta q).le
  · exact reverseDyadicEpochConfidence_summable delta
  · intro q
    unfold continuousReverseDyadicEpochFailure
    exact continuousEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
      (reverseDyadicEpochHorizon q) (reverseDyadicEpochFloor q)
      (reverseDyadicEpochHorizon_two_le q)
      ⟨reverseDyadicEpochFloor_two_le q,
        reverseDyadicEpochFloor_le_horizon q⟩
      p hp prior ell hell_meas hell
      (reverseDyadicEpochConfidence_pos hdelta q)
  · rw [reverseDyadicEpochConfidence_tsum]

omit [MeasurableSpace Z] in
/-- Outside the stitched event, every `n ≥ 2` and every finite-KL posterior
obey the exact dyadic-floor continuous-posterior empirical-Bernstein bound. -/
theorem continuousInfiniteEmpiricalBernstein_posteriorRisk_lt_of_not_mem
    [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : ℕ → Z)
    (hx : x ∉ continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
      p prior ell delta)
    (n : ℕ) (hn : 2 ≤ n)
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (natSamplePrefix n x) ∂posterior) +
        (5 / 4 : ℝ) * Real.sqrt
          (2 * (∫ θ, finiteEmpiricalVariance ell θ (natSamplePrefix n x)
            ∂posterior) *
            continuousInfiniteEmpiricalBernsteinComplexity
              n delta prior posterior /
            (reverseDyadicEpochFloor (reverseDyadicEpochIndex n) : ℝ)) +
        (5 / 2 : ℝ) *
          continuousInfiniteEmpiricalBernsteinComplexity
            n delta prior posterior /
          (reverseDyadicEpochFloor (reverseDyadicEpochIndex n) : ℝ) := by
  let q := reverseDyadicEpochIndex n
  have hspec := reverseDyadicEpochIndex_spec hn
  have hmn : reverseDyadicEpochFloor q ≤ n := by
    simpa [q] using hspec.1
  have hnN : n ≤ reverseDyadicEpochHorizon q := by
    exact Nat.le_of_lt (by simpa [q] using hspec.2)
  have hconf_pos := reverseDyadicEpochConfidence_pos hdelta q
  have hconf_one := reverseDyadicEpochConfidence_lt_one hdelta_one q
  have hxq : natSamplePrefix (reverseDyadicEpochHorizon q) x ∉
      continuousReverseDyadicEpochFailure q p prior ell delta := by
    intro hxq
    apply hx
    unfold continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
    exact Set.mem_iUnion.mpr ⟨q, hxq⟩
  have hfinite :=
    continuousEmpiricalBernsteinReverseSqrt_posteriorRisk_prefix_lt_of_not_mem
      (reverseDyadicEpochHorizon q) (reverseDyadicEpochFloor q) n
      (reverseDyadicEpochHorizon_two_le q)
      (reverseDyadicEpochFloor_two_le q) hmn hnN p hp prior posterior
      hposteriorPrior ell hell_meas hell hconf_pos hconf_one
      (natSamplePrefix (reverseDyadicEpochHorizon q) x)
      (by simpa [continuousReverseDyadicEpochFailure] using hxq) hllr
  rw [reverseDyadicEpoch_ratio q hdelta.ne'] at hfinite
  have hq1 : q + 1 = Nat.log 2 n := by
    simpa [q] using reverseDyadicEpochIndex_add_one hn
  have hq2 : q + 2 = Nat.log 2 n + 1 := by omega
  have hq1R : (q : ℝ) + 1 = (Nat.log 2 n : ℝ) := by
    exact_mod_cast hq1
  have hq2R : (q : ℝ) + 2 = (Nat.log 2 n : ℝ) + 1 := by
    exact_mod_cast hq2
  have hcomplexity :
      (InformationTheory.klDiv posterior prior).toReal +
          Real.log
            ((((q : ℝ) + 1) * ((q : ℝ) + 2) ^ (2 : Nat)) / delta) =
        continuousInfiniteEmpiricalBernsteinComplexity
          n delta prior posterior := by
    unfold continuousInfiniteEmpiricalBernsteinComplexity
    rw [hq1R, hq2R]
  rw [hcomplexity] at hfinite
  simpa [q, samplePrefix_natSamplePrefix] using hfinite

omit [MeasurableSpace Z] in
/-- Cleaner all-sample-size bound.  Replacing the lower dyadic endpoint by
`n` costs at most a factor two, giving constants `5/2` and `5`. -/
theorem continuousInfiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem
    [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (prior posterior : Measure Θ)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (hposteriorPrior : posterior ≪ prior)
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (x : ℕ → Z)
    (hx : x ∉ continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
      p prior ell delta)
    (n : ℕ) (hn : 2 ≤ n)
    (hllr : Integrable (llr posterior prior) posterior) :
    (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (natSamplePrefix n x) ∂posterior) +
        (5 / 2 : ℝ) * Real.sqrt
          ((∫ θ, finiteEmpiricalVariance ell θ (natSamplePrefix n x)
            ∂posterior) *
            continuousInfiniteEmpiricalBernsteinComplexity
              n delta prior posterior / (n : ℝ)) +
        5 * continuousInfiniteEmpiricalBernsteinComplexity
          n delta prior posterior / (n : ℝ) := by
  let q := reverseDyadicEpochIndex n
  let m := reverseDyadicEpochFloor q
  let V := ∫ θ, finiteEmpiricalVariance ell θ (natSamplePrefix n x) ∂posterior
  let L := continuousInfiniteEmpiricalBernsteinComplexity
    n delta prior posterior
  have hbase :=
    continuousInfiniteEmpiricalBernstein_posteriorRisk_lt_of_not_mem
      p hp prior posterior hposteriorPrior ell hell_meas hell hdelta
      hdelta_one x hx n hn hllr
  have hm_nat : 2 ≤ m := by
    dsimp [m]
    exact reverseDyadicEpochFloor_two_le q
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have hL : 0 < L := by
    dsimp [L]
    exact continuousInfiniteEmpiricalBernsteinComplexity_pos
      hn hdelta hdelta_one prior posterior
  have hV : 0 ≤ V := by
    dsimp [V]
    exact (continuousPosterior_finiteEmpiricalVariance_mem_Icc
      hn ell (natSamplePrefix n x) hell_meas hell posterior).1
  have hn2m_nat : n ≤ 2 * m := by
    have hspec := (reverseDyadicEpochIndex_spec hn).2
    rw [reverseDyadicEpochHorizon_eq_two_mul_floor] at hspec
    exact Nat.le_of_lt (by simpa [q, m] using hspec)
  have hn2m : (n : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hn2m_nat
  have hrecip : 1 / (m : ℝ) ≤ 2 / (n : ℝ) := by
    rw [div_le_div_iff₀ hmR hnR]
    simpa using hn2m
  have hsarg : 2 * V * L / (m : ℝ) ≤ 4 * (V * L / (n : ℝ)) := by
    calc
      2 * V * L / (m : ℝ) = (2 * V * L) * (1 / (m : ℝ)) := by ring
      _ ≤ (2 * V * L) * (2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 4 * (V * L / (n : ℝ)) := by ring
  have hsqrt := Real.sqrt_le_sqrt hsarg
  have hsqrt_four : Real.sqrt (4 * (V * L / (n : ℝ))) =
      2 * Real.sqrt (V * L / (n : ℝ)) := by
    calc
      Real.sqrt (4 * (V * L / (n : ℝ))) =
          Real.sqrt 4 * Real.sqrt (V * L / (n : ℝ)) :=
        Real.sqrt_mul (by norm_num) (V * L / (n : ℝ))
      _ = 2 * Real.sqrt (V * L / (n : ℝ)) := by
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          convert Real.sqrt_sq_eq_abs (2 : ℝ) using 1 <;> norm_num
        rw [hsqrt4]
  rw [hsqrt_four] at hsqrt
  have hsqrt_term :
      (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (m : ℝ)) ≤
        (5 / 2 : ℝ) * Real.sqrt (V * L / (n : ℝ)) := by
    nlinarith
  have hLdiv : L / (m : ℝ) ≤ 2 * L / (n : ℝ) := by
    calc
      L / (m : ℝ) = L * (1 / (m : ℝ)) := by ring
      _ ≤ L * (2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip hL.le
      _ = 2 * L / (n : ℝ) := by ring
  have hlinear_term :
      (5 / 2 : ℝ) * L / (m : ℝ) ≤ 5 * L / (n : ℝ) := by
    calc
      (5 / 2 : ℝ) * L / (m : ℝ) = (5 / 2 : ℝ) * (L / (m : ℝ)) := by
        ring
      _ ≤ (5 / 2 : ℝ) * (2 * L / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hLdiv (by norm_num)
      _ = 5 * L / (n : ℝ) := by ring
  change (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (natSamplePrefix n x) ∂posterior) +
        (5 / 2 : ℝ) * Real.sqrt (V * L / (n : ℝ)) +
        5 * L / (n : ℝ)
  change (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
      (∫ θ, finiteEmpiricalRisk ell θ (natSamplePrefix n x) ∂posterior) +
        (5 / 4 : ℝ) * Real.sqrt (2 * V * L / (m : ℝ)) +
        (5 / 2 : ℝ) * L / (m : ℝ) at hbase
  linarith

/-- **All-sample-size continuous-posterior empirical-Bernstein event.**

There is one measurable prior-dependent, posterior-independent exceptional
set of infinite iid paths with mass at most `delta`.  Off it, every `n ≥ 2`
and every posterior probability measure absolutely continuous with respect to
the prior with integrable log-likelihood ratio satisfy

`Rρ < Rhatρ,n + (5/2) sqrt(Vhatρ,n * Lρ,n / n) + 5 Lρ,n / n`.

The variance is the posterior integral of each hypothesis's Bessel empirical
variance. -/
theorem exists_continuousInfiniteEmpiricalBernstein_event
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (p : Z → ℝ) (hp : IsPMF p)
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (ell : Θ → Z → ℝ)
    (hell_meas : ∀ z, StronglyMeasurable (fun θ ↦ ell θ z))
    (hell : ∀ θ z, ell θ z ∈ Set.Icc (0 : ℝ) 1)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta < 1) :
    ∃ E : Set (ℕ → Z),
      MeasurableSet E ∧
      Measure.infinitePi (fun _ : ℕ ↦ hp.toPMF.toMeasure) E ≤
        ENNReal.ofReal delta ∧
      ∀ x, x ∉ E → ∀ n : ℕ, 2 ≤ n →
        ∀ posterior : Measure Θ, IsProbabilityMeasure posterior →
          posterior ≪ prior →
          Integrable (llr posterior prior) posterior →
          (∫ θ, finitePopulationRisk p ell θ ∂posterior) <
            (∫ θ, finiteEmpiricalRisk ell θ (natSamplePrefix n x)
              ∂posterior) +
              (5 / 2 : ℝ) * Real.sqrt
                ((∫ θ, finiteEmpiricalVariance ell θ (natSamplePrefix n x)
                  ∂posterior) *
                  continuousInfiniteEmpiricalBernsteinComplexity
                    n delta prior posterior / (n : ℝ)) +
              5 * continuousInfiniteEmpiricalBernsteinComplexity
                n delta prior posterior / (n : ℝ) := by
  let E := continuousInfiniteEmpiricalBernsteinReverseSqrtFailure
    p prior ell delta
  refine ⟨E,
    continuousInfiniteEmpiricalBernsteinReverseSqrtFailure_measurable
      p prior ell delta, ?_, ?_⟩
  · exact continuousInfiniteEmpiricalBernsteinReverseSqrtFailure_mass_le_delta
      p hp prior ell hell_meas hell hdelta
  · intro x hx n hn posterior hposteriorProb hposteriorPrior hllr
    letI : IsProbabilityMeasure posterior := hposteriorProb
    exact continuousInfiniteEmpiricalBernstein_posteriorRisk_lt_n_of_not_mem
      p hp prior posterior hposteriorPrior ell hell_meas hell hdelta
      hdelta_one x hx n hn hllr

end

end FormalSLT.PACBayes.ContinuousInfiniteEmpiricalBernsteinStitch
