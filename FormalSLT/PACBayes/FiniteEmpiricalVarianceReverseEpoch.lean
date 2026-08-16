/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseMaximal
import FormalSLT.PACBayes.FiniteProductMeasureBridge
import FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF

/-!
# A reverse-time empirical-variance epoch bound

This module joins three independently checked ingredients:

* the reverse Bessel exponential submartingale;
* Doob's finite-horizon maximal inequality;
* the exact finite-product lower-tail MGF for Bessel empirical variance.

For fixed `2 ≤ m ≤ N` and fixed `eta ≥ 0`, one exponential crossing controls
every prefix size from `N` down to `m`.  The proof derives the endpoint law by
the structural product-measure prefix bridge and then applies the existing
normalized `m`-sample MGF theorem.  No marginal-law or endpoint-MGF interface
is assumed.

This is an offline finite-horizon epoch theorem.  The reverse filtration sees
the ordered suffix, and the coefficient is fixed using the epoch endpoint
`m`.  This module does not yet mix hypotheses or tilts, stitch epochs, or state
a time-uniform PAC-Bayes theorem.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

open Finset BigOperators MeasureTheory
open scoped NNReal ENNReal
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
open FormalSLT.PACBayes.FiniteProductMeasureBridge

noncomputable section

variable {ι Z : Type*} [MeasurableSpace Z]

/-- The deterministic normalization in the endpoint-`m` lower-tail Bessel
variance MGF. -/
def reverseBesselEpochPenalty (m : ℕ) (eta variance : ℝ) : ℝ :=
  eta ^ (2 : Nat) * (m : ℝ) ^ (2 : Nat) * variance /
    (2 * ((m : ℝ) - 1))

/-- The endpoint expectation of a reverse Bessel epoch is at most one.  The
proof transports the horizon law to the prefix law and then invokes the exact
normalized finite-sample empirical-variance MGF. -/
theorem reverseBesselEpoch_endpoint_integral_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    {N m : ℕ} (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ x, Real.exp
        (eta * (m : ℝ) *
            (finitePopulationVariance p ell i -
              prefixBesselVariance hm.2 (ell i) x) -
          reverseBesselEpochPenalty m eta
            (finitePopulationVariance p ell i))
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) ≤ 1 := by
  let g : (Fin m → Z) → ℝ := fun S ↦ Real.exp
    (eta * (m : ℝ) *
        (finitePopulationVariance p ell i -
          finiteEmpiricalVariance ell i S) -
      reverseBesselEpochPenalty m eta (finitePopulationVariance p ell i))
  have hbridge := integral_comp_samplePrefix_eq_finiteProductSum hm.2 hp g
  have hmgf := finiteEmpiricalVariance_normalizedLowerTailMGF_le_one
    hm.1 p hp ell i hell heta
  calc
    (∫ x, Real.exp
        (eta * (m : ℝ) *
            (finitePopulationVariance p ell i -
              prefixBesselVariance hm.2 (ell i) x) -
          reverseBesselEpochPenalty m eta
            (finitePopulationVariance p ell i))
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) =
      ∑ S : Fin m → Z, finiteProductSampleWeight p S * g S := by
        simpa only [g, prefixBesselVariance, finiteEmpiricalVariance,
          Function.comp_apply] using hbridge
    _ ≤ 1 := by
      simpa only [g, reverseBesselEpochPenalty] using hmgf

/-- **Finite empirical-variance reverse-epoch crossing bound.**  With one
fixed endpoint-normalized coefficient, the lower-tail Bessel exponential may
cross anywhere from prefix size `N` down to `m`, yet threshold times crossing
mass remains at most one. -/
theorem reverseBesselEpoch_maximal_le_one
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta : ℝ} (heta : 0 ≤ eta) (ε : ℝ≥0) :
    ε * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | (ε : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess N hN (ell i)
              (finitePopulationVariance p ell i)
              (eta * (m : ℝ))
              (reverseBesselEpochPenalty m eta
                (finitePopulationVariance p ell i)) k x)} ≤ 1 := by
  have hmax := reverseBesselExponentialProcess_epoch_maximal_ineq
    hp.toPMF.toMeasure N m hN hm (ell i)
      (finitePopulationVariance p ell i) (eta * (m : ℝ))
      (reverseBesselEpochPenalty m eta (finitePopulationVariance p ell i)) ε
  have hend := reverseBesselEpoch_endpoint_integral_le_one
    hm p hp ell i hell heta
  calc
    _ ≤ ENNReal.ofReal
        (∫ x, Real.exp
          ((eta * (m : ℝ)) *
              (finitePopulationVariance p ell i -
                prefixBesselVariance hm.2 (ell i) x) -
            reverseBesselEpochPenalty m eta
              (finitePopulationVariance p ell i))
          ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) := hmax
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hend
    _ = 1 := by norm_num

/-- Confidence form of `reverseBesselEpoch_maximal_le_one`: the probability
that the endpoint-normalized exponential crosses `1 / delta` anywhere in the
epoch is at most `delta`. -/
theorem reverseBesselEpoch_crossing_mass_le_delta
    [Fintype Z] [DecidableEq Z] [MeasurableSingletonClass Z]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (p : Z → ℝ) (hp : IsPMF p)
    (ell : ι → Z → ℝ) (i : ι)
    (hell : ∀ z : Z, ell i z ∈ Set.Icc (0 : ℝ) 1)
    {eta delta : ℝ} (heta : 0 ≤ eta) (hdelta : 0 < delta) :
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | delta⁻¹ ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess N hN (ell i)
              (finitePopulationVariance p ell i)
              (eta * (m : ℝ))
              (reverseBesselEpochPenalty m eta
                (finitePopulationVariance p ell i)) k x)} ≤
      ENNReal.ofReal delta := by
  let ε : ℝ≥0 := ⟨delta⁻¹, inv_nonneg.mpr hdelta.le⟩
  let d : ℝ≥0∞ := ENNReal.ofReal delta
  have hscaled := reverseBesselEpoch_maximal_le_one
    N m hN hm p hp ell i hell heta ε
  have hεReal : (ε : ℝ) = delta⁻¹ := rfl
  have hε : (ε : ℝ≥0∞) = d⁻¹ := by
    calc
      (ε : ℝ≥0∞) = ENNReal.ofReal delta⁻¹ := by
        symm
        exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hdelta.le)
      _ = d⁻¹ := by rw [ENNReal.ofReal_inv_of_pos hdelta]
  have hscaled' : d⁻¹ * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | delta⁻¹ ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess N hN (ell i)
              (finitePopulationVariance p ell i)
              (eta * (m : ℝ))
              (reverseBesselEpochPenalty m eta
                (finitePopulationVariance p ell i)) k x)} ≤ 1 := by
    rw [hε] at hscaled
    rw [hεReal] at hscaled
    exact hscaled
  have hd0 : d ≠ 0 := by
    simpa [d] using (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hdtop : d ≠ ∞ := by
    exact ENNReal.ofReal_ne_top
  calc
    Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | delta⁻¹ ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess N hN (ell i)
              (finitePopulationVariance p ell i)
              (eta * (m : ℝ))
              (reverseBesselEpochPenalty m eta
                (finitePopulationVariance p ell i)) k x)} =
      d * (d⁻¹ * Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)
        {x | delta⁻¹ ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess N hN (ell i)
              (finitePopulationVariance p ell i)
              (eta * (m : ℝ))
              (reverseBesselEpochPenalty m eta
                (finitePopulationVariance p ell i)) k x)}) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, one_mul]
    _ ≤ d * 1 := mul_le_mul_right hscaled' d
    _ = ENNReal.ofReal delta := by simp [d]

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
