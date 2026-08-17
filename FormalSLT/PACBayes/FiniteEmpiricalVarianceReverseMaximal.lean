/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseExponential
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# A finite-epoch maximal inequality for the reverse Bessel process

Doob's maximal inequality applied to the nonnegative exponential transform of
the reverse Bessel martingale controls a crossing anywhere in a finite reverse
sample-size epoch by the full expectation at the epoch endpoint.

At reverse-process time `k`, the underlying Bessel variance uses prefix size
`max 2 (N - k)`.  Thus the specialization with horizon `N - m`, for
`2 ≤ m ≤ N`, covers every prefix size from `N` down to `m` using one fixed
coefficient, center, and deterministic penalty.

This module does not bound the endpoint expectation by one, connect it to the
fixed-sample empirical-variance MGF, optimize the coefficient, stitch epochs,
or state a PAC-Bayes theorem.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

variable {Z : Type*} [MeasurableSpace Z]

/-- Doob's finite-horizon inequality for the reverse-Bessel exponential
submartingale, strengthened from the crossing-event integral to the full
endpoint expectation. -/
theorem reverseBesselExponentialProcess_maximal_ineq [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ)
    (center lam penalty : ℝ) (ε : ℝ≥0) (r : ℕ) :
    ε * Measure.pi (fun _ : Fin N ↦ mu)
        {x | (ε : ℝ) ≤
          (Finset.range (r + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess
              N hN ell center lam penalty k x)} ≤
      ENNReal.ofReal
        (∫ x, reverseBesselExponentialProcess
          N hN ell center lam penalty r x
          ∂Measure.pi (fun _ : Fin N ↦ mu)) := by
  let muN := Measure.pi (fun _ : Fin N ↦ mu)
  let M := reverseBesselExponentialProcess N hN ell center lam penalty
  have hsub : Submartingale M (reverseBesselFiltration (Z := Z) N) muN :=
    reverseBesselExponentialProcess_submartingale
      mu N hN ell center lam penalty
  have hnonneg : 0 ≤ M :=
    reverseBesselExponentialProcess_nonneg N hN ell center lam penalty
  have hdoob := MeasureTheory.maximal_ineq hsub hnonneg (ε := ε) r
  have hendpoint :
      ∫ x in {x | (ε : ℝ) ≤
          (Finset.range (r + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ M k x)}, M r x ∂muN ≤
        ∫ x, M r x ∂muN :=
    setIntegral_le_integral (hsub.integrable r)
      (Filter.Eventually.of_forall (fun x ↦ hnonneg r x))
  change ε * muN
      {x | (ε : ℝ) ≤
        (Finset.range (r + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ M k x)} ≤
    ENNReal.ofReal (∫ x, M r x ∂muN)
  exact hdoob.trans (ENNReal.ofReal_le_ofReal hendpoint)

omit [MeasurableSpace Z] in
/-- At reverse time `N - m`, an epoch ending at `m` has exactly the
prefix-`m` Bessel-variance exponential as its endpoint. -/
theorem reverseBesselExponentialProcess_epoch_endpoint
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N) (ell : Z → ℝ)
    (center lam penalty : ℝ) :
    reverseBesselExponentialProcess N hN ell center lam penalty (N - m) =
      fun x ↦ Real.exp
        (lam * (center - prefixBesselVariance hm.2 ell x) - penalty) := by
  funext x
  simp only [reverseBesselExponentialProcess, reverseBesselAffineScore]
  rw [reverseBesselProcess_sub_eq_prefix hN hm.1 hm.2 ell x]

/-- The epoch form of
`reverseBesselExponentialProcess_maximal_ineq`: reverse times `0, ..., N - m`
correspond exactly to prefix sizes `N, ..., m` when `2 ≤ m ≤ N`.  The endpoint
is exposed as a prefix-`m` statistic for the subsequent product-measure MGF
bridge. -/
theorem reverseBesselExponentialProcess_epoch_maximal_ineq [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m ∧ m ≤ N)
    (ell : Z → ℝ) (center lam penalty : ℝ) (ε : ℝ≥0) :
    ε * Measure.pi (fun _ : Fin N ↦ mu)
        {x | (ε : ℝ) ≤
          (Finset.range (N - m + 1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ reverseBesselExponentialProcess
              N hN ell center lam penalty k x)} ≤
      ENNReal.ofReal
        (∫ x, Real.exp
          (lam * (center - prefixBesselVariance hm.2 ell x) - penalty)
          ∂Measure.pi (fun _ : Fin N ↦ mu)) := by
  simpa only [reverseBesselExponentialProcess_epoch_endpoint N m hN hm ell
    center lam penalty] using
      (reverseBesselExponentialProcess_maximal_ineq
        mu N hN ell center lam penalty ε (N - m))

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
