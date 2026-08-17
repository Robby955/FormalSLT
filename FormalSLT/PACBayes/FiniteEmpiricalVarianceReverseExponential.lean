/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverseMartingale
import FormalSLT.Concentration.SubGamma.CondJensen

/-!
# Exponential transforms of the reverse Bessel martingale

For a fixed horizon and fixed exponential coefficient, an affine transform of
the reverse Bessel martingale remains a martingale.  Conditional Jensen then
makes its exponential a nonnegative submartingale.  This is the load-bearing
process needed to apply Doob's finite-horizon maximal inequality to a whole
sample-size epoch.

The coefficient, center, and deterministic penalty are fixed before process
time.  In particular, this module does not claim that a coefficient depending
on the moving prefix size produces a submartingale.  It also does not yet
connect the endpoint expectation to the finite-product empirical-variance MGF
or state a PAC-Bayes result.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

open MeasureTheory
open FormalSLT.Concentration.SubGamma

noncomputable section

variable {Z : Type*} [MeasurableSpace Z]

/-- A fixed affine lower-tail score built from the reverse Bessel process. -/
def reverseBesselAffineScore (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ)
    (center lam penalty : ℝ) : ℕ → (Fin N → Z) → ℝ :=
  fun k x ↦ lam * (center - reverseBesselProcess N hN ell k x) - penalty

theorem reverseBesselAffineScore_martingale [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ)
    (center lam penalty : ℝ) :
    Martingale (reverseBesselAffineScore N hN ell center lam penalty)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  let filt := reverseBesselFiltration (Z := Z) N
  let muN := Measure.pi (fun _ : Fin N ↦ mu)
  have hvariance : Martingale (reverseBesselProcess N hN ell) filt muN :=
    reverseBesselProcess_martingale mu N hN ell
  have hcenter : Martingale (fun _ _ ↦ center) filt muN :=
    martingale_const filt muN center
  have hpenalty : Martingale (fun _ _ ↦ penalty) filt muN :=
    martingale_const filt muN penalty
  have hscore := (hcenter.sub hvariance).smul lam |>.sub hpenalty
  change Martingale (reverseBesselAffineScore N hN ell center lam penalty)
    filt muN
  convert hscore using 1
  funext k x
  simp only [reverseBesselAffineScore, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]

/-- Exponential of the fixed affine reverse-Bessel score. -/
def reverseBesselExponentialProcess (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ)
    (center lam penalty : ℝ) : ℕ → (Fin N → Z) → ℝ :=
  fun k x ↦ Real.exp (reverseBesselAffineScore N hN ell center lam penalty k x)

theorem reverseBesselExponentialProcess_submartingale [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ)
    (center lam penalty : ℝ) :
    Submartingale
      (reverseBesselExponentialProcess N hN ell center lam penalty)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  let filt := reverseBesselFiltration (Z := Z) N
  let muN := Measure.pi (fun _ : Fin N ↦ mu)
  let score := reverseBesselAffineScore N hN ell center lam penalty
  have hscore : Martingale score filt muN :=
    reverseBesselAffineScore_martingale mu N hN ell center lam penalty
  have hadapted : StronglyAdapted filt
      (reverseBesselExponentialProcess N hN ell center lam penalty) := by
    intro k
    exact Real.continuous_exp.comp_stronglyMeasurable
      (hscore.stronglyMeasurable k)
  refine submartingale_nat hadapted (fun _ ↦ Integrable.of_finite) ?_
  intro k
  have hjensen := condJensen_real
    (μ := muN) (m := filt k) (X := score (k + 1)) (φ := Real.exp)
    (filt.le k) convexOn_exp Real.continuous_exp.lowerSemicontinuous
    Integrable.of_finite Integrable.of_finite
  have hstep := hscore.condExp_ae_eq (Nat.le_succ k)
  filter_upwards [hjensen, hstep] with x hj hx
  change Real.exp (score k x) ≤
    condExp (filt k) muN (fun y ↦ Real.exp (score (k + 1) y)) x
  rw [← hx]
  exact hj

omit [MeasurableSpace Z] in
theorem reverseBesselExponentialProcess_nonneg
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ)
    (center lam penalty : ℝ) :
    0 ≤ reverseBesselExponentialProcess N hN ell center lam penalty := by
  intro k x
  exact Real.exp_pos _ |>.le

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
