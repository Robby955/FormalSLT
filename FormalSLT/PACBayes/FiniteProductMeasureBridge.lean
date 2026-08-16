/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
import FormalSLT.PACBayes.FinitePMFBridge
import FormalSLT.PACBayes.FiniteProductBernstein

/-!
# Finite iid product-measure bridges

This module connects the finite-product measures used by mathlib's martingale
API to FormalSLT's finite iid sample weights.  Its load-bearing result is that
restricting a horizon sample to its first `t` coordinates is
measure-preserving from the horizon iid law to the prefix iid law.

The construction is structural: split the horizon product into the prefix and
its complement, project to the prefix, and reindex the prefix subtype by
`Fin t`.  It therefore does not assume the desired marginal law as an
interface hypothesis.
-/

namespace FormalSLT.PACBayes.FiniteProductMeasureBridge

open Finset BigOperators MeasureTheory
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

noncomputable section

variable {Z : Type*} [MeasurableSpace Z]

/-- Restricting a finite iid horizon sample to its first `t` coordinates
preserves the corresponding iid product law. -/
theorem measurePreserving_samplePrefix {N t : ℕ} (ht : t ≤ N)
    (mu : Measure Z) [IsProbabilityMeasure mu] :
    MeasurePreserving (samplePrefix ht)
      (Measure.pi (fun _ : Fin N ↦ mu))
      (Measure.pi (fun _ : Fin t ↦ mu)) := by
  let p : Fin N → Prop := fun k ↦ k.1 < t
  let e : Fin t ≃ {k : Fin N // p k} := finPrefixEquiv ht
  have hsplit :
      MeasurePreserving
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N ↦ Z) p)
        (Measure.pi (fun _ : Fin N ↦ mu))
        ((Measure.pi (fun _ : {k : Fin N // p k} ↦ mu)).prod
          (Measure.pi (fun _ : {k : Fin N // ¬ p k} ↦ mu))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N ↦ mu) p
  have hprefixSubtype :
      MeasurePreserving
        (fun x : Fin N → Z ↦ fun k : {k : Fin N // p k} ↦ x k.1)
        (Measure.pi (fun _ : Fin N ↦ mu))
        (Measure.pi (fun _ : {k : Fin N // p k} ↦ mu)) := by
    exact (measurePreserving_fst
      (μ := Measure.pi (fun _ : {k : Fin N // p k} ↦ mu))
      (ν := Measure.pi (fun _ : {k : Fin N // ¬ p k} ↦ mu))).comp hsplit
  have hrename :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : Fin t ↦ Z) e.symm)
        (Measure.pi (fun _ : {k : Fin N // p k} ↦ mu))
        (Measure.pi (fun _ : Fin t ↦ mu)) := by
    simpa using
      (measurePreserving_piCongrLeft
        (μ := fun _ : Fin t ↦ mu)
        (α := fun _ : Fin t ↦ Z) e.symm)
  have hcomp := hrename.comp hprefixSubtype
  convert hcomp using 1
  funext x k
  rfl

/-- Pulling a real-valued function back along `samplePrefix` does not change
its expectation under the corresponding finite iid laws. -/
theorem integral_comp_samplePrefix_eq {N t : ℕ} [Fintype Z]
    [MeasurableSingletonClass Z] (ht : t ≤ N) (mu : Measure Z)
    [IsProbabilityMeasure mu] (g : (Fin t → Z) → ℝ) :
    (∫ x, g (samplePrefix ht x) ∂Measure.pi (fun _ : Fin N ↦ mu)) =
      ∫ y, g y ∂Measure.pi (fun _ : Fin t ↦ mu) := by
  have hprefix := measurePreserving_samplePrefix ht mu
  have hmap := MeasureTheory.integral_map
    (μ := Measure.pi (fun _ : Fin N ↦ mu))
    hprefix.measurable.aemeasurable
    (measurable_of_finite g).aestronglyMeasurable
  rw [hprefix.map_eq] at hmap
  exact hmap.symm

/-! ### Finite weights as an actual product measure -/

/-- The mathlib product of the one-coordinate measure associated to `p` is
exactly the measure associated to FormalSLT's finite iid product weights. -/
theorem productMeasure_eq_finiteProductSampleWeight_toMeasure
    {n : ℕ} [Fintype Z] [MeasurableSingletonClass Z]
    {p : Z → ℝ} (hp : IsPMF p) :
    Measure.pi (fun _ : Fin n ↦ hp.toPMF.toMeasure) =
      (finiteProductSampleWeight_isPMF (n := n) hp).toPMF.toMeasure := by
  apply Measure.ext_of_singleton
  intro S
  rw [Measure.pi_singleton]
  rw [PMF.toMeasure_apply_singleton
    (finiteProductSampleWeight_isPMF (n := n) hp).toPMF S
    (MeasurableSet.singleton S)]
  have hbase (k : Fin n) :
      hp.toPMF.toMeasure {S k} = hp.toPMF (S k) :=
    hp.toPMF.toMeasure_apply_singleton (S k) (MeasurableSet.singleton (S k))
  simp_rw [hbase, IsPMF.toPMF_apply]
  unfold finiteProductSampleWeight
  exact (ENNReal.ofReal_prod_of_nonneg
    (s := Finset.univ) (f := fun k : Fin n ↦ p (S k))
    (fun k _ ↦ hp.nonneg (S k))).symm

/-- Integration against the finite iid product measure is the explicit finite
sum weighted by `finiteProductSampleWeight`. -/
theorem integral_productMeasure_eq_finiteProductSum
    {n : ℕ} [Fintype Z] [MeasurableSingletonClass Z]
    {p : Z → ℝ} (hp : IsPMF p) (g : (Fin n → Z) → ℝ) :
    (∫ S, g S ∂Measure.pi (fun _ : Fin n ↦ hp.toPMF.toMeasure)) =
      ∑ S : Fin n → Z, finiteProductSampleWeight p S * g S := by
  rw [productMeasure_eq_finiteProductSampleWeight_toMeasure hp]
  exact (finiteProductSampleWeight_isPMF (n := n) hp).integral_toPMF_eq_sum g

/-- The horizon expectation of a statistic depending only on its first `t`
coordinates is the explicit `t`-sample finite iid weighted sum. -/
theorem integral_comp_samplePrefix_eq_finiteProductSum
    {N t : ℕ} [Fintype Z] [MeasurableSingletonClass Z]
    (ht : t ≤ N) {p : Z → ℝ} (hp : IsPMF p) (g : (Fin t → Z) → ℝ) :
    (∫ x, g (samplePrefix ht x)
        ∂Measure.pi (fun _ : Fin N ↦ hp.toPMF.toMeasure)) =
      ∑ y : Fin t → Z, finiteProductSampleWeight p y * g y := by
  rw [integral_comp_samplePrefix_eq ht hp.toPMF.toMeasure g]
  exact integral_productMeasure_eq_finiteProductSum hp g

end

end FormalSLT.PACBayes.FiniteProductMeasureBridge
