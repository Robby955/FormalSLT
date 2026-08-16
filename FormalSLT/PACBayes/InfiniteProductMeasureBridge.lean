/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import Mathlib.Probability.ProductMeasure

/-!
# Infinite iid paths and finite prefixes

This module proves structurally that restricting a countably infinite iid path
to its first `N` coordinates preserves the finite iid product law.  It is the
measure bridge needed to pull finite reverse-epoch events onto one common
infinite sample space before countable stitching.
-/

namespace FormalSLT.PACBayes.InfiniteProductMeasureBridge

open Finset MeasureTheory

noncomputable section

variable {Z : Type*} [MeasurableSpace Z]

/-- The first `N` coordinates of a countably infinite path. -/
def natSamplePrefix (N : ℕ) (x : ℕ → Z) : Fin N → Z :=
  fun k ↦ x k.1

theorem measurable_natSamplePrefix (N : ℕ) :
    Measurable (natSamplePrefix (Z := Z) N) := by
  exact measurable_pi_lambda _ fun k ↦ measurable_pi_apply k.1

/-- Restricting an infinite iid path to `Fin N` preserves the finite iid
product law. -/
theorem measurePreserving_natSamplePrefix (N : ℕ)
    (mu : Measure Z) [IsProbabilityMeasure mu] :
    MeasurePreserving (natSamplePrefix N)
      (Measure.infinitePi (fun _ : ℕ ↦ mu))
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  let I := Finset.range N
  let e : Fin N ≃ I :=
    { toFun := fun k ↦ ⟨k.1, Finset.mem_range.mpr k.2⟩
      invFun := fun k ↦ ⟨k.1, Finset.mem_range.mp k.2⟩
      left_inv := fun k ↦ by cases k; rfl
      right_inv := fun k ↦ by cases k; rfl }
  have hrestrict :
      MeasurePreserving
        (I.restrict : (ℕ → Z) → (I → Z))
        (Measure.infinitePi (fun _ : ℕ ↦ mu))
        (Measure.pi (fun _ : I ↦ mu)) := by
    refine ⟨measurable_restrict I, ?_⟩
    exact Measure.infinitePi_map_restrict (fun _ : ℕ ↦ mu)
  have hrename :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : Fin N ↦ Z) e.symm)
        (Measure.pi (fun _ : I ↦ mu))
        (Measure.pi (fun _ : Fin N ↦ mu)) := by
    simpa using
      (measurePreserving_piCongrLeft
        (μ := fun _ : Fin N ↦ mu)
        (α := fun _ : Fin N ↦ Z) e.symm)
  have hcomp := hrename.comp hrestrict
  convert hcomp using 1
  funext x k
  rfl

/-- A finite-prefix event has exactly the same mass after pullback to the
infinite iid product space. -/
theorem measure_natSamplePrefix_preimage
    [Fintype Z] [MeasurableSingletonClass Z]
    (N : ℕ) (mu : Measure Z) [IsProbabilityMeasure mu]
    (E : Set (Fin N → Z)) :
    Measure.infinitePi (fun _ : ℕ ↦ mu) (natSamplePrefix N ⁻¹' E) =
      Measure.pi (fun _ : Fin N ↦ mu) E := by
  exact (measurePreserving_natSamplePrefix N mu).measure_preimage
    (Set.toFinite E).measurableSet.nullMeasurableSet

/-- Countably many finite-prefix events may be pulled back to one infinite iid
space and unioned at the sum of their real-valued confidence budgets. -/
theorem natPrefix_iUnion_mass_le
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ → ℕ) (budget : ℕ → ℝ)
    (E : (j : ℕ) → Set (Fin (N j) → Z))
    (hbudget_nonneg : ∀ j, 0 ≤ budget j)
    (hbudget_summable : Summable budget)
    (hE : ∀ j,
      Measure.pi (fun _ : Fin (N j) ↦ mu) (E j) ≤
        ENNReal.ofReal (budget j))
    {delta : ℝ} (hbudget_total : (∑' j, budget j) ≤ delta) :
    Measure.infinitePi (fun _ : ℕ ↦ mu)
        (⋃ j, natSamplePrefix (N j) ⁻¹' E j) ≤
      ENNReal.ofReal delta := by
  calc
    Measure.infinitePi (fun _ : ℕ ↦ mu)
          (⋃ j, natSamplePrefix (N j) ⁻¹' E j) ≤
        ∑' j, Measure.infinitePi (fun _ : ℕ ↦ mu)
          (natSamplePrefix (N j) ⁻¹' E j) := measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal (budget j) := by
      apply ENNReal.tsum_le_tsum
      intro j
      exact ((measurePreserving_natSamplePrefix (N j) mu).measure_preimage_le
        (E j)).trans (hE j)
    _ = ENNReal.ofReal (∑' j, budget j) :=
      (ENNReal.ofReal_tsum_of_nonneg hbudget_nonneg hbudget_summable).symm
    _ ≤ ENNReal.ofReal delta := ENNReal.ofReal_le_ofReal hbudget_total

end

end FormalSLT.PACBayes.InfiniteProductMeasureBridge
