/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayesFiniteProductMGF

/-!
# Exact variance of finite indicator losses

This module records the elementary but useful variance identity behind the
finite PAC-Bayes--Bernstein route. For an arbitrary Boolean-valued bad-event
predicate on a finite data domain, the associated indicator loss has exact
population variance `R * (1 - R)`, where `R` is its population risk.

The result is distribution-generic within the finite setting: it assumes only
a finite probability mass function. It is not restricted to a literal
Bernoulli sample space or a particular classifier representation.
-/

namespace FormalSLT.PACBayes.IndicatorVariance

open Finset BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF

noncomputable section

variable {ι Z : Type*}

/-- The real-valued indicator loss associated with a Boolean bad-event predicate. -/
def indicatorLoss (bad : ι → Z → Bool) : ι → Z → ℝ :=
  fun i z => if bad i z then 1 else 0

/-- Population risk of a Boolean indicator loss under a finite mass function. -/
def indicatorPopulationRisk [Fintype Z]
    (p : Z → ℝ) (bad : ι → Z → Bool) (i : ι) : ℝ :=
  finitePopulationRisk p (indicatorLoss bad) i

@[simp] theorem indicatorLoss_sq (bad : ι → Z → Bool) (i : ι) (z : Z) :
    (indicatorLoss bad i z) ^ (2 : Nat) = indicatorLoss bad i z := by
  cases h : bad i z <;> simp [indicatorLoss, h]

theorem indicatorLoss_nonneg (bad : ι → Z → Bool) (i : ι) (z : Z) :
    0 ≤ indicatorLoss bad i z := by
  cases h : bad i z <;> simp [indicatorLoss, h]

theorem indicatorLoss_le_one (bad : ι → Z → Bool) (i : ι) (z : Z) :
    indicatorLoss bad i z ≤ 1 := by
  cases h : bad i z <;> simp [indicatorLoss, h]

theorem indicatorPopulationRisk_nonneg [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι) :
    0 ≤ indicatorPopulationRisk p bad i := by
  unfold indicatorPopulationRisk finitePopulationRisk
  exact Finset.sum_nonneg
    (fun z _ => mul_nonneg (hp.nonneg z) (indicatorLoss_nonneg bad i z))

theorem indicatorPopulationRisk_le_one [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι) :
    indicatorPopulationRisk p bad i ≤ 1 := by
  unfold indicatorPopulationRisk finitePopulationRisk
  calc
    (∑ z : Z, p z * indicatorLoss bad i z) ≤ ∑ z : Z, p z * 1 := by
      exact Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (indicatorLoss_le_one bad i z) (hp.nonneg z))
    _ = 1 := by simp [hp.sum_one]

theorem indicatorPopulationRisk_mem_Icc [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι) :
    indicatorPopulationRisk p bad i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨indicatorPopulationRisk_nonneg p hp bad i,
    indicatorPopulationRisk_le_one p hp bad i⟩

/-- The population-centered indicator loss has mean zero. -/
theorem indicatorDeviation_centered [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι) :
    (∑ z : Z,
        p z * (indicatorPopulationRisk p bad i - indicatorLoss bad i z)) = 0 := by
  unfold indicatorPopulationRisk finitePopulationRisk
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.sum_one, one_mul, sub_self]

/-- Exact variance identity for an arbitrary finite Boolean indicator loss. -/
theorem indicatorDeviation_secondMoment_eq [Fintype Z]
    (p : Z → ℝ) (hp : IsPMF p) (bad : ι → Z → Bool) (i : ι) :
    (∑ z : Z,
        p z * (indicatorPopulationRisk p bad i - indicatorLoss bad i z) ^ (2 : Nat)) =
      indicatorPopulationRisk p bad i * (1 - indicatorPopulationRisk p bad i) := by
  let R := indicatorPopulationRisk p bad i
  have hR : (∑ z : Z, p z * indicatorLoss bad i z) = R := by
    rfl
  have hconst : (∑ z : Z, p z * R ^ (2 : Nat)) = R ^ (2 : Nat) := by
    rw [← Finset.sum_mul, hp.sum_one, one_mul]
  have hlinear :
      (∑ z : Z, p z * (2 * R * indicatorLoss bad i z)) = 2 * R * R := by
    calc
      (∑ z : Z, p z * (2 * R * indicatorLoss bad i z)) =
          2 * R * ∑ z : Z, p z * indicatorLoss bad i z := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            ring
      _ = 2 * R * R := by rw [hR]
  calc
    (∑ z : Z, p z * (R - indicatorLoss bad i z) ^ (2 : Nat)) =
        ∑ z : Z,
          (p z * R ^ (2 : Nat) -
            p z * (2 * R * indicatorLoss bad i z) +
            p z * indicatorLoss bad i z) := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [sub_sq, indicatorLoss_sq]
          ring
    _ = (∑ z : Z, p z * R ^ (2 : Nat)) -
          (∑ z : Z, p z * (2 * R * indicatorLoss bad i z)) +
          (∑ z : Z, p z * indicatorLoss bad i z) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = R ^ (2 : Nat) - 2 * R * R + R := by rw [hconst, hlinear, hR]
    _ = R * (1 - R) := by ring

end

end FormalSLT.PACBayes.IndicatorVariance
