/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
import Mathlib.Probability.Martingale.Basic

/-!
# The finite-horizon reverse Bessel martingale

This module packages the one-step reverse conditional-expectation identity for
Bessel sample variance into one genuine martingale on a common finite iid
product space.  Forward process time `k` corresponds to reverse sample size
`max 2 (N - k)`: the process starts at the horizon-`N` Bessel variance, removes
one observation at each step, and stays constant after reaching sample size
two.

The construction proves all martingale quantifiers through mathlib's
`martingale_nat`; it does not assume a caller-supplied martingale interface.
It still does **not** provide a reverse maximal inequality, an exponential
process, or a time-uniform PAC-Bayes theorem.
-/

namespace FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse

open MeasureTheory

noncomputable section

variable {Z : Type*} [MeasurableSpace Z]

/-- Prefix size at reverse-process time `k`.  When `2 ≤ N`, it decreases from
`N` to two and then stays at two. -/
def reverseBesselPrefixSize (N k : ℕ) : ℕ :=
  max 2 (N - k)

theorem reverseBesselPrefixSize_two_le (N k : ℕ) :
    2 ≤ reverseBesselPrefixSize N k := by
  simp [reverseBesselPrefixSize]

theorem reverseBesselPrefixSize_le {N : ℕ} (hN : 2 ≤ N) (k : ℕ) :
    reverseBesselPrefixSize N k ≤ N := by
  simp only [reverseBesselPrefixSize, max_le_iff]
  exact ⟨hN, Nat.sub_le N k⟩

theorem reverseBesselPrefixSize_antitone (N : ℕ) :
    Antitone (reverseBesselPrefixSize N) := by
  intro k l hkl
  unfold reverseBesselPrefixSize
  exact max_le_max_left 2 (Nat.sub_le_sub_left hkl N)

/-- At reverse time `N - m`, the schedule reaches the requested prefix size
`m`, provided that `m` lies in the substantive range `[2, N]`. -/
theorem reverseBesselPrefixSize_sub_eq {N m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) :
    reverseBesselPrefixSize N (N - m) = m := by
  simp [reverseBesselPrefixSize, Nat.sub_sub_self hmN, max_eq_right hm]

/-- The prefix-exchangeable filtration read in reverse sample-size order. -/
def reverseBesselFiltration (N : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin N → Z)) where
  seq k := prefixExchangeableSpace (Z := Z) N (reverseBesselPrefixSize N k)
  mono' := by
    intro k l hkl
    exact prefixExchangeableSpace_antitone (Z := Z) N
      (reverseBesselPrefixSize_antitone N hkl)
  le' k := prefixExchangeableSpace_le (Z := Z) N
    (reverseBesselPrefixSize N k)

/-- Bessel sample variance along the reverse prefix-size schedule. -/
def reverseBesselProcess (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) :
    ℕ → (Fin N → Z) → ℝ :=
  fun k ↦ prefixBesselVariance (reverseBesselPrefixSize_le hN k) ell

theorem reverseBesselProcess_stronglyAdapted [Fintype Z]
    [MeasurableSingletonClass Z] (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) :
    StronglyAdapted (reverseBesselFiltration (Z := Z) N)
      (reverseBesselProcess N hN ell) := by
  intro k
  exact (measurable_prefixBesselVariance
    (reverseBesselPrefixSize_le hN k) ell).stronglyMeasurable

omit [MeasurableSpace Z] in
private theorem prefixBesselVariance_eq_of_size_eq {N t u : ℕ}
    (ht : t ≤ N) (hu : u ≤ N) (ell : Z → ℝ) (htu : t = u) :
    prefixBesselVariance ht ell = prefixBesselVariance hu ell := by
  subst u
  rfl

omit [MeasurableSpace Z] in
/-- The reverse process endpoint at time `N - m` is exactly the Bessel
variance of the first `m` observations. -/
theorem reverseBesselProcess_sub_eq_prefix {N m : ℕ} (hN : 2 ≤ N)
    (hm : 2 ≤ m) (hmN : m ≤ N) (ell : Z → ℝ) (x : Fin N → Z) :
    reverseBesselProcess N hN ell (N - m) x =
      prefixBesselVariance hmN ell x := by
  unfold reverseBesselProcess
  exact congrFun (prefixBesselVariance_eq_of_size_eq _ _ ell
    (reverseBesselPrefixSize_sub_eq hm hmN)) x

private theorem prefixBesselVariance_ae_eq_condExp_of_succ_eq [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    {N t u : ℕ} (hu_two : 2 ≤ u) (ht : t ≤ N) (hu : u ≤ N)
    (ell : Z → ℝ) (hsucc : u + 1 = t) :
    prefixBesselVariance ht ell =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (prefixExchangeableSpace (Z := Z) N t)
        (Measure.pi (fun _ : Fin N ↦ mu))
        (prefixBesselVariance hu ell) := by
  subst t
  simpa only using
    (prefixBesselVariance_ae_eq_condExp mu hu_two ht ell)

theorem reverseBesselProcess_ae_eq_condExp_succ [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) (k : ℕ) :
    reverseBesselProcess N hN ell k =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (reverseBesselFiltration (Z := Z) N k)
        (Measure.pi (fun _ : Fin N ↦ mu))
        (reverseBesselProcess N hN ell (k + 1)) := by
  let t := reverseBesselPrefixSize N k
  let u := reverseBesselPrefixSize N (k + 1)
  have ht_two : 2 ≤ t := reverseBesselPrefixSize_two_le N k
  have hu_two : 2 ≤ u := reverseBesselPrefixSize_two_le N (k + 1)
  have htN : t ≤ N := reverseBesselPrefixSize_le hN k
  have huN : u ≤ N := reverseBesselPrefixSize_le hN (k + 1)
  have hut : u ≤ t := reverseBesselPrefixSize_antitone N (Nat.le_succ k)
  by_cases ht : t = 2
  · have hu : u = 2 := le_antisymm (ht ▸ hut) hu_two
    have hsame :
        reverseBesselProcess N hN ell (k + 1) =
          reverseBesselProcess N hN ell k := by
      have hsize : reverseBesselPrefixSize N (k + 1) =
          reverseBesselPrefixSize N k := hu.trans ht.symm
      unfold reverseBesselProcess
      exact prefixBesselVariance_eq_of_size_eq _ _ ell hsize
    rw [hsame]
    rw [condExp_of_stronglyMeasurable
      ((reverseBesselFiltration (Z := Z) N).le k)
      (reverseBesselProcess_stronglyAdapted N hN ell k)
      Integrable.of_finite]
  · have hsucc : u + 1 = t := by
      dsimp [t, u, reverseBesselPrefixSize] at *
      omega
    change prefixBesselVariance htN ell =ᵐ[Measure.pi (fun _ : Fin N ↦ mu)]
      condExp (prefixExchangeableSpace (Z := Z) N t)
        (Measure.pi (fun _ : Fin N ↦ mu))
        (prefixBesselVariance huN ell)
    exact prefixBesselVariance_ae_eq_condExp_of_succ_eq mu hu_two htN huN
      ell hsucc

/-- **Finite-horizon reverse Bessel martingale.**  Under a finite iid product
law, the Bessel variances at prefix sizes `N, N - 1, ..., 2`, followed by a
constant tail at size two, form a martingale in reverse sample-size time. -/
theorem reverseBesselProcess_martingale [Fintype Z]
    [MeasurableSingletonClass Z] (mu : Measure Z) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 2 ≤ N) (ell : Z → ℝ) :
    Martingale (reverseBesselProcess N hN ell)
      (reverseBesselFiltration (Z := Z) N)
      (Measure.pi (fun _ : Fin N ↦ mu)) := by
  exact martingale_nat
    (reverseBesselProcess_stronglyAdapted N hN ell)
    (fun _ ↦ Integrable.of_finite)
    (reverseBesselProcess_ae_eq_condExp_succ mu N hN ell)

end

end FormalSLT.PACBayes.FiniteEmpiricalVarianceReverse
