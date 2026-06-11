import FormalSLT.Covering.DudleyChainingSum
import FormalSLT.Covering.TotalBoundedDudley

/-!
# Finite Dudley sum-to-integral comparison

This module closes the finite G3 Dudley lane: q086 gives the centered
finite-net chaining sum, and this file compares the dyadic entropy sum with a
truncated entropy integral.

All statements stay finite-scale. The terminal theorem is stated for finite
outcome spaces, finite index sets, and an abstract finite covering-number
profile supplied by the caller.
-/

namespace FormalSLT.Covering.DudleySumToIntegral

open Finset
open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.DudleyChainingSum

noncomputable section

variable {Ω T : Type*}

/-- Entropy from a positive antitone covering-number profile is antitone. -/
theorem coveringNumber_entropy_antitone
    (coveringNumberAtRadius : ℝ → ℕ)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε) :
    Antitone
      (fun ε : ℝ => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  intro ε δ hεδ
  apply Real.sqrt_le_sqrt
  have hpos : 0 < (coveringNumberAtRadius δ : ℝ) := by
    exact_mod_cast hcover_pos δ
  have hle :
      (coveringNumberAtRadius δ : ℝ) ≤ (coveringNumberAtRadius ε : ℝ) := by
    exact_mod_cast hcover_antitone hεδ
  exact Real.log_le_log hpos hle

/--
Interval integrability of the finite covering-number entropy profile from
antitonicity and positivity.
-/
theorem coveringNumber_entropy_integrable_of_antitone
    (coveringNumberAtRadius : ℝ → ℕ) (a b : ℝ)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε) :
    IntervalIntegrable
      (fun ε : ℝ => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
      MeasureTheory.volume a b := by
  exact (coveringNumber_entropy_antitone
    coveringNumberAtRadius hcover_antitone hcover_pos).intervalIntegrable

/--
Interval-integrability compatibility wrapper for callers that still carry a
finite boundedness receipt on the interval.
-/
theorem coveringNumber_entropy_integrable
    (coveringNumberAtRadius : ℝ → ℕ) (a b : ℝ)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (_hcover_bound : ∃ M : ℕ,
      ∀ ε ∈ Set.uIcc a b, coveringNumberAtRadius ε ≤ M)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε) :
    IntervalIntegrable
      (fun ε : ℝ => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ)))
      MeasureTheory.volume a b := by
  exact coveringNumber_entropy_integrable_of_antitone
    coveringNumberAtRadius a b hcover_antitone hcover_pos

/--
Dyadic upper-sum comparison for an abstract antitone entropy profile. The
factor is `2` for the finite truncated interval
`[radiusScale / 2^(m+1), radiusScale / 2]`; the later Dudley theorem pays one
more factor `2` when rewriting geometric radii as dyadic annulus widths.
-/
theorem dyadic_sum_le_entropy_integral
    {radiusScale : ℝ} (m : ℕ) (entropyAtRadius : ℝ → ℝ)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) :
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
        radiusScale m entropyAtRadius ≤
      2 * ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
        entropyAtRadius ε := by
  exact
    FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum_le_two_mul_truncatedIntervalIntegral
      (m := m) (entropyAtRadius := entropyAtRadius)
      hradiusScale_nonneg hentropy_antitone hintervalIntegrable

/--
Centered finite Dudley entropy integral, assembled from q086's chaining sum
and the dyadic sum-to-integral comparison above.

The covering profile is supplied as a positive antitone Nat-valued function
`coveringNumberAtRadius`. The per-scale hypothesis compares the adjacent
finite-net product `(N_j * N_{j+1})` with that profile at the lower endpoint of
the dyadic annulus.
-/
theorem dudley_entropy_integral_of_antitone_coveringNumber
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (t₀ : T) (radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hroot : ∀ t : T, (N 0).projection t = t₀)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε)
    (hcover_product : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hcenter : ∀ j ∈ Finset.range m,
      ∀ pair : FiniteNet.ProjectionPair (N j) (N (j + 1)),
        finiteExpectation P.weight
          (fun ω => P.X ω ((N (j + 1)).center pair.1.2) -
            P.X ω ((N j).center pair.1.1)) = 0) :
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t : T => P.X ω t - P.X ω t₀)) ≤
      4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  classical
  let entropyAtRadius : ℝ → ℝ :=
    fun ε => Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))
  have hentropy_antitone : Antitone entropyAtRadius := by
    simpa [entropyAtRadius] using
      coveringNumber_entropy_antitone
        coveringNumberAtRadius hcover_antitone hcover_pos
  have hintervalIntegrable : ∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1)) := by
    intro j hj
    simpa [entropyAtRadius] using
      coveringNumber_entropy_integrable_of_antitone
        coveringNumberAtRadius
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))
        hcover_antitone hcover_pos
  have hupper :
      FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
          radiusScale m entropyAtRadius ≤
        2 * ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          entropyAtRadius ε := by
    exact dyadic_sum_le_entropy_integral
      (m := m) (entropyAtRadius := entropyAtRadius)
      hradiusScale_nonneg hentropy_antitone hintervalIntegrable
  have hsum_to_profile :
      (∑ j ∈ Finset.range m,
        ((N j).radius + (N (j + 1)).radius) *
          Real.sqrt
            (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))) ≤
        2 * FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
          radiusScale m entropyAtRadius := by
    calc
      (∑ j ∈ Finset.range m,
        ((N j).radius + (N (j + 1)).radius) *
          Real.sqrt
            (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)))
          ≤
        ∑ j ∈ Finset.range m,
          (radiusScale / (2 : ℝ) ^ j) *
            entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hterm_nonneg :
              0 ≤ Real.sqrt
                (Real.log
                  ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) :=
            Real.sqrt_nonneg _
          have hgeom_nonneg :
              0 ≤ radiusScale / (2 : ℝ) ^ j :=
            div_nonneg hradiusScale_nonneg (pow_pos (by norm_num : (0 : ℝ) < 2) j).le
          have hproduct_pos_nat :
              0 < (N j).coveringNumber * (N (j + 1)).coveringNumber := by
            obtain ⟨t⟩ := (inferInstance : Nonempty T)
            haveI : Nonempty (A j) := ⟨(N j).project t⟩
            haveI : Nonempty (A (j + 1)) := ⟨(N (j + 1)).project t⟩
            exact Nat.mul_pos
              (by simpa [FiniteNet.coveringNumber] using
                (Fintype.card_pos (α := A j)))
              (by simpa [FiniteNet.coveringNumber] using
                (Fintype.card_pos (α := A (j + 1))))
          have hproduct_pos_real :
              0 < ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) := by
            exact_mod_cast hproduct_pos_nat
          have hproduct_le_cover_real :
              ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ) ≤
                (coveringNumberAtRadius
                  (radiusScale / (2 : ℝ) ^ (j + 1)) : ℝ) := by
            exact_mod_cast hcover_product j hj
          have hentropy_step :
              Real.sqrt
                  (Real.log
                    ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) ≤
                entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) := by
            dsimp [entropyAtRadius]
            exact Real.sqrt_le_sqrt
              (Real.log_le_log hproduct_pos_real hproduct_le_cover_real)
          calc
            ((N j).radius + (N (j + 1)).radius) *
                Real.sqrt
                  (Real.log
                    ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ))
                ≤
              (radiusScale / (2 : ℝ) ^ j) *
                Real.sqrt
                  (Real.log
                    ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) := by
                exact mul_le_mul_of_nonneg_right
                  (hradius_geometric j hj) hterm_nonneg
            _ ≤ (radiusScale / (2 : ℝ) ^ j) *
                  entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)) := by
                exact mul_le_mul_of_nonneg_left hentropy_step hgeom_nonneg
      _ =
        2 * FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
          radiusScale m entropyAtRadius := by
          rw [FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [FiniteSubGaussianProcess.dyadic_radius_eq_two_mul_annulus_width
            radiusScale j]
          ring
  have hchain :=
    dudley_chaining_sum
      (P := P) (N := N) (m := m) (t₀ := t₀)
      hdist hsymm htri hroot hlast hvariance hradius_pos hcenter
  have hcoef_nonneg : 0 ≤ Real.sqrt (2 * P.varianceProxy) :=
    Real.sqrt_nonneg _
  calc
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t : T => P.X ω t - P.X ω t₀))
        ≤
      Real.sqrt (2 * P.varianceProxy) *
        ∑ j ∈ Finset.range m,
          ((N j).radius + (N (j + 1)).radius) *
            Real.sqrt
              (Real.log ((N j).coveringNumber * (N (j + 1)).coveringNumber : ℝ)) :=
        hchain
    _ ≤ Real.sqrt (2 * P.varianceProxy) *
          (2 * FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
            radiusScale m entropyAtRadius) := by
        exact mul_le_mul_of_nonneg_left hsum_to_profile hcoef_nonneg
    _ ≤ Real.sqrt (2 * P.varianceProxy) *
          (2 * (2 * ∫ ε in
            (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            entropyAtRadius ε)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hupper (by norm_num : 0 ≤ (2 : ℝ)))
          hcoef_nonneg
    _ = 4 * Real.sqrt (2 * P.varianceProxy) *
          (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
            Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
        simp [entropyAtRadius]
        ring

/--
Centered finite Dudley entropy-integral compatibility wrapper for callers that
still provide an interval boundedness receipt for the covering profile.
-/
theorem dudley_entropy_integral
    [Fintype Ω] [Fintype T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    {A : ℕ → Type*} [∀ j : ℕ, Fintype (A j)]
    (N : ∀ j : ℕ, FiniteNet T (A j))
    (m : ℕ) (t₀ : T) (radiusScale : ℝ)
    (coveringNumberAtRadius : ℝ → ℕ)
    (hdist : ∀ j : ℕ, (N j).dist = P.dist)
    (hsymm : ∀ s t : T, P.dist s t = P.dist t s)
    (htri : ∀ x y z : T, P.dist x z ≤ P.dist x y + P.dist y z)
    (hroot : ∀ t : T, (N 0).projection t = t₀)
    (hlast : ∀ t : T, (N m).projection t = t)
    (hvariance : 0 < P.varianceProxy)
    (hradiusScale_nonneg : 0 ≤ radiusScale)
    (hradius_pos : ∀ j ∈ Finset.range m, 0 < (N j).radius + (N (j + 1)).radius)
    (hradius_geometric : ∀ j ∈ Finset.range m,
      (N j).radius + (N (j + 1)).radius ≤ radiusScale / (2 : ℝ) ^ j)
    (hcover_antitone : Antitone coveringNumberAtRadius)
    (_hcover_bound : ∀ j ∈ Finset.range m, ∃ M : ℕ,
      ∀ ε ∈ Set.uIcc
          (radiusScale / (2 : ℝ) ^ (j + 2))
          (radiusScale / (2 : ℝ) ^ (j + 1)),
        coveringNumberAtRadius ε ≤ M)
    (hcover_pos : ∀ ε : ℝ, 0 < coveringNumberAtRadius ε)
    (hcover_product : ∀ j ∈ Finset.range m,
      (N j).coveringNumber * (N (j + 1)).coveringNumber ≤
        coveringNumberAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hcenter : ∀ j ∈ Finset.range m,
      ∀ pair : FiniteNet.ProjectionPair (N j) (N (j + 1)),
        finiteExpectation P.weight
          (fun ω => P.X ω ((N (j + 1)).center pair.1.2) -
            P.X ω ((N j).center pair.1.1)) = 0) :
    finiteExpectation P.weight
        (fun ω => finiteSup (fun t : T => P.X ω t - P.X ω t₀)) ≤
      4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2),
          Real.sqrt (Real.log (coveringNumberAtRadius ε : ℝ))) := by
  exact
    dudley_entropy_integral_of_antitone_coveringNumber
      (P := P) (N := N) (m := m) (t₀ := t₀)
      (radiusScale := radiusScale)
      (coveringNumberAtRadius := coveringNumberAtRadius)
      hdist hsymm htri hroot hlast hvariance hradiusScale_nonneg
      hradius_pos hradius_geometric hcover_antitone hcover_pos
      hcover_product hcenter

end

end FormalSLT.Covering.DudleySumToIntegral
