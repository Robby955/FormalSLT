import FormalSLT.Covering.TotalBoundedMinimalCovering
import FormalSLT.Covering.ContinuousDudleyUnitInterval
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Function.Floor

/-!
# Total-bounded Dudley capstone with a cardinal-minimal dyadic net schedule

This module threads the cardinal-minimal dyadic finite-net schedule from
`TotalBoundedMinimalCovering` through the projected finite-chain wrapper, then
assembles the guarded continuous-Dudley bound with the resulting real-radius
entropy staircase.

The integrand is the adjacent-product envelope induced by the cardinal-minimal
dyadic nets. Each factor is a genuine `minimalMetricCoveringNumber` at its
sampled radius, but the finite chaining theorem still pays for adjacent
projection pairs, so this is not a pure one-radius `sqrt(log N(T,d,ε))`
integrand.
-/

namespace FormalSLT.Covering.TotalBoundedDudleyMinimalCapstone

open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.TotalBoundedDudley
open FormalSLT.Covering.TotalBoundedDudleyCovering
open FormalSLT.Covering.TotalBoundedMinimalCovering
open FormalSLT.Covering.ContinuousDudleyUnitInterval

noncomputable section

universe u

variable {T : Type u}

/-- Adjacent product of the cardinal-minimal dyadic finite-net counts. -/
def minimalDyadicChainingCoverCount
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : ℕ :=
  (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale j).coveringNumber *
  (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
    (T := T) hT hradiusScale (j + 1)).coveringNumber

/-- The adjacent product is the product of genuine minimal covering numbers at
the two dyadic sampled radii. -/
theorem minimalDyadicChainingCoverCount_eq_minimalMetricCoveringNumber_mul
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalDyadicChainingCoverCount (T := T) hT hradiusScale j =
      minimalMetricCoveringNumber
          (T := T) hT (dyadicChainingNetRadius_pos hradiusScale j) *
        minimalMetricCoveringNumber
          (T := T) hT (dyadicChainingNetRadius_pos hradiusScale (j + 1)) := by
  unfold minimalDyadicChainingCoverCount
  rw [minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_coveringNumber_eq,
    minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_coveringNumber_eq]

lemma minimalDyadicChainingCoverCount_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 < minimalDyadicChainingCoverCount (T := T) hT hradiusScale j := by
  unfold minimalDyadicChainingCoverCount
  exact Nat.mul_pos
    (FiniteNet.coveringNumber_pos
      ((minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net))
    (FiniteNet.coveringNumber_pos
      ((minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net))

/-- Adjacent cardinal-minimal dyadic nets have positive combined radius. -/
theorem minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 <
      (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.radius +
      (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net.radius := by
  have hleft :
      0 <
        (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale j).net.radius := by
    simp [dyadicChainingNetRadius_pos hradiusScale j]
  have hright :
      0 ≤
        (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net.radius :=
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale (j + 1)).net.radius_nonneg
  linarith

/-- Adjacent cardinal-minimal dyadic nets satisfy the geometric radius budget
required by the finite chaining theorem. -/
theorem minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.radius +
      (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net.radius ≤
      radiusScale / (2 : ℝ) ^ j := by
  simpa using
    dyadicChainingNetRadius_pair_sum_le
      (radiusScale := radiusScale) hradiusScale.le j

/-- Monotone prefix envelope of the adjacent cardinal-minimal dyadic cover
products. -/
def minimalDyadicCoverCountEnvelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) : ℕ :=
  (Finset.range (j + 1)).sup' (by simp)
    (fun k => minimalDyadicChainingCoverCount (T := T) hT hradiusScale k)

/-- Real-radius staircase for the cardinal-minimal dyadic cover-count
envelope. -/
def minimalDyadicCoverCountEnvelopeAtRadius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) : ℕ :=
  minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale
    (totalBoundedCoveringIndex radiusScale ε)

/-- Entropy profile induced by the cardinal-minimal dyadic cover-count
envelope. -/
def minimalDyadicCoverCountEntropyAtRadius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) : ℝ :=
  Real.sqrt
    (Real.log
      (minimalDyadicCoverCountEnvelopeAtRadius
        (T := T) hT hradiusScale ε : ℝ))

private lemma div_dyadic_radius
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    radiusScale / (radiusScale / (2 : ℝ) ^ (j + 1)) =
      (2 : ℝ) ^ (j + 1) := by
  field_simp [hradiusScale.ne', pow_ne_zero (j + 1) (by norm_num : (2 : ℝ) ≠ 0)]

private lemma logb_div_dyadic_radius
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    Real.logb 2 (radiusScale / (radiusScale / (2 : ℝ) ^ (j + 1))) =
      (j + 1 : ℝ) := by
  rw [div_dyadic_radius hradiusScale j, ← Real.rpow_natCast]
  simp [Nat.cast_add, Nat.cast_one]

private lemma totalBoundedCoveringIndex_dyadic
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    totalBoundedCoveringIndex radiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) = j := by
  unfold totalBoundedCoveringIndex
  rw [logb_div_dyadic_radius hradiusScale j]
  rw [show (j + 1 : ℝ) = ((j + 1 : ℕ) : ℝ) by simp]
  rw [Nat.floor_natCast]
  omega

private lemma totalBoundedCoveringIndex_of_mem_halfOpenAnnulus
    {radiusScale ε : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ)
    (hleft : radiusScale / (2 : ℝ) ^ (j + 2) < ε)
    (hright : ε ≤ radiusScale / (2 : ℝ) ^ (j + 1)) :
    totalBoundedCoveringIndex radiusScale ε = j := by
  have hleft_pos : 0 < radiusScale / (2 : ℝ) ^ (j + 2) := by positivity
  have hε_pos : 0 < ε := lt_trans hleft_pos hleft
  have hratio_lower :
      (2 : ℝ) ^ (j + 1) ≤ radiusScale / ε := by
    have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
    have hmul :
        (2 : ℝ) ^ (j + 1) * ε ≤ radiusScale := by
      calc
        (2 : ℝ) ^ (j + 1) * ε
            ≤ (2 : ℝ) ^ (j + 1) *
                (radiusScale / (2 : ℝ) ^ (j + 1)) := by
              exact mul_le_mul_of_nonneg_left hright hp.le
        _ = radiusScale := by
              field_simp [pow_ne_zero (j + 1)
                (by norm_num : (2 : ℝ) ≠ 0)]
    exact (le_div_iff₀ hε_pos).mpr hmul
  have hratio_upper :
      radiusScale / ε < (2 : ℝ) ^ (j + 2) := by
    have hp : 0 < (2 : ℝ) ^ (j + 2) := by positivity
    have hmul :
        radiusScale < (2 : ℝ) ^ (j + 2) * ε := by
      calc
        radiusScale =
            (2 : ℝ) ^ (j + 2) *
              (radiusScale / (2 : ℝ) ^ (j + 2)) := by
                field_simp [pow_ne_zero (j + 2)
                  (by norm_num : (2 : ℝ) ≠ 0)]
        _ < (2 : ℝ) ^ (j + 2) * ε := by
              exact mul_lt_mul_of_pos_left hleft hp
    exact (div_lt_iff₀ hε_pos).mpr hmul
  have hlog_lower :
      (j + 1 : ℝ) ≤ Real.logb 2 (radiusScale / ε) := by
    have hratio_pos : 0 < radiusScale / ε := div_pos hradiusScale hε_pos
    have h := (Real.logb_le_logb (b := 2)
      (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))
      hratio_pos).mpr hratio_lower
    simpa [← Real.rpow_natCast, Real.logb_rpow
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h
  have hlog_upper :
      Real.logb 2 (radiusScale / ε) < (j + 2 : ℝ) := by
    have hratio_pos : 0 < radiusScale / ε := div_pos hradiusScale hε_pos
    have h := Real.logb_lt_logb (b := 2)
      (by norm_num : (1 : ℝ) < 2) hratio_pos hratio_upper
    simpa [← Real.rpow_natCast, Real.logb_rpow
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h
  unfold totalBoundedCoveringIndex
  have hfloor : Nat.floor (Real.logb 2 (radiusScale / ε)) = j + 1 := by
    rw [Nat.floor_eq_iff]
    · exact ⟨by simpa [Nat.cast_add, Nat.cast_one] using hlog_lower,
        by
          norm_num [Nat.cast_add, Nat.cast_one] at hlog_upper ⊢
          linarith⟩
    · exact le_trans (by exact_mod_cast Nat.zero_le (j + 1)) hlog_lower
  rw [hfloor]
  omega

/-- The real-radius minimal dyadic envelope samples the prefix envelope at
dyadic radii. -/
theorem minimalDyadicCoverCountEnvelopeAtRadius_dyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalDyadicCoverCountEnvelopeAtRadius (T := T) hT hradiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) =
      minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
  rw [minimalDyadicCoverCountEnvelopeAtRadius,
    totalBoundedCoveringIndex_dyadic hradiusScale j]

/-- The real-radius minimal dyadic envelope is constant on each half-open,
right-closed dyadic annulus. -/
theorem minimalDyadicCoverCountEnvelopeAtRadius_const_on_halfOpenAnnulus
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale ε : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ)
    (hleft : radiusScale / (2 : ℝ) ^ (j + 2) < ε)
    (hright : ε ≤ radiusScale / (2 : ℝ) ^ (j + 1)) :
    minimalDyadicCoverCountEnvelopeAtRadius (T := T) hT hradiusScale ε =
      minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
  simp [minimalDyadicCoverCountEnvelopeAtRadius,
    totalBoundedCoveringIndex_of_mem_halfOpenAnnulus hradiusScale j hleft hright]

lemma minimalDyadicCoverCountEnvelope_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    0 < minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale j :=
  lt_of_lt_of_le (minimalDyadicChainingCoverCount_pos (T := T) hT hradiusScale j)
    (by
      unfold minimalDyadicCoverCountEnvelope
      exact Finset.le_sup' _ (by simp))

lemma monotone_minimalDyadicCoverCountEnvelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) :
    Monotone (minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale) := by
  intro i j hij
  unfold minimalDyadicCoverCountEnvelope
  have hsubset : Finset.range (i + 1) ⊆ Finset.range (j + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.succ_le_succ hij)
  have hnonempty : (Finset.range (i + 1)).Nonempty := by simp
  simpa using Finset.sup'_mono
    (f := fun k => minimalDyadicChainingCoverCount (T := T) hT hradiusScale k)
    hsubset hnonempty

lemma monotone_minimalDyadicCoverCountEntropyAtScale
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) :
    Monotone
      (fun j : ℕ =>
        Real.sqrt (Real.log
          (minimalDyadicCoverCountEnvelope
            (T := T) hT hradiusScale j : ℝ))) := by
  intro i j hij
  apply Real.sqrt_le_sqrt
  have hpos :
      (0 : ℝ) <
        (minimalDyadicCoverCountEnvelope
          (T := T) hT hradiusScale i : ℝ) := by
    exact_mod_cast minimalDyadicCoverCountEnvelope_pos
      (T := T) hT hradiusScale i
  have hle :
      (minimalDyadicCoverCountEnvelope
          (T := T) hT hradiusScale i : ℝ) ≤
        (minimalDyadicCoverCountEnvelope
          (T := T) hT hradiusScale j : ℝ) := by
    exact_mod_cast
      (monotone_minimalDyadicCoverCountEnvelope
        (T := T) hT hradiusScale hij)
  exact Real.log_le_log hpos hle

theorem minimalDyadicCoverCountEntropyAtRadius_nonneg
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (ε : ℝ) :
    0 ≤ minimalDyadicCoverCountEntropyAtRadius (T := T) hT hradiusScale ε := by
  simp [minimalDyadicCoverCountEntropyAtRadius]

private theorem minimalDyadicCoverCountEntropyAtRadius_dyadic
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalDyadicCoverCountEntropyAtRadius (T := T) hT hradiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) =
      Real.sqrt
        (Real.log
          (minimalDyadicCoverCountEnvelope
            (T := T) hT hradiusScale j : ℝ)) := by
  simp [minimalDyadicCoverCountEntropyAtRadius,
    minimalDyadicCoverCountEnvelopeAtRadius_dyadic]

/-- The cardinal-minimal dyadic envelope entropy satisfies the guarded
closed-annulus condition. -/
theorem minimalDyadicCoverCountEntropyAtRadius_guarded
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    GuardedAntitoneOnDyadicAnnulus
      (minimalDyadicCoverCountEntropyAtRadius
        (T := T) hT hradiusScale) radiusScale j := by
  intro ε hleft hright
  by_cases hstrict : radiusScale / (2 : ℝ) ^ (j + 2) < ε
  · rw [minimalDyadicCoverCountEntropyAtRadius_dyadic]
    have hconst :=
      minimalDyadicCoverCountEnvelopeAtRadius_const_on_halfOpenAnnulus
        (T := T) hT hradiusScale j hstrict hright
    simp [minimalDyadicCoverCountEntropyAtRadius, hconst]
  · have hε_left : ε = radiusScale / (2 : ℝ) ^ (j + 2) := by
      exact le_antisymm (le_of_not_gt hstrict) hleft
    have hleft_dyadic :
        minimalDyadicCoverCountEntropyAtRadius (T := T) hT hradiusScale
            (radiusScale / (2 : ℝ) ^ (j + 2)) =
          Real.sqrt
            (Real.log
              (minimalDyadicCoverCountEnvelope
                (T := T) hT hradiusScale (j + 1) : ℝ)) := by
      simpa [show j + 1 + 1 = j + 2 by omega] using
        minimalDyadicCoverCountEntropyAtRadius_dyadic
          (T := T) hT hradiusScale (j + 1)
    rw [hε_left, minimalDyadicCoverCountEntropyAtRadius_dyadic, hleft_dyadic]
    exact monotone_minimalDyadicCoverCountEntropyAtScale
      (T := T) hT hradiusScale (Nat.le_succ j)

/-- At a dyadic radius, the minimal-schedule real-radius entropy dominates the
finite dyadic entropy envelope used by the finite projected-chain wrapper. -/
theorem minimalDyadicCoverCountEntropy_dominates_dyadicEnvelope_sample
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    FiniteSubGaussianProcess.finitePrefixSupEnvelope
        (fun k => Real.sqrt
          (Real.log (minimalDyadicChainingCoverCount
            (T := T) hT hradiusScale k : ℝ))) j ≤
      minimalDyadicCoverCountEntropyAtRadius (T := T) hT hradiusScale
        (radiusScale / (2 : ℝ) ^ (j + 1)) := by
  unfold FiniteSubGaussianProcess.finitePrefixSupEnvelope
  rw [minimalDyadicCoverCountEntropyAtRadius_dyadic]
  refine Finset.sup'_le _ _ ?_
  intro k hk
  apply Real.sqrt_le_sqrt
  have hpos :
      (0 : ℝ) <
        (minimalDyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ) := by
    exact_mod_cast minimalDyadicChainingCoverCount_pos (T := T) hT hradiusScale k
  have hk_le_j : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hcount_le :
      minimalDyadicChainingCoverCount (T := T) hT hradiusScale k ≤
        minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
    have hkj :
        minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale k ≤
          minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale j :=
      monotone_minimalDyadicCoverCountEnvelope
        (T := T) hT hradiusScale hk_le_j
    have hsample :
        minimalDyadicChainingCoverCount (T := T) hT hradiusScale k ≤
          minimalDyadicCoverCountEnvelope (T := T) hT hradiusScale k := by
      unfold minimalDyadicCoverCountEnvelope
      exact Finset.le_sup' _ (by simp)
    exact hsample.trans hkj
  have hcount_le_real :
      (minimalDyadicChainingCoverCount (T := T) hT hradiusScale k : ℝ) ≤
        (minimalDyadicCoverCountEnvelope
          (T := T) hT hradiusScale j : ℝ) := by
    exact_mod_cast hcount_le
  exact Real.log_le_log hpos hcount_le_real

/-- Projected finite-chain wrapper for the cardinal-minimal dyadic schedule,
compared against a supplied finite entropy-at-radius upper-sum budget. -/
theorem finite_projectedNet_dudley_entropy_sum_totalBounded_minimalDyadic_entropy_integral_comparison_nonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (m : ℕ) (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ) (integralBudget : ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropyAtRadius : ∀ j ∈ Finset.range m,
      FiniteSubGaussianProcess.finitePrefixSupEnvelope
          (fun j => Real.sqrt (Real.log
            (minimalDyadicChainingCoverCount (T := T) hT hradiusScale j : ℝ))) j ≤
        entropyAtRadius (radiusScale / (2 : ℝ) ^ (j + 1)))
    (hupperSum :
      FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
        radiusScale m entropyAtRadius ≤ integralBudget)
    (hcoarse :
      finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale 0).net.projection
                (FiniteNet.ProjectedIndex.source
                  (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
                    (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget) :
    finiteExpectation P.weight
        (fun ω => finiteSup
          (fun u : FiniteNet.ProjectedIndex
              (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net =>
            P.X ω
              ((minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
                (T := T) hT hradiusScale m).net.center u.1))) ≤
      coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) * integralBudget := by
  classical
  let A : ℕ → Type u := fun j =>
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).A
  let N : ∀ j : ℕ, FiniteNet T (A j) := fun j =>
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net
  refine FiniteSubGaussianProcess.finite_projectedNet_dudley_entropy_sum_coveringNumbers_geometric_entropy_integral_comparison_nonempty
    (P := P) (A := A) (N := N) (m := m) (coarseBudget := coarseBudget)
    (radiusScale := radiusScale)
    (coverCount := fun j => minimalDyadicChainingCoverCount (T := T) hT hradiusScale j)
    (entropyAtRadius := entropyAtRadius) (integralBudget := integralBudget)
    ?hdist ?hsymm ?htri hvariance hradiusScale.le ?hradius_pos
    ?hradius_geometric ?hcoverCount ?hentropyAtRadius hupperSum ?hcoarse
  · intro j
    dsimp [N]
    rw [minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_dist, hdistP]
  · intro s t
    rw [hdistP]
    exact dist_comm s t
  · intro x y z
    rw [hdistP]
    exact dist_triangle x y z
  · intro j _hj
    dsimp [N]
    exact minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_pos
      (T := T) hT hradiusScale j
  · intro j _hj
    dsimp [N]
    exact minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_pair_radius_le
      (T := T) hT hradiusScale j
  · intro j _hj
    rfl
  · intro j hj
    simpa using hentropyAtRadius j hj
  · exact hcoarse

/-- Boundary certificate for the cardinal-minimal dyadic net schedule.

The terminal and coarse terms are stated using
`minimalDyadicChainingFiniteNetOfTotallyBoundedUniv`; no separate "covers are
minimal" hypothesis is introduced. -/
def MinimalSeparableTerminalSupremumBoundaryChoiceNonempty
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget : ℕ → ℝ) (radiusScale : ℝ)
    (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (eta : ℝ) (m : ℕ) : Prop :=
  ∃ (K : Type u), ∃ (_instK : Fintype K), ∃ (_nonemptyK : Nonempty K),
  ∃ (embed : K → T),
  ∃ (separabilityError : ℝ), ∃ (terminalError : ℝ),
    separabilityError + terminalError ≤ eta ∧
    (∀ j ∈ Finset.range m,
      IntervalIntegrable entropyAtRadius MeasureTheory.volume
        (radiusScale / (2 : ℝ) ^ (j + 2))
        (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
    (∀ ω : Ω,
      supFunctional ω ≤
        finiteSup (fun k : K => P.X ω (embed k)) + separabilityError) ∧
    (∀ ω : Ω, ∀ k : K,
      P.X ω (embed k) ≤
        P.X ω
          ((minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
            (T := T) hT hradiusScale m).net.projection (embed k)) +
          terminalError) ∧
    (finiteExpectation P.weight
      (fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex
            (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale m).net =>
          P.X ω
            ((minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
              (T := T) hT hradiusScale 0).net.projection
              (FiniteNet.ProjectedIndex.source
                (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
                  (T := T) hT hradiusScale m).net u)))) ≤
      coarseBudget m)

/-- Boundary certificates imply the finite dyadic upper-sum input needed by
the guarded continuous wrapper, using the cardinal-minimal dyadic cover-count
entropy profile. -/
theorem totalBoundedMinimalDyadicCoverCount_dyadicProfileBound_of_boundaryChoice
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        MinimalSeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius :=
            minimalDyadicCoverCountEntropyAtRadius
              (T := T) hT hradiusScale)
          (supFunctional := supFunctional) eta m) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        (∀ j ∈ Finset.range m,
          GuardedAntitoneOnDyadicAnnulus
            (minimalDyadicCoverCountEntropyAtRadius
              (T := T) hT hradiusScale) radiusScale j) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable
            (minimalDyadicCoverCountEntropyAtRadius
              (T := T) hT hradiusScale) MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        finiteExpectation P.weight supFunctional ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m
              (minimalDyadicCoverCountEntropyAtRadius
                (T := T) hT hradiusScale) + eta := by
  intro eta heta
  rcases hchoose eta heta with ⟨m, hchoice⟩
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, separabilityError, terminalError,
      herror, hintervalIntegrable, hseparable,
      hterminalApprox, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  refine ⟨m, ?_, ?_, ?_⟩
  · intro j _hj
    exact minimalDyadicCoverCountEntropyAtRadius_guarded
      (T := T) hT hradiusScale j
  · intro j hj
    exact hintervalIntegrable j hj
  · let minimalEntropy : ℝ → ℝ :=
      minimalDyadicCoverCountEntropyAtRadius (T := T) hT hradiusScale
    let terminalNet :=
      (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale m).net
    let projectedSup : Ω → ℝ :=
      fun ω => finiteSup
        (fun u : FiniteNet.ProjectedIndex terminalNet =>
          P.X ω (terminalNet.center u.1))
    have hadapter :
        finiteExpectation P.weight supFunctional ≤
          finiteExpectation P.weight projectedSup +
            (separabilityError + terminalError) := by
      exact finiteExpectation_supFunctional_le_projected_add_skeleton_terminalError
        P.weight_nonneg P.weight_sum_one terminalNet embed P.X
        supFunctional separabilityError terminalError hseparable
        hterminalApprox
    have hprojected :
        finiteExpectation P.weight projectedSup ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m minimalEntropy := by
      simpa [minimalEntropy, terminalNet, projectedSup] using
        finite_projectedNet_dudley_entropy_sum_totalBounded_minimalDyadic_entropy_integral_comparison_nonempty
          (P := P) (hT := hT) (m := m) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (entropyAtRadius := minimalEntropy)
          (integralBudget :=
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m minimalEntropy)
          hradiusScale hdistP hvariance
          (by
            intro j hj
            simpa [minimalEntropy] using
              minimalDyadicCoverCountEntropy_dominates_dyadicEnvelope_sample
                (T := T) hT hradiusScale j)
          le_rfl
          hcoarse
    have hwithError :
        finiteExpectation P.weight supFunctional ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m minimalEntropy +
            (separabilityError + terminalError) := by
      linarith [hadapter, hprojected]
    have herrorBudget :
        coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m minimalEntropy +
            (separabilityError + terminalError) ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m minimalEntropy + eta := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left herror
          (coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m minimalEntropy)
    exact hwithError.trans herrorBudget

/-- Continuous Dudley bound for a totally bounded index space using the
cardinal-minimal dyadic cover-count envelope.

The integrand is
`ε ↦ minimalDyadicCoverCountEntropyAtRadius hT hradiusScale ε`, the entropy of
the adjacent-product prefix envelope generated by the cardinal-minimal dyadic
finite nets. Each sampled net count equals the genuine
`minimalMetricCoveringNumber`, but the finite chaining surface still uses
adjacent products. -/
-- fidelity: the entropy integrand is the cardinal-minimal dyadic adjacent
-- product envelope, not a pure one-radius minimal covering number.
theorem continuous_dudley_entropy_integral_iSup_totalBounded_minimalDyadicCoverCountEnvelope
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hint0 :
      IntervalIntegrable
        (minimalDyadicCoverCountEntropyAtRadius
          (T := T) hT hradiusScale) MeasureTheory.volume
        0 (radiusScale / 2))
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        MinimalSeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius :=
            minimalDyadicCoverCountEntropyAtRadius
              (T := T) hT hradiusScale)
          (supFunctional := supFunctional) eta m) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2),
          minimalDyadicCoverCountEntropyAtRadius
            (T := T) hT hradiusScale ε) := by
  exact
    continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded
      (P := P) (coarseBudget := coarseBudget) (radiusScale := radiusScale)
      (entropyAtRadius :=
        minimalDyadicCoverCountEntropyAtRadius (T := T) hT hradiusScale)
      (supFunctional := supFunctional) hradiusScale
      (minimalDyadicCoverCountEntropyAtRadius_nonneg
        (T := T) hT hradiusScale)
      hint0
      (totalBoundedMinimalDyadicCoverCount_dyadicProfileBound_of_boundaryChoice
        (P := P) (hT := hT) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (supFunctional := supFunctional)
        hradiusScale hdistP hvariance hchoose)

/-- Unit-interval non-vacuity witness for the cardinal-minimal dyadic
cover-count envelope surface. -/
theorem unitInterval_minimalDyadicCoverCountEnvelope_sample_positive :
    0 <
      minimalDyadicCoverCountEnvelopeAtRadius
        (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
        FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
        (by norm_num : (0 : ℝ) < 1) ((1 : ℝ) / 2) := by
  have hsample :=
    minimalDyadicCoverCountEnvelopeAtRadius_dyadic
      (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
      FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
      (by norm_num : (0 : ℝ) < 1) 0
  norm_num at hsample
  rw [hsample]
  exact minimalDyadicCoverCountEnvelope_pos
    (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
    FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
    (by norm_num : (0 : ℝ) < 1) 0

end

end FormalSLT.Covering.TotalBoundedDudleyMinimalCapstone
