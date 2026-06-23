/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real
import FormalSLT.AnytimeValid.OptimizedLambdaCS

/-!
# Dyadic-epoch p-series stitch for the optimized-lambda CS

This module records why the all-`n` literal `subGammaLogLogWidth` theorem is not
discharged by a countable dyadic mixture.

The finite-grid theorem in `OptimizedLambdaCS` pays a budget
`Real.log ((Lam.card : Real) / delta)`. A countable mixture with epoch weights
`w_j` would pay the corresponding term `Real.log (1 / (delta * w_j))`
(up to the existing two-sided factor). On the dyadic epoch where
`Real.log (Real.log n)` is comparable to `Real.log j`, matching the current
literal budget `logLogBudget n delta` with no extra stitching charge forces
`w_j` to be comparable to `1 / j`.

The checked theorem below records the obstruction: shifted harmonic weights are
not summable, so they cannot be the weights of a probability mixture. A dyadic
stitch with summable weights, for example p-series weights, pays an extra epoch
term in the boundary. That proves a different theorem from the literal
`subGammaLogLogWidth` statement requested here.

The weakened route is formalized below. The new prerequisite
`countableWeightedSupermartingale_tsum` proves that a countable weighted series
of real supermartingales is again a supermartingale under the Bochner
summability, adaptedness, and integrability hypotheses needed to exchange
`tsum` and set integrals. The dyadic-epoch CS then applies this brick to
epoch-indexed finite stitched grids and pays the explicit penalty
`log(epochWeightTotal w / w_j)` through `dyadicEpochGridBudget`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/--
The epoch weights forced by matching the current literal `logLogBudget` with no
extra countable-stitching charge. The shift avoids the zero denominator.
-/
def literalDyadicEpochWeight (j : ℕ) : ℝ :=
  1 / ((j + 1 : ℕ) : ℝ)

/--
Shifted harmonic epoch weights are not summable. Hence they cannot normalize a
countable probability mixture, which is the obstruction to proving the existing
literal `subGammaLogLogWidth` as an unconditional all-`n` stitched CS by the
dyadic-epoch route.
-/
theorem literalDyadicEpochWeight_not_summable :
    ¬ Summable literalDyadicEpochWeight := by
  unfold literalDyadicEpochWeight
  simpa [Nat.cast_add, Nat.cast_one] using
    (mt (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 1).mp
      Real.not_summable_one_div_natCast)

/-! ## Summable p-series epoch weights -/

/--
A concrete summable dyadic-epoch weight. The factor `1/2` is deliberately
conservative: the exact normalizing constant is irrelevant for the countable
mixture brick, while the p-series exponent `2` is the essential summability
choice.
-/
def pSeriesDyadicEpochWeight (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2

/-- The p-series dyadic-epoch weights are summable. -/
theorem pSeriesDyadicEpochWeight_summable :
    Summable pSeriesDyadicEpochWeight := by
  have hbase : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 := by
    exact Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable fun j : ℕ => (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 2) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using
      (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hbase
  unfold pSeriesDyadicEpochWeight
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hshift.mul_left (1 / 2 : ℝ)

/-- The p-series dyadic-epoch weights are pointwise nonnegative. -/
theorem pSeriesDyadicEpochWeight_nonneg (j : ℕ) :
    0 ≤ pSeriesDyadicEpochWeight j := by
  unfold pSeriesDyadicEpochWeight
  positivity

/-- The p-series dyadic-epoch weights are strictly positive. -/
theorem pSeriesDyadicEpochWeight_pos (j : ℕ) :
    0 < pSeriesDyadicEpochWeight j := by
  unfold pSeriesDyadicEpochWeight
  positivity

/-- The first p-series epoch has weight `1/2`. -/
theorem pSeriesDyadicEpochWeight_zero :
    pSeriesDyadicEpochWeight 0 = 1 / 2 := by
  norm_num [pSeriesDyadicEpochWeight]

/-- The concrete unit-capital stitching penalty for epoch `0` is `log 2`. -/
theorem pSeriesDyadicEpochWeight_zero_unitPenalty :
    Real.log (1 / pSeriesDyadicEpochWeight 0) = Real.log 2 := by
  rw [pSeriesDyadicEpochWeight_zero]
  norm_num

/-! ## Countable weighted supermartingale sums -/

/--
Weighted countable sums of real supermartingales are supermartingales, provided
the weighted series is adapted and integrable and the Bochner integral may be
interchanged with the countable sum on every filtration test set.

This is the countable analogue of `supermartingale_finset_sum`. The explicit
`hsummable_integral_norm` hypothesis is exactly the domination needed by
`integral_tsum_of_summable_integral_norm`; it is the missing mathlib brick this
dyadic-epoch route needs before specializing to p-series epoch mixtures.
-/
theorem countableWeightedSupermartingale_tsum
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {M : ℕ → ℕ → Ω → ℝ} {w : ℕ → ℝ}
    (hw_nonneg : ∀ k, 0 ≤ w k)
    (hM : ∀ k, Supermartingale (M k) ℱ μ)
    (hadapted : StronglyAdapted ℱ (fun n ω => ∑' k, w k * M k n ω))
    (hintegrable : ∀ n, Integrable (fun ω => ∑' k, w k * M k n ω) μ)
    (hsummable_integral_norm :
      ∀ n, ∀ s : Set Ω, MeasurableSet s →
        Summable fun k => ∫ ω in s, ‖w k * M k n ω‖ ∂μ) :
    Supermartingale (fun n ω => ∑' k, w k * M k n ω) ℱ μ := by
  refine supermartingale_of_setIntegral_succ_le hadapted hintegrable ?_
  intro i s hs
  have hs_meas : MeasurableSet s := ℱ.le i s hs
  have hnext_int :
      ∀ k, Integrable (fun ω => w k * M k (i + 1) ω) (μ.restrict s) := by
    intro k
    exact (((hM k).integrable (i + 1)).const_mul (w k)).restrict
  have hcur_int :
      ∀ k, Integrable (fun ω => w k * M k i ω) (μ.restrict s) := by
    intro k
    exact (((hM k).integrable i).const_mul (w k)).restrict
  have hnext_swap :
      (∑' k, ∫ ω in s, w k * M k (i + 1) ω ∂μ)
        = ∫ ω in s, (∑' k, w k * M k (i + 1) ω) ∂μ := by
    have hsum :
        Summable fun k => ∫ ω, ‖w k * M k (i + 1) ω‖ ∂(μ.restrict s) := by
      simpa using hsummable_integral_norm (i + 1) s hs_meas
    simpa using
      (integral_tsum_of_summable_integral_norm
        (μ := μ.restrict s)
        (F := fun k ω => w k * M k (i + 1) ω)
        hnext_int hsum)
  have hcur_swap :
      (∑' k, ∫ ω in s, w k * M k i ω ∂μ)
        = ∫ ω in s, (∑' k, w k * M k i ω) ∂μ := by
    have hsum :
        Summable fun k => ∫ ω, ‖w k * M k i ω‖ ∂(μ.restrict s) := by
      simpa using hsummable_integral_norm i s hs_meas
    simpa using
      (integral_tsum_of_summable_integral_norm
        (μ := μ.restrict s)
        (F := fun k ω => w k * M k i ω)
        hcur_int hsum)
  have hterm :
      ∀ k,
        ∫ ω in s, w k * M k (i + 1) ω ∂μ
          ≤ ∫ ω in s, w k * M k i ω ∂μ := by
    intro k
    have hraw :
        ∫ ω in s, M k (i + 1) ω ∂μ
          ≤ ∫ ω in s, M k i ω ∂μ := by
      have hcond := (hM k).condExp_ae_le (Nat.le_succ i)
      calc
        ∫ ω in s, M k (i + 1) ω ∂μ
            = ∫ ω in s, (condExp (ℱ i) μ (M k (i + 1))) ω ∂μ := by
                exact (setIntegral_condExp (ℱ.le i) ((hM k).integrable (i + 1)) hs).symm
        _ ≤ ∫ ω in s, M k i ω ∂μ := by
                exact setIntegral_mono_ae integrable_condExp.integrableOn
                  ((hM k).integrable i).integrableOn hcond
    have hweighted := mul_le_mul_of_nonneg_left hraw (hw_nonneg k)
    calc
      ∫ ω in s, w k * M k (i + 1) ω ∂μ
          = w k * ∫ ω in s, M k (i + 1) ω ∂μ := by
              exact integral_const_mul (μ := μ.restrict s) (w k) (fun ω => M k (i + 1) ω)
      _ ≤ w k * ∫ ω in s, M k i ω ∂μ := hweighted
      _ = ∫ ω in s, w k * M k i ω ∂μ := by
              exact (integral_const_mul (μ := μ.restrict s) (w k) (fun ω => M k i ω)).symm
  have hnext_num_summable :
      Summable fun k => ∫ ω in s, w k * M k (i + 1) ω ∂μ := by
    refine Summable.of_norm_bounded (hsummable_integral_norm (i + 1) s hs_meas) ?_
    intro k
    exact norm_integral_le_integral_norm (μ := μ.restrict s)
      (fun ω => w k * M k (i + 1) ω)
  have hcur_num_summable :
      Summable fun k => ∫ ω in s, w k * M k i ω ∂μ := by
    refine Summable.of_norm_bounded (hsummable_integral_norm i s hs_meas) ?_
    intro k
    exact norm_integral_le_integral_norm (μ := μ.restrict s)
      (fun ω => w k * M k i ω)
  have htsum :
      (∑' k, ∫ ω in s, w k * M k (i + 1) ω ∂μ)
        ≤ (∑' k, ∫ ω in s, w k * M k i ω ∂μ) :=
    hnext_num_summable.tsum_le_tsum hterm hcur_num_summable
  calc
    ∫ ω in s, (∑' k, w k * M k (i + 1) ω) ∂μ
        = (∑' k, ∫ ω in s, w k * M k (i + 1) ω ∂μ) := hnext_swap.symm
    _ ≤ (∑' k, ∫ ω in s, w k * M k i ω ∂μ) := htsum
    _ = ∫ ω in s, (∑' k, w k * M k i ω) ∂μ := hcur_swap

/-! ## Dyadic-epoch stitched-grid mixture -/

/-- Total capital of a countable epoch-weight sequence. -/
def epochWeightTotal (w : ℕ → ℝ) : ℝ :=
  ∑' j, w j

/--
Countable dyadic-epoch mixture over epoch-indexed finite tilt grids. Each epoch
`j` contributes the finite stitched-grid process from `OptimizedLambdaCS`,
weighted by `w j`.
-/
def dyadicEpochMixtureProcess {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (Lam : ℕ → Finset ℝ) (w : ℕ → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑' j, w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω

/--
The epoch-grid budget paid by epoch `j`. Compared with the finite-grid budget
`log(card / delta)`, this carries the explicit countable-stitching penalty
`log(epochWeightTotal w / w j)`.
-/
def dyadicEpochGridBudget (w : ℕ → ℝ) (Lam : ℕ → Finset ℝ) (j : ℕ) (delta : ℝ) : ℝ :=
  Real.log (((Lam j).card : ℝ) / (delta * w j / epochWeightTotal w))

/-- The explicit extra p-series or general epoch-stitching penalty. -/
def dyadicEpochExtraStitchingPenalty (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.log (epochWeightTotal w / w j)

/-- Generic sub-Gamma closed-form width at an arbitrary confidence budget. -/
def subGammaWidthAtBudget (sigma2 b : ℝ) (n : ℕ) (budget : ℝ) : ℝ :=
  Real.sqrt (2 * sigma2 * budget / (n : ℝ))
    + b * budget / (3 * (n : ℝ))

/--
Width-level penalty induced by adding `extraBudget` to the iterated-log budget.
This is the deterministic "closed-form width plus stitching penalty" wrapper:
adding it to `subGammaLogLogWidth` gives the closed-form width evaluated at the
inflated budget.
-/
def subGammaLogLogWidthStitchingPenalty
    (sigma2 b : ℝ) (n : ℕ) (delta extraBudget : ℝ) : ℝ :=
  subGammaWidthAtBudget sigma2 b n (logLogBudget n delta + extraBudget)
    - subGammaLogLogWidth sigma2 b n delta

/-- The inflated-budget width is literally `subGammaLogLogWidth` plus the penalty above. -/
theorem subGammaLogLogWidth_add_stitchingPenalty
    (sigma2 b : ℝ) (n : ℕ) (delta extraBudget : ℝ) :
    subGammaLogLogWidth sigma2 b n delta
      + subGammaLogLogWidthStitchingPenalty sigma2 b n delta extraBudget
        = subGammaWidthAtBudget sigma2 b n (logLogBudget n delta + extraBudget) := by
  unfold subGammaLogLogWidthStitchingPenalty
  abel

/-- Nonnegativity of the countable epoch mixture. -/
theorem dyadicEpochMixtureProcess_nonneg {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b : ℝ) (Lam : ℕ → Finset ℝ) {w : ℕ → ℝ}
    (hw_nonneg : ∀ j, 0 ≤ w j) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicEpochMixtureProcess X sigma2 b Lam w n ω := by
  unfold dyadicEpochMixtureProcess
  exact tsum_nonneg fun j =>
    mul_nonneg (hw_nonneg j) (stitchedExponentialProcess_nonneg X sigma2 b (Lam j) n ω)

/--
The countable dyadic-epoch mixture is a supermartingale once each finite epoch
grid is an admissible stitched-grid supermartingale and the countable sum has the
integrability package required by `countableWeightedSupermartingale_tsum`.
-/
theorem dyadicEpochMixture_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b : ℝ} {Lam : ℕ → Finset ℝ} {w : ℕ → ℝ}
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hLam_mem : ∀ j, ∀ lam ∈ Lam j, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (h_integrable_grid :
      ∀ j, ∀ lam ∈ Lam j, ∀ n, Integrable (subGammaExponentialProcess X sigma2 b lam n) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2)
    (hadapted_mix :
      StronglyAdapted ℱ (dyadicEpochMixtureProcess X sigma2 b Lam w))
    (hintegrable_mix :
      ∀ n, Integrable (dyadicEpochMixtureProcess X sigma2 b Lam w n) μ)
    (hsummable_integral_norm :
      ∀ n, ∀ s : Set Ω, MeasurableSet s →
        Summable fun j => ∫ ω in s,
          ‖w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω‖ ∂μ) :
    Supermartingale (dyadicEpochMixtureProcess X sigma2 b Lam w) ℱ μ := by
  unfold dyadicEpochMixtureProcess at hadapted_mix hintegrable_mix ⊢
  refine countableWeightedSupermartingale_tsum hw_nonneg ?_ hadapted_mix hintegrable_mix
    hsummable_integral_norm
  intro j
  exact (subGamma_stitched_boundary_supermartingale
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (Lam := Lam j)
    hb hσ (hLam_mem j) hX_meas hX_int hX_adapted (h_integrable_grid j)
    hbound hcenter hvar).1

/-- Countable-time Ville crossing bound for the dyadic-epoch mixture. -/
theorem dyadicEpochMixture_atTop_crossing_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ} {Lam : ℕ → Finset ℝ} {w : ℕ → ℝ}
    (hδ : 0 < delta)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hcapital_pos : 0 < epochWeightTotal w)
    (hsup : Supermartingale (dyadicEpochMixtureProcess X sigma2 b Lam w) ℱ μ)
    (hM0_le :
      ∫ ω, dyadicEpochMixtureProcess X sigma2 b Lam w 0 ω ∂μ ≤ epochWeightTotal w) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      epochWeightTotal w / delta ≤ dyadicEpochMixtureProcess X sigma2 b Lam w n ω} ≤ delta := by
  have ha : 0 < epochWeightTotal w / delta := div_pos hcapital_pos hδ
  have hnonneg : 0 ≤ dyadicEpochMixtureProcess X sigma2 b Lam w :=
    dyadicEpochMixtureProcess_nonneg X sigma2 b Lam hw_nonneg
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ)
      (M := dyadicEpochMixtureProcess X sigma2 b Lam w)
      hsup hnonneg ha
  have h_atTop :
      μ.real
        (atTopCrossingEvent
          (dyadicEpochMixtureProcess X sigma2 b Lam w) (epochWeightTotal w / delta))
        ≤ delta := by
    have hville' :
        (epochWeightTotal w / delta) *
          μ.real
            (atTopCrossingEvent
              (dyadicEpochMixtureProcess X sigma2 b Lam w) (epochWeightTotal w / delta))
          ≤ epochWeightTotal w := hville.trans hM0_le
    calc
      μ.real
          (atTopCrossingEvent
            (dyadicEpochMixtureProcess X sigma2 b Lam w) (epochWeightTotal w / delta))
          = (delta / epochWeightTotal w) *
            ((epochWeightTotal w / delta) *
              μ.real
                (atTopCrossingEvent
                  (dyadicEpochMixtureProcess X sigma2 b Lam w)
                  (epochWeightTotal w / delta))) := by
              field_simp [hδ.ne', hcapital_pos.ne']
      _ ≤ (delta / epochWeightTotal w) * epochWeightTotal w :=
            mul_le_mul_of_nonneg_left hville' (div_nonneg hδ.le hcapital_pos.le)
      _ = delta := by
            field_simp [hcapital_pos.ne']
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
        epochWeightTotal w / delta ≤ dyadicEpochMixtureProcess X sigma2 b Lam w n ω}
        ⊆ atTopCrossingEvent
          (dyadicEpochMixtureProcess X sigma2 b Lam w) (epochWeightTotal w / delta) := by
    intro ω hω
    rcases hω with ⟨n, _hn_pos, hn_cross⟩
    exact ⟨n, hn_cross⟩
  exact (measureReal_mono hsubset).trans h_atTop

/--
If one epoch-grid boundary is crossed at time `n`, then the countable epoch
mixture crosses its Ville threshold. The threshold uses
`delta * w j / epochWeightTotal w` inside the finite-grid crossing, so the
extra term over the finite grid is `log(epochWeightTotal w / w j)`.
-/
theorem runningMean_dyadicEpochBoundary_subset_mixture_crossing
    {Ω : Type*} {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ}
    {Lam : ℕ → Finset ℝ} {w : ℕ → ℝ} {n j : ℕ} {ω : Ω}
    (hδ : 0 < delta) (hcapital_pos : 0 < epochWeightTotal w)
    (hw_pos : ∀ j, 0 < w j)
    (hsummable_terms :
      Summable fun k => w k * stitchedExponentialProcess X sigma2 b (Lam k) n ω)
    (hn_pos : 0 < n)
    (lam : ℝ) (hlam_mem : lam ∈ Lam j) (hlam_pos : 0 < lam)
    (hboundary :
      subGammaCgf sigma2 b lam / lam
        + dyadicEpochGridBudget w Lam j delta / ((n : ℝ) * lam)
          ≤ runningMean X n ω) :
    epochWeightTotal w / delta ≤ dyadicEpochMixtureProcess X sigma2 b Lam w n ω := by
  have hδj : 0 < delta * w j / epochWeightTotal w :=
    div_pos (mul_pos hδ (hw_pos j)) hcapital_pos
  have hcross_stitched :
      (1 / (delta * w j / epochWeightTotal w))
        ≤ stitchedExponentialProcess X sigma2 b (Lam j) n ω := by
    exact runningMean_boundary_subset_stitched_crossing
      (X := X) (sigma2 := sigma2) (b := b)
      (delta := delta * w j / epochWeightTotal w) (Lam := Lam j)
      (n := n) (ω := ω) hδj hn_pos lam hlam_mem hlam_pos hboundary
  have hweighted :
      epochWeightTotal w / delta
        ≤ w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω := by
    have hmul := mul_le_mul_of_nonneg_left hcross_stitched (hw_pos j).le
    calc
      epochWeightTotal w / delta
          = w j * (1 / (delta * w j / epochWeightTotal w)) := by
              field_simp [hδ.ne', (hw_pos j).ne', hcapital_pos.ne']
      _ ≤ w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω := hmul
  have hterm_le :
      w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω
        ≤ ∑' k, w k * stitchedExponentialProcess X sigma2 b (Lam k) n ω := by
    exact hsummable_terms.le_tsum j fun k _hk =>
      mul_nonneg (hw_pos k).le (stitchedExponentialProcess_nonneg X sigma2 b (Lam k) n ω)
  exact hweighted.trans hterm_le

/--
One-sided all-time dyadic-epoch confidence sequence. The boundary is the usual
finite-grid sub-Gamma line boundary with the countable epoch budget
`dyadicEpochGridBudget`, equivalently the finite-grid budget plus the explicit
stitching penalty `log(epochWeightTotal w / w j)`.
-/
theorem dyadic_epoch_confidence_sequence_subGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ} {Lam : ℕ → Finset ℝ} {w : ℕ → ℝ}
    (hδ : 0 < delta)
    (hw_pos : ∀ j, 0 < w j)
    (hcapital_pos : 0 < epochWeightTotal w)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hLam_mem : ∀ j, ∀ lam ∈ Lam j, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (h_integrable_grid :
      ∀ j, ∀ lam ∈ Lam j, ∀ n, Integrable (subGammaExponentialProcess X sigma2 b lam n) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2)
    (hadapted_mix :
      StronglyAdapted ℱ (dyadicEpochMixtureProcess X sigma2 b Lam w))
    (hintegrable_mix :
      ∀ n, Integrable (dyadicEpochMixtureProcess X sigma2 b Lam w n) μ)
    (hsummable_integral_norm :
      ∀ n, ∀ s : Set Ω, MeasurableSet s →
        Summable fun j => ∫ ω in s,
          ‖w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω‖ ∂μ)
    (hsummable_terms :
      ∀ n ω, Summable fun j => w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω)
    (hM0_le :
      ∫ ω, dyadicEpochMixtureProcess X sigma2 b Lam w 0 ω ∂μ ≤ epochWeightTotal w) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
        (∃ j : ℕ, ∃ lam ∈ Lam j,
          subGammaCgf sigma2 b lam / lam
            + dyadicEpochGridBudget w Lam j delta / ((n : ℝ) * lam)
              ≤ runningMean X n ω)} ≤ delta := by
  have hw_nonneg : ∀ j, 0 ≤ w j := fun j => (hw_pos j).le
  have hsup : Supermartingale (dyadicEpochMixtureProcess X sigma2 b Lam w) ℱ μ :=
    dyadicEpochMixture_supermartingale hw_nonneg hb hσ hLam_mem hX_meas hX_int hX_adapted
      h_integrable_grid hbound hcenter hvar hadapted_mix hintegrable_mix
      hsummable_integral_norm
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
          (∃ j : ℕ, ∃ lam ∈ Lam j,
            subGammaCgf sigma2 b lam / lam
              + dyadicEpochGridBudget w Lam j delta / ((n : ℝ) * lam)
                ≤ runningMean X n ω)}
        ⊆ {ω | ∃ n : ℕ, 0 < n ∧
          epochWeightTotal w / delta ≤ dyadicEpochMixtureProcess X sigma2 b Lam w n ω} := by
    intro ω hω
    rcases hω with ⟨n, hn_pos, j, lam, hlam_mem, hboundary⟩
    refine ⟨n, hn_pos, ?_⟩
    exact runningMean_dyadicEpochBoundary_subset_mixture_crossing
      (X := X) (sigma2 := sigma2) (b := b) (delta := delta)
      (Lam := Lam) (w := w) (n := n) (j := j) (ω := ω)
      hδ hcapital_pos hw_pos (hsummable_terms n ω) hn_pos lam hlam_mem
      (hLam_mem j lam hlam_mem).1 hboundary
  refine (measureReal_mono hsubset).trans ?_
  exact dyadicEpochMixture_atTop_crossing_bound
    (X := X) (sigma2 := sigma2) (b := b) (Lam := Lam) (w := w)
    hδ hw_nonneg hcapital_pos hsup hM0_le

/--
Two-sided all-time dyadic-epoch confidence sequence. The failure event uses the
same explicit countable-epoch budget, with `delta / 2` on each side.
-/
theorem dyadic_epoch_two_sided_confidence_sequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b delta : ℝ} {Lam : ℕ → Finset ℝ} {w : ℕ → ℝ}
    (hδ : 0 < delta)
    (hw_pos : ∀ j, 0 < w j)
    (hcapital_pos : 0 < epochWeightTotal w)
    (hb : 0 < b) (hσ : 0 ≤ sigma2)
    (hLam_mem : ∀ j, ∀ lam ∈ Lam j, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hX_adapted : IncrementAdapted ℱ X)
    (h_integrable_grid :
      ∀ j, ∀ lam ∈ Lam j, ∀ n, Integrable (subGammaExponentialProcess X sigma2 b lam n) μ)
    (h_integrable_grid_neg :
      ∀ j, ∀ lam ∈ Lam j, ∀ n,
        Integrable (subGammaExponentialProcess (fun k ω => -X k ω) sigma2 b lam n) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2)
    (hadapted_mix :
      StronglyAdapted ℱ (dyadicEpochMixtureProcess X sigma2 b Lam w))
    (hintegrable_mix :
      ∀ n, Integrable (dyadicEpochMixtureProcess X sigma2 b Lam w n) μ)
    (hsummable_integral_norm :
      ∀ n, ∀ s : Set Ω, MeasurableSet s →
        Summable fun j => ∫ ω in s,
          ‖w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω‖ ∂μ)
    (hsummable_terms :
      ∀ n ω, Summable fun j => w j * stitchedExponentialProcess X sigma2 b (Lam j) n ω)
    (hM0_le :
      ∫ ω, dyadicEpochMixtureProcess X sigma2 b Lam w 0 ω ∂μ ≤ epochWeightTotal w)
    (hadapted_mix_neg :
      StronglyAdapted ℱ (dyadicEpochMixtureProcess (fun k ω => -X k ω) sigma2 b Lam w))
    (hintegrable_mix_neg :
      ∀ n, Integrable (dyadicEpochMixtureProcess (fun k ω => -X k ω) sigma2 b Lam w n) μ)
    (hsummable_integral_norm_neg :
      ∀ n, ∀ s : Set Ω, MeasurableSet s →
        Summable fun j => ∫ ω in s,
          ‖w j * stitchedExponentialProcess (fun k ω => -X k ω) sigma2 b (Lam j) n ω‖ ∂μ)
    (hsummable_terms_neg :
      ∀ n ω, Summable fun j =>
        w j * stitchedExponentialProcess (fun k ω => -X k ω) sigma2 b (Lam j) n ω)
    (hM0_le_neg :
      ∫ ω, dyadicEpochMixtureProcess (fun k ω => -X k ω) sigma2 b Lam w 0 ω ∂μ
        ≤ epochWeightTotal w) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
        (∃ j : ℕ, ∃ lam ∈ Lam j,
          subGammaCgf sigma2 b lam / lam
            + dyadicEpochGridBudget w Lam j (delta / 2) / ((n : ℝ) * lam)
              ≤ |runningMean X n ω|)} ≤ delta := by
  have hδ2 : (0 : ℝ) < delta / 2 := by linarith
  have hupper := dyadic_epoch_confidence_sequence_subGamma
    (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b)
    (delta := delta / 2) (Lam := Lam) (w := w)
    hδ2 hw_pos hcapital_pos hb hσ hLam_mem hX_meas hX_int hX_adapted
    h_integrable_grid hbound hcenter hvar hadapted_mix hintegrable_mix
    hsummable_integral_norm hsummable_terms hM0_le
  have hbound_neg : ∀ k, ∀ᵐ ω ∂μ, |(fun k ω => -X k ω) k ω| ≤ b := by
    intro k
    filter_upwards [hbound k] with ω hω
    simpa [abs_neg] using hω
  have hcenter_neg : ∀ k, μ[(fun k ω => -X k ω) k | ℱ k] =ᵐ[μ] 0 := by
    intro k
    show μ[fun ω => -X k ω | ℱ k] =ᵐ[μ] 0
    have hne : (fun ω => -X k ω) = -(X k) := rfl
    rw [hne]
    refine (condExp_neg (μ := μ) (m := ℱ k) (X k)).trans ?_
    filter_upwards [hcenter k] with ω hc
    simp only [Pi.neg_apply, Pi.zero_apply] at hc ⊢
    rw [hc]
    simp
  have hvar_neg : ∀ k,
      μ[fun ω => ((fun k ω => -X k ω) k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2 := by
    intro k
    have hsq : (fun ω => ((fun k ω => -X k ω) k ω) ^ 2)
        = (fun ω => (X k ω) ^ 2) := by
      funext ω
      simp
    rw [hsq]
    exact hvar k
  have hlower := dyadic_epoch_confidence_sequence_subGamma
    (μ := μ) (ℱ := ℱ) (X := fun k ω => -X k ω) (sigma2 := sigma2) (b := b)
    (delta := delta / 2) (Lam := Lam) (w := w)
    hδ2 hw_pos hcapital_pos hb hσ hLam_mem
    (fun k => (hX_meas k).neg) (fun k => (hX_int k).neg)
    (incrementAdapted_neg hX_adapted) h_integrable_grid_neg
    hbound_neg hcenter_neg hvar_neg hadapted_mix_neg hintegrable_mix_neg
    hsummable_integral_norm_neg hsummable_terms_neg hM0_le_neg
  set Bn : ℕ → ℕ → ℝ → ℝ := fun n j lam =>
    subGammaCgf sigma2 b lam / lam
      + dyadicEpochGridBudget w Lam j (delta / 2) / ((n : ℝ) * lam)
    with hBn_def
  have hsubset :
      {ω | ∃ n : ℕ, 0 < n ∧
          (∃ j : ℕ, ∃ lam ∈ Lam j, Bn n j lam ≤ |runningMean X n ω|)}
        ⊆ {ω | ∃ n : ℕ, 0 < n ∧
            (∃ j : ℕ, ∃ lam ∈ Lam j, Bn n j lam ≤ runningMean X n ω)}
          ∪ {ω | ∃ n : ℕ, 0 < n ∧
              (∃ j : ℕ, ∃ lam ∈ Lam j,
                Bn n j lam ≤ runningMean (fun k ω => -X k ω) n ω)} := by
    intro ω hω
    rcases hω with ⟨n, hn_pos, j, lam, hlam_mem, hcross⟩
    rcases abs_cases (runningMean X n ω) with ⟨habs, _⟩ | ⟨habs, _⟩
    · left
      refine ⟨n, hn_pos, j, lam, hlam_mem, ?_⟩
      rw [habs] at hcross
      exact hcross
    · right
      refine ⟨n, hn_pos, j, lam, hlam_mem, ?_⟩
      rw [runningMean_neg]
      rw [habs] at hcross
      exact hcross
  calc
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
        (∃ j : ℕ, ∃ lam ∈ Lam j, Bn n j lam ≤ |runningMean X n ω|)}
        ≤ μ.real ({ω | ∃ n : ℕ, 0 < n ∧
            (∃ j : ℕ, ∃ lam ∈ Lam j, Bn n j lam ≤ runningMean X n ω)}
          ∪ {ω | ∃ n : ℕ, 0 < n ∧
              (∃ j : ℕ, ∃ lam ∈ Lam j,
                Bn n j lam ≤ runningMean (fun k ω => -X k ω) n ω)}) :=
          measureReal_mono hsubset
    _ ≤ μ.real {ω | ∃ n : ℕ, 0 < n ∧
            (∃ j : ℕ, ∃ lam ∈ Lam j, Bn n j lam ≤ runningMean X n ω)}
          + μ.real {ω | ∃ n : ℕ, 0 < n ∧
              (∃ j : ℕ, ∃ lam ∈ Lam j,
                Bn n j lam ≤ runningMean (fun k ω => -X k ω) n ω)} :=
          measureReal_union_le _ _
    _ ≤ delta / 2 + delta / 2 := by
          exact add_le_add hupper hlower
    _ = delta := by ring

end

end FormalSLT.AnytimeValid
