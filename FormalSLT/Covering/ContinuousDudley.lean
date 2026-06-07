import FormalSLT.Covering.TotalBoundedDudley
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Brick 3: the continuous Dudley entropy integral as a measure-theoretic limit

This module is *brick 3* of the Dudley chaining lane. Bricks 1 and 2 are:

* `FormalSLT.Covering.DudleyChaining` — discrete two-scale peeling;
* `FormalSLT.Covering.TotalBoundedDudley` — the total-bounded discrete sum,
  whose terminal bounds pay a finite *truncated* interval integral
  `∫ ε in (radiusScale / 2^(m+1))..(radiusScale / 2), entropyAtRadius ε`.

Brick 3 passes that verified finite machinery to the continuous limit under the
dyadic scale sequence `ε_k = 2^{-k} · diam(F)` (here realized by the dyadic
floor `radiusScale / 2^(k+1)`; choosing `radiusScale = 2 · diam(F)` makes the
floor exactly `2^{-k} · diam(F)` and the integration top exactly `diam(F)`).

## What is proved (and what stays a hypothesis)

This module keeps the honest discipline of brick 2: the genuinely hard analytic
inputs are *explicit hypotheses*, never silently discharged.

* `sup_measurable_countable_dense` — the supremum of a sample-continuous process
  over `T` equals the (countable) supremum over a countable dense subset, hence
  is measurable. This is the separability bridge to the integral. It relies on
  ℝ being a Borel space (`MeasurableSpace.borel`, `BorelSpace ℝ`); the countable
  supremum is measurable by `Measurable.iSup`, and the reduction to the dense
  skeleton is `Dense.ciSup'`. Continuity of paths is a hypothesis.

* `dyadic_limit_of_total_bounded_bricks` — the truncated interval integral from
  brick 2 (equivalently, by
  `FiniteSubGaussianChaining.shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral`,
  the discrete dyadic annulus-integral sum) converges to the continuous Dudley
  integral `∫ ε in 0..(radiusScale / 2), entropyAtRadius ε` as the dyadic scale
  sequence refines (`m → ∞`). Interval-integrability on `[0, radiusScale/2]` is
  a hypothesis; the limit then follows from continuity of the integral primitive
  (`continuousWithinAt_primitive`).

* `continuous_dudley_entropy_integral` — the empirical sub-Gaussian complexity is
  bounded by the *continuous* Dudley entropy integral:

    `E[ sup_F X ] ≤ coarseBudget + 4 · √(2 · σ²) · ∫ ε in 0..(radiusScale/2), entropyAtRadius ε`

  where `σ² = P.varianceProxy` and `entropyAtRadius ε` dominates the chosen
  `√(log N(F, ε))` covering-number envelope. Reading this in the empirical
  Rademacher normalization, `σ²` carries the `1/n` factor (for the Rademacher
  process `σ² ≍ B²/n`), so `4 · √(2 · σ²)` is the `C / √n` constant of
  Boucheron–Lugosi–Massart 2013 §13. The supremum / separability / terminal
  modulus content is carried by the `hchoose`
  (`SeparableTerminalSupremumBoundaryChoice`) hypothesis, exactly as in brick 2;
  this theorem does **not** construct an arbitrary measurable supremum on its
  own — that is the role of `sup_measurable_countable_dense` and of separability.

The contribution of brick 3 is the *limit-based* derivation of the continuous
integral from the verified discrete bricks 1+2, rather than a fresh chaining
proof.

## References (verbatim)

* R. M. Dudley, "The sizes of compact subsets of Hilbert space and continuity of
  Gaussian processes," Journal of Functional Analysis 1 (1967).
* M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*, Springer
  (2014).
* S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A
  Nonasymptotic Theory of Independence*, Oxford University Press (2013), §13.
* P. Massart, *Concentration Inequalities and Model Selection*, Springer Lecture
  Notes in Mathematics 1896 (2007).

Sonoda et al. 2025 (arXiv:2503.19605) and Zhang–Lee–Liu 2026 (arXiv:2602.02285)
mechanise related continuous Dudley results with different proof strategies; the
contribution of this brick is the limit-based proof from the verified discrete
bricks 1+2.

## Known mathlib4 gap (noted, not blocking)

The *sharp* McDiarmid route this lane ultimately feeds needs the conditional
product-measure kernel decomposition (a measure-theoretic disintegration of a
product measure into a base measure and a conditional kernel). That lemma is not
yet available in mathlib4 in directly usable form; brick 3 does not depend on it
(it works with the sub-Gaussian variance proxy interface), so this is recorded
as a forward dependency only.

No `sorry`, no `admit`, no custom `axiom`.
-/

namespace FormalSLT.Covering.ContinuousDudley

open MeasureTheory Filter Topology Set
open scoped BigOperators
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.TotalBoundedDudley

noncomputable section

universe u

variable {T : Type u}

/-! ## Separability bridge: measurability of the supremum over a countable dense set -/

/-- **Measurable supremum over a countable dense subset.**

For a process `g : T → α → ℝ` whose sample paths `t ↦ g t a` are continuous and
whose evaluations `a ↦ g t a` are measurable, the full supremum
`a ↦ ⨆ t, g t a` is measurable, because a countable dense subset `D ⊆ T`
already realizes the supremum (`Dense.ciSup'`) and a countable supremum of
measurable functions is measurable (`Measurable.iSup`, which uses that ℝ is a
Borel space, `MeasurableSpace.borel`).

This is the bridge from a pointwise process to its supremum functional that the
continuous Dudley integral integrates against. Continuity of paths is the
explicit separability/modulus hypothesis. -/
theorem sup_measurable_countable_dense
    {α : Type*} [MeasurableSpace α]
    [PseudoMetricSpace T]
    (g : T → α → ℝ)
    (D : Set T) (hDcount : D.Countable) (hDdense : Dense D)
    (hmeas : ∀ t : T, Measurable (g t))
    (hcont : ∀ a : α, Continuous fun t : T => g t a) :
    Measurable fun a : α => ⨆ t : T, g t a := by
  classical
  haveI : Countable D := (Set.countable_coe_iff).mpr hDcount
  have hrw : (fun a : α => ⨆ t : T, g t a)
      = fun a : α => ⨆ d : D, g (d : T) a := by
    funext a
    exact (hDdense.ciSup' (hcont a)).symm
  rw [hrw]
  exact Measurable.iSup fun d => hmeas (d : T)

/-! ## The dyadic refinement limit of the verified discrete bricks -/

/-- **Dyadic limit of the total-bounded discrete bricks.**

The finite truncated interval integral paid by the brick-2 terminal bounds,
`∫ ε in (radiusScale / 2^(m+1))..(radiusScale / 2), entropyAtRadius ε`,
converges to the continuous Dudley entropy integral
`∫ ε in 0..(radiusScale / 2), entropyAtRadius ε` as the dyadic scale sequence
refines (`m → ∞`), provided the entropy profile is interval-integrable on
`[0, radiusScale / 2]`.

By `FiniteSubGaussianChaining.shiftedDyadicIntervalIntegralSum_eq_truncatedIntervalIntegral`
the truncated integral equals the discrete dyadic annulus-integral sum, so this
is exactly "the discrete sum converges to the continuous integral." -/
theorem dyadic_limit_of_total_bounded_bricks
    (radiusScale : ℝ) (hradiusScale : 0 < radiusScale)
    (entropyAtRadius : ℝ → ℝ)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2)) :
    Tendsto
      (fun m : ℕ =>
        ∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
      atTop
      (𝓝 (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε)) := by
  have hb_pos : (0 : ℝ) < radiusScale / 2 := half_pos hradiusScale
  -- pointwise bounds on the dyadic floor `radiusScale / 2^(m+1)`
  have ha_nonneg : ∀ m : ℕ, (0 : ℝ) ≤ radiusScale / (2 : ℝ) ^ (m + 1) := fun m =>
    (div_pos hradiusScale (pow_pos (by norm_num) _)).le
  have ha_le : ∀ m : ℕ, radiusScale / (2 : ℝ) ^ (m + 1) ≤ radiusScale / 2 := by
    intro m
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.le_add_left 1 m)
      simpa using h
    gcongr
  -- the dyadic floor tends to 0
  have ha_tendsto :
      Tendsto (fun m : ℕ => radiusScale / (2 : ℝ) ^ (m + 1)) atTop (𝓝 0) := by
    have h12 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hshift : Tendsto (fun m : ℕ => ((1 : ℝ) / 2) ^ (m + 1)) atTop (𝓝 0) :=
      h12.comp (tendsto_add_atTop_nat 1)
    have hmul :
        Tendsto (fun m : ℕ => radiusScale * ((1 : ℝ) / 2) ^ (m + 1)) atTop
          (𝓝 (radiusScale * 0)) := hshift.const_mul radiusScale
    rw [mul_zero] at hmul
    refine hmul.congr ?_
    intro m
    rw [div_pow, one_pow, mul_one_div]
  -- ... refined to land inside `Icc 0 (radiusScale/2)`
  have ha_within :
      Tendsto (fun m : ℕ => radiusScale / (2 : ℝ) ^ (m + 1)) atTop
        (𝓝[Set.Icc (0 : ℝ) (radiusScale / 2)] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ha_tendsto
    · exact Eventually.of_forall (fun m => ⟨ha_nonneg m, ha_le m⟩)
  -- the integral primitive `x ↦ ∫ 0..x` is continuous within `Icc 0 (radiusScale/2)` at 0
  have hcwa :
      ContinuousWithinAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, entropyAtRadius t)
        (Set.Icc 0 (radiusScale / 2)) 0 := by
    refine intervalIntegral.continuousWithinAt_primitive ?_ ?_
    · simp
    · have hmin : min (0 : ℝ) 0 = 0 := min_self 0
      have hmax : max (0 : ℝ) (radiusScale / 2) = radiusScale / 2 := max_eq_right hb_pos.le
      rw [hmin, hmax]; exact hint0
  -- hence `∫ 0..(floor m)` tends to `∫ 0..0 = 0`
  have hsmall :
      Tendsto (fun m : ℕ => ∫ t in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius t)
        atTop (𝓝 0) := by
    have hcomp := (hcwa.tendsto).comp ha_within
    simpa [Function.comp, intervalIntegral.integral_same] using hcomp
  -- decompose each truncated integral via adjacent-interval additivity
  have hdecomp : ∀ m : ℕ,
      (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
        = (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε)
          - (∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε) := by
    intro m
    have hsub1 :
        Set.uIcc (0 : ℝ) (radiusScale / (2 : ℝ) ^ (m + 1))
          ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg m, ha_le m⟩)
    have hsub2 :
        Set.uIcc (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2)
          ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
      Set.uIcc_subset_uIcc
        (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg m, ha_le m⟩)
        Set.right_mem_uIcc
    have hI1 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / (2 : ℝ) ^ (m + 1)) :=
      hint0.mono_set hsub1
    have hI2 :
        IntervalIntegrable entropyAtRadius volume (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
      hint0.mono_set hsub2
    have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    linarith [hadd]
  -- assemble: `∫ 0..b - ∫ 0..(floor m) → ∫ 0..b - 0`
  have hmain :
      Tendsto
        (fun m : ℕ => (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε)
            - (∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε))
        atTop (𝓝 ((∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) - 0)) :=
    tendsto_const_nhds.sub hsmall
  rw [sub_zero] at hmain
  exact Filter.Tendsto.congr (fun m => (hdecomp m).symm) hmain

/-! ## The continuous Dudley entropy integral bound -/

/-- **Continuous Dudley entropy integral bound.**

The expected supremum of the finite sub-Gaussian process is bounded by the
continuous Dudley entropy integral:

  `E[supFunctional] ≤ coarseBudget + 4 · √(2 · varianceProxy) · ∫₀^{radiusScale/2} entropyAtRadius`.

The bound is obtained from the verified discrete total-bounded bricks via the
global-budget adapter
`TotalBoundedDudley.finite_separableTerminal_dudley_totalBounded_globalBudget`:
each finite truncated integral is dominated by the full continuous integral
(nonnegative entropy profile), and the resulting uniform budget removes the
boundary error. The dyadic refinement
`dyadic_limit_of_total_bounded_bricks` certifies that the continuous integral is
the limit of those finite truncated integrals, so the bound is the tight
limiting object rather than a loose over-estimate.

In the empirical Rademacher normalization `varianceProxy ≍ B²/n`, so
`4 · √(2 · varianceProxy)` is the `C / √n` constant of Boucheron–Lugosi–Massart
2013 §13, and `entropyAtRadius ε` plays the role of `√(log N(F, ε))`. -/
theorem continuous_dudley_entropy_integral
    {Ω : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [Nonempty T]
    (P : FiniteSubGaussianProcess Ω T)
    (hT : TotallyBounded (Set.univ : Set T))
    (coarseBudget radiusScale : ℝ)
    (entropyAtRadius : ℝ → ℝ)
    (supFunctional : Ω → ℝ)
    (hradiusScale : 0 < radiusScale)
    (hdistP : P.dist = fun s t => dist s t)
    (hvariance : 0 < P.varianceProxy)
    (hentropy_antitone : Antitone entropyAtRadius)
    (hentropy_nonneg : ∀ ε : ℝ, 0 ≤ entropyAtRadius ε)
    (hint0 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / 2))
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoice
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius := entropyAtRadius)
          (supFunctional := supFunctional) eta m) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε) := by
  -- discharge via the verified brick-2 global-budget adapter; the finite
  -- truncated integrals are each dominated by the full continuous integral
  refine finite_separableTerminal_dudley_totalBounded_globalBudget
    (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
    (radiusScale := radiusScale) (entropyAtRadius := entropyAtRadius)
    (supFunctional := supFunctional)
    (globalBudget := coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
      (∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε))
    hradiusScale hdistP hvariance hentropy_antitone hchoose ?_
  intro m
  dsimp only
  have hb_pos : (0 : ℝ) < radiusScale / 2 := half_pos hradiusScale
  have ha_nonneg : (0 : ℝ) ≤ radiusScale / (2 : ℝ) ^ (m + 1) :=
    (div_pos hradiusScale (pow_pos (by norm_num) _)).le
  have ha_le : radiusScale / (2 : ℝ) ^ (m + 1) ≤ radiusScale / 2 := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      have h := pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.le_add_left 1 m)
      simpa using h
    gcongr
  -- the finite truncated integral is dominated by the full continuous integral
  have hsub1 :
      Set.uIcc (0 : ℝ) (radiusScale / (2 : ℝ) ^ (m + 1))
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
  have hsub2 :
      Set.uIcc (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2)
        ⊆ Set.uIcc (0 : ℝ) (radiusScale / 2) :=
    Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨ha_nonneg, ha_le⟩)
      Set.right_mem_uIcc
  have hI1 : IntervalIntegrable entropyAtRadius volume 0 (radiusScale / (2 : ℝ) ^ (m + 1)) :=
    hint0.mono_set hsub1
  have hI2 :
      IntervalIntegrable entropyAtRadius volume (radiusScale / (2 : ℝ) ^ (m + 1)) (radiusScale / 2) :=
    hint0.mono_set hsub2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hnn : 0 ≤ ∫ ε in (0 : ℝ)..(radiusScale / (2 : ℝ) ^ (m + 1)), entropyAtRadius ε :=
    intervalIntegral.integral_nonneg ha_nonneg (fun u _ => hentropy_nonneg u)
  have hdom :
      (∫ ε in (radiusScale / (2 : ℝ) ^ (m + 1))..(radiusScale / 2), entropyAtRadius ε)
        ≤ ∫ ε in (0 : ℝ)..(radiusScale / 2), entropyAtRadius ε := by
    linarith [hadd, hnn]
  have hsqrt_nonneg : 0 ≤ 4 * Real.sqrt (2 * P.varianceProxy) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdom hsqrt_nonneg
  linarith [hmul]

end

end FormalSLT.Covering.ContinuousDudley
