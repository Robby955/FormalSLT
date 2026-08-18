/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.AllocationLogLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi

/-!
# Universal lower-bound interfaces for anytime boundaries

This file separates two lower-bound statements that are often conflated.

* The first section is an exact deterministic/probabilistic reduction: an upper-LIL
  crossing theorem implies that every genuinely anytime-valid deterministic boundary
  has asymptotic constant at least one.  The reduction is proved here, but its
  `UpperLILCrossing` hypothesis is not discharged.
* The second section uses mathlib's central limit theorem and Portmanteau theorem to
  prove an unconditional, distributional `sqrt n` floor for one-sided boundaries of
  the fair Rademacher walk.

The CLT floor is weaker than the LIL floor because it uses one-time marginals.  A full
formal LIL requires a new theorem controlling dependent crossings across infinitely
many times.  The countable-allocation theorem in `AllocationLogLog` is likewise only a
method-specific obstruction; neither result is presented as a substitute for the LIL.

Mathematical sources:

* Khinchin's law of the iterated logarithm for the Rademacher walk;
* the one-dimensional central limit theorem and Portmanteau theorem;
* Darling--Robbins boundary-crossing arguments;
* Balsubramani's finite-time LIL anti-concentration theorem.
-/

namespace FormalSLT.AnytimeValid.UniversalBoundaryLowerBound

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real Topology

noncomputable section

/-! ## Abstract reduction from upper-LIL crossings to boundary lower bounds -/

/-- The event that a process crosses a deterministic one-sided boundary at some time. -/
def oneSidedCrossingEvent {Ω : Type*} (S : ℕ → Ω → ℝ) (boundary : ℕ → ℝ) : Set Ω :=
  {ω | ∃ n, boundary n < S n ω}

/-- A pathwise upper-LIL crossing property at scale `scale`: every constant strictly
below one is exceeded infinitely often, almost surely. -/
def UpperLILCrossing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℕ → Ω → ℝ) (scale : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, c < 1 → ∀ᵐ ω ∂μ, ∃ᶠ n : ℕ in atTop, c * scale n < S n ω

/-- A valid anytime boundary cannot eventually lie below any fixed sub-LIL
multiple of the scale.  This is the exact probability-theoretic reduction; it does
not assume measurability of the crossing event. -/
theorem not_eventually_boundary_lt_mul_of_upperLILCrossing
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : ℕ → Ω → ℝ} {scale boundary : ℕ → ℝ} {delta : ℝ≥0∞}
    (hLIL : UpperLILCrossing μ S scale)
    (hvalid : μ (oneSidedCrossingEvent S boundary) ≤ delta)
    (hdelta : delta < 1) {c : ℝ} (hc : c < 1) :
    ¬ ∀ᶠ n : ℕ in atTop, boundary n < c * scale n := by
  intro hboundary
  have haeCross : ∀ᵐ ω ∂μ, ω ∈ oneSidedCrossingEvent S boundary :=
    (hLIL c hc).mono (by
      intro ω hfrequent
      obtain ⟨n, hnS, hnb⟩ := (hfrequent.and_eventually hboundary).exists
      exact ⟨n, hnb.trans hnS⟩)
  have hcrossing_eq_one : μ (oneSidedCrossingEvent S boundary) = 1 := by
    calc
      μ (oneSidedCrossingEvent S boundary) = μ Set.univ := by
        apply measure_congr
        filter_upwards [haeCross] with ω hω
        change (∃ n, boundary n < S n ω) = True
        exact propext ⟨fun _ ↦ trivial, fun _ ↦ hω⟩
      _ = 1 := measure_univ
  have hone_le : (1 : ℝ≥0∞) ≤ delta := by
    rw [← hcrossing_eq_one]
    exact hvalid
  exact (not_le_of_gt hdelta) hone_le

/-- Limsup form of the upper-LIL reduction.  The mild boundedness premise is the
standard side condition needed by the real-valued `Filter.limsup` API; the preceding
eventual-form theorem has no such premise. -/
theorem oneSidedAnytimeBoundary_limsup_ge_one_of_upperLILCrossing
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : ℕ → Ω → ℝ} {scale boundary : ℕ → ℝ} {delta : ℝ≥0∞}
    (hLIL : UpperLILCrossing μ S scale)
    (hvalid : μ (oneSidedCrossingEvent S boundary) ≤ delta)
    (hdelta : delta < 1)
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < scale n)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ boundary n / scale n)) :
    1 ≤ limsup (fun n ↦ boundary n / scale n) atTop := by
  by_contra hnot
  have hlimsup : limsup (fun n ↦ boundary n / scale n) atTop < 1 :=
    lt_of_not_ge hnot
  obtain ⟨c, hlimsup_c, hc_one⟩ := exists_between hlimsup
  have hratio : ∀ᶠ n : ℕ in atTop, boundary n / scale n < c :=
    eventually_lt_of_limsup_lt hlimsup_c hbounded
  have hboundary : ∀ᶠ n : ℕ in atTop, boundary n < c * scale n := by
    filter_upwards [hratio, hscale] with n hn hscale_n
    exact (div_lt_iff₀ hscale_n).mp hn
  exact
    (not_eventually_boundary_lt_mul_of_upperLILCrossing
      hLIL hvalid hdelta hc_one) hboundary

/-! ## A generic CLT/Portmanteau anti-concentration bridge -/

/-- Convergence in distribution forces every open upper tail whose limiting mass is
strictly above `delta` to have mass above `delta` eventually. -/
theorem eventually_map_Ioi_mass_gt_of_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hconv : TendstoInDistribution X atTop Y (fun _ ↦ μ) μ')
    {c : ℝ} {delta : ℝ≥0∞}
    (hdelta : delta < (μ'.map Y) (Set.Ioi c)) :
    ∀ᶠ n : ℕ in atTop, delta < (μ.map (X n)) (Set.Ioi c) := by
  have hportmanteau :
      (μ'.map Y) (Set.Ioi c) ≤
        liminf (fun n ↦ (μ.map (X n)) (Set.Ioi c)) atTop :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv.tendsto isOpen_Ioi
  exact eventually_lt_of_lt_liminf (hdelta.trans_le hportmanteau)

/-! ## The fair Rademacher product model -/

/-- The midpoint of the unit interval. -/
def fairHalf : unitInterval :=
  ⟨(1 : ℝ) / 2, by norm_num⟩

/-- The symmetric sign law on `{-1, 1}`. -/
def fairSignLaw : Measure ℝ :=
  bernoulliMeasure (-1 : ℝ) 1 fairHalf

/-- Infinite independent fair-sign paths. -/
def fairSignPathLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ ↦ fairSignLaw)

/-- Coordinate increments on the fair-sign product space. -/
def fairSignIncrement (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ω n

/-- Partial sum of the first `n` fair signs. -/
def fairSignSum (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, fairSignIncrement k ω

/-- CLT normalization of the first `n` fair signs. -/
def fairSignNormalizedSum (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * fairSignSum n ω

instance : IsProbabilityMeasure fairSignLaw := by
  unfold fairSignLaw
  infer_instance

instance : IsProbabilityMeasure fairSignPathLaw := by
  unfold fairSignPathLaw
  infer_instance

theorem fairSignIncrement_measurable (n : ℕ) :
    Measurable (fairSignIncrement n) := by
  unfold fairSignIncrement
  fun_prop

theorem fairSignIncrement_hasLaw (n : ℕ) :
    HasLaw (fairSignIncrement n) fairSignLaw fairSignPathLaw where
  aemeasurable := (fairSignIncrement_measurable n).aemeasurable
  map_eq := by
    unfold fairSignIncrement fairSignPathLaw
    exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ fairSignLaw) n

theorem fairSignIncrement_iIndep :
    iIndepFun fairSignIncrement fairSignPathLaw := by
  unfold fairSignIncrement fairSignPathLaw
  exact iIndepFun_infinitePi (X := fun _ : ℕ ↦ id) (fun _ ↦ measurable_id)

theorem fairSignIncrement_identDistrib (n : ℕ) :
    IdentDistrib (fairSignIncrement n) (fairSignIncrement 0)
      fairSignPathLaw fairSignPathLaw :=
  (fairSignIncrement_hasLaw n).identDistrib (fairSignIncrement_hasLaw 0)

theorem fairSignIncrement_mean_zero :
    fairSignPathLaw[fairSignIncrement 0] = 0 := by
  rw [(fairSignIncrement_hasLaw 0).integral_eq]
  unfold fairSignLaw
  rw [integral_bernoulliMeasure]
  norm_num [fairHalf]

theorem fairSignIncrement_secondMoment_one :
    fairSignPathLaw[(fairSignIncrement 0) ^ 2] = 1 := by
  rw [show (fairSignIncrement 0) ^ 2 =
      (fun x : ℝ ↦ x ^ 2) ∘ fairSignIncrement 0 by rfl]
  rw [(fairSignIncrement_hasLaw 0).integral_comp (by fun_prop)]
  unfold fairSignLaw
  rw [integral_bernoulliMeasure]
  norm_num [fairHalf]

/-- The normalized fair Rademacher sums converge to the standard Gaussian. -/
theorem fairSign_tendstoInDistribution_gaussian :
    TendstoInDistribution fairSignNormalizedSum atTop id
      (fun _ ↦ fairSignPathLaw) (gaussianReal 0 1) := by
  change TendstoInDistribution
    (fun (n : ℕ) (ω : ℕ → ℝ) ↦ (Real.sqrt (n : ℝ))⁻¹ *
      ∑ k ∈ Finset.range n, fairSignIncrement k ω)
    atTop id (fun _ ↦ fairSignPathLaw) (gaussianReal 0 1)
  exact
    (tendstoInDistribution_inv_sqrt_mul_sum
      (P := fairSignPathLaw) (P' := gaussianReal 0 1)
      (X := fairSignIncrement) (Y := id)
      (HasLaw.id : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1))
      fairSignIncrement_mean_zero fairSignIncrement_secondMoment_one
      fairSignIncrement_iIndep fairSignIncrement_identDistrib)

/-- Every standard-Gaussian upper tail has strictly positive mass. -/
theorem gaussianReal_zero_one_Ioi_pos (c : ℝ) :
    0 < gaussianReal 0 1 (Set.Ioi c) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hvolume_zero : volume (Set.Ioi c) = 0 :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hzero
  rw [Real.volume_Ioi] at hvolume_zero
  exact ENNReal.top_ne_zero hvolume_zero

/-- Unconditional CLT anti-concentration for the fair Rademacher walk: any open
normalized tail with standard-Gaussian mass above `delta` has mass above `delta`
for all sufficiently large times. -/
theorem fairSign_eventually_normalizedTail_mass_gt
    {c : ℝ} {delta : ℝ≥0∞}
    (hdelta : delta < gaussianReal 0 1 (Set.Ioi c)) :
    ∀ᶠ n : ℕ in atTop,
      delta < fairSignPathLaw {ω | c < fairSignNormalizedSum n ω} := by
  have h := eventually_map_Ioi_mass_gt_of_tendstoInDistribution
    fairSign_tendstoInDistribution_gaussian (c := c) (delta := delta) (by
      simpa using hdelta)
  filter_upwards [h] with n hn
  rw [Measure.map_apply_of_aemeasurable
    (fairSign_tendstoInDistribution_gaussian.forall_aemeasurable n)
    measurableSet_Ioi] at hn
  exact hn

/-- **Universal `sqrt n` floor for fair-sign anytime boundaries.** If the chance
of ever crossing a deterministic one-sided boundary is at most `delta`, then for
every `c` whose standard-Gaussian upper tail is larger than `delta`, the boundary
is eventually at least `c * sqrt n`.

This is a genuine lower bound for all deterministic anytime boundaries, but it is
only a CLT-scale result, not an LIL-scale result. -/
theorem fairSign_anytimeBoundary_eventually_ge_sqrt
    (boundary : ℕ → ℝ) {c : ℝ} {delta : ℝ≥0∞}
    (hvalid : fairSignPathLaw (oneSidedCrossingEvent fairSignSum boundary) ≤ delta)
    (hdelta : delta < gaussianReal 0 1 (Set.Ioi c)) :
    ∀ᶠ n : ℕ in atTop, c * Real.sqrt n ≤ boundary n := by
  have htail := fairSign_eventually_normalizedTail_mass_gt hdelta
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hnTail hnPos
  by_contra hboundary
  have hboundary_lt : boundary n < c * Real.sqrt n := lt_of_not_ge hboundary
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnPos)
  have hnormalized_subset :
      {ω | c < fairSignNormalizedSum n ω} ⊆
        {ω | boundary n < fairSignSum n ω} := by
    intro ω hω
    have hdiv : c < fairSignSum n ω / Real.sqrt n := by
      simpa [fairSignNormalizedSum, div_eq_mul_inv, mul_comm] using hω
    have hsum : c * Real.sqrt n < fairSignSum n ω :=
      (lt_div_iff₀ hsqrt).mp hdiv
    exact hboundary_lt.trans hsum
  have htime_subset :
      {ω | boundary n < fairSignSum n ω} ⊆
        oneSidedCrossingEvent fairSignSum boundary := by
    intro ω hω
    exact ⟨n, hω⟩
  have hle :
      fairSignPathLaw {ω | c < fairSignNormalizedSum n ω} ≤ delta :=
    (measure_mono (hnormalized_subset.trans htime_subset)).trans hvalid
  exact (not_lt_of_ge hle) hnTail

/-! ## Exact target for the missing LIL theorem -/

/-- Classical LIL normalization.  It is positive from time `3` onward. -/
def rademacherLILScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * Real.log (Real.log n))

theorem rademacherLILScale_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 < rademacherLILScale n := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnreal : Real.exp 1 < (n : ℝ) := by
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hlog : 1 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt (by positivity)).2 hnreal
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog
  unfold rademacherLILScale
  apply Real.sqrt_pos.2
  exact mul_pos (mul_pos (by norm_num) hnpos) hloglog

/-- The precise missing probabilistic input for the sharp anytime-boundary floor.
No theorem in this file claims this proposition has been proved. -/
def FairSignUpperLIL : Prop :=
  UpperLILCrossing fairSignPathLaw fairSignSum rademacherLILScale

/-- Once `FairSignUpperLIL` is supplied, the sharp universal boundary conclusion is
an immediate checked corollary of the abstract reduction. -/
theorem fairSign_anytimeBoundary_limsup_ge_one_of_upperLIL
    (hLIL : FairSignUpperLIL) (boundary : ℕ → ℝ) {delta : ℝ≥0∞}
    (hvalid : fairSignPathLaw (oneSidedCrossingEvent fairSignSum boundary) ≤ delta)
    (hdelta : delta < 1)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ boundary n / rademacherLILScale n)) :
    1 ≤ limsup (fun n ↦ boundary n / rademacherLILScale n) atTop :=
  oneSidedAnytimeBoundary_limsup_ge_one_of_upperLILCrossing
    hLIL hvalid hdelta rademacherLILScale_eventually_pos hbounded

end

end FormalSLT.AnytimeValid.UniversalBoundaryLowerBound
