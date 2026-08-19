/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.AllocationLogLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.BorelCantelli
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
* The third section groups coordinates into rapidly growing disjoint blocks and uses
  the second Borel--Cantelli lemma.  It proves unconditionally that the walk exceeds
  every fixed multiple of `sqrt n` infinitely often, and therefore that every valid
  deterministic anytime boundary is unbounded after `sqrt n` normalization.

The block theorem remains weaker than the LIL floor: it proves divergence after
`sqrt n` normalization but neither the `sqrt (2 n log log n)` rate nor its sharp
constant.  A full formal LIL needs finer multiscale control than the separated-block
argument supplied here.  The countable-allocation theorem in `AllocationLogLog` is
likewise only a method-specific obstruction; neither result is presented as a
substitute for the LIL.

Mathematical sources:

* Khinchin's law of the iterated logarithm for the Rademacher walk;
* the one-dimensional central limit theorem and Portmanteau theorem;
* the second Borel--Cantelli lemma for independent events;
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

/-! ## Grouping mutually independent coordinates into disjoint blocks -/

/-- Events measurable with respect to pairwise-disjoint blocks of mutually independent
coordinate sigma-algebras are mutually independent.  This is stronger than pairwise
independence and is the hypothesis required by the second Borel--Cantelli lemma. -/
theorem iIndepSet_of_disjoint_coordinate_blocks
    {I K Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω}
    [IsProbabilityMeasure mu]
    {m : I → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω))
    (hindep : iIndep m mu)
    (blocks : K → Set I)
    (hblocks : ∀ ⦃k l : K⦄, k ≠ l → Disjoint (blocks k) (blocks l))
    (events : K → Set Ω)
    (hevents : ∀ k, MeasurableSet[⨆ i ∈ blocks k, m i] (events k)) :
    iIndepSet events mu := by
  classical
  have hblock_le (k : K) : (⨆ i ∈ blocks k, m i) ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup_le fun i ↦ iSup_le fun _ ↦ hm i
  have hevents_global (k : K) : MeasurableSet (events k) :=
    hblock_le k _ (hevents k)
  rw [iIndepSet_iff_meas_biInter hevents_global]
  intro s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      let previous : Set I := ⋃ k ∈ (s : Set K), blocks k
      have hdisjoint : Disjoint (blocks a) previous := by
        rw [Set.disjoint_left]
        intro i hia hiprevious
        simp only [previous, Set.mem_iUnion] at hiprevious
        obtain ⟨k, hk, hik⟩ := hiprevious
        have hak : a ≠ k := by
          intro hak
          subst k
          exact ha hk
        exact Set.disjoint_left.mp (hblocks hak) hia hik
      have hindep_blocks :
          Indep (⨆ i ∈ blocks a, m i) (⨆ i ∈ previous, m i) mu :=
        indep_iSup_of_disjoint hm hindep hdisjoint
      have hprevious_meas :
          MeasurableSet[⨆ i ∈ previous, m i] (⋂ k ∈ s, events k) := by
        refine s.measurableSet_biInter fun k hk ↦ ?_
        have hspace_le :
            (⨆ i ∈ blocks k, m i) ≤ (⨆ i ∈ previous, m i) := by
          refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
          refine le_iSup_of_le i (le_iSup_of_le ?_ le_rfl)
          simp only [previous, Set.mem_iUnion]
          exact ⟨k, hk, hi⟩
        exact hspace_le _ (hevents k)
      have hindep_events :
          IndepSet (events a) (⋂ k ∈ s, events k) mu :=
        hindep_blocks.indepSet_of_measurableSet (hevents a) hprevious_meas
      rw [Finset.set_biInter_insert, Finset.prod_insert ha,
        hindep_events.measure_inter_eq_mul, ih]

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

/-- Drop the first `a` coordinates of a fair-sign path. -/
def fairSignShift (a : ℕ) (ω : ℕ → ℝ) (k : ℕ) : ℝ :=
  ω (a + k)

/-- Start points for a sequence of disjoint blocks.  The fourth-power block
length makes each new block dominate the deterministic contribution of every
earlier fair-sign increment. -/
def fairSignBlockStart : ℕ → ℕ
  | 0 => 1
  | k + 1 => fairSignBlockStart k + fairSignBlockStart k ^ 4

/-- Length of the `k`-th rapidly growing fair-sign block. -/
def fairSignBlockLength (k : ℕ) : ℕ :=
  fairSignBlockStart k ^ 4

/-- Coordinates used by the `k`-th fair-sign block. -/
def fairSignBlock (k : ℕ) : Set ℕ :=
  Set.Ico (fairSignBlockStart k) (fairSignBlockStart (k + 1))

/-- CLT-normalized sum over the `k`-th disjoint block. -/
def fairSignBlockNormalizedSum (k : ℕ) (ω : ℕ → ℝ) : ℝ :=
  fairSignNormalizedSum (fairSignBlockLength k)
    (fairSignShift (fairSignBlockStart k) ω)

/-- The `k`-th block exceeds a fixed normalized threshold. -/
def fairSignBlockTailEvent (c : ℝ) (k : ℕ) : Set (ℕ → ℝ) :=
  {ω | c < fairSignBlockNormalizedSum k ω}

/-- Sigma-algebra generated by one fair-sign coordinate. -/
@[reducible] def fairSignCoordinateSigma (i : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fairSignIncrement i)
    (inferInstance : MeasurableSpace ℝ)

/-- Sigma-algebra generated by the coordinates in one rapidly growing block. -/
@[reducible] def fairSignBlockSigma (k : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ i ∈ fairSignBlock k, fairSignCoordinateSigma i

instance : IsProbabilityMeasure fairSignLaw := by
  unfold fairSignLaw
  infer_instance

instance : IsProbabilityMeasure fairSignPathLaw := by
  unfold fairSignPathLaw
  infer_instance

theorem fairSignShift_measurable (a : ℕ) :
    Measurable (fairSignShift a) := by
  unfold fairSignShift
  fun_prop

/-- A coordinate shift preserves the iid fair-sign product law. -/
theorem fairSignShift_hasLaw (a : ℕ) :
    HasLaw (fairSignShift a) fairSignPathLaw fairSignPathLaw where
  aemeasurable := (fairSignShift_measurable a).aemeasurable
  map_eq := by
    unfold fairSignShift fairSignPathLaw
    simpa only using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ ↦ fairSignLaw)
        (f := fun k : ℕ ↦ a + k) (add_right_injective a))

@[simp]
theorem fairSignBlockStart_succ (k : ℕ) :
    fairSignBlockStart (k + 1) =
      fairSignBlockStart k + fairSignBlockLength k := by
  simp [fairSignBlockStart, fairSignBlockLength]

theorem fairSignBlockStart_pos (k : ℕ) :
    0 < fairSignBlockStart k := by
  induction k with
  | zero => simp [fairSignBlockStart]
  | succ k ih =>
      rw [fairSignBlockStart_succ]
      positivity

theorem fairSignBlockLength_pos (k : ℕ) :
    0 < fairSignBlockLength k := by
  unfold fairSignBlockLength
  positivity [fairSignBlockStart_pos k]

theorem fairSignBlockStart_strictMono : StrictMono fairSignBlockStart := by
  exact strictMono_nat_of_lt_succ fun k ↦ by
    rw [fairSignBlockStart_succ]
    exact Nat.lt_add_of_pos_right (fairSignBlockLength_pos k)

theorem fairSignBlockStart_tendsto_atTop :
    Tendsto fairSignBlockStart atTop atTop :=
  fairSignBlockStart_strictMono.tendsto_atTop

theorem fairSignBlockStart_le_length (k : ℕ) :
    fairSignBlockStart k ≤ fairSignBlockLength k := by
  unfold fairSignBlockLength
  have h₁ : 1 ≤ fairSignBlockStart k := fairSignBlockStart_pos k
  calc
    fairSignBlockStart k = fairSignBlockStart k ^ 1 := by simp
    _ ≤ fairSignBlockStart k ^ 4 :=
      pow_le_pow_right' h₁ (by norm_num)

theorem fairSignBlockLength_tendsto_atTop :
    Tendsto fairSignBlockLength atTop atTop :=
  tendsto_atTop_mono fairSignBlockStart_le_length
    fairSignBlockStart_tendsto_atTop

theorem fairSignBlock_pairwise_disjoint :
    ∀ ⦃k l : ℕ⦄, k ≠ l → Disjoint (fairSignBlock k) (fairSignBlock l) := by
  intro k l hkl
  have hpair :=
    fairSignBlockStart_strictMono.monotone.pairwise_disjoint_on_Ico_succ hkl
  simpa [fairSignBlock, Nat.succ_eq_add_one] using hpair

theorem fairSignBlockNormalizedSum_hasLaw (k : ℕ) :
    HasLaw (fairSignBlockNormalizedSum k)
      (fairSignPathLaw.map (fairSignNormalizedSum (fairSignBlockLength k)))
      fairSignPathLaw := by
  have hm : Measurable (fairSignNormalizedSum (fairSignBlockLength k)) := by
    unfold fairSignNormalizedSum fairSignSum fairSignIncrement
    fun_prop
  have hnormalized :
      HasLaw (fairSignNormalizedSum (fairSignBlockLength k))
        (fairSignPathLaw.map (fairSignNormalizedSum (fairSignBlockLength k)))
        fairSignPathLaw :=
    ⟨hm.aemeasurable, rfl⟩
  change HasLaw
    (fun ω ↦ fairSignNormalizedSum (fairSignBlockLength k)
      (fairSignShift (fairSignBlockStart k) ω))
    (fairSignPathLaw.map (fairSignNormalizedSum (fairSignBlockLength k)))
    fairSignPathLaw
  exact hnormalized.fun_comp (fairSignShift_hasLaw (fairSignBlockStart k))

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

theorem fairSignBlockNormalizedSum_measurable (k : ℕ) :
    Measurable (fairSignBlockNormalizedSum k) := by
  unfold fairSignBlockNormalizedSum fairSignNormalizedSum fairSignSum
    fairSignShift fairSignIncrement
  fun_prop

theorem fairSignBlockTailEvent_measurable (c : ℝ) (k : ℕ) :
    MeasurableSet (fairSignBlockTailEvent c k) := by
  exact measurableSet_Ioi.preimage (fairSignBlockNormalizedSum_measurable k)

theorem fairSignCoordinateSigma_le (i : ℕ) :
    fairSignCoordinateSigma i ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
  exact (fairSignIncrement_measurable i).comap_le

theorem fairSignBlockNormalizedSum_measurable_block (k : ℕ) :
    Measurable[fairSignBlockSigma k] (fairSignBlockNormalizedSum k) := by
  unfold fairSignBlockNormalizedSum fairSignNormalizedSum fairSignSum fairSignShift
    fairSignIncrement
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j hj
  have hjlt : j < fairSignBlockLength k := Finset.mem_range.mp hj
  have hmem : fairSignBlockStart k + j ∈ fairSignBlock k := by
    rw [fairSignBlock, fairSignBlockStart_succ]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hjlt _⟩
  apply Measurable.of_comap_le
  exact le_iSup_of_le (fairSignBlockStart k + j)
    (le_iSup_of_le hmem le_rfl)

theorem fairSignBlockTailEvent_measurable_block (c : ℝ) (k : ℕ) :
    MeasurableSet[fairSignBlockSigma k] (fairSignBlockTailEvent c k) := by
  exact measurableSet_Ioi.preimage
    (fairSignBlockNormalizedSum_measurable_block k)

/-- Tail events from the rapidly growing disjoint blocks are mutually independent. -/
theorem fairSignBlockTailEvent_iIndepSet (c : ℝ) :
    iIndepSet (fairSignBlockTailEvent c) fairSignPathLaw := by
  apply iIndepSet_of_disjoint_coordinate_blocks
    (m := fairSignCoordinateSigma)
    fairSignCoordinateSigma_le fairSignIncrement_iIndep.iIndep
    fairSignBlock fairSignBlock_pairwise_disjoint
  intro k
  exact fairSignBlockTailEvent_measurable_block c k

theorem fairSignBlockTailEvent_measure_eq (c : ℝ) (k : ℕ) :
    fairSignPathLaw (fairSignBlockTailEvent c k) =
      fairSignPathLaw {ω | c < fairSignNormalizedSum (fairSignBlockLength k) ω} := by
  calc
    fairSignPathLaw (fairSignBlockTailEvent c k) =
        (fairSignPathLaw.map (fairSignNormalizedSum (fairSignBlockLength k)))
          (Set.Ioi c) := by
      change fairSignPathLaw {ω | c < fairSignBlockNormalizedSum k ω} =
        (fairSignPathLaw.map (fairSignNormalizedSum (fairSignBlockLength k)))
          {x | c < x}
      exact (fairSignBlockNormalizedSum_hasLaw k).measure_eq measurableSet_Ioi
    _ = fairSignPathLaw
        {ω | c < fairSignNormalizedSum (fairSignBlockLength k) ω} := by
      rw [Measure.map_apply_of_aemeasurable]
      · rfl
      · exact (show Measurable (fairSignNormalizedSum (fairSignBlockLength k)) by
          unfold fairSignNormalizedSum fairSignSum fairSignIncrement
          fun_prop).aemeasurable
      · exact measurableSet_Ioi

/-- Every fixed normalized block tail has a positive uniform probability for
all sufficiently late rapidly growing blocks. -/
theorem fairSign_eventually_blockTail_mass_gt
    {c : ℝ} {delta : ℝ≥0∞}
    (hdelta : delta < gaussianReal 0 1 (Set.Ioi c)) :
    ∀ᶠ k : ℕ in atTop,
      delta < fairSignPathLaw (fairSignBlockTailEvent c k) := by
  have htail := fairSignBlockLength_tendsto_atTop.eventually
    (fairSign_eventually_normalizedTail_mass_gt hdelta)
  filter_upwards [htail] with k hk
  rwa [fairSignBlockTailEvent_measure_eq]

theorem fairSignBlockTailEvent_tsum_eq_top (c : ℝ) :
    (∑' k : ℕ, fairSignPathLaw (fairSignBlockTailEvent c k)) = ∞ := by
  let tail : ℝ≥0∞ := gaussianReal 0 1 (Set.Ioi c)
  let epsilon : ℝ≥0∞ := tail / 2
  have htail_pos : 0 < tail := gaussianReal_zero_one_Ioi_pos c
  have htail_ne_top : tail ≠ ∞ := measure_ne_top _ _
  have hepsilon_pos : 0 < epsilon := by
    exact ENNReal.div_pos htail_pos.ne' (by norm_num)
  have hepsilon_lt : epsilon < tail :=
    ENNReal.half_lt_self htail_pos.ne' htail_ne_top
  have heventually : ∀ᶠ k : ℕ in atTop,
      epsilon < fairSignPathLaw (fairSignBlockTailEvent c k) :=
    fairSign_eventually_blockTail_mass_gt hepsilon_lt
  rcases Filter.eventually_atTop.mp heventually with ⟨K, hK⟩
  apply top_unique
  calc
    ∞ = ∑' _ : ℕ, epsilon :=
      (ENNReal.tsum_const_eq_top_of_ne_zero hepsilon_pos.ne').symm
    _ ≤ ∑' k : ℕ, fairSignPathLaw (fairSignBlockTailEvent c (K + k)) :=
      ENNReal.tsum_le_tsum fun k ↦ (hK (K + k) (Nat.le_add_right K k)).le
    _ ≤ ∑' k : ℕ, fairSignPathLaw (fairSignBlockTailEvent c k) :=
      ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective K) _

/-- Every fixed normalized threshold is exceeded on infinitely many disjoint
blocks, almost surely. -/
theorem fairSignBlockTailEvent_limsup_measure_eq_one (c : ℝ) :
    fairSignPathLaw (limsup (fairSignBlockTailEvent c) atTop) = 1 :=
  ProbabilityTheory.measure_limsup_eq_one
    (fairSignBlockTailEvent_measurable c)
    (fairSignBlockTailEvent_iIndepSet c)
    (fairSignBlockTailEvent_tsum_eq_top c)

theorem fairSign_ae_frequently_blockTail (c : ℝ) :
    ∀ᵐ ω ∂fairSignPathLaw,
      ∃ᶠ k : ℕ in atTop, c < fairSignBlockNormalizedSum k ω := by
  have hmeas : MeasurableSet (limsup (fairSignBlockTailEvent c) atTop) :=
    MeasurableSet.measurableSet_limsup (fairSignBlockTailEvent_measurable c)
  have hae : limsup (fairSignBlockTailEvent c) atTop ∈ ae fairSignPathLaw :=
    (mem_ae_iff_prob_eq_one hmeas).2
      (fairSignBlockTailEvent_limsup_measure_eq_one c)
  filter_upwards [hae] with ω hω
  exact mem_limsup_iff_frequently_mem.mp hω

theorem fairSignLaw_Icc_neg_one_one :
    fairSignLaw (Set.Icc (-1 : ℝ) 1) = 1 := by
  unfold fairSignLaw
  exact bernoulliMeasure_apply_of_mem_of_mem fairHalf measurableSet_Icc
    (by norm_num) (by norm_num)

/-- Almost every product path consists entirely of increments in `[-1,1]`.
This support fact is used only to control the deterministic contribution of
coordinates preceding a large independent block. -/
theorem fairSign_ae_all_increment_mem_Icc :
    ∀ᵐ ω ∂fairSignPathLaw, ∀ n : ℕ, fairSignIncrement n ω ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_all_iff]
  intro n
  have hmeas : MeasurableSet
      {ω | fairSignIncrement n ω ∈ Set.Icc (-1 : ℝ) 1} :=
    measurableSet_Icc.preimage (fairSignIncrement_measurable n)
  apply (mem_ae_iff_prob_eq_one hmeas).2
  calc
    fairSignPathLaw {ω | fairSignIncrement n ω ∈ Set.Icc (-1 : ℝ) 1} =
        fairSignLaw (Set.Icc (-1 : ℝ) 1) := by
      change fairSignPathLaw
        {ω | -1 ≤ fairSignIncrement n ω ∧ fairSignIncrement n ω ≤ 1} =
          fairSignLaw {x | -1 ≤ x ∧ x ≤ 1}
      exact (fairSignIncrement_hasLaw n).measure_eq measurableSet_Icc
    _ = 1 := fairSignLaw_Icc_neg_one_one

theorem fairSignSum_neg_card_le_of_increment_mem_Icc
    {ω : ℕ → ℝ}
    (hω : ∀ n : ℕ, fairSignIncrement n ω ∈ Set.Icc (-1 : ℝ) 1)
    (n : ℕ) :
    -(n : ℝ) ≤ fairSignSum n ω := by
  unfold fairSignSum
  calc
    -(n : ℝ) = ∑ _k ∈ Finset.range n, (-1 : ℝ) := by simp
    _ ≤ ∑ k ∈ Finset.range n, fairSignIncrement k ω := by
      exact Finset.sum_le_sum fun k _hk ↦ (hω k).1

theorem fairSignSum_block_decomposition (k : ℕ) (ω : ℕ → ℝ) :
    fairSignSum (fairSignBlockStart (k + 1)) ω =
      fairSignSum (fairSignBlockStart k) ω +
        fairSignSum (fairSignBlockLength k)
          (fairSignShift (fairSignBlockStart k) ω) := by
  rw [fairSignBlockStart_succ]
  unfold fairSignSum fairSignShift fairSignIncrement
  exact Finset.sum_range_add _ _ _

theorem fairSignBlockLength_sqrt (k : ℕ) :
    Real.sqrt (fairSignBlockLength k : ℝ) =
      (fairSignBlockStart k : ℝ) ^ 2 := by
  unfold fairSignBlockLength
  rw [Nat.cast_pow]
  rw [show (fairSignBlockStart k : ℝ) ^ 4 =
      ((fairSignBlockStart k : ℝ) ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg (fairSignBlockStart k : ℝ))]

theorem fairSignBlockEndpoint_sqrt_le (k : ℕ) :
    Real.sqrt (fairSignBlockStart (k + 1) : ℝ) ≤
      2 * (fairSignBlockStart k : ℝ) ^ 2 := by
  have ha : 1 ≤ (fairSignBlockStart k : ℝ) := by
    exact_mod_cast fairSignBlockStart_pos k
  rw [Real.sqrt_le_left (by positivity)]
  rw [fairSignBlockStart_succ, fairSignBlockLength, Nat.cast_add, Nat.cast_pow]
  nlinarith [mul_nonneg (show 0 ≤ (fairSignBlockStart k : ℝ) by positivity)
    (show 0 ≤ (fairSignBlockStart k : ℝ) - 1 by linarith)]

/-- A sufficiently large normalized block increment forces the ordinary partial
sum at the block endpoint above the requested `sqrt n` multiple. -/
theorem fairSignBlockTail_imp_endpoint
    {C : ℝ} (hC : 0 ≤ C) {ω : ℕ → ℝ}
    (hω : ∀ n : ℕ, fairSignIncrement n ω ∈ Set.Icc (-1 : ℝ) 1)
    {k : ℕ}
    (hblock : 2 * C + 1 < fairSignBlockNormalizedSum k ω) :
    C * Real.sqrt (fairSignBlockStart (k + 1) : ℝ) <
      fairSignSum (fairSignBlockStart (k + 1)) ω := by
  let a : ℝ := fairSignBlockStart k
  have ha : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast fairSignBlockStart_pos k
  have hsqrt_pos : 0 < Real.sqrt (fairSignBlockLength k : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast fairSignBlockLength_pos k)
  have hblock_div :
      2 * C + 1 <
        fairSignSum (fairSignBlockLength k)
          (fairSignShift (fairSignBlockStart k) ω) /
            Real.sqrt (fairSignBlockLength k : ℝ) := by
    simpa [fairSignBlockNormalizedSum, fairSignNormalizedSum,
      div_eq_mul_inv, mul_comm] using hblock
  have hblock_sum :
      (2 * C + 1) * a ^ 2 <
        fairSignSum (fairSignBlockLength k)
          (fairSignShift (fairSignBlockStart k) ω) := by
    have := (lt_div_iff₀ hsqrt_pos).mp hblock_div
    rwa [fairSignBlockLength_sqrt] at this
  have hprefix : -a ≤ fairSignSum (fairSignBlockStart k) ω := by
    simpa [a] using
      fairSignSum_neg_card_le_of_increment_mem_Icc hω (fairSignBlockStart k)
  have hsqrt_endpoint :
      Real.sqrt (fairSignBlockStart (k + 1) : ℝ) ≤ 2 * a ^ 2 := by
    simpa [a] using fairSignBlockEndpoint_sqrt_le k
  rw [fairSignSum_block_decomposition]
  have hnonneg : 0 ≤ a ^ 2 - a := by
    nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ a - 1 by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hsqrt_endpoint hC]

/-- **Unconditional unbounded `sqrt n` excursions.** For every fixed
nonnegative constant, the fair-sign walk exceeds that multiple of `sqrt n`
infinitely often, almost surely.  This follows from the CLT applied to
independent, rapidly growing blocks and the second Borel--Cantelli lemma. -/
theorem fairSign_ae_frequently_sum_gt_mul_sqrt (C : ℝ) (hC : 0 ≤ C) :
    ∀ᵐ ω ∂fairSignPathLaw,
      ∃ᶠ n : ℕ in atTop, C * Real.sqrt n < fairSignSum n ω := by
  have hendpoint : Tendsto (fun k : ℕ ↦ fairSignBlockStart (k + 1)) atTop atTop :=
    fairSignBlockStart_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [fairSign_ae_all_increment_mem_Icc,
    fairSign_ae_frequently_blockTail (2 * C + 1)] with ω hω hblocks
  exact Tendsto.frequently_map
    (fun k : ℕ ↦ fairSignBlockStart (k + 1)) hendpoint
    (fun k hk ↦ fairSignBlockTail_imp_endpoint hC hω hk) hblocks

/-- **Universal unbounded `sqrt n` floor for anytime boundaries.** Any
deterministic one-sided boundary with crossing probability strictly below one
must itself exceed every fixed nonnegative multiple of `sqrt n` infinitely
often.  Unlike the sharp LIL theorem below, this conclusion is unconditional. -/
theorem fairSign_anytimeBoundary_frequently_ge_mul_sqrt
    (boundary : ℕ → ℝ) {delta : ℝ≥0∞}
    (hvalid : fairSignPathLaw (oneSidedCrossingEvent fairSignSum boundary) ≤ delta)
    (hdelta : delta < 1) (C : ℝ) (hC : 0 ≤ C) :
    ∃ᶠ n : ℕ in atTop, C * Real.sqrt n ≤ boundary n := by
  by_contra hnot
  have hboundary : ∀ᶠ n : ℕ in atTop, boundary n < C * Real.sqrt n := by
    filter_upwards [Filter.not_frequently.mp hnot] with n hn
    exact lt_of_not_ge hn
  have haeCross :
      ∀ᵐ ω ∂fairSignPathLaw, ω ∈ oneSidedCrossingEvent fairSignSum boundary :=
    (fairSign_ae_frequently_sum_gt_mul_sqrt C hC).mono (by
      intro ω hfrequent
      obtain ⟨n, hnS, hnb⟩ := (hfrequent.and_eventually hboundary).exists
      exact ⟨n, hnb.trans hnS⟩)
  have hcrossing_eq_one :
      fairSignPathLaw (oneSidedCrossingEvent fairSignSum boundary) = 1 := by
    calc
      fairSignPathLaw (oneSidedCrossingEvent fairSignSum boundary) =
          fairSignPathLaw Set.univ := by
        apply measure_congr
        filter_upwards [haeCross] with ω hω
        change (∃ n, boundary n < fairSignSum n ω) = True
        exact propext ⟨fun _ ↦ trivial, fun _ ↦ hω⟩
      _ = 1 := measure_univ
  have hone_le : (1 : ℝ≥0∞) ≤ delta := by
    rw [← hcrossing_eq_one]
    exact hvalid
  exact (not_le_of_gt hdelta) hone_le

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
