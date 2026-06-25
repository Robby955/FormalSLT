import FormalSLT.Covering.TotalBoundedDudleyCovering
import FormalSLT.Covering.UnitIntervalDudley

/-!
# Genuine minimal covering numbers for totally bounded index spaces

This module defines the genuine finite metric covering number of a nonempty
totally bounded metric index space at a positive radius, then compares it with
the selected dyadic finite-net counts used by the total-bounded Dudley bridge.

The comparison proved here has the mathematically valid orientation: the
minimal covering number is bounded above by every selected finite cover count.
The reverse inequality needed to replace selected counts by minimal counts in
the current upper-bound Dudley wrapper would require the selected covers to be
chosen cardinal-minimal, or an added minimality hypothesis.
-/

namespace FormalSLT.Covering.TotalBoundedMinimalCovering

open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.TotalBoundedDudley
open FormalSLT.Covering.TotalBoundedDudleyCovering

noncomputable section

universe u

variable {T : Type u}

/-- There is a finite metric `ε`-cover of the whole index space using at most
`n` centers. This is the predicate minimized by
`minimalMetricCoveringNumber`. -/
def MetricCoverCardinalityLe [PseudoMetricSpace T] (ε : ℝ) (n : ℕ) : Prop :=
  ∃ C : Finset T, C.card ≤ n ∧ ∀ t : T, ∃ c ∈ C, dist t c ≤ ε

private theorem metricCoverCardinalityLe_exists_of_totallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, MetricCoverCardinalityLe (T := T) ε n := by
  classical
  rcases finiteMetricCoverOfTotallyBoundedUniv (T := T) hT hε with
    ⟨C, hCfinite, hcover⟩
  let F : Finset T := hCfinite.toFinset
  refine ⟨F.card, F, le_rfl, ?_⟩
  intro t
  rcases hcover t with ⟨c, hc, hdist⟩
  exact ⟨c, by simpa [F] using (hCfinite.mem_toFinset.mpr hc), hdist⟩

/-- The genuine minimal metric covering number of a nonempty totally bounded
index space at a positive radius. -/
def minimalMetricCoveringNumber [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) : ℕ := by
  classical
  exact Nat.find
    (metricCoverCardinalityLe_exists_of_totallyBoundedUniv (T := T) hT hε)

/-- The minimal covering number is realized by an explicit finite metric cover. -/
theorem minimalMetricCoveringNumber_spec
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    MetricCoverCardinalityLe (T := T) ε
      (minimalMetricCoveringNumber (T := T) hT hε) := by
  classical
  unfold minimalMetricCoveringNumber
  exact Nat.find_spec
    (metricCoverCardinalityLe_exists_of_totallyBoundedUniv (T := T) hT hε)

/-- Minimality: any finite metric `ε`-cover with at most `n` centers bounds the
genuine minimal covering number by `n`. -/
theorem minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hcover : MetricCoverCardinalityLe (T := T) ε n) :
    minimalMetricCoveringNumber (T := T) hT hε ≤ n := by
  classical
  unfold minimalMetricCoveringNumber
  exact Nat.find_min'
    (metricCoverCardinalityLe_exists_of_totallyBoundedUniv (T := T) hT hε)
    hcover

/-- A nonempty index space has positive genuine minimal covering number at any
positive radius. -/
theorem minimalMetricCoveringNumber_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    0 < minimalMetricCoveringNumber (T := T) hT hε := by
  by_contra hnot
  have hzero :
      minimalMetricCoveringNumber (T := T) hT hε = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rcases minimalMetricCoveringNumber_spec (T := T) hT hε with
    ⟨C, hcard, hcover⟩
  have hcard_zero : C.card = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [hzero] using hcard)
  have hC_empty : C = ∅ := Finset.card_eq_zero.mp hcard_zero
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  rcases hcover t with ⟨c, hc, _hdist⟩
  simp [hC_empty] at hc

/-- A bundled finite net using the ambient metric distance gives a finite metric
cover with at most its selected covering count. -/
theorem metricCoverCardinalityLe_of_bundledFiniteNet
    [PseudoMetricSpace T] [Nonempty T]
    (B : BundledFiniteNet T)
    (hdist : B.net.dist = fun s t => dist s t) :
    MetricCoverCardinalityLe (T := T) B.net.radius B.coveringNumber := by
  classical
  letI : Fintype B.A := B.instFintype
  let C : Finset T := Finset.univ.image B.net.center
  refine ⟨C, ?_, ?_⟩
  · have hcard : C.card ≤ (Finset.univ : Finset B.A).card :=
      Finset.card_image_le
    simpa [C, BundledFiniteNet.coveringNumber, FiniteNet.coveringNumber] using hcard
  · intro t
    refine ⟨B.net.center (B.net.project t), ?_, ?_⟩
    · simp [C]
    · simpa [hdist] using B.net.covers t

/-- Any ambient-metric bundled finite net bounds the genuine minimal covering
number at its radius. -/
theorem minimalMetricCoveringNumber_le_bundledFiniteNet_coveringNumber
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    (B : BundledFiniteNet T)
    (hdist : B.net.dist = fun s t => dist s t)
    (hradius : 0 < B.net.radius) :
    minimalMetricCoveringNumber (T := T) hT hradius ≤ B.coveringNumber :=
  minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe
    (T := T) hT hradius
    (metricCoverCardinalityLe_of_bundledFiniteNet (T := T) B hdist)

/-- At each dyadic radius, the genuine minimal covering number is bounded by
the selected total-bounded dyadic net cardinality. -/
theorem minimalMetricCoveringNumber_le_dyadicSelectedCoveringNumber
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalMetricCoveringNumber (T := T) hT
        (dyadicChainingNetRadius_pos hradiusScale j) ≤
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.coveringNumber := by
  have hdist :
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.dist = fun s t => dist s t := by
    simp
  have hle :=
    minimalMetricCoveringNumber_le_bundledFiniteNet_coveringNumber
      (T := T) hT
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j)
      hdist
      (by simp [dyadicChainingNetRadius_pos hradiusScale j])
  simpa [BundledFiniteNet.coveringNumber] using hle

/-- The selected dyadic envelope dominates the genuine minimal covering number
at each sampled dyadic net radius. This is the true bridge from minimal
covering numbers to the currently selected-count staircase. -/
theorem minimalMetricCoveringNumber_le_totalBoundedDyadicCoverCountEnvelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalMetricCoveringNumber (T := T) hT
        (dyadicChainingNetRadius_pos hradiusScale j) ≤
      totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
  have hminimal :=
    minimalMetricCoveringNumber_le_dyadicSelectedCoveringNumber
      (T := T) hT hradiusScale j
  have hsucc_pos :
      0 <
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net.coveringNumber :=
    FiniteNet.coveringNumber_pos
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net)
  have hnet_le_product :
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.coveringNumber ≤
        dyadicChainingCoverCount (T := T) hT hradiusScale j := by
    unfold dyadicChainingCoverCount
    exact Nat.le_mul_of_pos_right
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.coveringNumber)
      hsucc_pos
  exact hminimal.trans
    (hnet_le_product.trans
      (dyadicChainingCoverCount_le_envelope (T := T) hT hradiusScale j))

/-- Non-vacuity witness: the genuine minimal covering number is positive on the
mechanized unit interval at a concrete positive radius. -/
theorem unitInterval_minimalMetricCoveringNumber_sample_positive :
    0 <
      minimalMetricCoveringNumber
        (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
        FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
        (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) :=
  minimalMetricCoveringNumber_pos
    (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
    FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)

end

end FormalSLT.Covering.TotalBoundedMinimalCovering
