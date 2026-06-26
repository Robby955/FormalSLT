import FormalSLT.Covering.TotalBoundedDudleyCovering
import FormalSLT.Covering.ContinuousDudleyUnitInterval

/-!
# Total-bounded Dudley capstone with selected-cover-count envelope

This module assembles the generic guarded continuous-Dudley wrapper with the
selected-cover-count staircase from `TotalBoundedDudleyCovering`.

The entropy integrand in the capstone is
`ε ↦ totalBoundedCoveringEntropyAtRadius hT hradiusScale ε`, built from the
finite covers selected by the total-bounded dyadic schedule. It is not the
genuine minimal metric covering number `minimalMetricCoveringNumber`.
-/

namespace FormalSLT.Covering.TotalBoundedDudleySelectedCapstone

open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.GuardedDudleyIntegral
open FormalSLT.Covering.TotalBoundedDudley
open FormalSLT.Covering.TotalBoundedDudleyCovering
open FormalSLT.Covering.ContinuousDudleyUnitInterval

noncomputable section

universe u

variable {T : Type u}

/-- Boundary certificates imply the finite dyadic upper-sum input needed by the
guarded continuous wrapper, using the selected-cover-count entropy profile.

This is still a selected-cover-count statement: the finite entropy samples are
the adjacent dyadic cover counts chosen by total boundedness and wrapped in the
prefix envelope, not the genuine minimal covering number. -/
theorem totalBoundedSelectedCoverCount_dyadicProfileBound_of_boundaryChoice
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
        SeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius :=
            totalBoundedCoveringEntropyAtRadius
              (T := T) hT hradiusScale)
          (supFunctional := supFunctional) eta m) :
    ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        (∀ j ∈ Finset.range m,
          GuardedAntitoneOnDyadicAnnulus
            (totalBoundedCoveringEntropyAtRadius
              (T := T) hT hradiusScale) radiusScale j) ∧
        (∀ j ∈ Finset.range m,
          IntervalIntegrable
            (totalBoundedCoveringEntropyAtRadius
              (T := T) hT hradiusScale) MeasureTheory.volume
            (radiusScale / (2 : ℝ) ^ (j + 2))
            (radiusScale / (2 : ℝ) ^ (j + 1))) ∧
        finiteExpectation P.weight supFunctional ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m
              (totalBoundedCoveringEntropyAtRadius
                (T := T) hT hradiusScale) + eta := by
  intro eta heta
  rcases hchoose eta heta with ⟨m, hchoice⟩
  rcases hchoice with
    ⟨K, instK, nonemptyK, embed, separabilityError, terminalError,
      herror, _hentropyAtRadius, hintervalIntegrable, hseparable,
      hterminalApprox, hcoarse⟩
  letI : Fintype K := instK
  letI : Nonempty K := nonemptyK
  refine ⟨m, ?_, ?_, ?_⟩
  · intro j _hj
    exact totalBoundedCoveringEntropyAtRadius_guarded
      (T := T) hT hradiusScale j
  · intro j hj
    exact hintervalIntegrable j hj
  · let selectedEntropy : ℝ → ℝ :=
      totalBoundedCoveringEntropyAtRadius (T := T) hT hradiusScale
    let terminalNet :=
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
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
              radiusScale m selectedEntropy := by
      simpa [selectedEntropy, terminalNet, projectedSup] using
        finite_projectedNet_dudley_entropy_sum_totalBounded_dyadic_entropy_integral_comparison_nonempty
          (P := P) (hT := hT) (m := m) (coarseBudget := coarseBudget)
          (radiusScale := radiusScale) (entropyAtRadius := selectedEntropy)
          (integralBudget :=
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m selectedEntropy)
          hradiusScale hdistP hvariance
          (by
            intro j hj
            simpa [selectedEntropy] using
              totalBoundedCoveringEntropy_dominates_dyadicEnvelope_sample
                (T := T) hT hradiusScale j)
          le_rfl
          hcoarse
    have hwithError :
        finiteExpectation P.weight supFunctional ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m selectedEntropy +
            (separabilityError + terminalError) := by
      linarith [hadapter, hprojected]
    have herrorBudget :
        coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m selectedEntropy +
            (separabilityError + terminalError) ≤
          coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m selectedEntropy + eta := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left herror
          (coarseBudget + 2 * Real.sqrt (2 * P.varianceProxy) *
            FiniteSubGaussianProcess.finiteDyadicEntropyAtRadiusUpperSum
              radiusScale m selectedEntropy)
    exact hwithError.trans herrorBudget

/-- Continuous Dudley bound for an arbitrary totally bounded index space using
the selected-cover-count envelope, not the genuine minimal covering number.

The integrand is exactly
`ε ↦ totalBoundedCoveringEntropyAtRadius hT hradiusScale ε`, i.e. the entropy
of the prefix envelope of the finite covers selected by the total-bounded
dyadic schedule. This theorem intentionally does not state
`sqrt (log (minimalMetricCoveringNumber ... ε))`; the minimal-`N` tightening is
a separate comparison/minimal-selection problem. -/
-- fidelity: the entropy integrand is the selected-cover-count envelope
-- `totalBoundedCoveringEntropyAtRadius hT hradiusScale`, not genuine minimal N.
theorem continuous_dudley_entropy_integral_iSup_totalBounded_selectedCoverCountEnvelope_not_minimalCoveringNumber
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
        (totalBoundedCoveringEntropyAtRadius
          (T := T) hT hradiusScale) MeasureTheory.volume
        0 (radiusScale / 2))
    (hchoose : ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ,
        SeparableTerminalSupremumBoundaryChoiceNonempty
          (P := P) (hT := hT) (coarseBudget := fun _ => coarseBudget)
          (radiusScale := radiusScale) (hradiusScale := hradiusScale)
          (entropyAtRadius :=
            totalBoundedCoveringEntropyAtRadius
              (T := T) hT hradiusScale)
          (supFunctional := supFunctional) eta m) :
    finiteExpectation P.weight supFunctional ≤
      coarseBudget + 4 * Real.sqrt (2 * P.varianceProxy) *
        (∫ ε in (0 : ℝ)..(radiusScale / 2),
          totalBoundedCoveringEntropyAtRadius
            (T := T) hT hradiusScale ε) := by
  exact
    continuous_dudley_entropy_integral_iSup_of_dyadicProfile_guarded
      (P := P) (coarseBudget := coarseBudget) (radiusScale := radiusScale)
      (entropyAtRadius :=
        totalBoundedCoveringEntropyAtRadius (T := T) hT hradiusScale)
      (supFunctional := supFunctional) hradiusScale
      (totalBoundedCoveringEntropyAtRadius_nonneg
        (T := T) hT hradiusScale)
      hint0
      (totalBoundedSelectedCoverCount_dyadicProfileBound_of_boundaryChoice
        (P := P) (hT := hT) (coarseBudget := coarseBudget)
        (radiusScale := radiusScale) (supFunctional := supFunctional)
        hradiusScale hdistP hvariance hchoose)

/-- Unit-interval non-vacuity witness for the selected-cover-count envelope
surface used by the capstone. -/
theorem unitInterval_totalBoundedSelectedCoverCountEnvelope_sample_positive :
    0 <
      totalBoundedCoveringNumberAtRadius
        (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
        FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
        (by norm_num : (0 : ℝ) < 1) ((1 : ℝ) / 2) :=
  unitInterval_totalBoundedCoveringNumber_sample_positive

end

end FormalSLT.Covering.TotalBoundedDudleySelectedCapstone
