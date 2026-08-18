import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence

/-!
# Empirical transition-confidence receipts

The explicit Boolean path below records four transitions:

`false -> true -> false -> false -> true`.

Thus both rows are visited, the `false` row is visited three times, and its
empirical frequencies are `1/3` to `false` and `2/3` to `true`.  The true
kernel is asymmetric while the path-selected candidate used in the final
receipt is fair.  The exact arithmetic checks that the empirical candidate
row discrepancy and true row total variation are both nonzero.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge

namespace FormalSLT.Examples.CheckEmpiricalTransitionConfidence

open FormalSLT.StochasticDynamics

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Asymmetric true kernel: the `false` row is `(3/4,1/4)` and the `true`
row is fair. -/
def transitionReceiptKernel (x : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if x then
      ((1 / 2 : NNReal) : ENNReal)
    else if y then
      ((1 / 4 : NNReal) : ENNReal)
    else
      ((3 / 4 : NNReal) : ENNReal))
    (by
      have hquarterNN : (1 / 4 : NNReal) + 3 / 4 = 1 := by norm_num
      have hquarter : ((1 / 4 : NNReal) : ENNReal) +
          ((3 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hquarterNN]
        rfl
      have hhalfNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
      have hhalf : ((1 / 2 : NNReal) : ENNReal) +
          ((1 / 2 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hhalfNN]
        rfl
      cases x
      · simpa [Fintype.sum_bool, add_comm] using hquarter
      · simpa [Fintype.sum_bool, add_comm, two_mul] using hhalf)

/-- Fair candidate kernel. -/
def transitionReceiptCandidate (_x : Bool) : PMF Bool :=
  PMF.ofFintype (fun _y ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
    have h : ((1 / 2 : NNReal) : ENNReal) +
        ((1 / 2 : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_add, hNN]
      rfl
    simpa [Fintype.sum_bool, two_mul] using h)

/-- `false,true,false,false,true`, followed by `true` forever. -/
def transitionReceiptPath : ℕ → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => false
  | _ => true

theorem transitionReceipt_false_visit_mass :
    transitionVisitMass false 4 transitionReceiptPath = 3 := by
  norm_num [transitionVisitMass, transitionReceiptPath, Finset.sum_range_succ]

theorem transitionReceipt_true_visit_mass :
    transitionVisitMass true 4 transitionReceiptPath = 1 := by
  norm_num [transitionVisitMass, transitionReceiptPath, Finset.sum_range_succ]

theorem transitionReceipt_all_rows_visited :
    ∀ z : Bool, 0 < transitionVisitMass z 4 transitionReceiptPath := by
  intro z
  cases z
  · rw [transitionReceipt_false_visit_mass]
    norm_num
  · rw [transitionReceipt_true_visit_mass]
    norm_num

theorem transitionReceipt_false_false_edge_mass :
    transitionEdgeMass false false 4 transitionReceiptPath = 1 := by
  norm_num [transitionEdgeMass, transitionIndicatorScore,
    transitionReceiptPath, Finset.sum_range_succ]

theorem transitionReceipt_false_true_edge_mass :
    transitionEdgeMass false true 4 transitionReceiptPath = 2 := by
  norm_num [transitionEdgeMass, transitionIndicatorScore,
    transitionReceiptPath, Finset.sum_range_succ]

theorem transitionReceipt_true_false_edge_mass :
    transitionEdgeMass true false 4 transitionReceiptPath = 1 := by
  norm_num [transitionEdgeMass, transitionIndicatorScore,
    transitionReceiptPath, Finset.sum_range_succ]

theorem transitionReceipt_true_true_edge_mass :
    transitionEdgeMass true true 4 transitionReceiptPath = 0 := by
  norm_num [transitionEdgeMass, transitionIndicatorScore,
    transitionReceiptPath, Finset.sum_range_succ]

theorem transitionReceipt_false_false_frequency :
    empiricalTransitionFrequency false false 4 transitionReceiptPath = 1 / 3 := by
  rw [empiricalTransitionFrequency, transitionReceipt_false_false_edge_mass,
    transitionReceipt_false_visit_mass]

theorem transitionReceipt_false_true_frequency :
    empiricalTransitionFrequency false true 4 transitionReceiptPath = 2 / 3 := by
  rw [empiricalTransitionFrequency, transitionReceipt_false_true_edge_mass,
    transitionReceipt_false_visit_mass]

theorem transitionReceipt_true_false_frequency :
    empiricalTransitionFrequency true false 4 transitionReceiptPath = 1 := by
  rw [empiricalTransitionFrequency, transitionReceipt_true_false_edge_mass,
    transitionReceipt_true_visit_mass]
  norm_num

theorem transitionReceipt_candidate_empirical_discrepancy :
    empiricalCandidateRowTotalVariation transitionReceiptCandidate false 4
      transitionReceiptPath = 1 / 6 := by
  norm_num [empiricalCandidateRowTotalVariation,
    transitionReceiptCandidate, PMF.ofFintype_apply, Fintype.sum_bool,
    transitionReceipt_false_false_frequency,
    transitionReceipt_false_true_frequency]

theorem transitionReceipt_true_candidate_rowTV :
    finitePMFTotalVariation (transitionReceiptKernel false)
      (transitionReceiptCandidate false) = 1 / 4 := by
  norm_num [finitePMFTotalVariation, transitionReceiptKernel,
    transitionReceiptCandidate, PMF.ofFintype_apply, Fintype.sum_bool]

/-- Uniform prior over the eight `(source,destination,side)` atoms. -/
def transitionReceiptPrior : TransitionCoordinate Bool → ℝ :=
  finiteUniformRealPMF (TransitionCoordinate Bool)

theorem transitionReceiptPrior_isFullSupport :
    IsFullSupportPMF transitionReceiptPrior := by
  exact finiteUniformRealPMF_isFullSupport (TransitionCoordinate Bool)

theorem transitionReceipt_coordinate_cardinality :
    Fintype.card (TransitionCoordinate Bool) = 8 := by
  decide

theorem transitionReceipt_dirac_complexity
    (c : TransitionCoordinate Bool) :
    klDiv (diracPosterior c) transitionReceiptPrior = Real.log 8 := by
  unfold transitionReceiptPrior
  rw [klDiv_dirac_finiteUniformRealPMF,
    transitionReceipt_coordinate_cardinality]
  norm_num

def transitionReceiptTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem transitionReceiptTiltWeight_isFullSupport :
    IsFullSupportPMF transitionReceiptTiltWeight := by
  constructor
  · constructor <;> simp [transitionReceiptTiltWeight]
  · intro j
    simp [transitionReceiptTiltWeight]

def transitionReceiptTilt (j : Bool) : ℝ :=
  if j then 1 / 4 else 1 / 8

theorem transitionReceiptTilt_pos (j : Bool) :
    0 < transitionReceiptTilt j := by
  cases j <;> norm_num [transitionReceiptTilt]

theorem transitionReceiptTilt_lt_one (j : Bool) :
    transitionReceiptTilt j < 1 := by
  cases j <;> norm_num [transitionReceiptTilt]

/-! ### A deterministic balanced-prefix threshold check

The named path in this section is an arithmetic witness only.  The statements
below do not assert that this particular path belongs to the statistical good
event.  Event membership remains the premise needed to turn the deterministic
threshold into a coverage-certified conclusion.
-/

/-- Period-four path `false,false,true,true,...`.  Each block contains one of
each directed Boolean transition. -/
def transitionBalancedPath (k : ℕ) : Bool :=
  if k % 4 < 2 then false else true

set_option maxRecDepth 100000 in
theorem transitionBalanced_false_visit_mass :
    transitionVisitMass false 1024 transitionBalancedPath = 512 := by
  norm_num [transitionVisitMass, transitionBalancedPath,
    Finset.sum_range_succ]
  norm_cast

set_option maxRecDepth 100000 in
theorem transitionBalanced_true_visit_mass :
    transitionVisitMass true 1024 transitionBalancedPath = 512 := by
  norm_num [transitionVisitMass, transitionBalancedPath,
    Finset.sum_range_succ]
  norm_cast

set_option maxRecDepth 100000 in
theorem transitionBalanced_edge_mass (z y : Bool) :
    transitionEdgeMass z y 1024 transitionBalancedPath = 256 := by
  cases z <;> cases y
  all_goals
    norm_num [transitionEdgeMass, transitionIndicatorScore,
      transitionBalancedPath, Finset.sum_range_succ]
    norm_cast

theorem transitionBalanced_frequency (z y : Bool) :
    empiricalTransitionFrequency z y 1024 transitionBalancedPath = 1 / 2 := by
  rw [empiricalTransitionFrequency, transitionBalanced_edge_mass]
  cases z
  · rw [transitionBalanced_false_visit_mass]
    norm_num
  · rw [transitionBalanced_true_visit_mass]
    norm_num

theorem transitionBalanced_candidate_empirical_discrepancy (z : Bool) :
    empiricalCandidateRowTotalVariation transitionReceiptCandidate z 1024
      transitionBalancedPath = 0 := by
  unfold empiricalCandidateRowTotalVariation
  simp_rw [transitionBalanced_frequency]
  norm_num [transitionReceiptCandidate, PMF.ofFintype_apply,
    Fintype.sum_bool]

theorem transitionReceipt_log_eight_le_three : Real.log 8 ≤ 3 := by
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  calc
    Real.log 8 = Real.log ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
    _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 3 := by linarith

theorem transitionReceipt_log_forty_le_six : Real.log 40 ≤ 6 := by
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  calc
    Real.log 40 ≤ Real.log 64 :=
      Real.log_le_log (by norm_num) (by norm_num)
    _ = Real.log ((2 : ℝ) ^ (6 : ℕ)) := by norm_num
    _ = 6 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 6 := by linarith

theorem transitionReceipt_psi_one_eighth_le_one_fiftySix :
    forwardEmpiricalBernsteinPsi (1 / 8 : ℝ) ≤ 1 / 56 := by
  have hlog : Real.log ((8 : ℝ) / 7) ≤ 1 / 7 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 / 7 by norm_num)
    norm_num at h ⊢
    exact h
  unfold forwardEmpiricalBernsteinPsi
  rw [show (1 - (1 / 8 : ℝ)) = 7 / 8 by norm_num, ← Real.log_inv]
  norm_num only [inv_div]
  linarith

theorem transitionBalanced_hybridPenalty_le
    [DecidableEq (TransitionCoordinate Bool)]
    (c : TransitionCoordinate Bool) :
    trajectoryPosteriorHybridBesselPenalty
        (diracPosterior c) transitionCoordinateTrajectoryScore 1024
          transitionBalancedPath ≤ 769 / 2 := by
  unfold trajectoryPosteriorHybridBesselPenalty
  rw [pacBayesPosteriorAverage_dirac]
  have hq := forwardBesselQ_le_quarter_card
    (fun k ↦ observedTrajectoryScore
      (transitionCoordinateTrajectoryScore c) k transitionBalancedPath)
    (n := 1024) (by norm_num)
    (fun i hi ↦ observedTrajectoryScore_mem_Icc
      (transitionCoordinateTrajectoryScore_mem_Icc c) i transitionBalancedPath)
  unfold forwardHybridBesselPenalty
  calc
    min
        ((1 : ℝ) / 2 + 3 / 2 *
          forwardBesselQ
            (fun k ↦ observedTrajectoryScore
              (transitionCoordinateTrajectoryScore c) k transitionBalancedPath)
            1024)
        ((1024 : ℝ) / ((1024 : ℝ) - 1) *
            forwardBesselQ
              (fun k ↦ observedTrajectoryScore
                (transitionCoordinateTrajectoryScore c) k transitionBalancedPath)
              1024 +
          (1 : ℝ) / 4 * (1 + ((harmonic (1024 - 2) : ℚ) : ℝ))) ≤
      (1 : ℝ) / 2 + 3 / 2 *
        forwardBesselQ
          (fun k ↦ observedTrajectoryScore
            (transitionCoordinateTrajectoryScore c) k transitionBalancedPath)
          1024 := min_le_left _ _
    _ ≤ 769 / 2 := by nlinarith

/-- Every direct or complement coordinate boundary at the declared
`lambda = 1/8` atom is strictly below `1/8` on the balanced prefix. -/
theorem transitionBalanced_coordinateBoundary_lt_one_eighth
    (z y side : Bool) :
    transitionCoordinateBoundary transitionReceiptPrior
        transitionReceiptTiltWeight transitionReceiptTilt z y side
        (1 / 20) false 1024 transitionBalancedPath < 1 / 8 := by
  letI : DecidableEq Bool :=
    fun a b ↦ FormalSLT.StochasticDynamics.transitionConfidencePropDecidable
      (a = b)
  letI : DecidableEq (TransitionCoordinate Bool) :=
    @instDecidableEqTransitionCoordinate Bool (inferInstance : DecidableEq Bool)
  have hpenalty := transitionBalanced_hybridPenalty_le
    (⟨z, y, side⟩ : TransitionCoordinate Bool)
  have hpsiNonneg : 0 ≤ forwardEmpiricalBernsteinPsi (1 / 8 : ℝ) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have hproduct :
      forwardEmpiricalBernsteinPsi (1 / 8 : ℝ) *
          trajectoryPosteriorHybridBesselPenalty
            (diracPosterior (⟨z, y, side⟩ : TransitionCoordinate Bool))
              transitionCoordinateTrajectoryScore 1024 transitionBalancedPath ≤
        (1 / 56 : ℝ) * (769 / 2) := by
    calc
      forwardEmpiricalBernsteinPsi (1 / 8 : ℝ) *
            trajectoryPosteriorHybridBesselPenalty
              (diracPosterior (⟨z, y, side⟩ : TransitionCoordinate Bool))
                transitionCoordinateTrajectoryScore 1024
                  transitionBalancedPath ≤
          forwardEmpiricalBernsteinPsi (1 / 8 : ℝ) * (769 / 2) :=
        mul_le_mul_of_nonneg_left hpenalty hpsiNonneg
      _ ≤ (1 / 56 : ℝ) * (769 / 2) :=
        mul_le_mul_of_nonneg_right
          transitionReceipt_psi_one_eighth_le_one_fiftySix (by norm_num)
  unfold transitionCoordinateBoundary
    trajectoryEmpiricalBernsteinPACBayesBoundary
  unfold transitionReceiptPrior
  rw [klDiv_dirac_finiteUniformRealPMF,
    transitionReceipt_coordinate_cardinality]
  norm_num [transitionReceiptTiltWeight, transitionReceiptTilt]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 128)]
  norm_num
  have hlogs := add_le_add transitionReceipt_log_eight_le_three
    transitionReceipt_log_forty_le_six
  have hproductSeven := hproduct.trans_lt
    (by norm_num : (1 / 56 : ℝ) * (769 / 2) < 7)
  have htotal := add_lt_add_of_le_of_lt hlogs hproductSeven
  norm_num at htotal
  exact htotal

theorem transitionBalanced_coordinateRadius_lt_one_quarter
    (z y : Bool) :
    transitionCoordinateRadius transitionReceiptPrior
        transitionReceiptTiltWeight transitionReceiptTilt z y
        (1 / 20) false 1024 transitionBalancedPath < 1 / 4 := by
  have hmax :
      max
          (transitionCoordinateBoundary transitionReceiptPrior
            transitionReceiptTiltWeight transitionReceiptTilt z y false
              (1 / 20) false 1024 transitionBalancedPath)
          (transitionCoordinateBoundary transitionReceiptPrior
            transitionReceiptTiltWeight transitionReceiptTilt z y true
              (1 / 20) false 1024 transitionBalancedPath) <
        1 / 8 :=
    (max_lt_iff.mpr ⟨
      transitionBalanced_coordinateBoundary_lt_one_eighth z y false,
      transitionBalanced_coordinateBoundary_lt_one_eighth z y true⟩)
  unfold transitionCoordinateRadius
  cases z
  · rw [transitionBalanced_false_visit_mass]
    norm_num
    linarith
  · rw [transitionBalanced_true_visit_mass]
    norm_num
    linarith

theorem transitionBalanced_rowRadius_lt_one_quarter (z : Bool) :
    empiricalTransitionRowRadius transitionReceiptPrior
        transitionReceiptTiltWeight transitionReceiptTilt z
        (1 / 20) false 1024 transitionBalancedPath < 1 / 4 := by
  have hfalse := transitionBalanced_coordinateRadius_lt_one_quarter z false
  have htrue := transitionBalanced_coordinateRadius_lt_one_quarter z true
  unfold empiricalTransitionRowRadius
  rw [Fintype.sum_bool]
  linarith

/-- The selected fair kernel has zero empirical row discrepancy on both rows
of the named balanced prefix, and the uniform all-row budget is below `1/4`. -/
theorem transitionBalanced_kernelTVBudget_lt_one_quarter :
    empiricalCandidateKernelTVBudget transitionReceiptCandidate
        transitionReceiptPrior transitionReceiptTiltWeight
          transitionReceiptTilt (1 / 20) false 1024
            transitionBalancedPath < 1 / 4 := by
  unfold empiricalCandidateKernelTVBudget finiteMaximum
  rw [Finset.sup'_lt_iff]
  intro z _hz
  rw [transitionBalanced_candidate_empirical_discrepancy]
  norm_num
  exact transitionBalanced_rowRadius_lt_one_quarter z

theorem transitionReceiptCandidate_dobrushin_zero :
    finiteDobrushinCoefficient transitionReceiptCandidate = 0 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    have hrows : transitionReceiptCandidate x =
        transitionReceiptCandidate y := rfl
    rw [hrows]
    exact (finitePMFTotalVariation_eq_zero_iff
      (transitionReceiptCandidate y) (transitionReceiptCandidate y)).mpr rfl |>.le
  · exact finiteDobrushinCoefficient_nonneg transitionReceiptCandidate

/-- Deterministic arithmetic check: the balanced prefix satisfies the
candidate-perturbation Dobrushin antecedent with strict slack.  This theorem
alone is not a probability or good-event membership statement. -/
theorem transitionBalanced_candidate_contraction_threshold :
    finiteDobrushinCoefficient transitionReceiptCandidate +
        2 * empiricalCandidateKernelTVBudget transitionReceiptCandidate
          transitionReceiptPrior transitionReceiptTiltWeight
            transitionReceiptTilt (1 / 20) false 1024
              transitionBalancedPath < 1 := by
  rw [transitionReceiptCandidate_dobrushin_zero]
  nlinarith [transitionBalanced_kernelTVBudget_lt_one_quarter]

/-- The checked statistical endpoint: one event controls every time, visited
row, declared tilt, and candidate kernel.  In particular, a candidate may be
chosen after observing the path because it is universally quantified inside
the event. -/
theorem transitionReceipt_rowTV_event :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure transitionReceiptKernel false).real goodEventᶜ ≤
          (1 / 20 : ℝ) ∧
        ∀ x ∈ goodEvent, ∀ j : Bool, ∀ n : ℕ, 2 ≤ n →
          ∀ z : Bool, 0 < transitionVisitMass z n x →
            ∀ Q : Bool → PMF Bool,
              finitePMFTotalVariation (transitionReceiptKernel z) (Q z) ≤
                empiricalCandidateRowTotalVariation Q z n x +
                  empiricalTransitionRowRadius
                    transitionReceiptPrior transitionReceiptTiltWeight
                    transitionReceiptTilt z (1 / 20) j n x := by
  exact exists_empiricalCandidateRowTotalVariation_event
    (τ := Bool) transitionReceiptKernel false
    transitionReceiptPrior_isFullSupport
    transitionReceiptTiltWeight_isFullSupport (by norm_num)
    transitionReceiptTilt_pos transitionReceiptTilt_lt_one

def transitionReceiptSelectedCandidate
    (_x : ℕ → Bool) (_n : ℕ) : Bool → PMF Bool :=
  transitionReceiptCandidate

/-- The same Boolean model instantiates the all-row plug-in capstone.  Below
the pathwise candidate-plus-radius threshold, the theorem certifies strict
contraction and uniqueness of every supplied true invariant law. -/
theorem transitionReceipt_selectedContraction_event :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure transitionReceiptKernel false).real goodEventᶜ ≤
          (1 / 20 : ℝ) ∧
        ∀ x ∈ goodEvent, ∀ j : Bool, ∀ n : ℕ, 2 ≤ n →
          (∀ z : Bool, 0 < transitionVisitMass z n x) →
            let Q := transitionReceiptSelectedCandidate x n
            let eta := empiricalCandidateKernelTVBudget
              Q transitionReceiptPrior transitionReceiptTiltWeight
                transitionReceiptTilt (1 / 20) j n x
            let alpha := finiteDobrushinCoefficient Q + 2 * eta
            finiteDobrushinCoefficient transitionReceiptKernel ≤ alpha ∧
              IsOscillationContraction transitionReceiptKernel alpha ∧
                (alpha < 1 →
                  finiteDobrushinCoefficient transitionReceiptKernel < 1 ∧
                    ∀ stationary₁ stationary₂ : PMF Bool,
                      IsInvariantPMF transitionReceiptKernel stationary₁ →
                        IsInvariantPMF transitionReceiptKernel stationary₂ →
                          stationary₁ = stationary₂) := by
  exact exists_selectedEmpiricalKernelContraction_event
    (τ := Bool) transitionReceiptKernel false
    transitionReceiptPrior_isFullSupport
    transitionReceiptTiltWeight_isFullSupport (by norm_num)
    transitionReceiptTilt_pos transitionReceiptTilt_lt_one
    transitionReceiptSelectedCandidate

/-- Coverage and deterministic nonvacuity are kept separate for the fair true
kernel.  The event has failure outer mass at most `1/20`; if the named balanced
path is in that event, the already-checked `eta < 1/4` arithmetic fires the
strict-contraction and invariant-uniqueness branch.  This does not prove named
path membership or a positive-probability intersection. -/
theorem transitionReceipt_balancedPath_contraction_of_good :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure transitionReceiptCandidate false).real goodEventᶜ ≤
          (1 / 20 : ℝ) ∧
        (transitionBalancedPath ∈ goodEvent →
          let eta := empiricalCandidateKernelTVBudget
            transitionReceiptCandidate transitionReceiptPrior
              transitionReceiptTiltWeight transitionReceiptTilt
                (1 / 20) false 1024 transitionBalancedPath
          finiteDobrushinCoefficient transitionReceiptCandidate ≤ 2 * eta ∧
            IsOscillationContraction transitionReceiptCandidate (2 * eta) ∧
              finiteDobrushinCoefficient transitionReceiptCandidate < 1 ∧
                ∀ stationary₁ stationary₂ : PMF Bool,
                  IsInvariantPMF transitionReceiptCandidate stationary₁ →
                    IsInvariantPMF transitionReceiptCandidate stationary₂ →
                      stationary₁ = stationary₂) := by
  rcases exists_selectedEmpiricalKernelContraction_event
      (τ := Bool) (prior := transitionReceiptPrior)
      (weight := transitionReceiptTiltWeight)
      (lam := transitionReceiptTilt) (delta := (1 / 20 : ℝ))
      transitionReceiptCandidate false
      transitionReceiptPrior_isFullSupport
      transitionReceiptTiltWeight_isFullSupport (by norm_num)
      transitionReceiptTilt_pos transitionReceiptTilt_lt_one
      transitionReceiptSelectedCandidate with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro hbalanced
  dsimp only
  have hall : ∀ z : Bool,
      0 < transitionVisitMass z 1024 transitionBalancedPath := by
    intro z
    cases z
    · rw [transitionBalanced_false_visit_mass]
      norm_num
    · rw [transitionBalanced_true_visit_mass]
      norm_num
  have hcertificate := hgood transitionBalancedPath hbalanced false 1024
    (by norm_num) hall
  have hcertificate' :
      finiteDobrushinCoefficient transitionReceiptCandidate ≤
          2 * empiricalCandidateKernelTVBudget transitionReceiptCandidate
            transitionReceiptPrior transitionReceiptTiltWeight
              transitionReceiptTilt (1 / 20) false 1024
                transitionBalancedPath ∧
        IsOscillationContraction transitionReceiptCandidate
          (2 * empiricalCandidateKernelTVBudget transitionReceiptCandidate
            transitionReceiptPrior transitionReceiptTiltWeight
              transitionReceiptTilt (1 / 20) false 1024
                transitionBalancedPath) ∧
          (2 * empiricalCandidateKernelTVBudget transitionReceiptCandidate
              transitionReceiptPrior transitionReceiptTiltWeight
                transitionReceiptTilt (1 / 20) false 1024
                  transitionBalancedPath < 1 →
            finiteDobrushinCoefficient transitionReceiptCandidate < 1 ∧
              ∀ stationary₁ stationary₂ : PMF Bool,
                IsInvariantPMF transitionReceiptCandidate stationary₁ →
                  IsInvariantPMF transitionReceiptCandidate stationary₂ →
                    stationary₁ = stationary₂) := by
    simpa [transitionReceiptSelectedCandidate,
      transitionReceiptCandidate_dobrushin_zero] using hcertificate
  have hstrict :
      2 * empiricalCandidateKernelTVBudget transitionReceiptCandidate
          transitionReceiptPrior transitionReceiptTiltWeight
            transitionReceiptTilt (1 / 20) false 1024
              transitionBalancedPath < 1 := by
    simpa [transitionReceiptCandidate_dobrushin_zero] using
      transitionBalanced_candidate_contraction_threshold
  exact ⟨hcertificate'.1, hcertificate'.2.1,
    (hcertificate'.2.2 hstrict).1, (hcertificate'.2.2 hstrict).2⟩

#check exists_empiricalTransitionCoordinate_event
#check exists_empiricalTransitionFrequency_event
#check exists_empiricalCandidateRowTotalVariation_event
#check exists_selectedEmpiricalCandidateRowTotalVariation_event
#check exists_empiricalCandidateKernelTV_event
#check exists_selectedEmpiricalKernelContraction_event
#check transitionReceipt_rowTV_event
#check transitionReceipt_selectedContraction_event
#check transitionBalanced_kernelTVBudget_lt_one_quarter
#check transitionBalanced_candidate_contraction_threshold
#check transitionReceipt_balancedPath_contraction_of_good

#print axioms exists_empiricalTransitionCoordinate_event
#print axioms exists_empiricalTransitionFrequency_event
#print axioms exists_empiricalCandidateRowTotalVariation_event
#print axioms exists_selectedEmpiricalCandidateRowTotalVariation_event
#print axioms exists_empiricalCandidateKernelTV_event
#print axioms exists_selectedEmpiricalKernelContraction_event
#print axioms transitionReceipt_rowTV_event
#print axioms transitionReceipt_selectedContraction_event
#print axioms transitionBalanced_kernelTVBudget_lt_one_quarter
#print axioms transitionBalanced_candidate_contraction_threshold
#print axioms transitionReceipt_balancedPath_contraction_of_good

end

end FormalSLT.Examples.CheckEmpiricalTransitionConfidence
