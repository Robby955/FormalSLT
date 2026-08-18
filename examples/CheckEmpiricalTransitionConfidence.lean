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
  native_decide

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
  if j then 1 / 2 else 1 / 4

theorem transitionReceiptTilt_pos (j : Bool) :
    0 < transitionReceiptTilt j := by
  cases j <;> norm_num [transitionReceiptTilt]

theorem transitionReceiptTilt_lt_one (j : Bool) :
    transitionReceiptTilt j < 1 := by
  cases j <;> norm_num [transitionReceiptTilt]

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

#check exists_empiricalTransitionCoordinate_event
#check exists_empiricalTransitionFrequency_event
#check exists_empiricalCandidateRowTotalVariation_event
#check exists_selectedEmpiricalCandidateRowTotalVariation_event
#check exists_empiricalCandidateKernelTV_event
#check exists_selectedEmpiricalKernelContraction_event
#check transitionReceipt_rowTV_event
#check transitionReceipt_selectedContraction_event

#print axioms exists_empiricalTransitionCoordinate_event
#print axioms exists_empiricalTransitionFrequency_event
#print axioms exists_empiricalCandidateRowTotalVariation_event
#print axioms exists_selectedEmpiricalCandidateRowTotalVariation_event
#print axioms exists_empiricalCandidateKernelTV_event
#print axioms exists_selectedEmpiricalKernelContraction_event
#print axioms transitionReceipt_rowTV_event
#print axioms transitionReceipt_selectedContraction_event

end

end FormalSLT.Examples.CheckEmpiricalTransitionConfidence
