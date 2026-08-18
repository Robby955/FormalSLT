import FormalSLT.StochasticDynamics.EmpiricalStationaryCatalog

/-!
# Two-candidate same-trajectory stationary-certificate receipt

The true Boolean chain has transition probabilities
`P(false,true)=1/4` and `P(true,false)=1/2`, with invariant law `(2/3,1/3)`.
The declared candidate catalog contains the true kernel and a fair-row kernel.
For the next-state indicator, their exact Dobrushin/centered-oscillation pairs
are `(1/4,1/4)` and `(0,0)`.  At depth two the resulting span/residual pairs
are `(5/16,1/64)` and `(0,0)`.

The selected theorem uses the same trajectory for both the risk process and
the transition-confidence process, with budgets `1/4+1/4`.  Two explicit
all-row-covered paths exercise both candidate-selector branches.  They are
arithmetic receipts only: neither path is claimed to belong to the theorem's
good event.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable

namespace FormalSLT.Examples.CheckEmpiricalStationaryCatalog

open FormalSLT.StochasticDynamics

noncomputable section

def catalogTrueKernel (x : Bool) : PMF Bool :=
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

def catalogFairKernel (_x : Bool) : PMF Bool :=
  PMF.ofFintype (fun _y ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
    have h : ((1 / 2 : NNReal) : ENNReal) +
        ((1 / 2 : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_add, hNN]
      rfl
    simpa [Fintype.sum_bool, two_mul] using h)

def catalogStationary : PMF Bool :=
  PMF.ofFintype
    (fun z ↦ if z then
      ((1 / 3 : NNReal) : ENNReal)
    else
      ((2 / 3 : NNReal) : ENNReal))
    (by
      have hNN : (1 / 3 : NNReal) + 2 / 3 = 1 := by norm_num
      have h : ((1 / 3 : NNReal) : ENNReal) +
          ((2 / 3 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hNN]
        rfl
      simpa [Fintype.sum_bool, add_comm] using h)

theorem catalogStationary_invariant :
    IsInvariantPMF catalogTrueKernel catalogStationary := by
  have htrueNN :
      (2 / 3 : NNReal) * (1 / 4) + (1 / 3) * (1 / 2) = 1 / 3 := by
    norm_num
  have htrue :
      ((2 / 3 : NNReal) : ENNReal) * ((1 / 4 : NNReal) : ENNReal) +
          ((1 / 3 : NNReal) : ENNReal) * ((1 / 2 : NNReal) : ENNReal) =
        ((1 / 3 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) htrueNN
  have hfalseNN :
      (2 / 3 : NNReal) * (3 / 4) + (1 / 3) * (1 / 2) = 2 / 3 := by
    norm_num
  have hfalse :
      ((2 / 3 : NNReal) : ENNReal) * ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 3 : NNReal) : ENNReal) * ((1 / 2 : NNReal) : ENNReal) =
        ((2 / 3 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) hfalseNN
  unfold IsInvariantPMF
  apply PMF.ext
  intro y
  cases y
  · simpa [PMF.bind_apply, tsum_fintype, catalogTrueKernel,
      catalogStationary, PMF.ofFintype_apply, Fintype.sum_bool,
      add_comm, mul_comm] using hfalse
  · simpa [PMF.bind_apply, tsum_fintype, catalogTrueKernel,
      catalogStationary, PMF.ofFintype_apply, Fintype.sum_bool,
      add_comm, mul_comm] using htrue

def catalogTransitionScore (_x y : Bool) : ℝ := if y then 1 else 0

theorem catalogTransitionScore_mem_Icc :
    ∀ x y, catalogTransitionScore x y ∈ Set.Icc (0 : ℝ) 1 := by
  intro x y
  fin_cases y <;> norm_num [catalogTransitionScore]

theorem catalogTrue_dobrushin :
    finiteDobrushinCoefficient catalogTrueKernel = 1 / 4 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    fin_cases x <;> fin_cases y <;>
      norm_num [finitePMFTotalVariation, catalogTrueKernel,
        PMF.ofFintype_apply, Fintype.sum_bool]
  · have h := finitePMFTotalVariation_le_finiteDobrushinCoefficient
      catalogTrueKernel false true
    norm_num [finitePMFTotalVariation, catalogTrueKernel,
      PMF.ofFintype_apply, Fintype.sum_bool] at h ⊢
    exact h

/-- For this strict-contraction receipt, the canonical invariant law is the
displayed `(2/3, 1/3)` PMF rather than merely an opaque choice. -/
theorem catalogCanonicalStationary_eq_displayed :
    finiteInvariantPMF catalogTrueKernel = catalogStationary :=
  invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one
    catalogTrueKernel (by rw [catalogTrue_dobrushin]; norm_num)
    (finiteInvariantPMF catalogTrueKernel) catalogStationary
    (finiteInvariantPMF_isInvariant catalogTrueKernel)
    catalogStationary_invariant

theorem catalogFair_dobrushin :
    finiteDobrushinCoefficient catalogFairKernel = 0 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    norm_num [finitePMFTotalVariation, catalogFairKernel,
      PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteDobrushinCoefficient_nonneg _

theorem catalogTrue_centeredOscillation :
    finiteOscillation
      (centeredMarkovRowRisk catalogTrueKernel catalogStationary
        catalogTransitionScore) = 1 / 4 := by
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [centeredMarkovRowRisk, stationaryMarkovRisk, markovRowRisk,
        catalogTrueKernel, catalogStationary, catalogTransitionScore,
        PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]
  · have h := abs_sub_le_finiteOscillation
      (centeredMarkovRowRisk catalogTrueKernel catalogStationary
        catalogTransitionScore) false true
    norm_num [centeredMarkovRowRisk, stationaryMarkovRisk, markovRowRisk,
      catalogTrueKernel, catalogStationary, catalogTransitionScore,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool] at h ⊢
    exact h

theorem catalogFair_centeredOscillation :
    finiteOscillation
      (centeredMarkovRowRisk catalogFairKernel catalogStationary
        catalogTransitionScore) = 0 := by
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [centeredMarkovRowRisk, stationaryMarkovRisk, markovRowRisk,
        catalogFairKernel, catalogStationary, catalogTransitionScore,
        PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteOscillation_nonneg _

/-- `false` selects the exact true kernel; `true` selects the fair kernel. -/
def catalogCandidate (c : Bool) : Bool → PMF Bool :=
  if c then catalogFairKernel else catalogTrueKernel

def catalogReference (_c : Bool) : PMF Bool := catalogStationary

def catalogScore (_i : Unit) : MarkovTransitionScore Bool :=
  catalogTransitionScore

def catalogD (c : Bool) : ℝ := if c then 0 else 1 / 4

theorem catalogCandidate_coefficient_lt_one :
    ∀ c, finiteDobrushinCoefficient (catalogCandidate c) < 1 := by
  intro c
  cases c
  · norm_num [catalogCandidate, catalogTrue_dobrushin]
  · norm_num [catalogCandidate, catalogFair_dobrushin]

theorem catalogD_nonneg : ∀ c, 0 ≤ catalogD c := by
  intro c
  cases c <;> norm_num [catalogD]

theorem catalogD_bounds : ∀ c i,
    finiteOscillation
      (centeredMarkovRowRisk (catalogCandidate c) (catalogReference c)
        (catalogScore i)) ≤ catalogD c := by
  intro c i
  cases c
  · simpa [catalogCandidate, catalogReference, catalogScore, catalogD]
      using catalogTrue_centeredOscillation.le
  · simpa [catalogCandidate, catalogReference, catalogScore, catalogD]
      using catalogFair_centeredOscillation.le

def catalogCandidateWeight (_c : Bool) : ℝ := 1 / 2

theorem catalogCandidateWeight_isFullSupport :
    IsFullSupportPMF catalogCandidateWeight := by
  constructor
  · constructor
    · intro c
      norm_num [catalogCandidateWeight]
    · norm_num [catalogCandidateWeight, Fintype.sum_bool]
  · intro c
    norm_num [catalogCandidateWeight]

def catalogPrior (_i : Unit) : ℝ := 1

theorem catalogPrior_isFullSupport : IsFullSupportPMF catalogPrior := by
  constructor
  · constructor <;> simp [catalogPrior]
  · intro i
    cases i
    norm_num [catalogPrior]

def catalogTransitionPrior : TransitionCoordinate Bool → ℝ :=
  finiteUniformRealPMF (TransitionCoordinate Bool)

theorem catalogTransitionPrior_isFullSupport :
    IsFullSupportPMF catalogTransitionPrior :=
  finiteUniformRealPMF_isFullSupport (TransitionCoordinate Bool)

def catalogTransitionWeight (_k : Unit) : ℝ := 1

theorem catalogTransitionWeight_isFullSupport :
    IsFullSupportPMF catalogTransitionWeight := by
  constructor
  · constructor <;> simp [catalogTransitionWeight]
  · intro k
    cases k
    norm_num [catalogTransitionWeight]

def catalogTransitionTilt (_k : Unit) : ℝ := 1 / 4

theorem catalogTransitionTilt_pos : ∀ k, 0 < catalogTransitionTilt k := by
  intro k
  norm_num [catalogTransitionTilt]

theorem catalogTransitionTilt_lt_one : ∀ k, catalogTransitionTilt k < 1 := by
  intro k
  norm_num [catalogTransitionTilt]

def catalogPosterior (_x : ℕ → Bool) (_n : ℕ) (_i : Unit) : ℝ := 1

theorem catalogPosterior_isPMF : ∀ x n, IsPMF (catalogPosterior x n) := by
  intro x n
  constructor
  · intro i
    norm_num [catalogPosterior]
  · simp [catalogPosterior]

def catalogSelector (x : ℕ → Bool) (n : ℕ) : Bool := x n

def catalogDepthSelector (_x : ℕ → Bool) (_n : ℕ) : ℕ := 2

def catalogRiskTiltSelector (_x : ℕ → Bool) (_n : ℕ) : ℕ := 0

def catalogTransitionTiltSelector (_x : ℕ → Bool) (_n : ℕ) : Unit := ()

/-- The canonical-invariant selected theorem specialized to the two-candidate
receipt.  The all-row-visit premise is retained exactly. -/
theorem boolCatalog_sameData_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure catalogTrueKernel false).real goodEventᶜ ≤ 1 / 2 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          (∀ z : Bool, 0 < transitionVisitMass z n x) →
            let c := catalogSelector x n
            let eta := empiricalCandidateKernelTVBudget
              (catalogCandidate c) catalogTransitionPrior
              catalogTransitionWeight catalogTransitionTilt
              (1 / 4) (catalogTransitionTiltSelector x n) n x
            stationaryPosteriorMarkovRisk catalogTrueKernel
                (finiteInvariantPMF catalogTrueKernel)
                catalogScore (catalogPosterior x n) <
              empiricalTransitionPosteriorRisk
                  catalogScore (catalogPosterior x n) n x +
                empiricalStationaryCatalogBoundary
                  catalogCandidate catalogReference catalogScore catalogD
                  catalogCandidateWeight catalogPrior (catalogPosterior x n)
                  (1 / 4) eta c (catalogDepthSelector x n)
                  (catalogRiskTiltSelector x n) n x ∧
            finiteDobrushinCoefficient catalogTrueKernel ≤
              finiteDobrushinCoefficient (catalogCandidate c) + 2 * eta ∧
            IsOscillationContraction catalogTrueKernel
              (finiteDobrushinCoefficient (catalogCandidate c) + 2 * eta) ∧
            (finiteDobrushinCoefficient (catalogCandidate c) + 2 * eta < 1 →
              ∀ stationaryOne stationaryTwo : PMF Bool,
                IsInvariantPMF catalogTrueKernel stationaryOne →
                IsInvariantPMF catalogTrueKernel stationaryTwo →
                stationaryOne = stationaryTwo) := by
  have h := exists_selectedCanonicalEmpiricalStationaryCatalog_event
    catalogTrueKernel false catalogCandidate catalogReference
    (fun i x y ↦ by
      simpa [catalogScore] using catalogTransitionScore_mem_Icc x y)
    catalogD_nonneg catalogCandidate_coefficient_lt_one catalogD_bounds
    catalogCandidateWeight_isFullSupport catalogPrior_isFullSupport
    catalogTransitionPrior_isFullSupport
    catalogTransitionWeight_isFullSupport
    catalogTransitionTilt_pos catalogTransitionTilt_lt_one
    (deltaRisk := (1 : ℝ) / 4) (deltaTransition := (1 : ℝ) / 4)
    (by norm_num) (by norm_num)
    catalogSelector catalogDepthSelector catalogRiskTiltSelector
    catalogTransitionTiltSelector catalogPosterior catalogPosterior_isPMF
  norm_num at h ⊢
  exact h

/-! ## Exact numerical terms and branch receipts -/

theorem catalogTrue_depthTwo_span :
    empiricalStationaryCatalogSpan catalogCandidate catalogD false 2 =
      5 / 16 := by
  norm_num [empiricalStationaryCatalogSpan, catalogCandidate, catalogD,
    catalogTrue_dobrushin, finiteDepthPoissonClosedSpanBound]

theorem catalogTrue_depthTwo_residual :
    finiteDobrushinCoefficient (catalogCandidate false) ^ 2 *
        catalogD false = 1 / 64 := by
  norm_num [catalogCandidate, catalogD, catalogTrue_dobrushin]

theorem catalogFair_depthTwo_span :
    empiricalStationaryCatalogSpan catalogCandidate catalogD true 2 = 0 := by
  norm_num [empiricalStationaryCatalogSpan, catalogCandidate, catalogD,
    catalogFair_dobrushin, finiteDepthPoissonClosedSpanBound]

theorem catalogFair_depthTwo_residual :
    finiteDobrushinCoefficient (catalogCandidate true) ^ 2 *
        catalogD true = 0 := by
  norm_num [catalogCandidate, catalogD, catalogFair_dobrushin]

theorem catalogTrue_depthTwo_atom_budget :
    (1 / 4 : ℝ) * catalogCandidateWeight false *
        polynomialForwardTiltWeight 2 = 1 / 96 := by
  norm_num [catalogCandidateWeight, polynomialForwardTiltWeight,
    FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight]

/-- Alternating prefix `false,true,false,true,false`, then `false`. -/
def catalogFalseBranchPath : ℕ → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true
  | _ => false

/-- Prefix `false,true,false,false,true`, then `true`. -/
def catalogTrueBranchPath : ℕ → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => false
  | _ => true

theorem catalogFalseBranch_allRowsVisited :
    ∀ z : Bool, 0 < transitionVisitMass z 4 catalogFalseBranchPath := by
  intro z
  cases z <;>
    norm_num [transitionVisitMass, catalogFalseBranchPath,
      Finset.sum_range_succ]

theorem catalogTrueBranch_allRowsVisited :
    ∀ z : Bool, 0 < transitionVisitMass z 4 catalogTrueBranchPath := by
  intro z
  cases z <;>
    norm_num [transitionVisitMass, catalogTrueBranchPath,
      Finset.sum_range_succ]

theorem catalogSelector_false_branch :
    catalogSelector catalogFalseBranchPath 4 = false := by
  rfl

theorem catalogSelector_true_branch :
    catalogSelector catalogTrueBranchPath 4 = true := by
  rfl

/-- If the exact candidate has zero row-TV error, its depth-two deterministic
robust remainder is `1/64`. -/
theorem catalogTrue_depthTwo_zeroEta_remainder :
    finiteDobrushinCoefficient (catalogCandidate false) ^ 2 *
          catalogD false +
        2 * ((1 + empiricalStationaryCatalogSpan
          catalogCandidate catalogD false 2) * (0 : ℝ)) =
      1 / 64 := by
  rw [catalogTrue_depthTwo_residual, catalogTrue_depthTwo_span]
  norm_num

/-- At the actual maximum row-TV misspecification `1/4`, the fair candidate's
depth-two deterministic transfer remainder is `1/2`. -/
theorem catalogFair_depthTwo_quarterEta_remainder :
    finiteDobrushinCoefficient (catalogCandidate true) ^ 2 *
          catalogD true +
        2 * ((1 + empiricalStationaryCatalogSpan
          catalogCandidate catalogD true 2) * (1 / 4 : ℝ)) =
      1 / 2 := by
  rw [catalogFair_depthTwo_residual, catalogFair_depthTwo_span]
  norm_num

#check empiricalStationaryCatalogExceptionalEvent_mass_le
#check empiricalStationaryCatalog_allPosteriors_of_not_mem
#check exists_empiricalStationaryCatalog_event
#check exists_selectedEmpiricalStationaryCatalog_event
#check exists_selectedCanonicalEmpiricalStationaryCatalog_event

#print axioms empiricalStationaryCatalogExceptionalEvent_mass_le
#print axioms empiricalStationaryCatalog_allPosteriors_of_not_mem
#print axioms exists_empiricalStationaryCatalog_event
#print axioms exists_selectedEmpiricalStationaryCatalog_event
#print axioms exists_selectedCanonicalEmpiricalStationaryCatalog_event
#print axioms catalogCanonicalStationary_eq_displayed
#print axioms boolCatalog_sameData_certificate
#print axioms catalogTrue_depthTwo_zeroEta_remainder
#print axioms catalogFair_depthTwo_quarterEta_remainder

end

end FormalSLT.Examples.CheckEmpiricalStationaryCatalog
