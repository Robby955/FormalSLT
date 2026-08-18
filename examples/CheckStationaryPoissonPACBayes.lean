import FormalSLT.StochasticDynamics.StationaryPoissonPACBayes

/-!
# Supplied-Poisson stationary-risk receipt

The receipt uses an asymmetric Boolean Markov chain.  Its transition
probabilities are `false -> true = 1/4` and `true -> false = 1/2`, so its
invariant PMF is `(2/3, 1/3)`.  Two complementary next-state scores have
state-dependent row risks.  Nonconstant exact Poisson potentials flatten
their corrected conditional risks to `2/5` and `3/5`, respectively, and the
corrected scores genuinely attain both endpoints `0` and `1`.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Examples.CheckStationaryPoissonPACBayes

open FormalSLT.StochasticDynamics

noncomputable section

/-- Asymmetric transition matrix:
`P(false,true)=1/4` and `P(true,false)=1/2`. -/
def asymmetricBoolPMF (x : Bool) : PMF Bool :=
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

/-- The invariant PMF `(false,true)=(2/3,1/3)`. -/
def asymmetricBoolStationary : PMF Bool :=
  PMF.ofFintype
    (fun z ↦ if z then
      ((1 / 3 : NNReal) : ENNReal)
    else
      ((2 / 3 : NNReal) : ENNReal))
    (by
      have hstationaryNN : (1 / 3 : NNReal) + 2 / 3 = 1 := by norm_num
      have hstationary : ((1 / 3 : NNReal) : ENNReal) +
          ((2 / 3 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hstationaryNN]
        rfl
      simpa [Fintype.sum_bool, add_comm] using hstationary)

/-- Direct stationarity receipt for the asymmetric chain. -/
theorem asymmetricBoolStationary_invariant :
    IsInvariantPMF asymmetricBoolPMF asymmetricBoolStationary := by
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
  · simpa [PMF.bind_apply, tsum_fintype, asymmetricBoolPMF,
      asymmetricBoolStationary, PMF.ofFintype_apply, Fintype.sum_bool,
      add_comm, mul_comm] using hfalse
  · simpa [PMF.bind_apply, tsum_fintype, asymmetricBoolPMF,
      asymmetricBoolStationary, PMF.ofFintype_apply, Fintype.sum_bool,
      add_comm, mul_comm] using htrue

/-- Hypothesis `i` scores one exactly when the next state differs from `i`.
The two atoms are complementary, nonconstant transition scores. -/
def asymmetricBoolScore (i : Bool) : MarkovTransitionScore Bool :=
  fun _x y ↦ if y = i then 0 else 1

theorem asymmetricBoolScore_mem_Icc :
    ∀ i x y, asymmetricBoolScore i x y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i x y
  simp only [asymmetricBoolScore]
  split_ifs <;> norm_num

/-- Exact Poisson potentials.  The `false` score uses `(0,1/3)` and the
`true` score uses `(0,-1/3)` on `(false,true)`. -/
def asymmetricBoolPotential (i z : Bool) : ℝ :=
  if z then if i then -(1 / 3) else 1 / 3 else 0

theorem asymmetricBoolPotential_span :
    ∀ i x y, |asymmetricBoolPotential i y - asymmetricBoolPotential i x| ≤
      (1 / 3 : ℝ) := by
  intro i x y
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    norm_num [asymmetricBoolPotential]

/-- The two invariant risks are `1/3` and `2/3`. -/
theorem asymmetricBool_stationaryRisk (i : Bool) :
    stationaryMarkovRisk asymmetricBoolPMF asymmetricBoolStationary
        (asymmetricBoolScore i) =
      if i then (2 / 3 : ℝ) else 1 / 3 := by
  fin_cases i <;>
    norm_num [stationaryMarkovRisk, markovRowRisk,
      asymmetricBoolPMF, asymmetricBoolStationary, asymmetricBoolScore,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

/-- Both nonconstant potentials solve their Poisson equations exactly. -/
theorem asymmetricBoolPotential_exact (i : Bool) :
    IsExactPoissonSolution asymmetricBoolPMF asymmetricBoolStationary
      (asymmetricBoolScore i) (asymmetricBoolPotential i) := by
  intro z
  fin_cases i <;> fin_cases z <;>
    norm_num [IsExactPoissonSolution, approximatePoissonResidual,
      stationaryMarkovRisk, markovRowRisk, markovPotentialMean,
      asymmetricBoolPMF, asymmetricBoolStationary, asymmetricBoolScore,
      asymmetricBoolPotential, PMF.integral_eq_sum, PMF.ofFintype_apply,
      Fintype.sum_bool]

/-- The affine correction is substantive: for the `false` score it attains
both `0` and `1` on transitions of the asymmetric chain. -/
theorem asymmetricBool_corrected_endpoint_witness :
    poissonCorrectedTransitionScore (1 / 3)
        (asymmetricBoolScore false) (asymmetricBoolPotential false)
        false true = 1 ∧
      poissonCorrectedTransitionScore (1 / 3)
        (asymmetricBoolScore false) (asymmetricBoolPotential false)
        true false = 0 := by
  constructor <;>
    norm_num [poissonCorrectedTransitionScore, asymmetricBoolScore,
      asymmetricBoolPotential]

/-- The corrected row means are constant even though the original row risks
are state-dependent. -/
theorem asymmetricBool_corrected_rowRisk (i z : Bool) :
    markovRowRisk asymmetricBoolPMF
        (poissonCorrectedTransitionScore (1 / 3)
          (asymmetricBoolScore i) (asymmetricBoolPotential i)) z =
      if i then (3 / 5 : ℝ) else 2 / 5 := by
  fin_cases i <;> fin_cases z <;>
    norm_num [markovRowRisk, poissonCorrectedTransitionScore,
      asymmetricBoolPMF, asymmetricBoolScore, asymmetricBoolPotential,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

def stationaryBoolUniformPrior (_i : Bool) : ℝ := 1 / 2

theorem stationaryBoolUniformPrior_isFullSupportPMF :
    IsFullSupportPMF stationaryBoolUniformPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [stationaryBoolUniformPrior]
  · norm_num [stationaryBoolUniformPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [stationaryBoolUniformPrior]

def stationaryBoolTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem stationaryBoolTiltWeight_isFullSupportPMF :
    IsFullSupportPMF stationaryBoolTiltWeight := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    fin_cases j <;> norm_num [stationaryBoolTiltWeight]
  · norm_num [stationaryBoolTiltWeight, Fintype.sum_bool]
  · intro j
    fin_cases j <;> norm_num [stationaryBoolTiltWeight]

def stationaryBoolTilts (j : Bool) : ℝ := if j then 1 / 4 else 1 / 5

theorem stationaryBoolTilts_pos (j : Bool) : 0 < stationaryBoolTilts j := by
  fin_cases j <;> norm_num [stationaryBoolTilts]

theorem stationaryBoolTilts_lt_one (j : Bool) : stationaryBoolTilts j < 1 := by
  fin_cases j <;> norm_num [stationaryBoolTilts]

/-- Concrete all-time, all-posterior stationary-risk certificate for the
asymmetric chain.  The only Poisson endpoint price is `1/(3n)`; the
empirical-Bernstein width is computed from the corrected observed scores. -/
theorem asymmetricBool_stationaryExactPoisson_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure asymmetricBoolPMF false).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk
                  asymmetricBoolPMF asymmetricBoolStationary
                    asymmetricBoolScore posterior <
                empiricalTransitionPosteriorRisk
                    asymmetricBoolScore posterior n x +
                  (1 + 2 * (1 / 3 : ℝ)) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      stationaryBoolUniformPrior stationaryBoolTiltWeight
                        stationaryBoolTilts
                        (fun i ↦ poissonCorrectedTrajectoryScore (1 / 3)
                          (asymmetricBoolScore i) (asymmetricBoolPotential i))
                        posterior (1 / 20) j n x +
                  (1 / 3 : ℝ) / (n : ℝ) := by
  exact exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_span_event
    (ι := Bool) (τ := Bool)
    asymmetricBoolPMF asymmetricBoolStationary
    asymmetricBoolStationary_invariant false
    asymmetricBoolScore_mem_Icc (by norm_num) asymmetricBoolPotential_span
    asymmetricBoolPotential_exact
    stationaryBoolUniformPrior_isFullSupportPMF
    stationaryBoolTiltWeight_isFullSupportPMF
    (lam := stationaryBoolTilts) (delta := (1 / 20 : ℝ))
    (by norm_num) stationaryBoolTilts_pos stationaryBoolTilts_lt_one

/-! Public endpoint and receipt audit. -/

#check IsInvariantPMF
#check markovRowRisk
#check stationaryMarkovRisk
#check approximatePoissonResidual
#check poissonCorrectedTransitionScore
#check conditionalTrajectoryRisk_poissonCorrectedTrajectoryScore
#check sum_poissonPotential_increment
#check trajectoryEmpiricalPrequentialRisk_poissonCorrected
#check stationaryPoissonEmpiricalBernsteinPACBayesBoundary
#check exists_stationaryPoissonEmpiricalBernsteinPACBayes_event
#check exists_stationaryPoissonEmpiricalBernsteinPACBayes_envelope_event
#check exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_event
#check exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_span_event

#print axioms conditionalTrajectoryRisk_poissonCorrectedTrajectoryScore
#print axioms sum_poissonPotential_increment
#print axioms trajectoryEmpiricalPrequentialRisk_poissonCorrected
#print axioms exists_stationaryPoissonEmpiricalBernsteinPACBayes_event
#print axioms exists_stationaryPoissonEmpiricalBernsteinPACBayes_envelope_event
#print axioms exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_event
#print axioms exists_stationaryExactPoissonEmpiricalBernsteinPACBayes_span_event

#check asymmetricBoolStationary_invariant
#check asymmetricBool_stationaryRisk
#check asymmetricBoolPotential_exact
#check asymmetricBool_corrected_endpoint_witness
#check asymmetricBool_corrected_rowRisk
#check asymmetricBool_stationaryExactPoisson_certificate

#print axioms asymmetricBoolStationary_invariant
#print axioms asymmetricBool_stationaryRisk
#print axioms asymmetricBoolPotential_exact
#print axioms asymmetricBool_corrected_endpoint_witness
#print axioms asymmetricBool_corrected_rowRisk
#print axioms asymmetricBool_stationaryExactPoisson_certificate

end

end FormalSLT.Examples.CheckStationaryPoissonPACBayes
