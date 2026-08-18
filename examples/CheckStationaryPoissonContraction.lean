import FormalSLT.StochasticDynamics.StationaryPoissonDobrushin

/-!
# Finite-depth Poisson contraction receipt

The receipt uses the asymmetric Boolean chain
`P(false,true)=1/4`, `P(true,false)=1/2`, with invariant law `(2/3,1/3)`.
Its Markov operator contracts finite oscillation by exactly `alpha=1/4`.
For the next-state indicator score, the centered row risk has oscillation
`D=1/4`.  At depth `m=2`, the constructed potential has exact span `5/16`
and its exact Poisson residual is bounded by `1/64`.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.Examples.CheckStationaryPoissonContraction

open FormalSLT.StochasticDynamics

noncomputable section

def contractionBoolPMF (x : Bool) : PMF Bool :=
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

def contractionBoolStationary : PMF Bool :=
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

theorem contractionBoolStationary_invariant :
    IsInvariantPMF contractionBoolPMF contractionBoolStationary := by
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
  · simpa [PMF.bind_apply, tsum_fintype, contractionBoolPMF,
      contractionBoolStationary, PMF.ofFintype_apply, Fintype.sum_bool,
      add_comm, mul_comm] using hfalse
  · simpa [PMF.bind_apply, tsum_fintype, contractionBoolPMF,
      contractionBoolStationary, PMF.ofFintype_apply, Fintype.sum_bool,
      add_comm, mul_comm] using htrue

def contractionBoolScore (_x y : Bool) : ℝ := if y then 1 else 0

theorem contractionBoolScore_mem_Icc :
    ∀ x y, contractionBoolScore x y ∈ Set.Icc (0 : ℝ) 1 := by
  intro x y
  fin_cases y <;> norm_num [contractionBoolScore]

theorem contractionBool_stationaryRisk :
    stationaryMarkovRisk contractionBoolPMF contractionBoolStationary
      contractionBoolScore = 1 / 3 := by
  norm_num [stationaryMarkovRisk, markovRowRisk, contractionBoolPMF,
    contractionBoolStationary, contractionBoolScore, PMF.integral_eq_sum,
    PMF.ofFintype_apply, Fintype.sum_bool]

theorem contractionBool_centeredRowRisk (z : Bool) :
    centeredMarkovRowRisk contractionBoolPMF contractionBoolStationary
      contractionBoolScore z = if z then (1 / 6 : ℝ) else -(1 / 12) := by
  fin_cases z <;>
    norm_num [centeredMarkovRowRisk, stationaryMarkovRisk, markovRowRisk,
      contractionBoolPMF, contractionBoolStationary, contractionBoolScore,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

theorem contractionBool_finiteOscillation_centered :
    finiteOscillation
      (centeredMarkovRowRisk contractionBoolPMF contractionBoolStationary
        contractionBoolScore) = 1 / 4 := by
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [contractionBool_centeredRowRisk]
  · have h := abs_sub_le_finiteOscillation
      (centeredMarkovRowRisk contractionBoolPMF contractionBoolStationary
        contractionBoolScore) false true
    rw [contractionBool_centeredRowRisk, contractionBool_centeredRowRisk] at h
    norm_num at h ⊢
    exact h

theorem contractionBool_totalVariation_false_true :
    finitePMFTotalVariation (contractionBoolPMF false)
      (contractionBoolPMF true) = 1 / 4 := by
  norm_num [finitePMFTotalVariation, contractionBoolPMF,
    PMF.ofFintype_apply, Fintype.sum_bool]

/-- The computable Dobrushin coefficient recovers the sharp contraction
factor used by the original receipt. -/
theorem contractionBool_dobrushinCoefficient :
    finiteDobrushinCoefficient contractionBoolPMF = 1 / 4 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    fin_cases x <;> fin_cases y <;>
      norm_num [finitePMFTotalVariation, contractionBoolPMF,
        PMF.ofFintype_apply, Fintype.sum_bool]
  · rw [← contractionBool_totalVariation_false_true]
    exact finitePMFTotalVariation_le_finiteDobrushinCoefficient
      contractionBoolPMF false true

theorem contractionBool_oscillation_contraction :
    IsOscillationContraction contractionBoolPMF (1 / 4) := by
  rw [← contractionBool_dobrushinCoefficient]
  exact finiteDobrushinCoefficient_isOscillationContraction contractionBoolPMF

theorem contractionBool_indicator_finiteOscillation :
    finiteOscillation (fun z : Bool ↦ if z then (1 : ℝ) else 0) = 1 := by
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    fin_cases x <;> fin_cases y <;> norm_num
  · have h := abs_sub_le_finiteOscillation
      (fun z : Bool ↦ if z then (1 : ℝ) else 0) false true
    norm_num at h ⊢
    exact h

theorem contractionBool_indicator_mean_finiteOscillation :
    finiteOscillation
      (markovPotentialMean contractionBoolPMF
        (fun z : Bool ↦ if z then (1 : ℝ) else 0)) = 1 / 4 := by
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [markovPotentialMean, contractionBoolPMF,
        PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]
  · have h := abs_sub_le_finiteOscillation
      (markovPotentialMean contractionBoolPMF
        (fun z : Bool ↦ if z then (1 : ℝ) else 0)) false true
    norm_num [markovPotentialMean, contractionBoolPMF,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool] at h ⊢
    exact h

/-- The Boolean indicator attains equality in Dobrushin oscillation
contraction, so the coefficient `1/4` is sharp for this kernel. -/
theorem contractionBool_indicator_oscillation_equality :
    finiteOscillation
        (markovPotentialMean contractionBoolPMF
          (fun z : Bool ↦ if z then (1 : ℝ) else 0)) =
      finiteDobrushinCoefficient contractionBoolPMF *
        finiteOscillation (fun z : Bool ↦ if z then (1 : ℝ) else 0) := by
  rw [contractionBool_indicator_mean_finiteOscillation,
    contractionBool_dobrushinCoefficient,
    contractionBool_indicator_finiteOscillation]
  norm_num

theorem contractionBool_T_centered (z : Bool) :
    markovPotentialMean contractionBoolPMF
        (centeredMarkovRowRisk contractionBoolPMF contractionBoolStationary
          contractionBoolScore) z =
      if z then (1 / 24 : ℝ) else -(1 / 48) := by
  fin_cases z <;>
    norm_num [markovPotentialMean, contractionBoolPMF,
      contractionBool_centeredRowRisk, PMF.integral_eq_sum,
      PMF.ofFintype_apply, Fintype.sum_bool]

theorem contractionBool_T2_centered (z : Bool) :
    markovPotentialMean contractionBoolPMF
        (markovPotentialMean contractionBoolPMF
          (centeredMarkovRowRisk contractionBoolPMF contractionBoolStationary
            contractionBoolScore)) z =
      if z then (1 / 96 : ℝ) else -(1 / 192) := by
  rw [show
      markovPotentialMean contractionBoolPMF
          (centeredMarkovRowRisk contractionBoolPMF contractionBoolStationary
            contractionBoolScore) =
        fun y ↦ if y then (1 / 24 : ℝ) else -(1 / 48) by
    funext y
    exact contractionBool_T_centered y]
  fin_cases z <;>
    norm_num [markovPotentialMean, contractionBoolPMF,
      PMF.integral_eq_sum,
      PMF.ofFintype_apply, Fintype.sum_bool]

theorem contractionBool_depthTwo_potential (z : Bool) :
    finiteDepthPoissonPotential contractionBoolPMF contractionBoolStationary
      contractionBoolScore 2 z = if z then (5 / 24 : ℝ) else -(5 / 48) := by
  fin_cases z <;>
    norm_num [finiteDepthPoissonPotential, iteratedMarkovPotentialMean,
      Finset.sum_range_succ, Function.iterate_zero_apply,
      Function.iterate_one, contractionBool_centeredRowRisk,
      contractionBool_T_centered]

theorem contractionBool_depthTwo_span :
    finiteDepthPoissonSpanBound (1 / 4) (1 / 4) 2 = 5 / 16 := by
  norm_num [finiteDepthPoissonSpanBound]

theorem contractionBool_depthTwo_residual_bound :
    finiteDepthPoissonResidualBound (1 / 4) (1 / 4) 2 = 1 / 64 := by
  norm_num [finiteDepthPoissonResidualBound]

theorem contractionBool_depthTwo_residual_values (z : Bool) :
    approximatePoissonResidual contractionBoolPMF contractionBoolStationary
        contractionBoolScore
        (finiteDepthPoissonPotential contractionBoolPMF
          contractionBoolStationary contractionBoolScore 2) z =
      if z then (1 / 96 : ℝ) else -(1 / 192) := by
  rw [finiteDepthPoisson_residual_identity]
  change markovPotentialMean contractionBoolPMF
      (markovPotentialMean contractionBoolPMF
        (centeredMarkovRowRisk contractionBoolPMF contractionBoolStationary
          contractionBoolScore)) z = _
  exact contractionBool_T2_centered z

theorem contractionBool_depthTwo_residual_le (z : Bool) :
    |approximatePoissonResidual contractionBoolPMF contractionBoolStationary
        contractionBoolScore
        (finiteDepthPoissonPotential contractionBoolPMF
          contractionBoolStationary contractionBoolScore 2) z| ≤ 1 / 64 := by
  rw [contractionBool_depthTwo_residual_values]
  fin_cases z <;> norm_num

def contractionBoolUniformPrior (_i : Bool) : ℝ := 1 / 2

theorem contractionBoolUniformPrior_isFullSupportPMF :
    IsFullSupportPMF contractionBoolUniformPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [contractionBoolUniformPrior]
  · norm_num [contractionBoolUniformPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [contractionBoolUniformPrior]

def contractionBoolTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem contractionBoolTiltWeight_isFullSupportPMF :
    IsFullSupportPMF contractionBoolTiltWeight := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j
    fin_cases j <;> norm_num [contractionBoolTiltWeight]
  · norm_num [contractionBoolTiltWeight, Fintype.sum_bool]
  · intro j
    fin_cases j <;> norm_num [contractionBoolTiltWeight]

def contractionBoolTilts (j : Bool) : ℝ := if j then 1 / 4 else 1 / 5

theorem contractionBoolTilts_pos (j : Bool) : 0 < contractionBoolTilts j := by
  fin_cases j <;> norm_num [contractionBoolTilts]

theorem contractionBoolTilts_lt_one (j : Bool) : contractionBoolTilts j < 1 := by
  fin_cases j <;> norm_num [contractionBoolTilts]

/-- Concrete all-time, all-posterior stationary-risk certificate with an
automatically constructed depth-two potential. -/
theorem contractionBool_depthTwo_stationary_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure contractionBoolPMF false).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk contractionBoolPMF
                  contractionBoolStationary (fun _i ↦ contractionBoolScore)
                  posterior <
                empiricalTransitionPosteriorRisk
                    (fun _i ↦ contractionBoolScore) posterior n x +
                  (1 + 2 * finiteDepthPoissonClosedSpanBound
                    (1 / 4) (1 / 4) 2) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      contractionBoolUniformPrior contractionBoolTiltWeight
                        contractionBoolTilts
                        (fun _i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonClosedSpanBound (1 / 4) (1 / 4) 2)
                          contractionBoolScore
                          (finiteDepthPoissonPotential contractionBoolPMF
                            contractionBoolStationary contractionBoolScore 2))
                        posterior (1 / 20) j n x +
                  finiteDepthPoissonClosedSpanBound (1 / 4) (1 / 4) 2 /
                      (n : ℝ) +
                    finiteDepthPoissonResidualBound (1 / 4) (1 / 4) 2 := by
  simpa only [contractionBool_dobrushinCoefficient] using
    (exists_stationaryFiniteDepthDobrushinEmpiricalBernsteinPACBayes_closed_event
      (I := Bool) (T := Bool)
      contractionBoolPMF contractionBoolStationary
      contractionBoolStationary_invariant false
      (score := fun _i ↦ contractionBoolScore)
      (fun _i ↦ contractionBoolScore_mem_Icc)
      (D := (1 / 4 : ℝ)) (by rw [contractionBool_dobrushinCoefficient]; norm_num)
      (by norm_num)
      (fun _i ↦ by rw [contractionBool_finiteOscillation_centered]) 2
      contractionBoolUniformPrior_isFullSupportPMF
      contractionBoolTiltWeight_isFullSupportPMF
      (by norm_num) contractionBoolTilts_pos contractionBoolTilts_lt_one)

#check finiteOscillation
#check finiteDepthPoissonPotential
#check finiteDepthPoisson_residual_identity
#check iteratedMarkovPotentialMean_oscillation_le
#check finiteDepthPoissonPotential_span
#check finiteDepthPoissonResidual_le
#check finiteDepthPoissonSpanBound_closed
#check exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_event
#check exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_closed_event
#check exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_unit_event
#check finitePMFTotalVariation
#check finiteDobrushinCoefficient
#check finiteDobrushinCoefficient_isOscillationContraction
#check exists_stationaryFiniteDepthDobrushinEmpiricalBernsteinPACBayes_closed_event
#check exists_stationaryFiniteDepthDobrushinEmpiricalBernsteinPACBayes_unit_event

#print axioms finiteDepthPoisson_residual_identity
#print axioms iteratedMarkovPotentialMean_oscillation_le
#print axioms finiteDepthPoissonPotential_span
#print axioms finiteDepthPoissonResidual_le
#print axioms exists_stationaryFiniteDepthPoissonEmpiricalBernsteinPACBayes_closed_event
#print axioms abs_finitePMFExpectation_sub_le_totalVariation_mul_oscillation
#print axioms finiteDobrushinCoefficient_isOscillationContraction
#print axioms exists_stationaryFiniteDepthDobrushinEmpiricalBernsteinPACBayes_closed_event

#check contractionBoolStationary_invariant
#check contractionBool_oscillation_contraction
#check contractionBool_dobrushinCoefficient
#check contractionBool_indicator_oscillation_equality
#check contractionBool_depthTwo_potential
#check contractionBool_depthTwo_residual_values
#check contractionBool_depthTwo_stationary_certificate

#print axioms contractionBoolStationary_invariant
#print axioms contractionBool_oscillation_contraction
#print axioms contractionBool_dobrushinCoefficient
#print axioms contractionBool_indicator_oscillation_equality
#print axioms contractionBool_depthTwo_potential
#print axioms contractionBool_depthTwo_residual_values
#print axioms contractionBool_depthTwo_stationary_certificate

end

end FormalSLT.Examples.CheckStationaryPoissonContraction
