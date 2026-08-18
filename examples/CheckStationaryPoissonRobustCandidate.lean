import FormalSLT.StochasticDynamics.StationaryPoissonRobustCandidate

/-!
# Robust candidate-kernel Poisson receipt

The true Boolean kernel is the identity kernel while the fixed candidate has
two fair rows.  The supplied true invariant law is concentrated at `true`,
the score is the next-state indicator, and the potential is zero.  Every true
row is at probabilists' TV distance `1/2` from its candidate row.

The candidate drift is constant `1/2`, but the true stationary-centered
residual at `false` has absolute value `1`.  Thus a factor-one transfer price
would give only `1/2` and is false; the theorem's doubled price is attained
exactly.  The same genuinely misspecified pair also instantiates the
finite-depth empirical-Bernstein PAC-Bayes event.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL

namespace FormalSLT.Examples.CheckStationaryPoissonRobustCandidate

open FormalSLT.StochasticDynamics

noncomputable section

/-- True identity transition kernel. -/
def robustBoolTrueKernel (x : Bool) : PMF Bool :=
  PMF.ofFintype (fun y ↦ if y = x then 1 else 0) (by
    cases x <;> simp)

/-- Fixed candidate kernel with two fair rows. -/
def robustBoolCandidateKernel (_x : Bool) : PMF Bool :=
  PMF.ofFintype (fun _y ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
    have h : ((1 / 2 : NNReal) : ENNReal) +
        ((1 / 2 : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_add, hNN]
      rfl
    simpa [Fintype.sum_bool, two_mul] using h)

/-- Supplied invariant law of the true kernel, concentrated at `true`. -/
def robustBoolStationary : PMF Bool :=
  PMF.ofFintype (fun z ↦ if z then 1 else 0) (by
    simp)

theorem robustBoolStationary_invariant :
    IsInvariantPMF robustBoolTrueKernel robustBoolStationary := by
  unfold IsInvariantPMF
  apply PMF.ext
  intro y
  fin_cases y <;>
    simp [PMF.bind_apply, tsum_fintype, robustBoolTrueKernel,
      robustBoolStationary]

def robustBoolScore (_x y : Bool) : ℝ := if y then 1 else 0

theorem robustBoolScore_mem_Icc :
    ∀ x y, robustBoolScore x y ∈ Set.Icc (0 : ℝ) 1 := by
  intro x y
  fin_cases y <;> norm_num [robustBoolScore]

def robustBoolPotential (_z : Bool) : ℝ := 0

theorem robustBoolPotential_span :
    ∀ x y, |robustBoolPotential y - robustBoolPotential x| ≤ (0 : ℝ) := by
  intro x y
  norm_num [robustBoolPotential]

theorem robustBool_rowTV (z : Bool) :
    finitePMFTotalVariation (robustBoolTrueKernel z)
      (robustBoolCandidateKernel z) = 1 / 2 := by
  fin_cases z <;>
    norm_num [finitePMFTotalVariation, robustBoolTrueKernel,
      robustBoolCandidateKernel, PMF.ofFintype_apply, Fintype.sum_bool]

theorem robustBool_candidateDrift (z : Bool) :
    markovPoissonDrift robustBoolCandidateKernel robustBoolScore
      robustBoolPotential z = 1 / 2 := by
  fin_cases z <;>
    norm_num [markovPoissonDrift, markovRowRisk, markovPotentialMean,
      robustBoolCandidateKernel, robustBoolScore, robustBoolPotential,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

theorem robustBool_trueDrift (z : Bool) :
    markovPoissonDrift robustBoolTrueKernel robustBoolScore
      robustBoolPotential z = if z then 1 else 0 := by
  fin_cases z <;>
    norm_num [markovPoissonDrift, markovRowRisk, markovPotentialMean,
      robustBoolTrueKernel, robustBoolScore, robustBoolPotential,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

theorem robustBool_stationaryRisk :
    stationaryMarkovRisk robustBoolTrueKernel robustBoolStationary
      robustBoolScore = 1 := by
  norm_num [stationaryMarkovRisk, markovRowRisk, robustBoolTrueKernel,
    robustBoolStationary, robustBoolScore, PMF.integral_eq_sum,
    PMF.ofFintype_apply, Fintype.sum_bool]

theorem robustBool_false_residual :
    approximatePoissonResidual robustBoolTrueKernel robustBoolStationary
      robustBoolScore robustBoolPotential false = -1 := by
  rw [approximatePoissonResidual_eq_markovPoissonDrift_sub,
    robustBool_trueDrift, robustBool_stationaryRisk]
  norm_num

theorem robustBool_candidateDrift_oscillation :
    finiteOscillation
      (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
        robustBoolPotential) = 0 := by
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    rw [robustBool_candidateDrift, robustBool_candidateDrift]
    norm_num
  · exact finiteOscillation_nonneg _

/-- A same-constant absolute transfer is false: its right side is `1/2`
while the true residual is `1`. -/
theorem robustBool_factorOne_transfer_false :
    finiteOscillation
        (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
          robustBoolPotential) +
        (1 + 0) * (1 / 2 : ℝ) <
      |approximatePoissonResidual robustBoolTrueKernel robustBoolStationary
        robustBoolScore robustBoolPotential false| := by
  rw [robustBool_candidateDrift_oscillation, robustBool_false_residual]
  norm_num

/-- The corrected doubled misspecification price is attained exactly. -/
theorem robustBool_factorTwo_transfer_sharp :
    |approximatePoissonResidual robustBoolTrueKernel robustBoolStationary
        robustBoolScore robustBoolPotential false| =
      finiteOscillation
          (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
            robustBoolPotential) +
        2 * ((1 + 0) * (1 / 2 : ℝ)) := by
  rw [robustBool_candidateDrift_oscillation, robustBool_false_residual]
  norm_num

/-- The general robust theorem reproduces the sharp Boolean receipt. -/
theorem robustBool_factorTwo_transfer_checked :
    |approximatePoissonResidual robustBoolTrueKernel robustBoolStationary
        robustBoolScore robustBoolPotential false| ≤
      finiteOscillation
          (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
            robustBoolPotential) +
        2 * ((1 + 0) * (1 / 2 : ℝ)) := by
  exact abs_stationaryPoissonResidual_le_candidateOscillation
    robustBoolTrueKernel robustBoolCandidateKernel robustBoolStationary
    robustBoolStationary_invariant (by norm_num)
    robustBoolScore_mem_Icc robustBoolPotential_span
    (fun z ↦ by rw [robustBool_rowTV]) false

theorem robustBool_candidateDobrushin :
    finiteDobrushinCoefficient robustBoolCandidateKernel = 0 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    norm_num [finitePMFTotalVariation, robustBoolCandidateKernel,
      PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteDobrushinCoefficient_nonneg _

theorem robustBool_candidateCenteredOscillation_zero :
    finiteOscillation
      (centeredMarkovRowRisk robustBoolCandidateKernel robustBoolStationary
        robustBoolScore) = 0 := by
  apply le_antisymm
  · apply finiteOscillation_le
    intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [centeredMarkovRowRisk, stationaryMarkovRisk, markovRowRisk,
        robustBoolCandidateKernel, robustBoolStationary, robustBoolScore,
        PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteOscillation_nonneg _

def robustBoolUniform (_b : Bool) : ℝ := 1 / 2

theorem robustBoolUniform_isFullSupportPMF :
    IsFullSupportPMF robustBoolUniform := by
  constructor
  · constructor
    · intro b
      norm_num [robustBoolUniform]
    · norm_num [robustBoolUniform, Fintype.sum_bool]
  · intro b
    norm_num [robustBoolUniform]

def robustBoolTilt (_j : Bool) : ℝ := 1 / 2

theorem robustBoolTilt_pos : ∀ j, 0 < robustBoolTilt j := by
  intro j
  norm_num [robustBoolTilt]

theorem robustBoolTilt_lt_one : ∀ j, robustBoolTilt j < 1 := by
  intro j
  norm_num [robustBoolTilt]

/-- The genuinely misspecified pair instantiates the automatic finite-depth
empirical-Bernstein PAC-Bayes event. -/
theorem robustBool_finiteDepth_stationary_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure robustBoolTrueKernel false).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk robustBoolTrueKernel
                  robustBoolStationary (fun _i ↦ robustBoolScore) posterior <
                empiricalTransitionPosteriorRisk
                    (fun _i ↦ robustBoolScore) posterior n x +
                  (1 + 2 * finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient robustBoolCandidateKernel) 0 1) *
                    trajectoryEmpiricalBernsteinPACBayesBoundary
                      robustBoolUniform robustBoolUniform robustBoolTilt
                        (fun _i ↦ poissonCorrectedTrajectoryScore
                          (finiteDepthPoissonClosedSpanBound
                            (finiteDobrushinCoefficient robustBoolCandidateKernel) 0 1)
                          robustBoolScore
                          (finiteDepthPoissonPotential robustBoolCandidateKernel
                            robustBoolStationary robustBoolScore 1))
                        posterior (1 / 20) j n x +
                  finiteDepthPoissonClosedSpanBound
                    (finiteDobrushinCoefficient robustBoolCandidateKernel) 0 1 /
                      (n : ℝ) +
                  ((finiteDobrushinCoefficient robustBoolCandidateKernel) ^ 1 * 0 +
                    2 * ((1 + finiteDepthPoissonClosedSpanBound
                      (finiteDobrushinCoefficient robustBoolCandidateKernel) 0 1) *
                        (1 / 2 : ℝ))) := by
  exact exists_stationaryRobustCandidateFiniteDepthDobrushinPACBayes_event
    (I := Bool) (T := Bool)
    robustBoolTrueKernel robustBoolCandidateKernel robustBoolStationary
    robustBoolStationary robustBoolStationary_invariant false
    (score := fun _i ↦ robustBoolScore)
    (fun _i ↦ robustBoolScore_mem_Icc)
    (D := (0 : ℝ)) (eta := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (fun z ↦ by rw [robustBool_rowTV])
    (by rw [robustBool_candidateDobrushin]; norm_num)
    (fun _i ↦ by rw [robustBool_candidateCenteredOscillation_zero]) 1
    robustBoolUniform_isFullSupportPMF robustBoolUniform_isFullSupportPMF
    (by norm_num) robustBoolTilt_pos robustBoolTilt_lt_one

#check markovPoissonDrift
#check abs_markovPoissonDrift_sub_candidate_le
#check abs_stationaryPoissonResidual_le_candidateOscillation
#check neg_poissonResidualAverage_le_candidateMaxGapAverage
#check exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_event
#check exists_stationaryRobustCandidateFiniteDepthDobrushinPACBayes_event

#print axioms abs_markovPoissonDrift_sub_candidate_le
#print axioms abs_stationaryPoissonResidual_le_candidateOscillation
#print axioms neg_poissonResidualAverage_le_candidateMaxGapAverage
#print axioms exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_event
#print axioms exists_stationaryRobustCandidateFiniteDepthDobrushinPACBayes_event

#check robustBool_factorOne_transfer_false
#check robustBool_factorTwo_transfer_sharp
#check robustBool_factorTwo_transfer_checked
#check robustBool_finiteDepth_stationary_certificate

#print axioms robustBool_factorOne_transfer_false
#print axioms robustBool_factorTwo_transfer_sharp
#print axioms robustBool_factorTwo_transfer_checked
#print axioms robustBool_finiteDepth_stationary_certificate

end

end FormalSLT.Examples.CheckStationaryPoissonRobustCandidate
