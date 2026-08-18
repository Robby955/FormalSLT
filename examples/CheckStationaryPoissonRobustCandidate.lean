import FormalSLT.StochasticDynamics.StationaryPoissonRobustCandidate

/-!
# Robust candidate-kernel Poisson receipts

The first receipt is deliberately nonergodic: the true Boolean kernel is the
identity kernel while the fixed candidate has two fair rows.  The supplied
true invariant law is concentrated at `true`, the score is the next-state
indicator, and the potential is zero.  Every true row is at probabilists' TV
distance `1/2` from its candidate row.

The candidate drift is constant `1/2`, but the true stationary-centered
residual at `false` has absolute value `1`.  Thus a factor-one transfer price
would give only `1/2` and is false; the theorem's doubled price is attained
exactly.  This is a sharpness counterexample, not an ergodic application.

The second receipt uses a full-support symmetric true kernel with persistence
probability `3/4` against the same fair-row candidate.  Its unique invariant
law is fair and gives positive mass to the declared start.  The kernels differ,
their maximum row TV is `1/4`, and the true residual at `false` is `-1/4`.
It instantiates the path-adaptive empirical-Bernstein PAC-Bayes event.
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

/-- The nonergodic sharpness pair also instantiates the automatic finite-depth
event.  This checks theorem plumbing; the ergodic receipt below is the intended
finite-certificate application. -/
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

/-! ## Ergodic misspecification receipt -/

/-- Full-support symmetric true kernel: stay with probability `3/4` and switch
with probability `1/4`. -/
def ergodicBoolTrueKernel (x : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if y = x then
      ((3 / 4 : NNReal) : ENNReal)
    else
      ((1 / 4 : NNReal) : ENNReal))
    (by
      have hNN : (1 / 4 : NNReal) + 3 / 4 = 1 := by norm_num
      have h : ((1 / 4 : NNReal) : ENNReal) +
          ((3 / 4 : NNReal) : ENNReal) = 1 := by
        rw [← ENNReal.coe_add, hNN]
        rfl
      cases x <;> simpa [Fintype.sum_bool, add_comm] using h)

/-- The fair law, written separately to make its role as the true invariant
law explicit. -/
def ergodicBoolStationary : PMF Bool :=
  robustBoolCandidateKernel false

theorem ergodicBoolTrueKernel_fullSupport (x y : Bool) :
    0 < (ergodicBoolTrueKernel x y).toReal := by
  fin_cases x <;> fin_cases y <;>
    norm_num [ergodicBoolTrueKernel, PMF.ofFintype_apply]

theorem ergodicBoolStationary_fullSupport (z : Bool) :
    0 < (ergodicBoolStationary z).toReal := by
  fin_cases z <;>
    norm_num [ergodicBoolStationary, robustBoolCandidateKernel,
      PMF.ofFintype_apply]

theorem ergodicBoolStationary_startMass :
    (ergodicBoolStationary false).toReal = 1 / 2 := by
  norm_num [ergodicBoolStationary, robustBoolCandidateKernel,
    PMF.ofFintype_apply]

theorem ergodicBoolStationary_invariant :
    IsInvariantPMF ergodicBoolTrueKernel ergodicBoolStationary := by
  have hNN :
      (1 / 2 : NNReal) * (3 / 4) + (1 / 2) * (1 / 4) = 1 / 2 := by
    norm_num
  have h :
      ((1 / 2 : NNReal) : ENNReal) * ((3 / 4 : NNReal) : ENNReal) +
          ((1 / 2 : NNReal) : ENNReal) * ((1 / 4 : NNReal) : ENNReal) =
        ((1 / 2 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) hNN
  unfold IsInvariantPMF
  apply PMF.ext
  intro y
  cases y
  · simpa [PMF.bind_apply, tsum_fintype, ergodicBoolTrueKernel,
      ergodicBoolStationary, robustBoolCandidateKernel,
      PMF.ofFintype_apply, Fintype.sum_bool, add_comm] using h
  · simpa [PMF.bind_apply, tsum_fintype, ergodicBoolTrueKernel,
      ergodicBoolStationary, robustBoolCandidateKernel,
      PMF.ofFintype_apply, Fintype.sum_bool, add_comm] using h

/-- The supplied fair invariant law is the only invariant PMF of the
full-support true kernel. -/
theorem ergodicBoolStationary_unique (stationary : PMF Bool)
    (hstationary : IsInvariantPMF ergodicBoolTrueKernel stationary) :
    stationary = ergodicBoolStationary := by
  have hinvariant := markovPotentialMean_invariant
    ergodicBoolTrueKernel stationary hstationary
      (fun z : Bool ↦ if z then (1 : ℝ) else 0)
  have hmass :
      (stationary true).toReal + (stationary false).toReal = 1 := by
    simpa [Fintype.sum_bool] using finitePMF_real_mass_sum stationary
  have hbalance :
      (stationary true).toReal * (3 / 4 : ℝ) +
          (stationary false).toReal * (1 / 4 : ℝ) =
        (stationary true).toReal := by
    simpa [markovPotentialMean, PMF.integral_eq_sum,
      ergodicBoolTrueKernel, PMF.ofFintype_apply, Fintype.sum_bool] using
        hinvariant
  have hfalse : (stationary false).toReal = 1 / 2 := by linarith
  have htrue : (stationary true).toReal = 1 / 2 := by linarith
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top stationary z)
    (PMF.apply_ne_top ergodicBoolStationary z)).mp
  cases z
  · simpa [ergodicBoolStationary, robustBoolCandidateKernel,
      PMF.ofFintype_apply] using hfalse
  · simpa [ergodicBoolStationary, robustBoolCandidateKernel,
      PMF.ofFintype_apply] using htrue

theorem ergodicBool_kernels_ne :
    ergodicBoolTrueKernel ≠ robustBoolCandidateKernel := by
  intro heq
  have h := congrArg
    (fun K : Bool → PMF Bool ↦ (K false true).toReal) heq
  norm_num [ergodicBoolTrueKernel, robustBoolCandidateKernel,
    PMF.ofFintype_apply] at h

theorem ergodicBool_rowTV (z : Bool) :
    finitePMFTotalVariation (ergodicBoolTrueKernel z)
      (robustBoolCandidateKernel z) = 1 / 4 := by
  fin_cases z <;>
    norm_num [finitePMFTotalVariation, ergodicBoolTrueKernel,
      robustBoolCandidateKernel, PMF.ofFintype_apply, Fintype.sum_bool]

theorem ergodicBool_trueDrift (z : Bool) :
    markovPoissonDrift ergodicBoolTrueKernel robustBoolScore
      robustBoolPotential z = if z then (3 / 4 : ℝ) else 1 / 4 := by
  fin_cases z <;>
    norm_num [markovPoissonDrift, markovRowRisk, markovPotentialMean,
      ergodicBoolTrueKernel, robustBoolScore, robustBoolPotential,
      PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

theorem ergodicBool_stationaryRisk :
    stationaryMarkovRisk ergodicBoolTrueKernel ergodicBoolStationary
      robustBoolScore = 1 / 2 := by
  norm_num [stationaryMarkovRisk, markovRowRisk, ergodicBoolTrueKernel,
    ergodicBoolStationary, robustBoolCandidateKernel, robustBoolScore,
    PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

theorem ergodicBool_false_residual :
    approximatePoissonResidual ergodicBoolTrueKernel ergodicBoolStationary
      robustBoolScore robustBoolPotential false = -(1 / 4 : ℝ) := by
  rw [approximatePoissonResidual_eq_markovPoissonDrift_sub,
    ergodicBool_trueDrift, ergodicBool_stationaryRisk]
  norm_num

/-- The ergodic receipt has a nonzero true residual and a finite robust
certificate with `eta=1/4`. -/
theorem ergodicBool_residual_certificate :
    |approximatePoissonResidual ergodicBoolTrueKernel ergodicBoolStationary
        robustBoolScore robustBoolPotential false| ≤
      finiteOscillation
          (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
            robustBoolPotential) +
        2 * ((1 + 0) * (1 / 4 : ℝ)) := by
  exact abs_stationaryPoissonResidual_le_candidateOscillation
    ergodicBoolTrueKernel robustBoolCandidateKernel ergodicBoolStationary
    ergodicBoolStationary_invariant (by norm_num)
    robustBoolScore_mem_Icc robustBoolPotential_span
    (fun z ↦ by rw [ergodicBool_rowTV]) false

/-- Concrete finite values for the ergodic receipt: the actual residual is
`1/4`, while the certified robust envelope is `1/2`. -/
theorem ergodicBool_residual_certificate_values :
    |approximatePoissonResidual ergodicBoolTrueKernel ergodicBoolStationary
        robustBoolScore robustBoolPotential false| = 1 / 4 ∧
      finiteOscillation
          (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
            robustBoolPotential) +
        2 * ((1 + 0) * (1 / 4 : ℝ)) = 1 / 2 := by
  constructor
  · rw [ergodicBool_false_residual]
    norm_num
  · rw [robustBool_candidateDrift_oscillation]
    norm_num

theorem ergodicBool_candidateMaxGapAverage_zero (n : ℕ) (x : ℕ → Bool) :
    candidatePoissonMaxGapAverage robustBoolCandidateKernel robustBoolScore
      robustBoolPotential n x = 0 := by
  have hmax : finiteMaximum
      (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
        robustBoolPotential) = 1 / 2 := by
    apply le_antisymm
    · unfold finiteMaximum
      apply Finset.sup'_le Finset.univ_nonempty
      intro z _hz
      rw [robustBool_candidateDrift]
    · simpa [robustBool_candidateDrift] using
        le_finiteMaximum
          (markovPoissonDrift robustBoolCandidateKernel robustBoolScore
            robustBoolPotential) false
  unfold candidatePoissonMaxGapAverage runningMean runningSum
  simp [hmax, robustBool_candidateDrift]

/-- Full-support ergodic `Q ≠ P` path-adaptive PAC-Bayes receipt.  The event
accepts the explicitly proved unique invariant law; it does not estimate the
kernel or discover that law. -/
theorem ergodicBool_path_stationary_certificate :
    ∃ goodEvent : Set (ℕ → Bool),
      (markovPathMeasure ergodicBoolTrueKernel false).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              stationaryPosteriorMarkovRisk ergodicBoolTrueKernel
                  ergodicBoolStationary (fun _i ↦ robustBoolScore) posterior <
                empiricalTransitionPosteriorRisk
                    (fun _i ↦ robustBoolScore) posterior n x +
                  trajectoryEmpiricalBernsteinPACBayesBoundary
                    robustBoolUniform robustBoolUniform robustBoolTilt
                      (fun _i ↦ poissonCorrectedTrajectoryScore
                        0 robustBoolScore robustBoolPotential)
                      posterior (1 / 20) j n x +
                  posteriorCandidatePoissonMaxGapAverage
                    robustBoolCandidateKernel (fun _i ↦ robustBoolScore)
                      (fun _i ↦ robustBoolPotential) posterior n x +
                  2 * ((1 + 0) * (1 / 4 : ℝ)) := by
  simpa using
    (exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_path_event
      (I := Bool) (T := Bool)
      ergodicBoolTrueKernel robustBoolCandidateKernel ergodicBoolStationary
      ergodicBoolStationary_invariant false
      (score := fun _i ↦ robustBoolScore)
      (fun _i ↦ robustBoolScore_mem_Icc)
      (potential := fun _i ↦ robustBoolPotential)
      (B := (0 : ℝ)) (eta := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      (fun _i ↦ robustBoolPotential_span)
      (fun z ↦ by rw [ergodicBool_rowTV])
      robustBoolUniform_isFullSupportPMF robustBoolUniform_isFullSupportPMF
      (by norm_num) robustBoolTilt_pos robustBoolTilt_lt_one)

#check markovPoissonDrift
#check abs_markovPoissonDrift_sub_candidate_le
#check abs_stationaryPoissonResidual_le_candidateOscillation
#check neg_poissonResidualAverage_le_candidateMaxGapAverage
#check neg_posteriorPoissonResidualAverage_le_candidateMaxGapAverage
#check exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_path_event
#check exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_event
#check exists_stationaryRobustCandidateFiniteDepthDobrushinPACBayes_event

#print axioms abs_markovPoissonDrift_sub_candidate_le
#print axioms abs_stationaryPoissonResidual_le_candidateOscillation
#print axioms neg_poissonResidualAverage_le_candidateMaxGapAverage
#print axioms neg_posteriorPoissonResidualAverage_le_candidateMaxGapAverage
#print axioms exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_path_event
#print axioms exists_stationaryRobustCandidatePoissonEmpiricalBernsteinPACBayes_event
#print axioms exists_stationaryRobustCandidateFiniteDepthDobrushinPACBayes_event

#check robustBool_factorOne_transfer_false
#check robustBool_factorTwo_transfer_sharp
#check robustBool_factorTwo_transfer_checked
#check robustBool_finiteDepth_stationary_certificate
#check ergodicBoolTrueKernel_fullSupport
#check ergodicBoolStationary_fullSupport
#check ergodicBoolStationary_startMass
#check ergodicBoolStationary_invariant
#check ergodicBoolStationary_unique
#check ergodicBool_kernels_ne
#check ergodicBool_rowTV
#check ergodicBool_residual_certificate
#check ergodicBool_residual_certificate_values
#check ergodicBool_candidateMaxGapAverage_zero
#check ergodicBool_path_stationary_certificate

#print axioms robustBool_factorOne_transfer_false
#print axioms robustBool_factorTwo_transfer_sharp
#print axioms robustBool_factorTwo_transfer_checked
#print axioms robustBool_finiteDepth_stationary_certificate
#print axioms ergodicBoolTrueKernel_fullSupport
#print axioms ergodicBoolStationary_fullSupport
#print axioms ergodicBoolStationary_startMass
#print axioms ergodicBoolStationary_invariant
#print axioms ergodicBoolStationary_unique
#print axioms ergodicBool_kernels_ne
#print axioms ergodicBool_rowTV
#print axioms ergodicBool_residual_certificate
#print axioms ergodicBool_residual_certificate_values
#print axioms ergodicBool_candidateMaxGapAverage_zero
#print axioms ergodicBool_path_stationary_certificate

end

end FormalSLT.Examples.CheckStationaryPoissonRobustCandidate
