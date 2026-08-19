import FormalSLT.StochasticDynamics.StationaryPoissonRobustInvariant

/-!
Executable two-state receipt for robust contraction and invariant-target
uniqueness.

The candidate kernel has identical fair rows.  The true kernel stays put with
probability `3/4`, so the kernels differ, every row is exactly `1/4` away from
its candidate row, and the true Dobrushin coefficient is exactly
`0 + 2 * (1/4) = 1/2`.  Thus the perturbation factor two is attained.

The fair PMF is explicitly invariant for the true kernel.  The general
uniqueness theorem then proves that every supplied invariant PMF is that fair
law and that every stationary-risk target agrees with the displayed value.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

/-- Candidate with identical fair rows. -/
def robustInvariantBoolCandidate (_x : Bool) : PMF Bool :=
  PMF.ofFintype (fun _y ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
    have h : ((1 / 2 : NNReal) : ENNReal) +
        ((1 / 2 : NNReal) : ENNReal) = 1 := by
      rw [← ENNReal.coe_add, hNN]
      rfl
    simpa [Fintype.sum_bool, two_mul] using h)

/-- True symmetric kernel: stay with probability `3/4`, switch with
probability `1/4`. -/
def robustInvariantBoolTrue (x : Bool) : PMF Bool :=
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

/-- Fair invariant law of the true symmetric kernel. -/
def robustInvariantBoolStationary : PMF Bool :=
  robustInvariantBoolCandidate false

/-- Score used to expose the stationary target: indicator of next state
`true`. -/
def robustInvariantBoolScore : MarkovTransitionScore Bool :=
  fun _x y ↦ if y then 1 else 0

theorem robustInvariantBool_kernels_ne :
    robustInvariantBoolTrue ≠ robustInvariantBoolCandidate := by
  intro h
  have hpoint := congrArg
    (fun K : Bool → PMF Bool ↦ (K false false).toReal) h
  norm_num [robustInvariantBoolTrue, robustInvariantBoolCandidate,
    PMF.ofFintype_apply] at hpoint

theorem robustInvariantBool_rowTV (z : Bool) :
    finitePMFTotalVariation (robustInvariantBoolTrue z)
      (robustInvariantBoolCandidate z) = 1 / 4 := by
  fin_cases z <;>
    norm_num [finitePMFTotalVariation, robustInvariantBoolTrue,
      robustInvariantBoolCandidate, PMF.ofFintype_apply, Fintype.sum_bool]

theorem robustInvariantBool_candidateCoefficient :
    finiteDobrushinCoefficient robustInvariantBoolCandidate = 0 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    norm_num [finitePMFTotalVariation, robustInvariantBoolCandidate,
      PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteDobrushinCoefficient_nonneg _

theorem robustInvariantBool_extremeRowsTV :
    finitePMFTotalVariation (robustInvariantBoolTrue false)
      (robustInvariantBoolTrue true) = 1 / 2 := by
  norm_num [finitePMFTotalVariation, robustInvariantBoolTrue,
    PMF.ofFintype_apply, Fintype.sum_bool]

/-- The perturbation upper bound is exact on this nontrivial kernel pair. -/
theorem robustInvariantBool_trueCoefficient :
    finiteDobrushinCoefficient robustInvariantBoolTrue = 1 / 2 := by
  apply le_antisymm
  · have h := finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
      robustInvariantBoolTrue robustInvariantBoolCandidate
      (eta := (1 / 4 : ℝ)) (fun z ↦ le_of_eq (robustInvariantBool_rowTV z))
    rw [robustInvariantBool_candidateCoefficient] at h
    norm_num at h ⊢
    exact h
  · rw [← robustInvariantBool_extremeRowsTV]
    exact finitePMFTotalVariation_le_finiteDobrushinCoefficient
      robustInvariantBoolTrue false true

theorem robustInvariantBool_candidateCertificate :
    finiteDobrushinCoefficient robustInvariantBoolCandidate +
        2 * (1 / 4 : ℝ) < 1 := by
  rw [robustInvariantBool_candidateCoefficient]
  norm_num

theorem robustInvariantBool_trueContracts :
    IsOscillationContraction robustInvariantBoolTrue (1 / 2 : ℝ) := by
  have h :=
    candidateDobrushin_add_two_mul_rowTV_isOscillationContraction
      robustInvariantBoolTrue robustInvariantBoolCandidate
      (eta := (1 / 4 : ℝ))
      (fun z ↦ le_of_eq (robustInvariantBool_rowTV z))
  rw [robustInvariantBool_candidateCoefficient] at h
  norm_num at h
  exact h

theorem robustInvariantBoolStationary_invariant :
    IsInvariantPMF robustInvariantBoolTrue robustInvariantBoolStationary := by
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
  · simpa [PMF.bind_apply, tsum_fintype, robustInvariantBoolTrue,
      robustInvariantBoolStationary, robustInvariantBoolCandidate,
      PMF.ofFintype_apply, Fintype.sum_bool, add_comm] using h
  · simpa [PMF.bind_apply, tsum_fintype, robustInvariantBoolTrue,
      robustInvariantBoolStationary, robustInvariantBoolCandidate,
      PMF.ofFintype_apply, Fintype.sum_bool, add_comm] using h

/-- Every supplied invariant PMF is forced to be the displayed fair law. -/
theorem robustInvariantBoolStationary_unique (stationary : PMF Bool)
    (hstationary : IsInvariantPMF robustInvariantBoolTrue stationary) :
    stationary = robustInvariantBoolStationary :=
  invariantPMF_unique_of_candidate_rowTV
    robustInvariantBoolTrue robustInvariantBoolCandidate
    (eta := (1 / 4 : ℝ))
    (fun z ↦ le_of_eq (robustInvariantBool_rowTV z))
    robustInvariantBool_candidateCertificate stationary
    robustInvariantBoolStationary hstationary
    robustInvariantBoolStationary_invariant

theorem robustInvariantBool_stationaryRisk :
    stationaryMarkovRisk robustInvariantBoolTrue
      robustInvariantBoolStationary robustInvariantBoolScore = 1 / 2 := by
  norm_num [stationaryMarkovRisk, markovRowRisk,
    robustInvariantBoolTrue, robustInvariantBoolStationary,
    robustInvariantBoolCandidate, robustInvariantBoolScore,
    PMF.integral_eq_sum, PMF.ofFintype_apply, Fintype.sum_bool]

/-- The numerical target is independent of any alternative invariant witness
the caller might supply. -/
theorem robustInvariantBool_stationaryTarget_independent
    (stationary : PMF Bool)
    (hstationary : IsInvariantPMF robustInvariantBoolTrue stationary) :
    stationaryMarkovRisk robustInvariantBoolTrue stationary
      robustInvariantBoolScore = 1 / 2 := by
  calc
    stationaryMarkovRisk robustInvariantBoolTrue stationary
        robustInvariantBoolScore =
      stationaryMarkovRisk robustInvariantBoolTrue
        robustInvariantBoolStationary robustInvariantBoolScore :=
      stationaryMarkovRisk_eq_of_candidate_rowTV
        robustInvariantBoolTrue robustInvariantBoolCandidate
        (eta := (1 / 4 : ℝ))
        (fun z ↦ le_of_eq (robustInvariantBool_rowTV z))
        robustInvariantBool_candidateCertificate stationary
        robustInvariantBoolStationary hstationary
        robustInvariantBoolStationary_invariant robustInvariantBoolScore
    _ = 1 / 2 := robustInvariantBool_stationaryRisk

#check finitePMFTotalVariation_triangle
#check finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
#check finiteDobrushinCoefficient_lt_one_of_candidate_rowTV
#check candidateDobrushin_add_two_mul_rowTV_isOscillationContraction
#check invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one
#check invariantPMF_unique_of_candidate_rowTV
#check stationaryMarkovRisk_eq_of_candidate_rowTV
#check stationaryPosteriorMarkovRisk_eq_of_candidate_rowTV

#print axioms finitePMFTotalVariation_triangle
#print axioms finiteDobrushinCoefficient_le_candidate_add_two_mul_rowTV
#print axioms finiteDobrushinCoefficient_lt_one_of_candidate_rowTV
#print axioms candidateDobrushin_add_two_mul_rowTV_isOscillationContraction
#print axioms invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one
#print axioms invariantPMF_unique_of_candidate_rowTV
#print axioms stationaryMarkovRisk_eq_of_candidate_rowTV
#print axioms stationaryPosteriorMarkovRisk_eq_of_candidate_rowTV

#check robustInvariantBool_kernels_ne
#check robustInvariantBool_rowTV
#check robustInvariantBool_trueCoefficient
#check robustInvariantBool_trueContracts
#check robustInvariantBoolStationary_invariant
#check robustInvariantBoolStationary_unique
#check robustInvariantBool_stationaryTarget_independent

#print axioms robustInvariantBool_kernels_ne
#print axioms robustInvariantBool_rowTV
#print axioms robustInvariantBool_trueCoefficient
#print axioms robustInvariantBool_trueContracts
#print axioms robustInvariantBoolStationary_invariant
#print axioms robustInvariantBoolStationary_unique
#print axioms robustInvariantBool_stationaryTarget_independent

#check finitePMFTotalVariation_comm
#check finitePMFTotalVariation_eq_zero_iff
#print axioms finitePMFTotalVariation_comm
#print axioms finitePMFTotalVariation_eq_zero_iff

#check robustInvariantBool_candidateCoefficient
#check robustInvariantBool_extremeRowsTV
#check robustInvariantBool_candidateCertificate
#check robustInvariantBool_stationaryRisk
#print axioms robustInvariantBool_candidateCoefficient
#print axioms robustInvariantBool_extremeRowsTV
#print axioms robustInvariantBool_candidateCertificate
#print axioms robustInvariantBool_stationaryRisk

end

end FormalSLT.StochasticDynamics
