import FormalSLT.StochasticDynamics.FiniteInvariantExistence

/-!
Executable asymmetric two-state receipt for finite invariant-law existence.

The kernel sends `false` to `true` with probability `1/4` and `true` to
`false` with probability `1/2`.  Its invariant law is therefore
`P(false)=2/3`, `P(true)=1/3`, and its Dobrushin coefficient is `1/4`.
The receipt checks explicit invariance, generic existence, Dobrushin-based
existence-and-uniqueness, and equality of the canonical chosen law with the
displayed asymmetric law.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

/-- Asymmetric two-state kernel. -/
def invariantExistenceBoolKernel (x : Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ match x, y with
      | false, false => ((3 / 4 : NNReal) : ENNReal)
      | false, true => ((1 / 4 : NNReal) : ENNReal)
      | true, false => ((1 / 2 : NNReal) : ENNReal)
      | true, true => ((1 / 2 : NNReal) : ENNReal))
    (by
      cases x
      · have hNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
        simpa [Fintype.sum_bool, ENNReal.coe_add, add_comm] using
          congrArg (fun q : NNReal ↦ (q : ENNReal)) hNN
      · have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
        simpa [Fintype.sum_bool, ENNReal.coe_add] using
          congrArg (fun q : NNReal ↦ (q : ENNReal)) hNN)

/-- The displayed asymmetric invariant law. -/
def invariantExistenceBoolStationary : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if y then
      ((1 / 3 : NNReal) : ENNReal)
    else
      ((2 / 3 : NNReal) : ENNReal))
    (by
      have hNN : (2 / 3 : NNReal) + 1 / 3 = 1 := by norm_num
      simpa [Fintype.sum_bool, ENNReal.coe_add, add_comm] using
        congrArg (fun q : NNReal ↦ (q : ENNReal)) hNN)

/-- Identical fair candidate rows used for the row-TV certificate. -/
def invariantExistenceBoolCandidate (_x : Bool) : PMF Bool :=
  PMF.ofFintype (fun _y ↦ ((1 / 2 : NNReal) : ENNReal)) (by
    have hNN : (1 / 2 : NNReal) + 1 / 2 = 1 := by norm_num
    simpa [Fintype.sum_bool, ENNReal.coe_add, two_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) hNN)

/-- Explicit arithmetic verification of the asymmetric invariant law. -/
theorem invariantExistenceBoolStationary_invariant :
    IsInvariantPMF invariantExistenceBoolKernel
      invariantExistenceBoolStationary := by
  have hfalseNN :
      (1 / 3 : NNReal) * (1 / 2) + (2 / 3) * (3 / 4) = 2 / 3 := by
    norm_num
  have htrueNN :
      (1 / 3 : NNReal) * (1 / 2) + (2 / 3) * (1 / 4) = 1 / 3 := by
    norm_num
  have hfalse :
      ((1 / 3 : NNReal) : ENNReal) * ((1 / 2 : NNReal) : ENNReal) +
          ((2 / 3 : NNReal) : ENNReal) * ((3 / 4 : NNReal) : ENNReal) =
        ((2 / 3 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) hfalseNN
  have htrue :
      ((1 / 3 : NNReal) : ENNReal) * ((1 / 2 : NNReal) : ENNReal) +
          ((2 / 3 : NNReal) : ENNReal) * ((1 / 4 : NNReal) : ENNReal) =
        ((1 / 3 : NNReal) : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul] using
      congrArg (fun q : NNReal ↦ (q : ENNReal)) htrueNN
  unfold IsInvariantPMF
  apply PMF.ext
  intro y
  cases y
  · simpa [PMF.bind_apply, tsum_fintype, invariantExistenceBoolKernel,
      invariantExistenceBoolStationary, PMF.ofFintype_apply,
      Fintype.sum_bool] using hfalse
  · simpa [PMF.bind_apply, tsum_fintype, invariantExistenceBoolKernel,
      invariantExistenceBoolStationary, PMF.ofFintype_apply,
      Fintype.sum_bool] using htrue

theorem invariantExistenceBool_extremeRowsTV :
    finitePMFTotalVariation (invariantExistenceBoolKernel false)
      (invariantExistenceBoolKernel true) = 1 / 4 := by
  norm_num [finitePMFTotalVariation, invariantExistenceBoolKernel,
    PMF.ofFintype_apply, Fintype.sum_bool]

theorem invariantExistenceBool_coefficient :
    finiteDobrushinCoefficient invariantExistenceBoolKernel = 1 / 4 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    fin_cases x <;> fin_cases y <;>
      norm_num [finitePMFTotalVariation, invariantExistenceBoolKernel,
        PMF.ofFintype_apply, Fintype.sum_bool]
  · rw [← invariantExistenceBool_extremeRowsTV]
    exact finitePMFTotalVariation_le_finiteDobrushinCoefficient
      invariantExistenceBoolKernel false true

theorem invariantExistenceBool_coefficient_lt_one :
    finiteDobrushinCoefficient invariantExistenceBoolKernel < 1 := by
  rw [invariantExistenceBool_coefficient]
  norm_num

theorem invariantExistenceBool_candidate_rowTV (z : Bool) :
    finitePMFTotalVariation (invariantExistenceBoolKernel z)
      (invariantExistenceBoolCandidate z) ≤ 1 / 4 := by
  fin_cases z <;>
    norm_num [finitePMFTotalVariation, invariantExistenceBoolKernel,
      invariantExistenceBoolCandidate, PMF.ofFintype_apply,
      Fintype.sum_bool]

theorem invariantExistenceBool_candidateCoefficient :
    finiteDobrushinCoefficient invariantExistenceBoolCandidate = 0 := by
  apply le_antisymm
  · unfold finiteDobrushinCoefficient
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro x _hx
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro y _hy
    norm_num [finitePMFTotalVariation, invariantExistenceBoolCandidate,
      PMF.ofFintype_apply, Fintype.sum_bool]
  · exact finiteDobrushinCoefficient_nonneg _

theorem invariantExistenceBool_candidateCertificate :
    finiteDobrushinCoefficient invariantExistenceBoolCandidate +
        2 * (1 / 4 : ℝ) < 1 := by
  rw [invariantExistenceBool_candidateCoefficient]
  norm_num

/-- Generic existence specializes to the asymmetric kernel. -/
theorem invariantExistenceBool_exists :
    ∃ stationary : PMF Bool,
      IsInvariantPMF invariantExistenceBoolKernel stationary :=
  exists_invariantPMF invariantExistenceBoolKernel

/-- The asymmetric kernel has exactly one invariant law. -/
theorem invariantExistenceBool_existsUnique :
    ∃! stationary : PMF Bool,
      IsInvariantPMF invariantExistenceBoolKernel stationary :=
  existsUnique_invariantPMF_of_finiteDobrushinCoefficient_lt_one
    invariantExistenceBoolKernel invariantExistenceBool_coefficient_lt_one

/-- The candidate row-TV route independently certifies the same unique law. -/
theorem invariantExistenceBool_existsUnique_of_candidate :
    ∃! stationary : PMF Bool,
      IsInvariantPMF invariantExistenceBoolKernel stationary :=
  existsUnique_invariantPMF_of_candidate_rowTV
    invariantExistenceBoolKernel invariantExistenceBoolCandidate
    (eta := (1 / 4 : ℝ)) invariantExistenceBool_candidate_rowTV
    invariantExistenceBool_candidateCertificate

/-- The canonical law constructed by the general theorem is the displayed
`(2/3,1/3)` law. -/
theorem invariantExistenceBool_canonical_eq_displayed :
    finiteInvariantPMF invariantExistenceBoolKernel =
      invariantExistenceBoolStationary :=
  invariantPMF_unique_of_finiteDobrushinCoefficient_lt_one
    invariantExistenceBoolKernel invariantExistenceBool_coefficient_lt_one
    (finiteInvariantPMF invariantExistenceBoolKernel)
    invariantExistenceBoolStationary
    (finiteInvariantPMF_isInvariant invariantExistenceBoolKernel)
    invariantExistenceBoolStationary_invariant

#check finiteKernelPushLinear
#check finiteKernelPushSimplex
#check finiteKernelCesaro
#check exists_finiteKernelPushSimplex_fixedPoint
#check exists_invariantPMF
#check finiteInvariantPMF
#check finiteInvariantPMF_isInvariant
#check existsUnique_invariantPMF_of_finiteDobrushinCoefficient_lt_one
#check existsUnique_invariantPMF_of_candidate_rowTV

#print axioms exists_finiteKernelPushSimplex_fixedPoint
#print axioms exists_invariantPMF
#print axioms finiteInvariantPMF_isInvariant
#print axioms existsUnique_invariantPMF_of_finiteDobrushinCoefficient_lt_one
#print axioms existsUnique_invariantPMF_of_candidate_rowTV

#check invariantExistenceBoolStationary_invariant
#check invariantExistenceBool_coefficient
#check invariantExistenceBool_exists
#check invariantExistenceBool_existsUnique
#check invariantExistenceBool_existsUnique_of_candidate
#check invariantExistenceBool_canonical_eq_displayed

#print axioms invariantExistenceBoolStationary_invariant
#print axioms invariantExistenceBool_coefficient
#print axioms invariantExistenceBool_exists
#print axioms invariantExistenceBool_existsUnique
#print axioms invariantExistenceBool_existsUnique_of_candidate
#print axioms invariantExistenceBool_canonical_eq_displayed

end

end FormalSLT.StochasticDynamics
