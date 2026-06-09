import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import FormalSLT.Probability.IIDConcentration

/-!
# Online-to-PAC regret conversion

This module states the finite-time bounded-loss conversion used by the
Cesa-Bianchi-Conconi-Gentile online-to-batch result. The concentration part is
an explicit high-probability deviation gate supplied as a hypothesis; this file
also provides the q059 iid-derived variant that obtains that gate from the
finite-sum bad-event complement exposed by
`FormalSLT.Probability.IIDConcentration`.

Reference: Cesa-Bianchi, Conconi, Gentile (2004), "On the Generalization
Ability of On-Line Learning Algorithms," IEEE Transactions on Information
Theory 50(9), DOI 10.1109/TIT.2004.833339.
-/

namespace FormalSLT.OnlineToPAC

open Finset BigOperators

noncomputable section

/-- Average of a finite `Fin T` family, normalized by `T`. -/
def averageFin {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  (∑ t : Fin T, x t) / (T : ℝ)

/-- Finite bounded-loss data needed by the algebraic online-to-PAC conversion. -/
structure BoundedLossRegretConversionInput (T : ℕ) where
  lossBound : ℝ
  populationLoss : Fin T → ℝ
  empiricalLoss : Fin T → ℝ
  comparatorEmpiricalLoss : ℝ
  regretBound : ℝ
  deviationBound : ℝ

/-- Average population loss of the online predictions. -/
def averagePopulationLoss {T : ℕ} (input : BoundedLossRegretConversionInput T) : ℝ :=
  averageFin input.populationLoss

/-- Average empirical loss of the online predictions. -/
def averageEmpiricalLoss {T : ℕ} (input : BoundedLossRegretConversionInput T) : ℝ :=
  averageFin input.empiricalLoss

/-- Right-hand side emitted by the regret-conversion theorem. -/
def onlineToPACBound {T : ℕ} (input : BoundedLossRegretConversionInput T) : ℝ :=
  input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ) + input.deviationBound

/--
Finite-time bounded-loss iid online-to-PAC conversion, conditional on an
explicit high-probability deviation gate.

The bounded-loss and iid assumptions are represented by hypotheses, but the
proof only performs the algebraic conversion from:

* average population loss is controlled by average empirical loss plus the
  deviation gate;
* average empirical loss is controlled by comparator empirical loss plus
  average regret.

The theorem does not prove the deviation gate from iid sampling.
-/
theorem onlineToPAC_boundedLoss_iid_of_regret_and_deviation
    {T : ℕ} (hT : 0 < T)
    (input : BoundedLossRegretConversionInput T)
    (hlossBound : 0 ≤ input.lossBound)
    (hpopulationBounded :
      ∀ t : Fin T, 0 ≤ input.populationLoss t ∧
        input.populationLoss t ≤ input.lossBound)
    (hempiricalBounded :
      ∀ t : Fin T, 0 ≤ input.empiricalLoss t ∧
        input.empiricalLoss t ≤ input.lossBound)
    (hdeviation :
      averagePopulationLoss input ≤ averageEmpiricalLoss input + input.deviationBound)
    (hregret :
      averageEmpiricalLoss input ≤
        input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ)) :
    averagePopulationLoss input ≤ onlineToPACBound input := by
  have _ : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have _ := hlossBound
  have _ := hpopulationBounded
  have _ := hempiricalBounded
  unfold onlineToPACBound
  linarith

/--
Finite-time bounded-loss online-to-PAC conversion with the iid deviation gate
derived from the q059 bad-event complement.

The theorem is still a pointwise conversion on a sample point `ω`: it assumes
`ω` is outside `iidDeviationBadEvent μ X eps`.  The probability mass of that bad
event is supplied by
`FormalSLT.Probability.IIDConcentration.iidDeviationBadEventMass_le_exp_of_sharpMcDiarmid`.
-/
theorem regretConversion_iid
    {T : ℕ} (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (input : BoundedLossRegretConversionInput T)
    (X : Fin T → Ω → ℝ) (ω : Ω) {eps : ℝ}
    (hlossBound : 0 ≤ input.lossBound)
    (hpopulationBounded :
      ∀ t : Fin T, 0 ≤ input.populationLoss t ∧
        input.populationLoss t ≤ input.lossBound)
    (hempiricalBounded :
      ∀ t : Fin T, 0 ≤ input.empiricalLoss t ∧
        input.empiricalLoss t ≤ input.lossBound)
    (hpopulationEq :
      ∀ t : Fin T, input.populationLoss t = ∫ x, X t x ∂μ)
    (hempiricalEq :
      ∀ t : Fin T, input.empiricalLoss t = X t ω)
    (hdeviationRadius : eps ≤ input.deviationBound)
    (hnotBad :
      ω ∉ FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent μ X eps)
    (hregret :
      averageEmpiricalLoss input ≤
        input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ)) :
    averagePopulationLoss input ≤ onlineToPACBound input := by
  have hcore :=
    FormalSLT.Probability.IIDConcentration.iidDeviation_of_not_mem_badEvent
      hT μ X ω hnotBad
  have hpopulationAverage :
      averagePopulationLoss input =
        FormalSLT.Probability.IIDConcentration.iidPopulationAverage μ X := by
    unfold averagePopulationLoss averageFin
    unfold FormalSLT.Probability.IIDConcentration.iidPopulationAverage
    congr 1
    exact Finset.sum_congr rfl fun t _ => hpopulationEq t
  have hempiricalAverage :
      averageEmpiricalLoss input =
        FormalSLT.Probability.IIDConcentration.iidEmpiricalAverage X ω := by
    unfold averageEmpiricalLoss averageFin
    unfold FormalSLT.Probability.IIDConcentration.iidEmpiricalAverage
    congr 1
    exact Finset.sum_congr rfl fun t _ => hempiricalEq t
  have hdeviation :
      averagePopulationLoss input ≤ averageEmpiricalLoss input + input.deviationBound := by
    rw [hpopulationAverage, hempiricalAverage]
    linarith
  exact onlineToPAC_boundedLoss_iid_of_regret_and_deviation
    hT input hlossBound hpopulationBounded hempiricalBounded hdeviation hregret

end

end FormalSLT.OnlineToPAC
