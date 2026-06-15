/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipComposition

/-!
# Non-vacuous online/IID discharge of the flagship population-risk decomposition

An earlier synthetic component example set `populationRisk` equal to the assembled
right-hand side, so its `populationDecomposition` field held by construction.
This module discharges that field NON-vacuously for an online/IID component: the population risk is an
independently defined integral average over a genuine probability measure, and the decomposition
is derived from the q059 iid regret conversion
(`onlineToPACContribution_from_iidRegretConversion`, backed by the sharp-McDiarmid theorem),
not assumed.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.OnlineToPAC

namespace FormalSLT.TestTimeMeta

noncomputable section

/-- The flagship population-risk decomposition for the online/IID component, with the inequality
derived from the q059 iid regret conversion rather than assumed. The five gaps are
`(0, regretRate + deviationBound, 0, 0, 0)`, so the online gap is the only nonzero one. -/
theorem onlinePopulationDecomposition_of_iidRegretConversion
    {T : ℕ} (hT : 0 < T) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (input : BoundedLossRegretConversionInput T)
    (X : Fin T → Ω → ℝ) (ω : Ω) {eps : ℝ} (regretRate : ℝ)
    (hlossBound : 0 ≤ input.lossBound)
    (hpopulationBounded :
      ∀ t : Fin T, 0 ≤ input.populationLoss t ∧ input.populationLoss t ≤ input.lossBound)
    (hempiricalBounded :
      ∀ t : Fin T, 0 ≤ input.empiricalLoss t ∧ input.empiricalLoss t ≤ input.lossBound)
    (hpopulationEq : ∀ t : Fin T, input.populationLoss t = ∫ x, X t x ∂μ)
    (hempiricalEq : ∀ t : Fin T, input.empiricalLoss t = X t ω)
    (hdeviationRadius : eps ≤ input.deviationBound)
    (hnotBad :
      ω ∉ FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent μ X eps)
    (hregret :
      averageEmpiricalLoss input ≤ input.comparatorEmpiricalLoss + input.regretBound / (T : ℝ))
    (hregretRate : input.regretBound / (T : ℝ) ≤ regretRate) :
    averagePopulationLoss input
      ≤ input.comparatorEmpiricalLoss + 0 + (regretRate + input.deviationBound) + 0 + 0 + 0 := by
  have h := onlineToPACContribution_from_iidRegretConversion hT μ input X ω regretRate
    hlossBound hpopulationBounded hempiricalBounded hpopulationEq hempiricalEq
    hdeviationRadius hnotBad hregret hregretRate
  linarith

namespace OnlineDecompWorkedExample

/-- A genuine single-step iid input whose losses are real integrals against `Measure.dirac 0`. -/
def input : BoundedLossRegretConversionInput 1 where
  lossBound := 1
  populationLoss := fun _ => (1 : ℝ) / 4
  empiricalLoss := fun _ => (1 : ℝ) / 4
  comparatorEmpiricalLoss := (1 : ℝ) / 4
  regretBound := 0
  deviationBound := (1 : ℝ) / 2

/-- A bounded, nonconstant loss family on the two-point sample space. -/
def X : Fin 1 → Fin 2 → ℝ := fun _ i => if i = 0 then (1 : ℝ) / 4 else (3 : ℝ) / 4

def regretRate : ℝ := 0

theorem populationEq :
    ∀ t : Fin 1, input.populationLoss t = ∫ x, X t x ∂(Measure.dirac (0 : Fin 2)) := by
  intro t
  simp [input, X, integral_dirac]

theorem empiricalEq :
    ∀ t : Fin 1, input.empiricalLoss t = X t (0 : Fin 2) := by
  intro t
  simp [input, X]

theorem notBad :
    (0 : Fin 2) ∉ FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent
      (Measure.dirac (0 : Fin 2)) X ((1 : ℝ) / 2) := by
  simp [FormalSLT.Probability.IIDConcentration.iidDeviationBadEvent,
    FormalSLT.Probability.IIDConcentration.iidPopulationMinusEmpiricalSum]

theorem populationDecomposition_holds :
    averagePopulationLoss input
      ≤ input.comparatorEmpiricalLoss + 0 + (regretRate + input.deviationBound) + 0 + 0 + 0 := by
  refine onlinePopulationDecomposition_of_iidRegretConversion (T := 1) (by norm_num)
    (Measure.dirac (0 : Fin 2)) input X (0 : Fin 2) (eps := (1 : ℝ) / 2) regretRate
    (by norm_num [input]) ?_ ?_ populationEq empiricalEq (by norm_num [input]) notBad ?_ ?_
  · intro t; fin_cases t; norm_num [input]
  · intro t; fin_cases t; norm_num [input]
  · norm_num [averageEmpiricalLoss, averageFin, input]
  · norm_num [regretRate, input]

/-- The derived contributions: only the online slot is nonzero (and real). -/
def derived : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution := 0
  onlineIidContribution := flagshipOnlineIidContribution input regretRate
  bernsteinOrGaussianContribution := 0
  anytimeVilleContribution := 0
  prefixKernelContribution := 0
  mcAllesterGeneralWidthContributionNonnegative := le_rfl
  onlineIidContributionNonnegative := by
    unfold flagshipOnlineIidContribution
    norm_num [regretRate, input]
  bernsteinOrGaussianContributionNonnegative := le_rfl
  anytimeVilleContributionNonnegative := le_rfl
  prefixKernelContributionNonnegative := le_rfl

def user : FlagshipUserSupplied where
  sampleSize := 1
  targetConfidence := (19 : ℝ) / 20
  delta := (1 : ℝ) / 20
  lossWidth := 1
  empiricalRisk := input.comparatorEmpiricalLoss
  populationRisk := averagePopulationLoss input
  positiveSampleSize := by norm_num
  deltaPositive := by norm_num
  confidenceNonnegative := by norm_num
  lossWidthNonnegative := by norm_num
  empiricalRiskNonnegative := by norm_num [input]
  populationRiskNonnegative := by norm_num [averagePopulationLoss, averageFin, input]

theorem scalarBounds :
    FlagshipScalarComponentBounds user derived
      0 (regretRate + input.deviationBound) 0 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show averagePopulationLoss input
        ≤ input.comparatorEmpiricalLoss + 0 + (regretRate + input.deviationBound) + 0 + 0 + 0
    exact populationDecomposition_holds
  · simp [user, derived]
  · simp [derived, flagshipOnlineIidContribution]
  · simp [derived]
  · simp [derived]
  · simp [derived]

/-- NON-VACUOUS flagship bound: the population risk (a real integral average over `dirac`) is
bounded by the assembled flagship bound, with `populationDecomposition` derived from the q059
iid conversion rather than assumed. -/
theorem flagship_population_le_bound :
    user.populationRisk ≤ flagshipBound user derived :=
  flagshipScalarAssembly_from_componentInequalities user derived scalarBounds

end OnlineDecompWorkedExample

end

end FormalSLT.TestTimeMeta
