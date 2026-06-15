/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.FlagshipComposition

/-!
# Non-vacuous Bernstein discharge of the flagship population-risk decomposition

An earlier synthetic component example set `populationRisk` equal to the assembled
right-hand side, so its `populationDecomposition` field held by construction.
Its Bernstein route (`flagshipGaussianBernsteinContribution_from_sphericalGaussian`)
still threaded the PAC-Bayes risk gate `populationRisk ≤ empiricalRisk + penalty`
as an explicit premise, with the worked `gaussianSpec` setting `populationRisk = 0`,
so that slot stayed vacuous.

This module discharges the Bernstein flagship slot NON-vacuously, mirroring
`OnlinePopulationDecomposition` for the online/IID slot.  The penalty stored in the flagship
`bernsteinOrGaussianContribution` slot is the genuine derived Bernstein gap

`bernsteinGap = (klDiv ρ π + log (1/delta)) / lambda
                  + lambda * posteriorMarginVarianceProxy ρ varianceProxy / (2 * (1 - scale*lambda))`

and the flagship `populationRisk` is the real `posteriorRisk ρ riskFn`.  The component bound
`gaussianBernsteinGap ≤ bernsteinOrGaussianContribution` is exactly the finite PAC-Bayes Bernstein
posterior-risk theorem `finiteBernsteinPACBayesPosteriorRisk_bound_of_priorBernsteinExpMoment_le_inv_delta`
(bound side DERIVED, not assumed), whose confidence gate
`priorBernsteinExpMoment π lambda scale riskFn empiricalRiskFn varianceProxy ω ≤ 1/delta`
is discharged numerically on a concrete `Fin 1` spec.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayes
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein

namespace FormalSLT.TestTimeMeta

noncomputable section

namespace BernsteinDecompWorkedExample

/-- Single-hypothesis class. -/
abbrev Idx : Type := Fin 1

/-- Posterior `ρ`, equal to the prior so that `klDiv ρ π = 0`. -/
def rho : Idx → ℝ := fun _ => 1

/-- Full-support prior `π` (a point mass on the single hypothesis). -/
def pri : Idx → ℝ := fun _ => 1

/-- Per-hypothesis population risk. -/
def riskFn : Idx → ℝ := fun _ => (1 : ℝ) / 4

/-- Per-hypothesis empirical risk at the single sample outcome. -/
def empiricalRiskFn : Unit → Idx → ℝ := fun _ _ => (1 : ℝ) / 8

/-- Per-hypothesis Bernstein margin-variance proxy. -/
def varianceProxy : Idx → ℝ := fun _ => (1 : ℝ) / 4

/-- The single sample outcome. -/
def omega : Unit := ()

/-- Bernstein inverse-temperature. -/
def lambda : ℝ := (1 : ℝ) / 2

/-- Bernstein range scale; `scale * lambda = 1/2 < 1`. -/
def scale : ℝ := 1

/-- Confidence parameter; `1/delta = 20`. -/
def delta : ℝ := (1 : ℝ) / 20

theorem rho_isPMF : IsPMF rho := by
  refine ⟨?_, ?_⟩
  · intro i; simp [rho]
  · simp [rho]

theorem pri_isFullSupportPMF : IsFullSupportPMF pri := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; simp [pri]
  · simp [pri]
  · intro i; simp [pri]

theorem lambda_pos : 0 < lambda := by norm_num [lambda]

theorem scale_lambda_lt_one : scale * lambda < 1 := by norm_num [scale, lambda]

theorem delta_pos : 0 < delta := by norm_num [delta]

/-- The derived Bernstein penalty.  This is the genuine PAC-Bayes Bernstein gap, not a placeholder:
with `klDiv ρ π = 0`, `lambda = 1/2`, `scale*lambda = 1/2`, and the posterior variance proxy
`= 1/4`, it equals `2 * log 20 + 1/8`. -/
def bernsteinGap : ℝ :=
  (klDiv rho pri + Real.log (1 / delta)) / lambda +
    lambda * posteriorMarginVarianceProxy rho varianceProxy /
      (2 * (1 - scale * lambda))

/-- `klDiv ρ π = 0` because `ρ = π` is the single-point mass `1`. -/
theorem klDiv_rho_pri : klDiv rho pri = 0 := by
  unfold klDiv
  simp [rho, pri]

/-- The confidence gate: the Bernstein prior exponential moment equals `1` (the exponent is
designed to vanish), hence is `≤ 1/delta`. -/
theorem confidence_gate :
    priorBernsteinExpMoment pri lambda scale riskFn empiricalRiskFn varianceProxy omega
      ≤ 1 / delta := by
  have hmoment :
      priorBernsteinExpMoment pri lambda scale riskFn empiricalRiskFn varianceProxy omega = 1 := by
    unfold priorBernsteinExpMoment
    rw [Fin.sum_univ_one]
    have hexp :
        lambda * (riskFn 0 - empiricalRiskFn omega 0) -
            lambda ^ 2 * varianceProxy 0 / (2 * (1 - scale * lambda)) = 0 := by
      simp only [riskFn, empiricalRiskFn, varianceProxy, lambda, scale]
      norm_num
    rw [hexp]
    simp [pri]
  rw [hmoment]
  norm_num [delta]

/-- The concrete finite PAC-Bayes Bernstein posterior-risk inequality, with the bound side DERIVED
from `finiteBernsteinPACBayesPosteriorRisk_bound_of_priorBernsteinExpMoment_le_inv_delta`, not
assumed.  The penalty appearing here is `bernsteinGap`. -/
theorem posteriorRisk_le_empirical_add_bernsteinGap :
    posteriorRisk rho riskFn ≤
      posteriorEmpiricalRisk rho (empiricalRiskFn omega) + bernsteinGap := by
  have h :=
    finiteBernsteinPACBayesPosteriorRisk_bound_of_priorBernsteinExpMoment_le_inv_delta
      (ρ := rho) (π := pri) rho_isPMF pri_isFullSupportPMF
      lambda_pos scale_lambda_lt_one delta_pos
      riskFn empiricalRiskFn varianceProxy omega confidence_gate
  -- `h` is the bound with the penalty written out; `bernsteinGap` is definitionally that penalty.
  unfold bernsteinGap
  linarith [h]

/-- The gap actually carried by the flagship Bernstein slot: the real posterior generalization
gap `posteriorRisk - posteriorEmpiricalRisk`. -/
def gaussianBernsteinGap : ℝ :=
  posteriorRisk rho riskFn - posteriorEmpiricalRisk rho (empiricalRiskFn omega)

theorem bernsteinGap_nonneg : 0 ≤ bernsteinGap := by
  have hkl : klDiv rho pri = 0 := klDiv_rho_pri
  have hlog : 0 ≤ Real.log (1 / delta) := by
    apply Real.log_nonneg
    norm_num [delta]
  have hvar : 0 ≤ posteriorMarginVarianceProxy rho varianceProxy := by
    unfold posteriorMarginVarianceProxy
    rw [Fin.sum_univ_one]
    norm_num [rho, varianceProxy]
  unfold bernsteinGap
  rw [hkl]
  have hlam : (0 : ℝ) < lambda := lambda_pos
  have hden : (0 : ℝ) < 2 * (1 - scale * lambda) := by norm_num [scale, lambda]
  have h1 : 0 ≤ (0 + Real.log (1 / delta)) / lambda := by positivity
  have h2 : 0 ≤ lambda * posteriorMarginVarianceProxy rho varianceProxy /
      (2 * (1 - scale * lambda)) := by positivity
  linarith

/-- The derived flagship contributions: only the Bernstein slot is nonzero, and it carries the
real derived `bernsteinGap` (not a placeholder, not `populationRisk`). -/
def derived : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution := 0
  onlineIidContribution := 0
  bernsteinOrGaussianContribution := bernsteinGap
  anytimeVilleContribution := 0
  prefixKernelContribution := 0
  mcAllesterGeneralWidthContributionNonnegative := le_rfl
  onlineIidContributionNonnegative := le_rfl
  bernsteinOrGaussianContributionNonnegative := bernsteinGap_nonneg
  anytimeVilleContributionNonnegative := le_rfl
  prefixKernelContributionNonnegative := le_rfl

theorem posteriorEmpiricalRisk_nonneg :
    0 ≤ posteriorEmpiricalRisk rho (empiricalRiskFn omega) := by
  unfold posteriorEmpiricalRisk posteriorAverage
  rw [Fin.sum_univ_one]
  norm_num [rho, empiricalRiskFn]

theorem posteriorRisk_nonneg : 0 ≤ posteriorRisk rho riskFn := by
  unfold posteriorRisk posteriorAverage
  rw [Fin.sum_univ_one]
  norm_num [rho, riskFn]

/-- The flagship user inputs.  The `populationRisk` is the real `posteriorRisk ρ riskFn` and the
`empiricalRisk` is the real `posteriorEmpiricalRisk ρ (empiricalRiskFn ω)`. -/
def user : FlagshipUserSupplied where
  sampleSize := 1
  targetConfidence := (19 : ℝ) / 20
  delta := delta
  lossWidth := 1
  empiricalRisk := posteriorEmpiricalRisk rho (empiricalRiskFn omega)
  populationRisk := posteriorRisk rho riskFn
  positiveSampleSize := by norm_num
  deltaPositive := delta_pos
  confidenceNonnegative := by norm_num
  lossWidthNonnegative := by norm_num
  empiricalRiskNonnegative := posteriorEmpiricalRisk_nonneg
  populationRiskNonnegative := posteriorRisk_nonneg

/-- The five-gap decomposition with only the Bernstein gap nonzero.  The `populationDecomposition`
field is the genuine posterior identity, and `gaussianBernsteinGap_le` is exactly the derived
finite Bernstein theorem, so the Bernstein penalty is load-bearing. -/
theorem scalarBounds :
    FlagshipScalarComponentBounds user derived
      0 0 gaussianBernsteinGap 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- populationDecomposition: posteriorRisk ≤ posteriorEmpiricalRisk + 0 + 0 + gap + 0 + 0
    show posteriorRisk rho riskFn ≤
      posteriorEmpiricalRisk rho (empiricalRiskFn omega) + 0 + 0 + gaussianBernsteinGap + 0 + 0
    unfold gaussianBernsteinGap
    apply le_of_eq
    ring
  · -- mcAllesterGap_le: 0 ≤ lossWidth * 0
    simp [user, derived]
  · -- onlineGap_le: 0 ≤ 0
    simp [derived]
  · -- gaussianBernsteinGap_le: gaussianBernsteinGap ≤ bernsteinGap  (THE derived Bernstein bound)
    show gaussianBernsteinGap ≤ derived.bernsteinOrGaussianContribution
    unfold gaussianBernsteinGap
    show posteriorRisk rho riskFn - posteriorEmpiricalRisk rho (empiricalRiskFn omega) ≤
      derived.bernsteinOrGaussianContribution
    have h := posteriorRisk_le_empirical_add_bernsteinGap
    have : derived.bernsteinOrGaussianContribution = bernsteinGap := rfl
    rw [this]
    linarith
  · -- anytimeGap_le: 0 ≤ 0
    simp [derived]
  · -- prefixGap_le: 0 ≤ 0
    simp [derived]

/-- NON-VACUOUS flagship scalar bound: the real `posteriorRisk ρ riskFn` is bounded by the
assembled flagship bound, whose Bernstein slot carries the genuine derived `bernsteinGap`. -/
theorem flagship_population_le_bound :
    user.populationRisk ≤ flagshipBound user derived :=
  flagshipScalarAssembly_from_componentInequalities user derived scalarBounds

/-- Reviewer-facing flagship certificate with the Bernstein slot non-vacuously discharged. -/
def certificate : FlagshipCertificate where
  user := user
  derived := derived
  assembledBound := flagship_population_le_bound

/-- The final flagship conclusion via `pacBayesTestTimeFlagship_theorem`. -/
theorem flagship_conclusion : flagshipConclusion certificate :=
  pacBayesTestTimeFlagship_theorem certificate

end BernsteinDecompWorkedExample

end

end FormalSLT.TestTimeMeta
