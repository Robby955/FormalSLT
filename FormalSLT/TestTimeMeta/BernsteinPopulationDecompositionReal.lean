/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.BernsteinBound
import FormalSLT.TestTimeMeta.FlagshipComposition

/-!
# Real-variance Bernstein discharge of the flagship population-risk decomposition

This module adds a finite worked Bernstein slot where the variance proxy is data:
it is `BernsteinAnalytic.finiteCenteredSecondMoment` of a nonconstant loss
observable over a two-point sample law. The observed sample keeps a positive
population-minus-empirical gap, while the fixed Bernstein parameter makes the
normalized prior-moment exponent strictly negative.

The file makes no priority claim. It records the finite PAC-Bayes Bernstein
bridge needed by the flagship certificate API.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.PACBayes
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein

namespace FormalSLT.TestTimeMeta

noncomputable section

namespace BernsteinRealDecompWorkedExample

/-- Single-hypothesis class. -/
abbrev Idx : Type := Fin 1

/-- Two-point finite sample space. -/
abbrev Sample : Type := Fin 2

/-- A fair finite sample law. -/
def sampleLaw : Sample → ℝ := fun _ => (1 : ℝ) / 2

/-- A nonconstant loss observable over the two-point sample space. -/
def lossObservable : Idx → Sample → ℝ :=
  fun _ z => if z = 0 then 0 else 1

/-- Posterior `ρ`, equal to the prior so that `klDiv ρ π = 0`. -/
def rho : Idx → ℝ := fun _ => 1

/-- Full-support prior `π` (a point mass on the single hypothesis). -/
def pri : Idx → ℝ := fun _ => 1

/-- Per-hypothesis population risk, defined as the finite mean of the loss observable. -/
def riskFn : Idx → ℝ :=
  fun i => BernsteinAnalytic.finiteMean sampleLaw (lossObservable i)

/-- Per-hypothesis empirical risk at a sample outcome. -/
def empiricalRiskFn : Sample → Idx → ℝ :=
  fun z i => lossObservable i z

/-- Per-hypothesis Bernstein variance proxy, defined from the real centered second moment. -/
def varianceProxy : Idx → ℝ :=
  fun i => BernsteinAnalytic.finiteCenteredSecondMoment sampleLaw (lossObservable i)

/-- The observed sample outcome, where the empirical loss is `0`. -/
def omega : Sample := 0

/-- Bernstein inverse-temperature. -/
def lambda : ℝ := (9 : ℝ) / 10

/-- Bernstein range scale; `scale * lambda = 9/10 < 1`. -/
def scale : ℝ := 1

/-- Confidence parameter; `1/delta = 20`. -/
def delta : ℝ := (1 : ℝ) / 20

/-- The exact per-hypothesis Bernstein exponent at the observed sample. -/
def bernsteinExponent (i : Idx) : ℝ :=
  lambda * (riskFn i - empiricalRiskFn omega i) -
    lambda ^ 2 * varianceProxy i / (2 * (1 - scale * lambda))

theorem sampleLaw_isPMF : IsPMF sampleLaw := by
  refine ⟨?_, ?_⟩
  · intro z
    fin_cases z <;> norm_num [sampleLaw]
  · norm_num [sampleLaw, Fin.sum_univ_two]

theorem rho_isPMF : IsPMF rho := by
  refine ⟨?_, ?_⟩
  · intro i; simp [rho]
  · simp [rho]

theorem pri_isFullSupportPMF : IsFullSupportPMF pri := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i; simp [pri]
  · simp [pri]
  · intro i; simp [pri]

theorem lambda_pos : 0 < lambda := by
  norm_num [lambda]

theorem scale_lambda_lt_one : scale * lambda < 1 := by
  norm_num [scale, lambda]

theorem delta_pos : 0 < delta := by
  norm_num [delta]

theorem finiteMean_loss_eq_half :
    BernsteinAnalytic.finiteMean sampleLaw (lossObservable 0) = (1 : ℝ) / 2 := by
  norm_num [BernsteinAnalytic.finiteMean, sampleLaw, lossObservable, Fin.sum_univ_two]

theorem centeredSecondMoment_loss_eq_quarter :
    BernsteinAnalytic.finiteCenteredSecondMoment sampleLaw (lossObservable 0) =
      (1 : ℝ) / 4 := by
  norm_num [BernsteinAnalytic.finiteCenteredSecondMoment, BernsteinAnalytic.finiteMean,
    sampleLaw, lossObservable, Fin.sum_univ_two]

/-- The variance proxy fed to Bernstein is the centered second moment of the loss observable. -/
theorem bernsteinVarianceProxy_eq_centeredSecondMoment :
    varianceProxy 0 =
        BernsteinAnalytic.finiteCenteredSecondMoment sampleLaw (lossObservable 0) ∧
      BernsteinAnalytic.finiteCenteredSecondMoment sampleLaw (lossObservable 0) =
        (1 : ℝ) / 4 := by
  constructor
  · rfl
  · exact centeredSecondMoment_loss_eq_quarter

theorem klDiv_rho_pri : klDiv rho pri = 0 := by
  unfold klDiv
  simp [rho, pri]

theorem bernsteinExponent_eq_neg_nine_sixteen :
    bernsteinExponent 0 = -((9 : ℝ) / 16) := by
  norm_num [bernsteinExponent, lambda, scale, riskFn, empiricalRiskFn, varianceProxy,
    finiteMean_loss_eq_half, centeredSecondMoment_loss_eq_quarter, lossObservable, omega]

theorem bernsteinExponent_strictly_negative :
    bernsteinExponent 0 < 0 := by
  rw [bernsteinExponent_eq_neg_nine_sixteen]
  norm_num

/-- The prior Bernstein moment gate holds with a strict negative exponent on the real proxy. -/
theorem confidence_gate_of_realVarianceProxy :
    priorBernsteinExpMoment pri lambda scale riskFn empiricalRiskFn varianceProxy omega
        ≤ 1 / delta ∧
      bernsteinExponent 0 < 0 := by
  refine ⟨?_, bernsteinExponent_strictly_negative⟩
  have hexp :
      lambda * (riskFn 0 - empiricalRiskFn omega 0) -
          lambda ^ 2 * varianceProxy 0 / (2 * (1 - scale * lambda)) =
        -((9 : ℝ) / 16) := by
    simpa [bernsteinExponent] using bernsteinExponent_eq_neg_nine_sixteen
  have hmoment :
      priorBernsteinExpMoment pri lambda scale riskFn empiricalRiskFn varianceProxy omega =
        Real.exp (-((9 : ℝ) / 16)) := by
    unfold priorBernsteinExpMoment
    rw [Fin.sum_univ_one, hexp]
    simp [pri]
  have hle_one : Real.exp (-((9 : ℝ) / 16)) ≤ 1 := by
    calc
      Real.exp (-((9 : ℝ) / 16)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  calc
    priorBernsteinExpMoment pri lambda scale riskFn empiricalRiskFn varianceProxy omega
        = Real.exp (-((9 : ℝ) / 16)) := hmoment
    _ ≤ 1 := hle_one
    _ ≤ 1 / delta := by norm_num [delta]

/-- The derived Bernstein penalty from the finite PAC-Bayes Bernstein adapter. -/
def bernsteinGap : ℝ :=
  (klDiv rho pri + Real.log (1 / delta)) / lambda +
    lambda * posteriorMarginVarianceProxy rho varianceProxy /
      (2 * (1 - scale * lambda))

/-- The concrete finite PAC-Bayes Bernstein posterior-risk inequality. -/
theorem posteriorRisk_le_empirical_add_bernsteinGap :
    posteriorRisk rho riskFn ≤
      posteriorEmpiricalRisk rho (empiricalRiskFn omega) + bernsteinGap := by
  have h :=
    finiteBernsteinPACBayesPosteriorRisk_bound_of_priorBernsteinExpMoment_le_inv_delta
      (ρ := rho) (π := pri) rho_isPMF pri_isFullSupportPMF
      lambda_pos scale_lambda_lt_one delta_pos
      riskFn empiricalRiskFn varianceProxy omega confidence_gate_of_realVarianceProxy.1
  unfold bernsteinGap
  linarith [h]

/-- The flagship Bernstein gap is the real posterior generalization gap. -/
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
    norm_num [rho, varianceProxy, centeredSecondMoment_loss_eq_quarter, lossObservable]
  unfold bernsteinGap
  rw [hkl]
  have hden : (0 : ℝ) < 2 * (1 - scale * lambda) := by
    norm_num [scale, lambda]
  have h1 : 0 ≤ (0 + Real.log (1 / delta)) / lambda := by
    exact div_nonneg (by simpa using hlog) lambda_pos.le
  have h2 :
      0 ≤ lambda * posteriorMarginVarianceProxy rho varianceProxy /
        (2 * (1 - scale * lambda)) := by
    exact div_nonneg (mul_nonneg lambda_pos.le hvar) hden.le
  linarith

/-- The derived flagship contributions. Only the Bernstein slot is nonzero. -/
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
  unfold posteriorEmpiricalRisk posteriorAverage empiricalRiskFn lossObservable omega
  rw [Fin.sum_univ_one]
  norm_num [rho]

theorem posteriorRisk_nonneg : 0 ≤ posteriorRisk rho riskFn := by
  unfold posteriorRisk posteriorAverage riskFn
  rw [Fin.sum_univ_one]
  rw [finiteMean_loss_eq_half]
  norm_num [rho]

/-- The flagship user inputs with `populationRisk` equal to the real posterior risk. -/
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

theorem scalarBounds :
    FlagshipScalarComponentBounds user derived
      0 0 gaussianBernsteinGap 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show posteriorRisk rho riskFn ≤
      posteriorEmpiricalRisk rho (empiricalRiskFn omega) + 0 + 0 +
        gaussianBernsteinGap + 0 + 0
    unfold gaussianBernsteinGap
    apply le_of_eq
    ring
  · simp [user, derived]
  · simp [derived]
  · show gaussianBernsteinGap ≤ derived.bernsteinOrGaussianContribution
    unfold gaussianBernsteinGap
    have h := posteriorRisk_le_empirical_add_bernsteinGap
    change
      posteriorRisk rho riskFn - posteriorEmpiricalRisk rho (empiricalRiskFn omega) ≤
        bernsteinGap
    linarith
  · simp [derived]
  · simp [derived]

/-- The real posterior population risk is bounded by the assembled flagship bound. -/
theorem flagship_population_le_bound_real :
    user.populationRisk ≤ flagshipBound user derived :=
  flagshipScalarAssembly_from_componentInequalities user derived scalarBounds

/-- Reviewer-facing flagship certificate with the real-variance Bernstein slot. -/
def certificate : FlagshipCertificate where
  user := user
  derived := derived
  assembledBound := flagship_population_le_bound_real

/-- The final flagship conclusion via `pacBayesTestTimeFlagship_theorem`. -/
theorem flagship_conclusion : flagshipConclusion certificate :=
  pacBayesTestTimeFlagship_theorem certificate

end BernsteinRealDecompWorkedExample

end

end FormalSLT.TestTimeMeta
