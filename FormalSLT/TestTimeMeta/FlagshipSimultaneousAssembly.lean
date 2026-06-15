/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.BernsteinPopulationDecomposition
import FormalSLT.TestTimeMeta.McAllesterPopulationDecomposition
import FormalSLT.TestTimeMeta.OnlinePopulationDecomposition

/-!
# Simultaneous assembly of the three flagship scalar components

This module derives the flagship assembled bound from component inequalities,
rather than assuming it as certificate data.  The simultaneous worked instance
adds the three existing real component inequalities:

* `mcAllesterPointwiseRiskBound_of_not_mem_compiledBad`;
* `onlinePopulationDecomposition_of_iidRegretConversion`;
* `BernsteinDecompWorkedExample.posteriorRisk_le_empirical_add_bernsteinGap`.

The anytime/Ville and prefix-kernel slots remain zero in this rung.
-/

open FormalSLT.PACBayes
open FormalSLT.PACBayesBoundedLoss
open FormalSLT.PACBayesBernstein
open FormalSLT.OnlineToPAC

namespace FormalSLT.TestTimeMeta

noncomputable section

namespace FlagshipSimultaneousAssembly

def mcAllesterGap : ℝ :=
  mcAllesterGeneralPenalty
    McAllesterDecompWorkedExample.spec.sampleSize
    McAllesterDecompWorkedExample.spec.complexityBound
    McAllesterDecompWorkedExample.spec.lossBound

def onlineGap : ℝ :=
  OnlineDecompWorkedExample.regretRate +
    OnlineDecompWorkedExample.input.deviationBound

def gaussianBernsteinGap : ℝ :=
  BernsteinDecompWorkedExample.gaussianBernsteinGap

def empiricalRisk : ℝ :=
  McAllesterDecompWorkedExample.user.empiricalRisk +
    OnlineDecompWorkedExample.user.empiricalRisk +
    BernsteinDecompWorkedExample.user.empiricalRisk

def populationRisk : ℝ :=
  McAllesterDecompWorkedExample.user.populationRisk +
    OnlineDecompWorkedExample.user.populationRisk +
    BernsteinDecompWorkedExample.user.populationRisk

theorem mcAllesterContribution_pos :
    0 < flagshipMcAllesterContribution McAllesterDecompWorkedExample.spec := by
  unfold flagshipMcAllesterContribution mcAllesterPenalty
  apply Real.sqrt_pos.2
  norm_num [McAllesterDecompWorkedExample.spec]

theorem onlineContribution_pos :
    0 < flagshipOnlineIidContribution
      OnlineDecompWorkedExample.input
      OnlineDecompWorkedExample.regretRate := by
  unfold flagshipOnlineIidContribution
  norm_num [OnlineDecompWorkedExample.input, OnlineDecompWorkedExample.regretRate]

theorem bernsteinContribution_pos :
    0 < BernsteinDecompWorkedExample.bernsteinGap := by
  have hlog : 0 < Real.log (1 / BernsteinDecompWorkedExample.delta) := by
    apply Real.log_pos
    norm_num [BernsteinDecompWorkedExample.delta]
  have hvar :
      0 ≤ posteriorMarginVarianceProxy
        BernsteinDecompWorkedExample.rho
        BernsteinDecompWorkedExample.varianceProxy := by
    unfold posteriorMarginVarianceProxy
    rw [Fin.sum_univ_one]
    norm_num [BernsteinDecompWorkedExample.rho, BernsteinDecompWorkedExample.varianceProxy]
  have hden :
      0 < 2 * (1 -
        BernsteinDecompWorkedExample.scale * BernsteinDecompWorkedExample.lambda) := by
    norm_num [BernsteinDecompWorkedExample.scale, BernsteinDecompWorkedExample.lambda]
  have hfirst :
      0 <
        (0 + Real.log (1 / BernsteinDecompWorkedExample.delta)) /
          BernsteinDecompWorkedExample.lambda := by
    simpa using div_pos hlog BernsteinDecompWorkedExample.lambda_pos
  have hsecond :
      0 ≤
        BernsteinDecompWorkedExample.lambda *
            posteriorMarginVarianceProxy
              BernsteinDecompWorkedExample.rho
              BernsteinDecompWorkedExample.varianceProxy /
          (2 * (1 -
            BernsteinDecompWorkedExample.scale * BernsteinDecompWorkedExample.lambda)) := by
    exact div_nonneg
      (mul_nonneg (le_of_lt BernsteinDecompWorkedExample.lambda_pos) hvar)
      (le_of_lt hden)
  unfold BernsteinDecompWorkedExample.bernsteinGap
  rw [BernsteinDecompWorkedExample.klDiv_rho_pri]
  linarith

theorem mcAllesterGap_pos : 0 < mcAllesterGap := by
  unfold mcAllesterGap mcAllesterGeneralPenalty
  simpa [McAllesterDecompWorkedExample.spec] using mcAllesterContribution_pos

theorem onlineGap_pos : 0 < onlineGap := by
  simpa [onlineGap, flagshipOnlineIidContribution] using onlineContribution_pos

theorem gaussianBernsteinGap_pos : 0 < gaussianBernsteinGap := by
  unfold gaussianBernsteinGap BernsteinDecompWorkedExample.gaussianBernsteinGap
  unfold FormalSLT.PACBayesKL.posteriorRisk
    FormalSLT.PACBayesKL.posteriorEmpiricalRisk
    FormalSLT.PACBayesKL.posteriorAverage
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  norm_num [
    BernsteinDecompWorkedExample.rho,
    BernsteinDecompWorkedExample.riskFn,
    BernsteinDecompWorkedExample.empiricalRiskFn,
    BernsteinDecompWorkedExample.omega]

theorem empiricalRisk_nonnegative : 0 ≤ empiricalRisk := by
  unfold empiricalRisk
  linarith [
    McAllesterDecompWorkedExample.user.empiricalRiskNonnegative,
    OnlineDecompWorkedExample.user.empiricalRiskNonnegative,
    BernsteinDecompWorkedExample.user.empiricalRiskNonnegative]

theorem populationRisk_nonnegative : 0 ≤ populationRisk := by
  unfold populationRisk
  linarith [
    McAllesterDecompWorkedExample.user.populationRiskNonnegative,
    OnlineDecompWorkedExample.user.populationRiskNonnegative,
    BernsteinDecompWorkedExample.user.populationRiskNonnegative]

def user : FlagshipUserSupplied where
  sampleSize := 1
  targetConfidence := (19 : ℝ) / 20
  delta := BernsteinDecompWorkedExample.delta
  lossWidth := 1
  empiricalRisk := empiricalRisk
  populationRisk := populationRisk
  positiveSampleSize := by norm_num
  deltaPositive := BernsteinDecompWorkedExample.delta_pos
  confidenceNonnegative := by norm_num
  lossWidthNonnegative := by norm_num
  empiricalRiskNonnegative := empiricalRisk_nonnegative
  populationRiskNonnegative := populationRisk_nonnegative

def derived : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution :=
    flagshipMcAllesterContribution McAllesterDecompWorkedExample.spec
  onlineIidContribution :=
    flagshipOnlineIidContribution
      OnlineDecompWorkedExample.input
      OnlineDecompWorkedExample.regretRate
  bernsteinOrGaussianContribution := BernsteinDecompWorkedExample.bernsteinGap
  anytimeVilleContribution := 0
  prefixKernelContribution := 0
  mcAllesterGeneralWidthContributionNonnegative := le_of_lt mcAllesterContribution_pos
  onlineIidContributionNonnegative := le_of_lt onlineContribution_pos
  bernsteinOrGaussianContributionNonnegative := le_of_lt bernsteinContribution_pos
  anytimeVilleContributionNonnegative := le_rfl
  prefixKernelContributionNonnegative := le_rfl

theorem populationDecomposition_holds :
    user.populationRisk ≤
      user.empiricalRisk +
        mcAllesterGap +
        onlineGap +
        gaussianBernsteinGap +
        0 +
        0 := by
  have hmc := McAllesterDecompWorkedExample.populationDecomposition_holds
  have honline := OnlineDecompWorkedExample.populationDecomposition_holds
  have hbernstein := BernsteinDecompWorkedExample.scalarBounds.populationDecomposition
  have hmc' :
      McAllesterDecompWorkedExample.user.populationRisk ≤
        McAllesterDecompWorkedExample.user.empiricalRisk + mcAllesterGap := by
    simpa [mcAllesterGap, add_assoc] using hmc
  have honline' :
      OnlineDecompWorkedExample.user.populationRisk ≤
        OnlineDecompWorkedExample.user.empiricalRisk + onlineGap := by
    simpa [OnlineDecompWorkedExample.user, onlineGap, add_assoc] using honline
  have hbernstein' :
      BernsteinDecompWorkedExample.user.populationRisk ≤
        BernsteinDecompWorkedExample.user.empiricalRisk + gaussianBernsteinGap := by
    simpa [gaussianBernsteinGap, add_assoc] using hbernstein
  unfold user populationRisk empiricalRisk
  dsimp
  linarith [hmc', honline', hbernstein']

end FlagshipSimultaneousAssembly

/--
Scalar component bounds for one shared flagship instance whose McAllester,
online/IID, and Bernstein gaps are all real and strictly positive.
-/
theorem flagshipSimultaneous_scalarBounds :
    FlagshipScalarComponentBounds
      FlagshipSimultaneousAssembly.user
      FlagshipSimultaneousAssembly.derived
      FlagshipSimultaneousAssembly.mcAllesterGap
      FlagshipSimultaneousAssembly.onlineGap
      FlagshipSimultaneousAssembly.gaussianBernsteinGap
      0
      0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FlagshipSimultaneousAssembly.populationDecomposition_holds
  · simp [
      FlagshipSimultaneousAssembly.user,
      FlagshipSimultaneousAssembly.derived,
      FlagshipSimultaneousAssembly.mcAllesterGap,
      flagshipMcAllesterContribution,
      mcAllesterGeneralPenalty,
      McAllesterDecompWorkedExample.spec]
  · simp [
      FlagshipSimultaneousAssembly.derived,
      FlagshipSimultaneousAssembly.onlineGap,
      flagshipOnlineIidContribution]
  · unfold FlagshipSimultaneousAssembly.gaussianBernsteinGap
    unfold FlagshipSimultaneousAssembly.derived
    dsimp
    unfold BernsteinDecompWorkedExample.gaussianBernsteinGap
    have h := BernsteinDecompWorkedExample.posteriorRisk_le_empirical_add_bernsteinGap
    linarith
  · simp [FlagshipSimultaneousAssembly.derived]
  · simp [FlagshipSimultaneousAssembly.derived]

/--
The simultaneous flagship assembled bound is derived by the scalar assembly
lemma from the three component inequalities.
-/
theorem flagshipSimultaneous_population_le_bound :
    FlagshipSimultaneousAssembly.user.populationRisk ≤
      flagshipBound
        FlagshipSimultaneousAssembly.user
        FlagshipSimultaneousAssembly.derived :=
  flagshipScalarAssembly_from_componentInequalities
    FlagshipSimultaneousAssembly.user
    FlagshipSimultaneousAssembly.derived
    flagshipSimultaneous_scalarBounds

def flagshipSimultaneous_certificate : FlagshipCertificate where
  user := FlagshipSimultaneousAssembly.user
  derived := FlagshipSimultaneousAssembly.derived
  assembledBound := flagshipSimultaneous_population_le_bound

/--
The reviewer-facing flagship theorem consumes the certificate whose assembled
bound was constructed above.
-/
theorem flagshipSimultaneous_conclusion :
    flagshipConclusion flagshipSimultaneous_certificate :=
  pacBayesTestTimeFlagship_theorem flagshipSimultaneous_certificate

end

end FormalSLT.TestTimeMeta
