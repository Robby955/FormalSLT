/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.TestTimeMeta.BernsteinPopulationDecompositionReal

/-!
# Real-variance Bernstein bridge for the flagship assembly

This module exposes the q090 real-variance Bernstein worked example under names
used by the flagship assembly. The variance proxy is the finite centered second
moment of the nonconstant loss observable, and the prior-moment exponent is
strictly negative at the observed sample.
-/

open FormalSLT.PACBayes
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein

namespace FormalSLT.TestTimeMeta

noncomputable section

/-- The real-variance Bernstein posterior-risk inequality used by the flagship slot. -/
theorem bernsteinRealFlagship_posteriorRisk_le_empirical_add_bernsteinGap :
    posteriorRisk BernsteinRealDecompWorkedExample.rho BernsteinRealDecompWorkedExample.riskFn ≤
      posteriorEmpiricalRisk BernsteinRealDecompWorkedExample.rho
          (BernsteinRealDecompWorkedExample.empiricalRiskFn
            BernsteinRealDecompWorkedExample.omega) +
        BernsteinRealDecompWorkedExample.bernsteinGap :=
  BernsteinRealDecompWorkedExample.posteriorRisk_le_empirical_add_bernsteinGap

/-- The real posterior gap is bounded by the derived Bernstein penalty. -/
theorem bernsteinRealFlagship_gaussianGap_le_bernsteinGap :
    BernsteinRealDecompWorkedExample.gaussianBernsteinGap ≤
      BernsteinRealDecompWorkedExample.bernsteinGap := by
  unfold BernsteinRealDecompWorkedExample.gaussianBernsteinGap
  have h := bernsteinRealFlagship_posteriorRisk_le_empirical_add_bernsteinGap
  linarith

/--
The Bernstein penalty is strictly positive, and the prior-moment gate has a
strictly negative exponent on the real variance proxy.
-/
theorem bernsteinRealFlagship_gap_pos :
    0 < BernsteinRealDecompWorkedExample.bernsteinGap ∧
      priorBernsteinExpMoment
          BernsteinRealDecompWorkedExample.pri
          BernsteinRealDecompWorkedExample.lambda
          BernsteinRealDecompWorkedExample.scale
          BernsteinRealDecompWorkedExample.riskFn
          BernsteinRealDecompWorkedExample.empiricalRiskFn
          BernsteinRealDecompWorkedExample.varianceProxy
          BernsteinRealDecompWorkedExample.omega ≤
        1 / BernsteinRealDecompWorkedExample.delta ∧
      BernsteinRealDecompWorkedExample.bernsteinExponent 0 < 0 := by
  have hlog : 0 < Real.log (1 / BernsteinRealDecompWorkedExample.delta) := by
    apply Real.log_pos
    norm_num [BernsteinRealDecompWorkedExample.delta]
  have hvar :
      0 ≤ posteriorMarginVarianceProxy
        BernsteinRealDecompWorkedExample.rho
        BernsteinRealDecompWorkedExample.varianceProxy := by
    unfold posteriorMarginVarianceProxy
    rw [Fin.sum_univ_one]
    norm_num [
      BernsteinRealDecompWorkedExample.rho,
      BernsteinRealDecompWorkedExample.varianceProxy,
      BernsteinRealDecompWorkedExample.centeredSecondMoment_loss_eq_quarter,
      BernsteinRealDecompWorkedExample.lossObservable]
  have hden :
      0 < 2 * (1 -
        BernsteinRealDecompWorkedExample.scale * BernsteinRealDecompWorkedExample.lambda) := by
    norm_num [
      BernsteinRealDecompWorkedExample.scale,
      BernsteinRealDecompWorkedExample.lambda]
  have hfirst :
      0 <
        (0 + Real.log (1 / BernsteinRealDecompWorkedExample.delta)) /
          BernsteinRealDecompWorkedExample.lambda := by
    simpa using div_pos hlog BernsteinRealDecompWorkedExample.lambda_pos
  have hsecond :
      0 ≤
        BernsteinRealDecompWorkedExample.lambda *
            posteriorMarginVarianceProxy
              BernsteinRealDecompWorkedExample.rho
              BernsteinRealDecompWorkedExample.varianceProxy /
          (2 * (1 -
            BernsteinRealDecompWorkedExample.scale *
              BernsteinRealDecompWorkedExample.lambda)) := by
    exact div_nonneg
      (mul_nonneg BernsteinRealDecompWorkedExample.lambda_pos.le hvar)
      hden.le
  have hgap : 0 < BernsteinRealDecompWorkedExample.bernsteinGap := by
    unfold BernsteinRealDecompWorkedExample.bernsteinGap
    rw [BernsteinRealDecompWorkedExample.klDiv_rho_pri]
    linarith
  exact ⟨hgap,
    BernsteinRealDecompWorkedExample.confidence_gate_of_realVarianceProxy.1,
    BernsteinRealDecompWorkedExample.confidence_gate_of_realVarianceProxy.2⟩

end

end FormalSLT.TestTimeMeta
