import FormalSLT.TestTimeMeta.MainTheorem

/-!
# Paper-ready PAC-Bayes test-time flagship API

This module is the q063 reviewer-facing surface for the q057 test-time
meta-theorem.  The lower-level q057 statement keeps every contribution
explicit; this file separates:

* user-supplied quantities, such as sample size, confidence, loss width, and
  empirical/population risks;
* derived contribution quantities, supplied by the checked component theorems:
  q061 general-width McAllester compiler, q059 iid online-to-PAC conversion,
  q056/q060/q062 Bernstein/Gaussian posterior route, q084 anytime Ville step,
  and the prefix-kernel contribution.

The generic certificate adapter `pacBayesTestTimeFlagship_theorem` routes a
checked assembled bound through the q057 framework adapter. The public top
result for flagship citations is the four-component assembly theorem.

The q062 Gaussian-measure/KL backend can fill the
`bernsteinOrGaussianContribution` slot when it lands.  Until that backend is
available, the slot is still explicitly named and nonnegative rather than being
silently folded into an anonymous residual term.
-/

namespace FormalSLT.TestTimeMeta

noncomputable section

/-- User-facing inputs for the flagship theorem. -/
structure FlagshipUserSupplied where
  sampleSize : ℕ
  targetConfidence : ℝ
  delta : ℝ
  lossWidth : ℝ
  empiricalRisk : ℝ
  populationRisk : ℝ
  positiveSampleSize : 0 < sampleSize
  deltaPositive : 0 < delta
  confidenceNonnegative : 0 ≤ targetConfidence
  lossWidthNonnegative : 0 ≤ lossWidth
  empiricalRiskNonnegative : 0 ≤ empiricalRisk
  populationRiskNonnegative : 0 ≤ populationRisk

/-- Derived contributions supplied by the verified component theorems. -/
structure FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution : ℝ
  onlineIidContribution : ℝ
  bernsteinOrGaussianContribution : ℝ
  anytimeVilleContribution : ℝ
  prefixKernelContribution : ℝ
  mcAllesterGeneralWidthContributionNonnegative :
    0 ≤ mcAllesterGeneralWidthContribution
  onlineIidContributionNonnegative : 0 ≤ onlineIidContribution
  bernsteinOrGaussianContributionNonnegative : 0 ≤ bernsteinOrGaussianContribution
  anytimeVilleContributionNonnegative : 0 ≤ anytimeVilleContribution
  prefixKernelContributionNonnegative : 0 ≤ prefixKernelContribution

/-- Closed-form flagship bound side. -/
def flagshipBound
    (user : FlagshipUserSupplied)
    (derived : FlagshipDerivedContributions) : ℝ :=
  user.empiricalRisk +
    user.lossWidth * derived.mcAllesterGeneralWidthContribution +
    derived.onlineIidContribution +
    derived.bernsteinOrGaussianContribution +
    derived.anytimeVilleContribution +
    derived.prefixKernelContribution

/-- Reviewer-facing certificate bundle for the flagship theorem. -/
structure FlagshipCertificate where
  user : FlagshipUserSupplied
  derived : FlagshipDerivedContributions
  assembledBound :
    user.populationRisk ≤ flagshipBound user derived

/-- Convert the paper-ready bundle back to the q057 named-assumption interface. -/
def FlagshipCertificate.toTestTimeMetaAssumptions
    (certificate : FlagshipCertificate) : TestTimeMetaAssumptions where
  sampleConfidence := {
    sampleSize := certificate.user.sampleSize
    targetConfidence := certificate.user.targetConfidence
    delta := certificate.user.delta
    positiveSampleSize := certificate.user.positiveSampleSize
    deltaPositive := certificate.user.deltaPositive
    confidenceNonnegative := certificate.user.confidenceNonnegative
  }
  lossWidth := {
    lossWidth := certificate.user.lossWidth
    nonnegativeLossWidth := certificate.user.lossWidthNonnegative
  }
  mcAllester := {
    unitIntervalCompilerContribution :=
      certificate.derived.mcAllesterGeneralWidthContribution
    unitIntervalCompilerContributionNonnegative :=
      certificate.derived.mcAllesterGeneralWidthContributionNonnegative
  }
  online := {
    onlineRegretContribution := certificate.derived.onlineIidContribution
    onlineRegretContributionNonnegative :=
      certificate.derived.onlineIidContributionNonnegative
  }
  bernstein := {
    bernsteinContribution := certificate.derived.bernsteinOrGaussianContribution
    bernsteinContributionNonnegative :=
      certificate.derived.bernsteinOrGaussianContributionNonnegative
  }
  anytime := {
    anytimeContribution := certificate.derived.anytimeVilleContribution
    anytimeContributionNonnegative :=
      certificate.derived.anytimeVilleContributionNonnegative
  }
  prefixKernel := {
    prefixContribution := certificate.derived.prefixKernelContribution
    prefixContributionNonnegative :=
      certificate.derived.prefixKernelContributionNonnegative
  }
  empiricalRisk := certificate.user.empiricalRisk
  populationRisk := certificate.user.populationRisk
  empiricalRiskNonnegative := certificate.user.empiricalRiskNonnegative
  populationRiskNonnegative := certificate.user.populationRiskNonnegative

/-- The statement certified by the flagship bundle. -/
def flagshipConclusion (certificate : FlagshipCertificate) : Prop :=
  certificate.user.populationRisk ≤ flagshipBound certificate.user certificate.derived

/-- The q063 bound side is definitionally the q057 bound side after conversion. -/
theorem flagshipBound_eq_testTimeMetaBound
    (certificate : FlagshipCertificate) :
    flagshipBound certificate.user certificate.derived =
      testTimeMetaBound certificate.toTestTimeMetaAssumptions := by
  rfl

/--
Generic PAC-Bayes test-time flagship certificate adapter.

This is a reusable certificate object API: one certificate object, one bound.
The public top theorem is the four-component assembly, which supplies the
non-vacuous assembled bound before calling this adapter.
-/
theorem pacBayesTestTimeFlagship_theorem
    (certificate : FlagshipCertificate) :
    flagshipConclusion certificate := by
  have hscaled :
      0 ≤ certificate.user.lossWidth *
        certificate.derived.mcAllesterGeneralWidthContribution :=
    mul_nonneg
      certificate.user.lossWidthNonnegative
      certificate.derived.mcAllesterGeneralWidthContributionNonnegative
  have hmeta :
      testTimeMetaConclusion certificate.toTestTimeMetaAssumptions :=
    pacBayesTestTimeMeta_theorem
      certificate.toTestTimeMetaAssumptions
      hscaled
      (by
        change certificate.user.populationRisk ≤
          testTimeMetaBound certificate.toTestTimeMetaAssumptions
        rw [← flagshipBound_eq_testTimeMetaBound certificate]
        exact certificate.assembledBound)
  change certificate.user.populationRisk ≤
    testTimeMetaBound certificate.toTestTimeMetaAssumptions at hmeta
  unfold flagshipConclusion
  rw [flagshipBound_eq_testTimeMetaBound]
  exact hmeta

end

end FormalSLT.TestTimeMeta
