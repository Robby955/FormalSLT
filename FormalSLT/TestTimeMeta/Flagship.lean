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

The theorem `pacBayesTestTimeFlagship_theorem` is the single statement meant to
be cited from paper prose.  It routes through
`pacBayesTestTimeMeta_theorem`; no lower-level theorem is hidden or replaced.

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
Paper-ready PAC-Bayes test-time flagship theorem.

This is the reviewer-facing q063 statement: one certificate object, one bound.
The proof calls q057's `pacBayesTestTimeMeta_theorem`, so the public API is
smaller while the proof route remains the checked framework theorem.
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

namespace FlagshipWorkedExample

/-- Canonical q063 synthetic TTT sample size. -/
def sampleSize : Nat := 1000

/-- Canonical q063 confidence, represented as a percentage for display. -/
def confidencePercent : Nat := 95

def empiricalRiskMilli : Nat := 120

def mcAllesterContributionMilli : Nat := 60

def onlineIidContributionMilli : Nat := 40

def bernsteinOrGaussianContributionMilli : Nat := 45

def anytimeVilleContributionMilli : Nat := 30

def prefixKernelContributionMilli : Nat := 0

def populationRiskMilli : Nat := 295

def boundSideMilli : Nat :=
  empiricalRiskMilli +
    mcAllesterContributionMilli +
    onlineIidContributionMilli +
    bernsteinOrGaussianContributionMilli +
    anytimeVilleContributionMilli +
    prefixKernelContributionMilli

/-- Numerical closed-form side of the canonical worked example. -/
theorem boundSideMilli_eq : boundSideMilli = 295 := by
  native_decide

def user : FlagshipUserSupplied where
  sampleSize := sampleSize
  targetConfidence := (confidencePercent : ℝ) / 100
  delta := (1 : ℝ) / 20
  lossWidth := 1
  empiricalRisk := (empiricalRiskMilli : ℝ) / 1000
  populationRisk := (populationRiskMilli : ℝ) / 1000
  positiveSampleSize := by norm_num [sampleSize]
  deltaPositive := by norm_num
  confidenceNonnegative := by norm_num [confidencePercent]
  lossWidthNonnegative := by norm_num
  empiricalRiskNonnegative := by norm_num [empiricalRiskMilli]
  populationRiskNonnegative := by norm_num [populationRiskMilli]

def derived : FlagshipDerivedContributions where
  mcAllesterGeneralWidthContribution :=
    (mcAllesterContributionMilli : ℝ) / 1000
  onlineIidContribution :=
    (onlineIidContributionMilli : ℝ) / 1000
  bernsteinOrGaussianContribution :=
    (bernsteinOrGaussianContributionMilli : ℝ) / 1000
  anytimeVilleContribution :=
    (anytimeVilleContributionMilli : ℝ) / 1000
  prefixKernelContribution :=
    (prefixKernelContributionMilli : ℝ) / 1000
  mcAllesterGeneralWidthContributionNonnegative := by
    norm_num [mcAllesterContributionMilli]
  onlineIidContributionNonnegative := by
    norm_num [onlineIidContributionMilli]
  bernsteinOrGaussianContributionNonnegative := by
    norm_num [bernsteinOrGaussianContributionMilli]
  anytimeVilleContributionNonnegative := by
    norm_num [anytimeVilleContributionMilli]
  prefixKernelContributionNonnegative := by
    norm_num [prefixKernelContributionMilli]

/-- Canonical q063 worked-example certificate. -/
def certificate : FlagshipCertificate where
  user := user
  derived := derived
  assembledBound := by
    norm_num [user, derived, flagshipBound, empiricalRiskMilli,
      populationRiskMilli, mcAllesterContributionMilli, onlineIidContributionMilli,
      bernsteinOrGaussianContributionMilli, anytimeVilleContributionMilli,
      prefixKernelContributionMilli]

/-- Canonical worked-example conclusion. -/
def flagshipWorkedExampleConclusion : Prop :=
  flagshipConclusion certificate

/-- The canonical worked example instantiates the q063 flagship theorem. -/
theorem flagshipWorkedExample_certificate :
    flagshipWorkedExampleConclusion := by
  exact pacBayesTestTimeFlagship_theorem certificate

end FlagshipWorkedExample

end

end FormalSLT.TestTimeMeta
