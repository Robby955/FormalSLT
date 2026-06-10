import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Named assumptions for the PAC-Bayes test-time meta-theorem

This module exposes the named-assumption interface for the q057 meta-theorem.
Every narrowed premise from the contributing q053, q055, and q056 modules is
represented as an explicit field.
-/

namespace FormalSLT.TestTimeMeta

/-- Named sample-size and confidence assumptions. -/
structure SampleConfidenceAssumptions where
  sampleSize : ℕ
  targetConfidence : ℝ
  delta : ℝ
  positiveSampleSize : 0 < sampleSize
  deltaPositive : 0 < delta
  confidenceNonnegative : 0 ≤ targetConfidence

/-- Named loss-width assumptions. -/
structure LossWidthAssumptions where
  lossWidth : ℝ
  nonnegativeLossWidth : 0 ≤ lossWidth

/-- Named q053 compiler contribution. The q053 compiler route remains
unit-interval-normalized; the outer q057 bound scales it by `lossWidth`. -/
structure McAllesterCompilerAssumptions where
  unitIntervalCompilerContribution : ℝ
  unitIntervalCompilerContributionNonnegative : 0 ≤ unitIntervalCompilerContribution

/-- Named online-to-PAC contribution. The original q055 route is conditional on
an explicit deviation gate; q059 adds an iid-derived route that obtains the gate
from the sharp-McDiarmid bad-event complement. The q057 bundle stores the
assembled contribution amount rather than the lower-level route certificate. -/
structure OnlineRegretAssumptions where
  onlineRegretContribution : ℝ
  onlineRegretContributionNonnegative : 0 ≤ onlineRegretContribution

/-- Named q056 Bernstein contribution. It is the certificate-form continuous
prior/posterior route, not the analytic Vitale/Bernstein derivation. -/
structure BernsteinCertificateAssumptions where
  bernsteinContribution : ℝ
  bernsteinContributionNonnegative : 0 ≤ bernsteinContribution

/-- Named anytime-valid contribution from the available Ville-step machinery. -/
structure AnytimeVilleAssumptions where
  anytimeContribution : ℝ
  anytimeContributionNonnegative : 0 ≤ anytimeContribution

/-- Named conditional-kernel contribution. The exact pi-prefix kernel
decomposition remains external to this q057 assembly theorem. -/
structure PrefixKernelAssumptions where
  prefixContribution : ℝ
  prefixContributionNonnegative : 0 ≤ prefixContribution

/-- Full named-assumption bundle for the q057 meta-theorem. -/
structure TestTimeMetaAssumptions where
  sampleConfidence : SampleConfidenceAssumptions
  lossWidth : LossWidthAssumptions
  mcAllester : McAllesterCompilerAssumptions
  online : OnlineRegretAssumptions
  bernstein : BernsteinCertificateAssumptions
  anytime : AnytimeVilleAssumptions
  prefixKernel : PrefixKernelAssumptions
  empiricalRisk : ℝ
  populationRisk : ℝ
  empiricalRiskNonnegative : 0 ≤ empiricalRisk
  populationRiskNonnegative : 0 ≤ populationRisk

/-- The closed-form bound side assembled by the q057 theorem. -/
def testTimeMetaBound (assumptions : TestTimeMetaAssumptions) : ℝ :=
  assumptions.empiricalRisk +
    assumptions.lossWidth.lossWidth *
      assumptions.mcAllester.unitIntervalCompilerContribution +
    assumptions.online.onlineRegretContribution +
    assumptions.bernstein.bernsteinContribution +
    assumptions.anytime.anytimeContribution +
    assumptions.prefixKernel.prefixContribution

/-- The statement certified by the q057 named assumptions. -/
def testTimeMetaConclusion (assumptions : TestTimeMetaAssumptions) : Prop :=
  assumptions.populationRisk ≤ testTimeMetaBound assumptions

/-- Sanity theorem exposing the named-assumption bundle. -/
theorem testTimeNamedAssumptions_valid
    (assumptions : TestTimeMetaAssumptions)
    (hconclusion : testTimeMetaConclusion assumptions) :
    testTimeMetaConclusion assumptions :=
  hconclusion

end FormalSLT.TestTimeMeta
