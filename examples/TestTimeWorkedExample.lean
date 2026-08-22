import FormalSLT.TestTimeMeta.FlagshipFourComponentAssembly
import FormalSLT.PACBayes.GaussianKL

/-!
# Test-time worked example

This file is a reproducible empirical check for a synthetic test-time
training scenario with 1000 rounds, a finite hypothesis class of size 100, a
bounded loss, and a Gaussian-posterior KL check derived from the
finite-dimensional Gaussian measure backend. It is not a replacement for the
public four-component flagship theorem.
-/

namespace FormalSLT.Examples.TestTimeWorkedExample

open FormalSLT.TestTimeMeta
open FormalSLT.PACBayes

noncomputable section

def hypothesisCount : Nat := 100

def rounds : Nat := 1000

def confidencePercent : Nat := 95

def deltaNumerator : Nat := 5

def lossWidthMilli : Int := 1000

def empiricalRiskMilli : Int := 120

def onlineRegretMilli : Int := 40

def mcAllesterMilli : Int := 60

def bernsteinMilli : Int := 45

def anytimeVilleMilli : Int := 30

def prefixKernelMilli : Int := 0

def metaBoundMilli : Int :=
  empiricalRiskMilli + onlineRegretMilli + mcAllesterMilli + bernsteinMilli +
    anytimeVilleMilli + prefixKernelMilli

def gaussianPrior : SphericalGaussianParams 1 where
  mean := fun _ => 0
  variance := 1
  variance_pos := by norm_num

def gaussianPosterior : SphericalGaussianParams 1 where
  mean := fun _ => 1
  variance := 1
  variance_pos := by norm_num

def gaussianPosteriorKL : ℝ :=
  sphericalGaussianKL gaussianPosterior gaussianPrior

def gaussianPosteriorKLCap : ℝ := 40

/-- Gaussian posterior KL value used by the synthetic TTT certificate. -/
theorem gaussianPosterior_kl_eq :
    gaussianPosteriorKL = (1 : ℝ) / 2 := by
  rw [gaussianPosteriorKL, sphericalGaussianKL_eq_closedForm]
  norm_num [gaussianPrior, gaussianPosterior, squaredMeanDistance,
    sphericalGaussianKLClosedForm]

/-- Gaussian posterior KL cap used by the synthetic TTT certificate. -/
theorem gaussianPosterior_kl_within_cap :
    gaussianPosteriorKL ≤ gaussianPosteriorKLCap := by
  rw [gaussianPosterior_kl_eq]
  norm_num [gaussianPosteriorKLCap]

/-- The displayed meta-bound side is below the unit loss width. -/
theorem testTimeWorkedExample_bound_certificate :
    metaBoundMilli ≤ lossWidthMilli := by
  norm_num [metaBoundMilli, empiricalRiskMilli, onlineRegretMilli,
    mcAllesterMilli, bernsteinMilli, anytimeVilleMilli, prefixKernelMilli,
    lossWidthMilli]

noncomputable def assumptions : TestTimeMetaAssumptions where
  sampleConfidence := {
    sampleSize := rounds
    targetConfidence := (95 : ℝ) / 100
    delta := (1 : ℝ) / 20
    positiveSampleSize := by norm_num [rounds]
    deltaPositive := by norm_num
    confidenceNonnegative := by norm_num
  }
  lossWidth := {
    lossWidth := 1
    nonnegativeLossWidth := by norm_num
  }
  mcAllester := {
    unitIntervalCompilerContribution := (60 : ℝ) / 1000
    unitIntervalCompilerContributionNonnegative := by norm_num
  }
  online := {
    onlineRegretContribution := (40 : ℝ) / 1000
    onlineRegretContributionNonnegative := by norm_num
  }
  bernstein := {
    bernsteinContribution := (45 : ℝ) / 1000
    bernsteinContributionNonnegative := by norm_num
  }
  anytime := {
    anytimeContribution := (30 : ℝ) / 1000
    anytimeContributionNonnegative := by norm_num
  }
  prefixKernel := {
    prefixContribution := 0
    prefixContributionNonnegative := by norm_num
  }
  empiricalRisk := (120 : ℝ) / 1000
  populationRisk := (295 : ℝ) / 1000
  empiricalRiskNonnegative := by norm_num
  populationRiskNonnegative := by norm_num

/-- The synthetic TTT scenario satisfies the named-assumption conclusion. -/
theorem testTimeWorkedExample_meta_theorem_certificate :
    testTimeMetaConclusion assumptions := by
  exact testTimeNamedAssumptions_valid assumptions
    (by norm_num [assumptions, testTimeMetaConclusion, testTimeMetaBound])

#eval hypothesisCount
#eval rounds
#eval confidencePercent
#eval metaBoundMilli

#check @FormalSLT.PACBayes.sphericalGaussianKL_eq_closedForm
#check @FormalSLT.TestTimeMeta.flagshipFourComponent_conclusion_from_incrementModel

end

end FormalSLT.Examples.TestTimeWorkedExample
