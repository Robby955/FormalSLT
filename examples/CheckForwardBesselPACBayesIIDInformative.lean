import FormalSLT.PACBayes.ForwardBesselPACBayesIID
import FormalSLT.PACBayes.IIDContinuousGaussian
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Informative forward-Bessel IID PAC-Bayes receipt

This checker uses a genuinely random Bernoulli stream with
`P(label = true) = 31 / 32`, two constant Boolean hypotheses, and a
path-selected empirical-risk-minimizing point posterior.  The reported
observed coordinates `1, ..., 32` contain one `false` followed by 31 `true`
labels; coordinate `0` is the natural filtration's initial past and is not
part of the empirical risk.

On that prefix the selected posterior has

* empirical risk and population risk `1 / 32`;
* Bessel empirical variance exactly `1 / 32`;
* hypothesis complexity exactly `log 2`, checked in
  `(6931 / 10000, 6932 / 10000)`;
* selected tilt `3 / 4`, with weight `5 / 8` at confidence `1 / 160`;
* hybrid-Bessel penalty exactly `125 / 64`;
* forward-Bessel boundary exactly
  `(413 / 768) * log 2 - 125 / 2048`, checked in
  `(3117 / 10000, 3118 / 10000)`; and
* fixed-proxy sub-Gamma boundary exactly
  `1 / 2 + (3 / 8) * log 2`, checked in
  `(7599 / 10000, 7600 / 10000)`.

The two actual boundaries contain logarithms, so they are recorded by exact
symbolic identities and checked rational enclosures rather than falsely
described as rational numbers.  The strict same-prefix comparison is
`informative_besselBoundary_lt_subGammaBoundary`.

The selected prefix cylinder has probability
`(1 / 32) * (31 / 32)^31 > 1 / 160`.  Since the common exceptional event has
outer mass at most `1 / 160`, a path in this exact cylinder lies outside it.
Thus the final receipt is an actual theorem-produced certificate, not a
numeric calculation on a path that might belong to the exceptional event.
-/

namespace FormalSLT.Examples.CheckForwardBesselPACBayesIIDInformative

open MeasureTheory ProbabilityTheory
open Finset Real BigOperators
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniformIID
open FormalSLT.PACBayes.ForwardBesselPACBayes
open FormalSLT.PACBayes.ForwardBesselPACBayesIID
open scoped ENNReal

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## Biased IID Boolean model -/

/-- Bernoulli law with `P(true) = 31 / 32`. -/
noncomputable def biasedBoolLaw : Measure Bool :=
  bernoulliMeasure true false
    ⟨(31 : ℝ) / 32, by norm_num, by norm_num⟩

theorem biasedBoolLaw_isProbabilityMeasure :
    IsProbabilityMeasure biasedBoolLaw := by
  unfold biasedBoolLaw
  infer_instance

abbrev BiasedBoolStream := ℕ → Bool

/-- Infinite product law for the biased Boolean stream. -/
noncomputable def biasedBoolStreamLaw : Measure BiasedBoolStream :=
  Measure.infinitePi (fun _ : ℕ ↦ biasedBoolLaw)

theorem biasedBoolStreamLaw_isProbabilityMeasure :
    IsProbabilityMeasure biasedBoolStreamLaw := by
  letI := biasedBoolLaw_isProbabilityMeasure
  unfold biasedBoolStreamLaw
  infer_instance

def biasedBoolCoordinateSample (k : ℕ) (omega : BiasedBoolStream) : Bool :=
  omega k

theorem biasedBoolCoordinateSample_iIndep :
    iIndepFun biasedBoolCoordinateSample biasedBoolStreamLaw := by
  letI := biasedBoolLaw_isProbabilityMeasure
  exact iIndepFun_infinitePi (X := fun _ (z : Bool) ↦ z)
    (fun _ ↦ measurable_id)

theorem biasedBoolCoordinateSample_hasLaw (k : ℕ) :
    HasLaw (biasedBoolCoordinateSample k) biasedBoolLaw biasedBoolStreamLaw := by
  letI := biasedBoolLaw_isProbabilityMeasure
  exact MeasurePreserving.hasLaw
    (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ biasedBoolLaw) k)

/-! ## Hypotheses, posterior, and tilt catalog -/

def uniformBoolPrior : Bool → ℝ := fun _ ↦ (1 : ℝ) / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  constructor
  · constructor <;> simp [uniformBoolPrior]
  · intro i
    simp [uniformBoolPrior]

def truePosterior : Bool → ℝ := fun h ↦ if h then 1 else 0

def falsePosterior : Bool → ℝ := fun h ↦ if h then 0 else 1

theorem truePosterior_isPMF : IsPMF truePosterior := by
  constructor
  · intro h
    cases h <;> simp [truePosterior]
  · simp [truePosterior]

theorem falsePosterior_isPMF : IsPMF falsePosterior := by
  constructor
  · intro h
    cases h <;> simp [falsePosterior]
  · simp [falsePosterior]

/-- Zero-one disagreement loss for the two constant hypotheses. -/
def disagreementLoss (hypothesis label : Bool) : ℝ :=
  if hypothesis = label then 0 else 1

theorem disagreementLoss_stronglyMeasurable (hypothesis : Bool) :
    StronglyMeasurable (disagreementLoss hypothesis) :=
  (measurable_of_finite _).stronglyMeasurable

theorem disagreementLoss_mem_unitInterval (hypothesis label : Bool) :
    0 ≤ disagreementLoss hypothesis label ∧
      disagreementLoss hypothesis label ≤ 1 := by
  by_cases h : hypothesis = label <;> simp [disagreementLoss, h]

/-- Select the lower-empirical-risk point posterior; ties select `true`. -/
def selectedPosterior
    (omega : BiasedBoolStream) (n : ℕ) : Bool → ℝ :=
  if iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample true n omega ≤
      iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample false n omega then
    truePosterior
  else
    falsePosterior

theorem selectedPosterior_isPMF (omega : BiasedBoolStream) (n : ℕ) :
    IsPMF (selectedPosterior omega n) := by
  unfold selectedPosterior
  split
  · exact truePosterior_isPMF
  · exact falsePosterior_isPMF

theorem truePosterior_kl_eq_log_two :
    klDiv truePosterior uniformBoolPrior = Real.log 2 := by
  simp [klDiv, truePosterior, uniformBoolPrior]

theorem falsePosterior_kl_eq_log_two :
    klDiv falsePosterior uniformBoolPrior = Real.log 2 := by
  simp [klDiv, falsePosterior, uniformBoolPrior]

theorem selectedPosterior_kl_eq_log_two (omega : BiasedBoolStream) (n : ℕ) :
    klDiv (selectedPosterior omega n) uniformBoolPrior = Real.log 2 := by
  unfold selectedPosterior
  split
  · exact truePosterior_kl_eq_log_two
  · exact falsePosterior_kl_eq_log_two

/-- Unequal positive weights make the selected atom cost visible. -/
def tiltWeight : Bool → ℝ := fun j ↦
  if j then (5 : ℝ) / 8 else (3 : ℝ) / 8

theorem tiltWeight_isFullSupportPMF : IsFullSupportPMF tiltWeight := by
  constructor
  · constructor <;> norm_num [tiltWeight]
  · intro j
    cases j <;> norm_num [tiltWeight]

/-- Declared tilts `false ↦ 1/4` and `true ↦ 3/4`. -/
def tilts : Bool → ℝ := fun j ↦
  if j then (3 : ℝ) / 4 else (1 : ℝ) / 4

theorem tilts_pos (j : Bool) : 0 < tilts j := by
  cases j <;> norm_num [tilts]

theorem tilts_lt_one (j : Bool) : tilts j < 1 := by
  cases j <;> norm_num [tilts]

/-- Select the larger tilt exactly when the supplied posterior empirical risk
is at most `1/8`.  The selector reads the path, time, and posterior. -/
def tiltSelector
    (omega : BiasedBoolStream) (n : ℕ) (posterior : Bool → ℝ) : Bool :=
  decide
    (iidPosteriorEmpiricalRisk disagreementLoss biasedBoolCoordinateSample
      posterior n omega ≤ (1 : ℝ) / 8)

/-! ## Explicit prefixes exercising both selector branches -/

/-- Coordinate 1 is false and every other coordinate is true. -/
def oneFalseThirtyOneTrueStream : BiasedBoolStream := fun k ↦
  if k = 1 then false else true

/-- Alternating labels make either constant classifier incur risk `1/2`. -/
def balancedStream : BiasedBoolStream := fun k ↦ decide (Even k)

/-- Complementary one-common/31-rare prefix, used to exercise the other
sample-selected posterior branch. -/
def oneTrueThirtyOneFalseStream : BiasedBoolStream := fun k ↦
  if k = 1 then true else false

theorem selectedPosterior_oneFalse_eq_true :
    selectedPosterior oneFalseThirtyOneTrueStream 32 = truePosterior := by
  norm_num [selectedPosterior, iidLossEmpiricalRisk, disagreementLoss,
    biasedBoolCoordinateSample, oneFalseThirtyOneTrueStream,
    truePosterior, falsePosterior, Finset.sum_range_succ]

theorem informative_trueEmpiricalRisk_eq_one_thirtyTwo :
    iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample true 32
      oneFalseThirtyOneTrueStream = (1 : ℝ) / 32 := by
  norm_num [iidLossEmpiricalRisk, disagreementLoss,
    biasedBoolCoordinateSample, oneFalseThirtyOneTrueStream,
    Finset.sum_range_succ]

theorem informative_falseEmpiricalRisk_eq_thirtyOne_thirtyTwo :
    iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample false 32
      oneFalseThirtyOneTrueStream = (31 : ℝ) / 32 := by
  norm_num [iidLossEmpiricalRisk, disagreementLoss,
    biasedBoolCoordinateSample, oneFalseThirtyOneTrueStream,
    Finset.sum_range_succ]

theorem selectedPosterior_balanced_eq_true :
    selectedPosterior balancedStream 32 = truePosterior := by
  norm_num [selectedPosterior, iidLossEmpiricalRisk, disagreementLoss,
    biasedBoolCoordinateSample, balancedStream, truePosterior, falsePosterior,
    Finset.sum_range_succ]

theorem selectedPosterior_oneTrue_eq_false :
    selectedPosterior oneTrueThirtyOneFalseStream 32 = falsePosterior := by
  norm_num [selectedPosterior, iidLossEmpiricalRisk, disagreementLoss,
    biasedBoolCoordinateSample, oneTrueThirtyOneFalseStream,
    truePosterior, falsePosterior, Finset.sum_range_succ]

theorem tiltSelector_oneFalse_eq_true :
    tiltSelector oneFalseThirtyOneTrueStream 32
      (selectedPosterior oneFalseThirtyOneTrueStream 32) = true := by
  norm_num [tiltSelector, selectedPosterior_oneFalse_eq_true,
    iidPosteriorEmpiricalRisk, posteriorAverage, iidLossEmpiricalRisk,
    disagreementLoss, biasedBoolCoordinateSample,
    oneFalseThirtyOneTrueStream, truePosterior, Finset.sum_range_succ]

theorem tiltSelector_balanced_eq_false :
    tiltSelector balancedStream 32 (selectedPosterior balancedStream 32) = false := by
  norm_num [tiltSelector, selectedPosterior_balanced_eq_true,
    iidPosteriorEmpiricalRisk, posteriorAverage, iidLossEmpiricalRisk,
    disagreementLoss, biasedBoolCoordinateSample, balancedStream,
    truePosterior, Finset.sum_range_succ]

/-! ## Exact selected-prefix statistics -/

/-- Loss sequence of the selected `true` hypothesis on the informative path. -/
def informativeLossSequence (k : ℕ) : ℝ :=
  disagreementLoss true
    (biasedBoolCoordinateSample (k + 1) oneFalseThirtyOneTrueStream)

theorem informative_empiricalRisk_eq_one_thirtyTwo :
    iidPosteriorEmpiricalRisk disagreementLoss biasedBoolCoordinateSample
      (selectedPosterior oneFalseThirtyOneTrueStream 32) 32
        oneFalseThirtyOneTrueStream = (1 : ℝ) / 32 := by
  rw [selectedPosterior_oneFalse_eq_true]
  norm_num [iidPosteriorEmpiricalRisk, posteriorAverage,
    iidLossEmpiricalRisk, disagreementLoss, biasedBoolCoordinateSample,
    oneFalseThirtyOneTrueStream, truePosterior, Finset.sum_range_succ]

theorem true_populationRisk_eq_one_thirtyTwo :
    iidLossPopulationRisk biasedBoolLaw disagreementLoss true =
      (1 : ℝ) / 32 := by
  unfold iidLossPopulationRisk biasedBoolLaw
  rw [integral_bernoulliMeasure]
  norm_num [disagreementLoss]

theorem informative_populationRisk_eq_one_thirtyTwo :
    iidPosteriorPopulationRisk biasedBoolLaw disagreementLoss
      (selectedPosterior oneFalseThirtyOneTrueStream 32) =
        (1 : ℝ) / 32 := by
  rw [selectedPosterior_oneFalse_eq_true]
  simp [iidPosteriorPopulationRisk, posteriorAverage, truePosterior,
    true_populationRisk_eq_one_thirtyTwo]

theorem informative_kl_eq_log_two :
    klDiv (selectedPosterior oneFalseThirtyOneTrueStream 32)
      uniformBoolPrior = Real.log 2 :=
  selectedPosterior_kl_eq_log_two _ _

theorem informative_kl_pos :
    0 < klDiv (selectedPosterior oneFalseThirtyOneTrueStream 32)
      uniformBoolPrior := by
  rw [informative_kl_eq_log_two]
  exact Real.log_pos (by norm_num)

theorem informative_kl_rational_enclosure :
    (6931 : ℝ) / 10000 <
        klDiv (selectedPosterior oneFalseThirtyOneTrueStream 32)
          uniformBoolPrior ∧
      klDiv (selectedPosterior oneFalseThirtyOneTrueStream 32)
          uniformBoolPrior < (6932 : ℝ) / 10000 := by
  rw [informative_kl_eq_log_two]
  constructor <;> nlinarith [log_two_gt_d9, log_two_lt_d9]

theorem informative_forwardBesselQ_eq :
    forwardBesselQ informativeLossSequence 32 = (31 : ℝ) / 32 := by
  norm_num [forwardBesselQ, forwardPrefixMean, informativeLossSequence,
    disagreementLoss, biasedBoolCoordinateSample,
    oneFalseThirtyOneTrueStream, Finset.sum_range_succ]

/-- The exact Bessel sample variance is positive and strictly below `1/4`. -/
theorem informative_besselVariance_eq_one_thirtyTwo :
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin 32 ↦ informativeLossSequence i) =
      (1 : ℝ) / 32 := by
  have h := forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
    informativeLossSequence (n := 32) (by norm_num)
  rw [informative_forwardBesselQ_eq] at h
  norm_num at h ⊢
  linarith

theorem informative_besselVariance_mem_Ioo :
    0 <
        FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin 32 ↦ informativeLossSequence i) ∧
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin 32 ↦ informativeLossSequence i) < (1 : ℝ) / 4 := by
  rw [informative_besselVariance_eq_one_thirtyTwo]
  norm_num

theorem informative_hybridPenalty_eq :
    forwardHybridBesselPenalty informativeLossSequence 32 =
      (125 : ℝ) / 64 := by
  unfold forwardHybridBesselPenalty
  rw [informative_forwardBesselQ_eq]
  norm_num [harmonic]

theorem informative_posteriorHybridPenalty_eq :
    forwardPosteriorHybridBesselPenalty
        (selectedPosterior oneFalseThirtyOneTrueStream 32)
        (iidObservedLoss disagreementLoss biasedBoolCoordinateSample)
        32 oneFalseThirtyOneTrueStream = (125 : ℝ) / 64 := by
  rw [selectedPosterior_oneFalse_eq_true]
  unfold forwardPosteriorHybridBesselPenalty posteriorAverage
  rw [Fintype.sum_bool]
  simp only [truePosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  rw [add_zero]
  change forwardHybridBesselPenalty informativeLossSequence 32 =
    (125 : ℝ) / 64
  exact informative_hybridPenalty_eq

theorem selected_atom_logWeightCost_eq :
    Real.log
        (1 / (((1 : ℝ) / 160) * tiltWeight true)) =
      8 * Real.log 2 := by
  norm_num [tiltWeight]
  rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
  norm_num

theorem selected_tilt_psi_eq :
    forwardEmpiricalBernsteinPsi (tilts true) =
      2 * Real.log 2 - (3 : ℝ) / 4 := by
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogQuarter : Real.log ((1 : ℝ) / 4) = -Real.log 4 := by
    rw [show ((1 : ℝ) / 4) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  unfold forwardEmpiricalBernsteinPsi tilts
  rw [if_pos rfl]
  norm_num only [one_div, one_sub_div, Nat.cast_ofNat]
  rw [hlogQuarter, hlogFour]
  ring

/-! ## Same-prefix comparison with the fixed-proxy sub-Gamma lane -/

/-- The selected hybrid-Bessel boundary on the informative path. -/
def informativeBesselBoundary : ℝ :=
  forwardIIDBesselPACBayesBoundary
    uniformBoolPrior tiltWeight tilts disagreementLoss
      biasedBoolCoordinateSample
      (selectedPosterior oneFalseThirtyOneTrueStream 32)
      ((1 : ℝ) / 160) true 32 oneFalseThirtyOneTrueStream

/-- The PR63/68 fixed-proxy boundary on the identical path, posterior,
confidence level, weight, and selected tilt. -/
def informativeSubGammaBoundary : ℝ :=
  subGammaCgf 1 1 (tilts true) / tilts true +
    (klDiv (selectedPosterior oneFalseThirtyOneTrueStream 32)
        uniformBoolPrior +
      Real.log (1 / (((1 : ℝ) / 160) * tiltWeight true))) /
        ((32 : ℝ) * tilts true)

theorem informative_besselBoundary_eq :
    informativeBesselBoundary =
      (413 : ℝ) / 768 * Real.log 2 - (125 : ℝ) / 2048 := by
  unfold informativeBesselBoundary forwardIIDBesselPACBayesBoundary
    forwardBesselPACBayesBoundary
  rw [informative_kl_eq_log_two, selected_atom_logWeightCost_eq,
    informative_posteriorHybridPenalty_eq, selected_tilt_psi_eq]
  norm_num [tilts]
  ring

theorem informative_subGammaBoundary_eq :
    informativeSubGammaBoundary =
      (1 : ℝ) / 2 + (3 : ℝ) / 8 * Real.log 2 := by
  unfold informativeSubGammaBoundary
  rw [informative_kl_eq_log_two, selected_atom_logWeightCost_eq]
  norm_num [tilts, subGammaCgf]
  ring

theorem informative_besselBoundary_rational_enclosure :
    (3117 : ℝ) / 10000 < informativeBesselBoundary ∧
      informativeBesselBoundary < (3118 : ℝ) / 10000 := by
  rw [informative_besselBoundary_eq]
  constructor <;> nlinarith [log_two_gt_d9, log_two_lt_d9]

theorem informative_subGammaBoundary_rational_enclosure :
    (7599 : ℝ) / 10000 < informativeSubGammaBoundary ∧
      informativeSubGammaBoundary < (7600 : ℝ) / 10000 := by
  rw [informative_subGammaBoundary_eq]
  constructor <;> nlinarith [log_two_gt_d9, log_two_lt_d9]

/-- Checked rational enclosure for the actual logarithmic Bessel boundary. -/
theorem informative_besselBoundary_le_2929_6144 :
    informativeBesselBoundary ≤ (2929 : ℝ) / 6144 := by
  rw [informative_besselBoundary_eq]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  nlinarith

theorem informative_besselBoundary_lt_half :
    informativeBesselBoundary < (1 : ℝ) / 2 :=
  informative_besselBoundary_le_2929_6144.trans_lt (by norm_num)

theorem informative_subGammaBoundary_gt_half :
    (1 : ℝ) / 2 < informativeSubGammaBoundary := by
  rw [informative_subGammaBoundary_eq]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- The paper's motivation display: on the identical selected prefix, the
hybrid-Bessel boundary is strictly smaller than the old fixed-proxy boundary. -/
theorem informative_besselBoundary_lt_subGammaBoundary :
    informativeBesselBoundary < informativeSubGammaBoundary :=
  informative_besselBoundary_lt_half.trans
    informative_subGammaBoundary_gt_half

theorem informative_fullRiskCeiling_lt_three_fifths :
    (1 : ℝ) / 32 + informativeBesselBoundary < (3 : ℝ) / 5 := by
  have h := informative_besselBoundary_lt_half
  nlinarith

theorem informative_fullRiskCeiling_lt_343_1000 :
    (1 : ℝ) / 32 + informativeBesselBoundary < (343 : ℝ) / 1000 := by
  rw [informative_besselBoundary_eq]
  nlinarith [log_two_lt_d9]

/-! ## A positive-mass exact prefix cylinder -/

def informativePrefixTarget (k : ℕ) : Bool :=
  if k = 1 then false else true

/-- Coordinates `1, ..., 32` equal the reported one-false/31-true prefix. -/
def informativePrefixCylinder : Set BiasedBoolStream :=
  Set.pi (Finset.Icc 1 32) (fun k ↦ {informativePrefixTarget k})

theorem measurableSet_informativePrefixCylinder :
    MeasurableSet informativePrefixCylinder := by
  exact MeasurableSet.pi (Finset.countable_toSet _)
    (fun _ _ ↦ MeasurableSet.singleton _)

theorem biasedBoolLaw_target_singleton (k : ℕ) :
    biasedBoolLaw {informativePrefixTarget k} =
      if k = 1 then ((1 : ℝ≥0∞) / 32) else ((31 : ℝ≥0∞) / 32) := by
  by_cases hk : k = 1
  · subst k
    simp only [biasedBoolLaw, informativePrefixTarget, if_pos,
      bernoulliMeasure_apply_of_notMem_of_mem,
      MeasurableSet.singleton, Set.mem_singleton_iff,
      Bool.true_eq_false, not_false_eq_true]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  · simp only [biasedBoolLaw, informativePrefixTarget, hk, if_false,
      bernoulliMeasure_apply_of_mem_of_notMem,
      MeasurableSet.singleton, Set.mem_singleton_iff,
      Bool.false_eq_true, not_false_eq_true]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num

theorem biasedBoolStreamLaw_informativePrefixCylinder :
    biasedBoolStreamLaw informativePrefixCylinder =
      ((1 : ℝ≥0∞) / 32) * (((31 : ℝ≥0∞) / 32) ^ (31 : ℕ)) := by
  letI := biasedBoolLaw_isProbabilityMeasure
  unfold biasedBoolStreamLaw informativePrefixCylinder
  rw [Measure.infinitePi_pi]
  · simp_rw [biasedBoolLaw_target_singleton]
    rw [← Finset.mul_prod_erase (Finset.Icc 1 32)
      (fun k ↦ if k = 1 then ((1 : ℝ≥0∞) / 32)
        else ((31 : ℝ≥0∞) / 32)) (by norm_num : 1 ∈ Finset.Icc 1 32)]
    norm_num only [if_pos]
    have hremaining :
        ∀ k ∈ (Finset.Icc 1 32).erase 1,
          (if k = 1 then ((1 : ℝ≥0∞) / 32)
            else ((31 : ℝ≥0∞) / 32)) = (31 : ℝ≥0∞) / 32 := by
      intro k hk
      rw [if_neg]
      exact Finset.ne_of_mem_erase hk
    calc
      ((1 : ℝ≥0∞) / 32) *
          ∏ k ∈ (Finset.Icc 1 32).erase 1,
            (if k = 1 then ((1 : ℝ≥0∞) / 32)
              else ((31 : ℝ≥0∞) / 32)) =
          ((1 : ℝ≥0∞) / 32) *
            ∏ _k ∈ (Finset.Icc 1 32).erase 1,
              ((31 : ℝ≥0∞) / 32) := by
            congr 1
      _ = ((1 : ℝ≥0∞) / 32) *
          (((31 : ℝ≥0∞) / 32) ^ (31 : ℕ)) := by
            rw [Finset.prod_const]
            norm_num
  · intro i hi
    exact MeasurableSet.singleton _

theorem biasedBoolStreamLaw_real_informativePrefixCylinder :
    biasedBoolStreamLaw.real informativePrefixCylinder =
      ((1 : ℝ) / 32) * (((31 : ℝ) / 32) ^ (31 : ℕ)) := by
  rw [measureReal_def, biasedBoolStreamLaw_informativePrefixCylinder]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow]

theorem informativePrefixCylinder_mass_gt_delta :
    (1 : ℝ) / 160 <
      biasedBoolStreamLaw.real informativePrefixCylinder := by
  rw [biasedBoolStreamLaw_real_informativePrefixCylinder]
  norm_num

theorem informativePrefixCylinder_coordinate
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder)
    {k : ℕ} (hk : k < 32) :
    biasedBoolCoordinateSample (k + 1) omega =
      biasedBoolCoordinateSample (k + 1) oneFalseThirtyOneTrueStream := by
  have hkIcc : k + 1 ∈ Finset.Icc 1 32 := by
    simp only [Finset.mem_Icc]
    omega
  have hmem := homega (k + 1) hkIcc
  change omega (k + 1) = oneFalseThirtyOneTrueStream (k + 1)
  change omega (k + 1) ∈ {informativePrefixTarget (k + 1)} at hmem
  rw [Set.mem_singleton_iff] at hmem
  simpa [informativePrefixTarget, oneFalseThirtyOneTrueStream] using hmem

theorem trueEmpiricalRisk_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample true 32 omega =
      (1 : ℝ) / 32 := by
  calc
    iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample true 32 omega =
        iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample true 32
          oneFalseThirtyOneTrueStream := by
      unfold iidLossEmpiricalRisk
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [informativePrefixCylinder_coordinate homega hk]
    _ = (1 : ℝ) / 32 := informative_trueEmpiricalRisk_eq_one_thirtyTwo

theorem falseEmpiricalRisk_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample false 32 omega =
      (31 : ℝ) / 32 := by
  calc
    iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample false 32 omega =
        iidLossEmpiricalRisk disagreementLoss biasedBoolCoordinateSample false 32
          oneFalseThirtyOneTrueStream := by
      unfold iidLossEmpiricalRisk
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [informativePrefixCylinder_coordinate homega hk]
    _ = (31 : ℝ) / 32 := informative_falseEmpiricalRisk_eq_thirtyOne_thirtyTwo

theorem selectedPosterior_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    selectedPosterior omega 32 = truePosterior := by
  unfold selectedPosterior
  rw [trueEmpiricalRisk_of_mem_informativePrefixCylinder homega,
    falseEmpiricalRisk_of_mem_informativePrefixCylinder homega]
  norm_num

theorem tiltSelector_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    tiltSelector omega 32 (selectedPosterior omega 32) = true := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega]
  norm_num [tiltSelector, iidPosteriorEmpiricalRisk, posteriorAverage,
    truePosterior, trueEmpiricalRisk_of_mem_informativePrefixCylinder homega]

/-- Selected-hypothesis loss sequence on an arbitrary stream. -/
def selectedTrueLossSequence (omega : BiasedBoolStream) (k : ℕ) : ℝ :=
  iidObservedLoss disagreementLoss biasedBoolCoordinateSample true k omega

theorem selectedTrueLossSequence_eq_informative_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder)
    {k : ℕ} (hk : k < 32) :
    selectedTrueLossSequence omega k = informativeLossSequence k := by
  unfold selectedTrueLossSequence iidObservedLoss informativeLossSequence
  rw [informativePrefixCylinder_coordinate homega hk]

theorem forwardPrefixMean_selectedTrue_eq_informative_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPrefixMean (selectedTrueLossSequence omega) 32 =
      forwardPrefixMean informativeLossSequence 32 := by
  unfold forwardPrefixMean
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact selectedTrueLossSequence_eq_informative_of_mem homega
    (Finset.mem_range.mp hk)

theorem forwardBesselQ_selectedTrue_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardBesselQ (selectedTrueLossSequence omega) 32 = (31 : ℝ) / 32 := by
  unfold forwardBesselQ
  rw [forwardPrefixMean_selectedTrue_eq_informative_of_mem homega]
  calc
    (∑ i ∈ Finset.range 32,
        (selectedTrueLossSequence omega i -
          forwardPrefixMean informativeLossSequence 32) ^ 2) =
        ∑ i ∈ Finset.range 32,
          (informativeLossSequence i -
            forwardPrefixMean informativeLossSequence 32) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [selectedTrueLossSequence_eq_informative_of_mem homega
        (Finset.mem_range.mp hk)]
    _ = (31 : ℝ) / 32 := informative_forwardBesselQ_eq

theorem hybridPenalty_selectedTrue_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardHybridBesselPenalty (selectedTrueLossSequence omega) 32 =
      (125 : ℝ) / 64 := by
  unfold forwardHybridBesselPenalty
  rw [forwardBesselQ_selectedTrue_of_mem homega]
  norm_num [harmonic]

theorem posteriorHybridPenalty_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPosteriorHybridBesselPenalty (selectedPosterior omega 32)
        (iidObservedLoss disagreementLoss biasedBoolCoordinateSample)
        32 omega = (125 : ℝ) / 64 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega]
  unfold forwardPosteriorHybridBesselPenalty posteriorAverage
  rw [Fintype.sum_bool]
  simp only [truePosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  rw [add_zero]
  change forwardHybridBesselPenalty (selectedTrueLossSequence omega) 32 =
    (125 : ℝ) / 64
  exact hybridPenalty_selectedTrue_of_mem homega

theorem besselVariance_selectedTrue_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin 32 ↦ selectedTrueLossSequence omega i) =
      (1 : ℝ) / 32 := by
  have h := forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
    (selectedTrueLossSequence omega) (n := 32) (by norm_num)
  rw [forwardBesselQ_selectedTrue_of_mem homega] at h
  norm_num at h ⊢
  linarith

theorem besselBoundary_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardIIDBesselPACBayesBoundary
        uniformBoolPrior tiltWeight tilts disagreementLoss
          biasedBoolCoordinateSample (selectedPosterior omega 32)
          ((1 : ℝ) / 160) (tiltSelector omega 32 (selectedPosterior omega 32))
          32 omega = informativeBesselBoundary := by
  rw [tiltSelector_of_mem_informativePrefixCylinder homega]
  unfold informativeBesselBoundary forwardIIDBesselPACBayesBoundary
    forwardBesselPACBayesBoundary
  rw [posteriorHybridPenalty_of_mem_informativePrefixCylinder homega,
    selectedPosterior_of_mem_informativePrefixCylinder homega,
    truePosterior_kl_eq_log_two, selected_atom_logWeightCost_eq,
    informative_kl_eq_log_two, informative_posteriorHybridPenalty_eq]

/-! ## The common event and an actual informative good path -/

def informativeExceptionalEvent : Set BiasedBoolStream :=
  forwardIIDBesselPACBayesExceptionalEvent
    biasedBoolLaw uniformBoolPrior tiltWeight disagreementLoss
      biasedBoolCoordinateSample tilts ((1 : ℝ) / 160)

theorem informativeExceptionalEvent_mass_le_delta :
    biasedBoolStreamLaw.real informativeExceptionalEvent ≤ (1 : ℝ) / 160 := by
  letI := biasedBoolLaw_isProbabilityMeasure
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  exact forwardIIDBesselPACBayesExceptionalEvent_mass_le_delta
    (μ := biasedBoolStreamLaw) (dataLaw := biasedBoolLaw)
    (prior := uniformBoolPrior) (weight := tiltWeight)
    (loss := disagreementLoss) (sample := biasedBoolCoordinateSample)
    (lam := tilts) (delta := (1 : ℝ) / 160)
    uniformBoolPrior_isFullSupportPMF tiltWeight_isFullSupportPMF
    (by norm_num) tilts_pos tilts_lt_one
    disagreementLoss_stronglyMeasurable disagreementLoss_mem_unitInterval
    (fun k ↦ by
      change StronglyMeasurable (fun omega : ℕ → Bool ↦ omega k)
      exact (measurable_pi_apply k).stronglyMeasurable)
    biasedBoolCoordinateSample_iIndep biasedBoolCoordinateSample_hasLaw

/-- Direct instantiation of the merged end-to-end capstone. -/
theorem informative_exists_forwardIIDBesselPACBayes_event :
    ∃ goodEvent : Set BiasedBoolStream,
      biasedBoolStreamLaw.real goodEventᶜ ≤ (1 : ℝ) / 160 ∧
        ∀ omega ∈ goodEvent, ∀ j : Bool,
          ∀ posterior : Bool → ℝ, IsPMF posterior →
            ∀ n : ℕ, 2 ≤ n →
              iidPosteriorPopulationRisk biasedBoolLaw disagreementLoss posterior <
                iidPosteriorEmpiricalRisk disagreementLoss
                    biasedBoolCoordinateSample posterior n omega +
                  forwardIIDBesselPACBayesBoundary
                    uniformBoolPrior tiltWeight tilts disagreementLoss
                      biasedBoolCoordinateSample posterior ((1 : ℝ) / 160)
                        j n omega := by
  letI := biasedBoolLaw_isProbabilityMeasure
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  exact exists_forwardIIDBesselPACBayes_event
    (μ := biasedBoolStreamLaw) (dataLaw := biasedBoolLaw)
    (prior := uniformBoolPrior) (weight := tiltWeight)
    (loss := disagreementLoss) (sample := biasedBoolCoordinateSample)
    (lam := tilts) (delta := (1 : ℝ) / 160)
    uniformBoolPrior_isFullSupportPMF tiltWeight_isFullSupportPMF
    (by norm_num) tilts_pos tilts_lt_one
    disagreementLoss_stronglyMeasurable disagreementLoss_mem_unitInterval
    (fun k ↦ by
      change StronglyMeasurable (fun omega : ℕ → Bool ↦ omega k)
      exact (measurable_pi_apply k).stronglyMeasurable)
    biasedBoolCoordinateSample_iIndep biasedBoolCoordinateSample_hasLaw

theorem informative_goodCylinderPath_exists :
    ∃ omega : BiasedBoolStream,
      omega ∈ informativePrefixCylinder ∧ omega ∉ informativeExceptionalEvent := by
  by_contra h
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  have hsubset : informativePrefixCylinder ⊆ informativeExceptionalEvent := by
    intro omega homega
    by_contra hgood
    exact h ⟨omega, homega, hgood⟩
  have hmono :
      biasedBoolStreamLaw.real informativePrefixCylinder ≤
        biasedBoolStreamLaw.real informativeExceptionalEvent :=
    measureReal_mono hsubset
  have hbad := informativeExceptionalEvent_mass_le_delta
  have hcylinder := informativePrefixCylinder_mass_gt_delta
  linarith

theorem informative_selected_risk_of_not_mem
    {omega : BiasedBoolStream} (homega : omega ∉ informativeExceptionalEvent) :
    iidPosteriorPopulationRisk biasedBoolLaw disagreementLoss
        (selectedPosterior omega 32) <
      iidPosteriorEmpiricalRisk disagreementLoss biasedBoolCoordinateSample
          (selectedPosterior omega 32) 32 omega +
        forwardIIDBesselPACBayesBoundary
          uniformBoolPrior tiltWeight tilts disagreementLoss
            biasedBoolCoordinateSample (selectedPosterior omega 32)
              ((1 : ℝ) / 160)
              (tiltSelector omega 32 (selectedPosterior omega 32)) 32 omega := by
  exact forwardIIDBesselPACBayes_selected_of_not_mem
    uniformBoolPrior_isFullSupportPMF tiltWeight_isFullSupportPMF
    (by norm_num) tilts_pos tilts_lt_one
    disagreementLoss_mem_unitInterval
    (by simpa [informativeExceptionalEvent] using homega)
    (fun omega n ↦ selectedPosterior omega n)
    selectedPosterior_isPMF tiltSelector 32 (by norm_num)

theorem posteriorEmpiricalRisk_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    iidPosteriorEmpiricalRisk disagreementLoss biasedBoolCoordinateSample
        (selectedPosterior omega 32) 32 omega = (1 : ℝ) / 32 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega]
  simp [iidPosteriorEmpiricalRisk, posteriorAverage, truePosterior,
    trueEmpiricalRisk_of_mem_informativePrefixCylinder homega]

theorem posteriorPopulationRisk_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    iidPosteriorPopulationRisk biasedBoolLaw disagreementLoss
        (selectedPosterior omega 32) = (1 : ℝ) / 32 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega]
  simp [iidPosteriorPopulationRisk, posteriorAverage, truePosterior,
    true_populationRisk_eq_one_thirtyTwo]

theorem posteriorKL_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    klDiv (selectedPosterior omega 32) uniformBoolPrior = Real.log 2 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega]
  exact truePosterior_kl_eq_log_two

theorem informative_risk_lt_seventeen_thirtyTwo_of_goodCylinder
    {omega : BiasedBoolStream} (hcylinder : omega ∈ informativePrefixCylinder)
    (hgood : omega ∉ informativeExceptionalEvent) :
    iidPosteriorPopulationRisk biasedBoolLaw disagreementLoss
        (selectedPosterior omega 32) < (17 : ℝ) / 32 := by
  have hbound := informative_selected_risk_of_not_mem hgood
  rw [posteriorEmpiricalRisk_of_mem_informativePrefixCylinder hcylinder,
    besselBoundary_of_mem_informativePrefixCylinder hcylinder] at hbound
  exact hbound.trans_le (by
    have hhalf := informative_besselBoundary_lt_half
    linarith)

theorem informative_risk_lt_343_1000_of_goodCylinder
    {omega : BiasedBoolStream} (hcylinder : omega ∈ informativePrefixCylinder)
    (hgood : omega ∉ informativeExceptionalEvent) :
    iidPosteriorPopulationRisk biasedBoolLaw disagreementLoss
        (selectedPosterior omega 32) < (343 : ℝ) / 1000 := by
  have hbound := informative_selected_risk_of_not_mem hgood
  rw [posteriorEmpiricalRisk_of_mem_informativePrefixCylinder hcylinder,
    besselBoundary_of_mem_informativePrefixCylinder hcylinder] at hbound
  exact hbound.trans informative_fullRiskCeiling_lt_343_1000

/-- Final nonvacuity receipt.  It supplies one genuinely good path with the
exact reported prefix, positive sub-worst-case Bessel variance, positive KL,
an informative theorem-produced risk ceiling, and a strict same-path win over
the fixed-proxy boundary. -/
theorem informative_nonvacuous_receipt :
    ∃ omega : BiasedBoolStream,
      omega ∈ informativePrefixCylinder ∧
      omega ∉ informativeExceptionalEvent ∧
      selectedPosterior omega 32 = truePosterior ∧
      tiltSelector omega 32 (selectedPosterior omega 32) = true ∧
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin 32 ↦ selectedTrueLossSequence omega i) = (1 : ℝ) / 32 ∧
      klDiv (selectedPosterior omega 32) uniformBoolPrior = Real.log 2 ∧
      iidPosteriorPopulationRisk biasedBoolLaw disagreementLoss
          (selectedPosterior omega 32) <
        iidPosteriorEmpiricalRisk disagreementLoss biasedBoolCoordinateSample
            (selectedPosterior omega 32) 32 omega +
          forwardIIDBesselPACBayesBoundary
            uniformBoolPrior tiltWeight tilts disagreementLoss
              biasedBoolCoordinateSample (selectedPosterior omega 32)
                ((1 : ℝ) / 160)
                (tiltSelector omega 32 (selectedPosterior omega 32)) 32 omega ∧
      iidPosteriorEmpiricalRisk disagreementLoss biasedBoolCoordinateSample
            (selectedPosterior omega 32) 32 omega +
          forwardIIDBesselPACBayesBoundary
            uniformBoolPrior tiltWeight tilts disagreementLoss
              biasedBoolCoordinateSample (selectedPosterior omega 32)
                ((1 : ℝ) / 160)
                (tiltSelector omega 32 (selectedPosterior omega 32)) 32 omega <
        (343 : ℝ) / 1000 ∧
      informativeBesselBoundary < informativeSubGammaBoundary := by
  obtain ⟨omega, hcylinder, hgood⟩ := informative_goodCylinderPath_exists
  refine ⟨omega, hcylinder, hgood,
    selectedPosterior_of_mem_informativePrefixCylinder hcylinder,
    tiltSelector_of_mem_informativePrefixCylinder hcylinder,
    besselVariance_selectedTrue_of_mem hcylinder,
    posteriorKL_of_mem_informativePrefixCylinder hcylinder,
    informative_selected_risk_of_not_mem hgood, ?_,
    informative_besselBoundary_lt_subGammaBoundary⟩
  rw [posteriorEmpiricalRisk_of_mem_informativePrefixCylinder hcylinder,
    besselBoundary_of_mem_informativePrefixCylinder hcylinder]
  exact informative_fullRiskCeiling_lt_343_1000

#check exists_forwardIIDBesselPACBayes_event
#check informative_besselVariance_eq_one_thirtyTwo
#check informative_kl_eq_log_two
#check informative_kl_rational_enclosure
#check tiltSelector_oneFalse_eq_true
#check tiltSelector_balanced_eq_false
#check selectedPosterior_oneTrue_eq_false
#check selected_atom_logWeightCost_eq
#check informative_besselBoundary_eq
#check informative_subGammaBoundary_eq
#check informative_besselBoundary_rational_enclosure
#check informative_subGammaBoundary_rational_enclosure
#check informative_besselBoundary_lt_subGammaBoundary
#check informative_exists_forwardIIDBesselPACBayes_event
#check informative_goodCylinderPath_exists
#check informative_nonvacuous_receipt

#print axioms biasedBoolLaw_isProbabilityMeasure
#print axioms biasedBoolStreamLaw_isProbabilityMeasure
#print axioms biasedBoolCoordinateSample_iIndep
#print axioms biasedBoolCoordinateSample_hasLaw
#print axioms uniformBoolPrior_isFullSupportPMF
#print axioms truePosterior_isPMF
#print axioms falsePosterior_isPMF
#print axioms disagreementLoss_stronglyMeasurable
#print axioms disagreementLoss_mem_unitInterval
#print axioms selectedPosterior_isPMF
#print axioms truePosterior_kl_eq_log_two
#print axioms falsePosterior_kl_eq_log_two
#print axioms selectedPosterior_kl_eq_log_two
#print axioms tiltWeight_isFullSupportPMF
#print axioms tilts_pos
#print axioms tilts_lt_one
#print axioms selectedPosterior_oneFalse_eq_true
#print axioms informative_trueEmpiricalRisk_eq_one_thirtyTwo
#print axioms informative_falseEmpiricalRisk_eq_thirtyOne_thirtyTwo
#print axioms selectedPosterior_balanced_eq_true
#print axioms selectedPosterior_oneTrue_eq_false
#print axioms tiltSelector_oneFalse_eq_true
#print axioms tiltSelector_balanced_eq_false
#print axioms informative_empiricalRisk_eq_one_thirtyTwo
#print axioms true_populationRisk_eq_one_thirtyTwo
#print axioms informative_populationRisk_eq_one_thirtyTwo
#print axioms informative_kl_eq_log_two
#print axioms informative_kl_pos
#print axioms informative_kl_rational_enclosure
#print axioms informative_forwardBesselQ_eq
#print axioms informative_besselVariance_eq_one_thirtyTwo
#print axioms informative_besselVariance_mem_Ioo
#print axioms informative_hybridPenalty_eq
#print axioms informative_posteriorHybridPenalty_eq
#print axioms selected_atom_logWeightCost_eq
#print axioms selected_tilt_psi_eq
#print axioms informative_besselBoundary_eq
#print axioms informative_subGammaBoundary_eq
#print axioms informative_besselBoundary_rational_enclosure
#print axioms informative_subGammaBoundary_rational_enclosure
#print axioms informative_besselBoundary_le_2929_6144
#print axioms informative_besselBoundary_lt_half
#print axioms informative_subGammaBoundary_gt_half
#print axioms informative_besselBoundary_lt_subGammaBoundary
#print axioms informative_fullRiskCeiling_lt_three_fifths
#print axioms informative_fullRiskCeiling_lt_343_1000
#print axioms measurableSet_informativePrefixCylinder
#print axioms biasedBoolLaw_target_singleton
#print axioms biasedBoolStreamLaw_informativePrefixCylinder
#print axioms biasedBoolStreamLaw_real_informativePrefixCylinder
#print axioms informativePrefixCylinder_mass_gt_delta
#print axioms informativePrefixCylinder_coordinate
#print axioms trueEmpiricalRisk_of_mem_informativePrefixCylinder
#print axioms falseEmpiricalRisk_of_mem_informativePrefixCylinder
#print axioms selectedPosterior_of_mem_informativePrefixCylinder
#print axioms tiltSelector_of_mem_informativePrefixCylinder
#print axioms selectedTrueLossSequence_eq_informative_of_mem
#print axioms forwardPrefixMean_selectedTrue_eq_informative_of_mem
#print axioms forwardBesselQ_selectedTrue_of_mem
#print axioms hybridPenalty_selectedTrue_of_mem
#print axioms posteriorHybridPenalty_of_mem_informativePrefixCylinder
#print axioms besselVariance_selectedTrue_of_mem
#print axioms besselBoundary_of_mem_informativePrefixCylinder
#print axioms informativeExceptionalEvent_mass_le_delta
#print axioms informative_exists_forwardIIDBesselPACBayes_event
#print axioms informative_goodCylinderPath_exists
#print axioms informative_selected_risk_of_not_mem
#print axioms posteriorEmpiricalRisk_of_mem_informativePrefixCylinder
#print axioms posteriorPopulationRisk_of_mem_informativePrefixCylinder
#print axioms posteriorKL_of_mem_informativePrefixCylinder
#print axioms informative_risk_lt_seventeen_thirtyTwo_of_goodCylinder
#print axioms informative_risk_lt_343_1000_of_goodCylinder
#print axioms informative_nonvacuous_receipt

end

end FormalSLT.Examples.CheckForwardBesselPACBayesIIDInformative
