import FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
import FormalSLT.PACBayes.ForwardBesselPACBayesIID
import FormalSLT.PACBayes.IIDContinuousGaussian
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Informative predictable-tilt PAC-Bayes receipt

This checker instantiates the posterior-uniform, time-uniform predictable-tilt
PAC-Bayes theorem on two constant Boolean hypotheses.  The data are IID with
`P(true) = 31 / 32`.  Each hypothesis has one tilt rule fixed before the path
is observed: the rule skips the first loss, then uses tilt `1 / 4` after a
correct first prediction and tilt `1 / 2` after an incorrect first prediction.
Thus the schedule is predictable but genuinely path dependent.

On the prefix with one initial `false` label followed by 31 `true` labels, the
selected point posterior is concentrated on `true`, pays `KL = log 2`, has
total tilt `31 / 2`, and has zero tilt-weighted empirical loss.  At confidence
`1 - 1 / 128`, its checked normalized boundary is strictly below `2 / 5`.
The prefix cylinder has probability greater than `1 / 128`, so at least one
path with these statistics lies outside the common exceptional event.

The second receipt selects between two distinct predeclared predictable
strategies after observing the path.  It charges a separate `log 2` strategy
cost in addition to the `log 2` model cost and proves the checked boundary below
`7 / 16`, while retaining conditional risk `1 / 32`, zero normalized observed
loss, and positive-mass support outside the exceptional event.
-/

namespace FormalSLT.Examples.CheckForwardPredictableTiltPACBayesInformative

open Finset MeasureTheory ProbabilityTheory Real BigOperators
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniformIID
open FormalSLT.PACBayes.ForwardBesselPACBayesIID
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
open FormalSLT.PACBayes.ForwardPredictableStrategyPACBayes
open FormalSLT.PACBayes.StabilityBridge
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

theorem biasedBoolCoordinateSample_stronglyMeasurable (k : ℕ) :
    StronglyMeasurable (biasedBoolCoordinateSample k) := by
  exact (measurable_pi_apply k).stronglyMeasurable

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

abbrev streamFiltration : Filtration ℕ (inferInstance : MeasurableSpace BiasedBoolStream) :=
  Filtration.natural biasedBoolCoordinateSample
    biasedBoolCoordinateSample_stronglyMeasurable

/-! ## Two hypotheses, a selected posterior, and predictable tilts -/

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

/-- Loss revealed by process increment `k`, namely sample coordinate `k + 1`. -/
def observedLoss (h : Bool) (k : ℕ) (omega : BiasedBoolStream) : ℝ :=
  iidObservedLoss disagreementLoss biasedBoolCoordinateSample h k omega

/-- Deterministic conditional mean of each IID loss process. -/
def meanLoss (h : Bool) (_k : ℕ) (_omega : BiasedBoolStream) : ℝ :=
  iidLossPopulationRisk biasedBoolLaw disagreementLoss h

theorem observedLoss_incrementAdapted (h : Bool) :
    IncrementAdapted streamFiltration (observedLoss h) := by
  exact iidObservedLoss_incrementAdapted h
    (disagreementLoss_stronglyMeasurable h)
    biasedBoolCoordinateSample_stronglyMeasurable

theorem meanLoss_stronglyAdapted (h : Bool) :
    StronglyAdapted streamFiltration (meanLoss h) := by
  intro k
  exact stronglyMeasurable_const

theorem observedLoss_unit (h : Bool) (k : ℕ) (omega : BiasedBoolStream) :
    0 ≤ observedLoss h k omega ∧ observedLoss h k omega ≤ 1 := by
  exact disagreementLoss_mem_unitInterval h
    (biasedBoolCoordinateSample (k + 1) omega)

theorem observedLoss_condExp_eq_meanLoss (h : Bool) (k : ℕ) :
    biasedBoolStreamLaw[observedLoss h k | streamFiltration k]
        =ᵐ[biasedBoolStreamLaw] meanLoss h k := by
  letI := biasedBoolLaw_isProbabilityMeasure
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  change
    biasedBoolStreamLaw[
        iidObservedLoss disagreementLoss biasedBoolCoordinateSample h k |
          Filtration.natural biasedBoolCoordinateSample
            biasedBoolCoordinateSample_stronglyMeasurable k] =ᵐ[biasedBoolStreamLaw]
      fun _ ↦ iidLossPopulationRisk biasedBoolLaw disagreementLoss h
  exact iidObservedLoss_condExp_eq_populationRisk
    (μ := biasedBoolStreamLaw) (dataLaw := biasedBoolLaw)
    (loss := disagreementLoss) (sample := biasedBoolCoordinateSample)
    h k (disagreementLoss_stronglyMeasurable h)
    (disagreementLoss_mem_unitInterval h)
    biasedBoolCoordinateSample_stronglyMeasurable
    biasedBoolCoordinateSample_iIndep biasedBoolCoordinateSample_hasLaw

/-- After the first outcome, bet less following a correct prediction and more
following an error. -/
def afterFirstTilt (h label : Bool) : ℝ :=
  if h = label then 1 / 4 else 1 / 2

/-- Fixed-before-data predictable rule.  The first loss gets zero tilt; every
later tilt reads only the already observed first label. -/
def predictableTilt (h : Bool) (k : ℕ) (omega : BiasedBoolStream) : ℝ :=
  if k = 0 then 0 else afterFirstTilt h (biasedBoolCoordinateSample 1 omega)

theorem predictableTilt_stronglyAdapted (h : Bool) :
    StronglyAdapted streamFiltration (predictableTilt h) := by
  intro k
  change StronglyMeasurable[streamFiltration k] (predictableTilt h k)
  by_cases hk : k = 0
  · subst k
    have hfun : predictableTilt h 0 = fun _ : BiasedBoolStream ↦ (0 : ℝ) := by
      funext omega
      simp [predictableTilt]
    rw [hfun]
    exact stronglyMeasurable_const
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hsampleOne : StronglyMeasurable[streamFiltration k]
        (biasedBoolCoordinateSample 1) :=
      (Filtration.stronglyAdapted_natural
          biasedBoolCoordinateSample_stronglyMeasurable 1).mono
        (streamFiltration.mono hk1)
    have hafter : StronglyMeasurable (afterFirstTilt h) :=
      (measurable_of_finite _).stronglyMeasurable
    have hfun : predictableTilt h k =
        fun omega : BiasedBoolStream ↦
          afterFirstTilt h (biasedBoolCoordinateSample 1 omega) := by
      funext omega
      simp [predictableTilt, hk]
    rw [hfun]
    change StronglyMeasurable[streamFiltration k]
      (afterFirstTilt h ∘ biasedBoolCoordinateSample 1)
    exact hafter.comp_measurable hsampleOne.measurable

theorem predictableTilt_range (h : Bool) (k : ℕ)
    (omega : BiasedBoolStream) :
    0 ≤ predictableTilt h k omega ∧
      predictableTilt h k omega ≤ (1 / 2 : ℝ) := by
  by_cases hk : k = 0
  · simp [predictableTilt, hk]
  · cases h <;> cases hlabel : biasedBoolCoordinateSample 1 omega <;>
      norm_num [predictableTilt, afterFirstTilt, hk, hlabel]

/-- A path-selected posterior.  The first label chooses one of the two point
posteriors; the common event permits this post-observation choice. -/
def selectedPosterior (omega : BiasedBoolStream) (_n : ℕ) : Bool → ℝ :=
  if biasedBoolCoordinateSample 1 omega then falsePosterior else truePosterior

theorem selectedPosterior_isPMF (omega : BiasedBoolStream) (n : ℕ) :
    IsPMF (selectedPosterior omega n) := by
  unfold selectedPosterior
  split
  · exact falsePosterior_isPMF
  · exact truePosterior_isPMF

theorem truePosterior_kl_eq_log_two :
    klDiv truePosterior uniformBoolPrior = Real.log 2 := by
  simp [klDiv, truePosterior, uniformBoolPrior]

/-! ## Common all-time, all-posterior event -/

def informativeFailure : Set BiasedBoolStream :=
  forwardPredictableTiltPACBayesAnyPosteriorFailure
    uniformBoolPrior observedLoss meanLoss predictableTilt (1 / 128)

theorem informativeFailure_mass_le_delta :
    biasedBoolStreamLaw.real informativeFailure ≤ (1 : ℝ) / 128 := by
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  simpa [informativeFailure] using
    (forwardPredictableTiltPACBayesAnyPosteriorFailure_mass_le_delta
      (μ := biasedBoolStreamLaw) (ℱ := streamFiltration)
      (prior := uniformBoolPrior) (X := observedLoss) (mean := meanLoss)
      (lambda := predictableTilt) (L := (1 / 2 : ℝ))
      (delta := (1 / 128 : ℝ))
      uniformBoolPrior_isFullSupportPMF (by norm_num) (by norm_num)
      observedLoss_incrementAdapted meanLoss_stronglyAdapted
      predictableTilt_stronglyAdapted observedLoss_unit
      predictableTilt_range observedLoss_condExp_eq_meanLoss)

/-- Direct instantiation of the all-natural-time, all-posterior endpoint. -/
theorem informative_exists_allTime_allPosterior_event :
    ∃ goodEvent : Set BiasedBoolStream,
      biasedBoolStreamLaw.real goodEventᶜ ≤ (1 : ℝ) / 128 ∧
        ∀ omega ∈ goodEvent, ∀ posterior : Bool → ℝ, IsPMF posterior →
          ∀ n : ℕ,
            forwardPredictableTiltPosteriorMeanGap
                posterior observedLoss meanLoss predictableTilt n omega <
              klDiv posterior uniformBoolPrior + Real.log (1 / ((1 : ℝ) / 128)) +
                forwardPredictableTiltPosteriorQuadraticPenalty
                  posterior observedLoss predictableTilt n omega := by
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  exact exists_forwardPredictableTiltPACBayes_event
    (μ := biasedBoolStreamLaw) (ℱ := streamFiltration)
    uniformBoolPrior_isFullSupportPMF
    (L := (1 / 2 : ℝ)) (delta := (1 / 128 : ℝ))
    (by norm_num) (by norm_num)
    observedLoss_incrementAdapted meanLoss_stronglyAdapted
    predictableTilt_stronglyAdapted observedLoss_unit
    predictableTilt_range observedLoss_condExp_eq_meanLoss

/-! ## Positive-mass informative prefix -/

/-- Coordinate 1 is false and every other coordinate is true. -/
def oneFalseThirtyOneTrueStream : BiasedBoolStream := fun k ↦
  if k = 1 then false else true

def allTrueStream : BiasedBoolStream := fun _ ↦ true

/-- The tilt changes over time on the target path and changes across paths
after reading the first observed label. -/
theorem predictableTilt_nonconstant_prefix_witness :
    predictableTilt true 0 oneFalseThirtyOneTrueStream = 0 ∧
      predictableTilt true 1 oneFalseThirtyOneTrueStream = (1 : ℝ) / 2 ∧
      predictableTilt true 1 allTrueStream = (1 : ℝ) / 4 ∧
      predictableTilt true 1 oneFalseThirtyOneTrueStream ≠
        predictableTilt true 1 allTrueStream := by
  norm_num [predictableTilt, afterFirstTilt, biasedBoolCoordinateSample,
    oneFalseThirtyOneTrueStream, allTrueStream]

def informativePrefixTarget (k : ℕ) : Bool :=
  if k = 1 then false else true

/-- Coordinates `1, ..., 32` equal the one-false/31-true prefix. -/
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
    (1 : ℝ) / 128 <
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

theorem selectedPosterior_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    selectedPosterior omega 32 = truePosterior := by
  have hfirst := informativePrefixCylinder_coordinate homega
    (k := 0) (by norm_num)
  unfold selectedPosterior
  simp [biasedBoolCoordinateSample, oneFalseThirtyOneTrueStream] at hfirst
  simp [biasedBoolCoordinateSample, hfirst]

theorem informative_goodCylinderPath_exists :
    ∃ omega : BiasedBoolStream,
      omega ∈ informativePrefixCylinder ∧ omega ∉ informativeFailure := by
  by_contra h
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  have hsubset : informativePrefixCylinder ⊆ informativeFailure := by
    intro omega homega
    by_contra hgood
    exact h ⟨omega, homega, hgood⟩
  have hmono :
      biasedBoolStreamLaw.real informativePrefixCylinder ≤
        biasedBoolStreamLaw.real informativeFailure :=
    measureReal_mono hsubset
  have hbad := informativeFailure_mass_le_delta
  have hcylinder := informativePrefixCylinder_mass_gt_delta
  linarith

/-! ## Exact selected-prefix calculations -/

def informativeLossSequence (k : ℕ) : ℝ :=
  disagreementLoss true
    (biasedBoolCoordinateSample (k + 1) oneFalseThirtyOneTrueStream)

theorem true_populationRisk_eq_one_thirtyTwo :
    iidLossPopulationRisk biasedBoolLaw disagreementLoss true =
      (1 : ℝ) / 32 := by
  unfold iidLossPopulationRisk biasedBoolLaw
  rw [integral_bernoulliMeasure]
  norm_num [disagreementLoss]

theorem informative_forwardBesselQ_eq :
    forwardBesselQ informativeLossSequence 32 = (31 : ℝ) / 32 := by
  norm_num [forwardBesselQ, forwardPrefixMean, informativeLossSequence,
    disagreementLoss, biasedBoolCoordinateSample,
    oneFalseThirtyOneTrueStream, Finset.sum_range_succ]

theorem informative_hybridPenalty_eq :
    forwardHybridBesselPenalty informativeLossSequence 32 =
      (125 : ℝ) / 64 := by
  unfold forwardHybridBesselPenalty
  rw [informative_forwardBesselQ_eq]
  norm_num [harmonic]

def selectedTrueLossSequence (omega : BiasedBoolStream) (k : ℕ) : ℝ :=
  observedLoss true k omega

theorem selectedTrueLossSequence_eq_informative_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder)
    {k : ℕ} (hk : k < 32) :
    selectedTrueLossSequence omega k = informativeLossSequence k := by
  unfold selectedTrueLossSequence observedLoss iidObservedLoss
    informativeLossSequence
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

theorem true_predictableTilt_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder)
    (k : ℕ) :
    predictableTilt true k omega = if k = 0 then 0 else (1 : ℝ) / 2 := by
  have hfirst := informativePrefixCylinder_coordinate homega
    (k := 0) (by norm_num)
  simp [biasedBoolCoordinateSample, oneFalseThirtyOneTrueStream] at hfirst
  simp [predictableTilt, afterFirstTilt, biasedBoolCoordinateSample, hfirst]

def totalSelectedTilt (omega : BiasedBoolStream) : ℝ :=
  ∑ k ∈ Finset.range 32, predictableTilt true k omega

theorem totalSelectedTilt_eq_thirtyOne_halves_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    totalSelectedTilt omega = (31 : ℝ) / 2 := by
  unfold totalSelectedTilt
  simp_rw [true_predictableTilt_of_mem homega]
  norm_num [Finset.sum_range_succ]

theorem selected_weightedEmpiricalLoss_eq_zero_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    (∑ k ∈ Finset.range 32,
      predictableTilt true k omega * observedLoss true k omega) = 0 := by
  calc
    (∑ k ∈ Finset.range 32,
        predictableTilt true k omega * observedLoss true k omega) =
        ∑ k ∈ Finset.range 32,
          predictableTilt true k oneFalseThirtyOneTrueStream *
            observedLoss true k oneFalseThirtyOneTrueStream := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk32 := Finset.mem_range.mp hk
      have hcoord := informativePrefixCylinder_coordinate homega hk32
      unfold observedLoss iidObservedLoss
      rw [hcoord]
      rw [true_predictableTilt_of_mem homega k]
      simp [predictableTilt, afterFirstTilt, biasedBoolCoordinateSample,
        oneFalseThirtyOneTrueStream]
    _ = 0 := by
      norm_num [predictableTilt, afterFirstTilt, observedLoss, iidObservedLoss,
        disagreementLoss, biasedBoolCoordinateSample,
        oneFalseThirtyOneTrueStream, Finset.sum_range_succ]

theorem selected_point_meanGap_eq_thirtyOne_sixtyFour_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableTiltPosteriorMeanGap
        truePosterior observedLoss meanLoss predictableTilt 32 omega =
      (31 : ℝ) / 64 := by
  unfold forwardPredictableTiltPosteriorMeanGap posteriorAverage
  rw [Fintype.sum_bool]
  simp only [truePosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  rw [add_zero]
  have htilt := totalSelectedTilt_eq_thirtyOne_halves_of_mem homega
  have hemp := selected_weightedEmpiricalLoss_eq_zero_of_mem homega
  have hmean : ∀ k, meanLoss true k omega = (1 : ℝ) / 32 := by
    intro k
    simp [meanLoss, true_populationRisk_eq_one_thirtyTwo]
  simp_rw [hmean]
  calc
    (∑ k ∈ Finset.range 32,
        predictableTilt true k omega * ((1 : ℝ) / 32 - observedLoss true k omega)) =
        (1 : ℝ) / 32 * totalSelectedTilt omega -
          ∑ k ∈ Finset.range 32,
            predictableTilt true k omega * observedLoss true k omega := by
      unfold totalSelectedTilt
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (31 : ℝ) / 64 := by rw [htilt, hemp]; norm_num

theorem selected_point_quadraticPenalty_le_125_256_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableTiltPosteriorQuadraticPenalty
        truePosterior observedLoss predictableTilt 32 omega ≤
      (125 : ℝ) / 256 := by
  let x : ℕ → ℝ := selectedTrueLossSequence omega
  have hpsiNonneg :
      0 ≤ forwardEmpiricalBernsteinPsi ((1 : ℝ) / 2) :=
    forwardEmpiricalBernsteinPsi_nonneg (by norm_num) (by norm_num)
  have hsum :
      (∑ k ∈ Finset.range 32,
        forwardEmpiricalBernsteinPsi (predictableTilt true k omega) *
          (observedLoss true k omega -
            forwardPredictorProcess (observedLoss true) k omega) ^ 2) ≤
        forwardEmpiricalBernsteinPsi ((1 : ℝ) / 2) *
          forwardPredictableQuadratic x 32 := by
    unfold forwardPredictableQuadratic
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [true_predictableTilt_of_mem homega k]
    by_cases hk0 : k = 0
    · subst k
      simp only [if_pos]
      rw [show forwardEmpiricalBernsteinPsi 0 = 0 by
        simp [forwardEmpiricalBernsteinPsi], zero_mul]
      exact mul_nonneg hpsiNonneg
        (sq_nonneg (x 0 - forwardPredictor x 0))
    · simp only [hk0, if_false]
      rfl
  have hxUnit : ∀ i < 32, 0 ≤ x i ∧ x i ≤ 1 := by
    intro i hi
    exact observedLoss_unit true i omega
  have hQ : forwardPredictableQuadratic x 32 ≤ (125 : ℝ) / 64 := by
    have h := forwardPredictableQuadratic_le_hybrid_bessel
      x (by norm_num) hxUnit
    rw [hybridPenalty_selectedTrue_of_mem homega] at h
    exact h
  have hpsi :
      forwardEmpiricalBernsteinPsi ((1 : ℝ) / 2) ≤ (1 : ℝ) / 4 := by
    have h := forwardEmpiricalBernsteinPsi_le_quadratic
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 < 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hQnonneg : 0 ≤ forwardPredictableQuadratic x 32 := by
    unfold forwardPredictableQuadratic
    positivity
  unfold forwardPredictableTiltPosteriorQuadraticPenalty posteriorAverage
  rw [Fintype.sum_bool]
  simp only [truePosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  rw [add_zero]
  calc
    (∑ k ∈ Finset.range 32,
        forwardEmpiricalBernsteinPsi (predictableTilt true k omega) *
          (observedLoss true k omega -
            forwardPredictorProcess (observedLoss true) k omega) ^ 2) ≤
        forwardEmpiricalBernsteinPsi ((1 : ℝ) / 2) *
          forwardPredictableQuadratic x 32 := hsum
    _ ≤ (1 : ℝ) / 4 * forwardPredictableQuadratic x 32 :=
      mul_le_mul_of_nonneg_right hpsi hQnonneg
    _ ≤ (1 : ℝ) / 4 * ((125 : ℝ) / 64) :=
      mul_le_mul_of_nonneg_left hQ (by norm_num)
    _ = (125 : ℝ) / 256 := by norm_num

theorem selected_complexity_eq_eight_log_two_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    klDiv (selectedPosterior omega 32) uniformBoolPrior +
        Real.log (1 / ((1 : ℝ) / 128)) =
      8 * Real.log 2 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega,
    truePosterior_kl_eq_log_two]
  norm_num
  rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
  ring

/-- Normalized selected-posterior boundary; the denominator is the exact
positive selected total tilt on the informative prefix. -/
def informativeBoundary (omega : BiasedBoolStream) : ℝ :=
  (klDiv (selectedPosterior omega 32) uniformBoolPrior +
      Real.log (1 / ((1 : ℝ) / 128)) +
      forwardPredictableTiltPosteriorQuadraticPenalty
        (selectedPosterior omega 32) observedLoss predictableTilt 32 omega) /
    ((31 : ℝ) / 2)

theorem informativeBoundary_lt_two_fifths_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    informativeBoundary omega < (2 : ℝ) / 5 := by
  have hcomplexity := selected_complexity_eq_eight_log_two_of_mem homega
  have hposterior := selectedPosterior_of_mem_informativePrefixCylinder homega
  have hpenalty := selected_point_quadraticPenalty_le_125_256_of_mem homega
  have hlog : Real.log 2 < (7 : ℝ) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold informativeBoundary
  rw [hposterior]
  rw [show klDiv truePosterior uniformBoolPrior +
      Real.log (1 / ((1 : ℝ) / 128)) = 8 * Real.log 2 by
    simpa [hposterior] using hcomplexity]
  nlinarith

def selectedPopulationRisk (omega : BiasedBoolStream) : ℝ :=
  posteriorAverage (selectedPosterior omega 32)
    (iidLossPopulationRisk biasedBoolLaw disagreementLoss)

theorem selectedPopulationRisk_eq_one_thirtyTwo_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    selectedPopulationRisk omega = (1 : ℝ) / 32 := by
  rw [selectedPopulationRisk,
    selectedPosterior_of_mem_informativePrefixCylinder homega]
  simp [posteriorAverage, truePosterior, true_populationRisk_eq_one_thirtyTwo]

theorem selected_totalWeight_eq_thirtyOne_halves_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableTiltPosteriorTotalWeight
        (selectedPosterior omega 32) predictableTilt 32 omega =
      (31 : ℝ) / 2 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega]
  unfold forwardPredictableTiltPosteriorTotalWeight posteriorAverage
  rw [Fintype.sum_bool]
  simp only [truePosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul, add_zero]
  exact totalSelectedTilt_eq_thirtyOne_halves_of_mem homega

theorem selected_normalizedObservation_eq_zero_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableTiltPosteriorNormalizedObservation
        (selectedPosterior omega 32) observedLoss predictableTilt 32 omega = 0 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega]
  unfold forwardPredictableTiltPosteriorNormalizedObservation posteriorAverage
  rw [Fintype.sum_bool]
  simp only [truePosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul, add_zero]
  rw [selected_weightedEmpiricalLoss_eq_zero_of_mem homega]
  exact zero_div _

theorem selected_normalizedMean_eq_populationRisk_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableTiltPosteriorNormalizedMean
        (selectedPosterior omega 32) meanLoss predictableTilt 32 omega =
      selectedPopulationRisk omega := by
  have hidentity :=
    forwardPredictableTiltPosteriorNormalizedMean_sub_observation
      (selectedPosterior omega 32) observedLoss meanLoss predictableTilt 32 omega
  have hposterior :=
    selectedPosterior_of_mem_informativePrefixCylinder homega
  have hgap :
      forwardPredictableTiltPosteriorMeanGap
          (selectedPosterior omega 32) observedLoss meanLoss predictableTilt 32 omega =
        (31 : ℝ) / 64 := by
    rw [hposterior]
    exact selected_point_meanGap_eq_thirtyOne_sixtyFour_of_mem homega
  rw [selected_normalizedObservation_eq_zero_of_mem homega,
    hgap, selected_totalWeight_eq_thirtyOne_halves_of_mem homega] at hidentity
  rw [selectedPopulationRisk_eq_one_thirtyTwo_of_mem homega]
  norm_num at hidentity ⊢
  exact hidentity

theorem selectedPopulationRisk_lt_boundary_of_not_mem
    {omega : BiasedBoolStream} (hcylinder : omega ∈ informativePrefixCylinder)
    (hgood : omega ∉ informativeFailure) :
    selectedPopulationRisk omega < informativeBoundary omega := by
  have hweight : 0 < forwardPredictableTiltPosteriorTotalWeight
      (selectedPosterior omega 32) predictableTilt 32 omega := by
    rw [selected_totalWeight_eq_thirtyOne_halves_of_mem hcylinder]
    norm_num
  have hbound := forwardPredictableTiltPACBayes_normalized_selected_of_not_mem
    (prior := uniformBoolPrior) (X := observedLoss) (mean := meanLoss)
    (lambda := predictableTilt) (delta := (1 / 128 : ℝ))
    (by simpa [informativeFailure] using hgood)
    selectedPosterior selectedPosterior_isPMF 32 hweight
  rw [selected_normalizedMean_eq_populationRisk_of_mem hcylinder,
    selected_normalizedObservation_eq_zero_of_mem hcylinder,
    selected_totalWeight_eq_thirtyOne_halves_of_mem hcylinder,
    zero_add] at hbound
  simpa [informativeBoundary] using hbound

/-- Final theorem-produced nonvacuity receipt. -/
theorem informative_nonvacuous_receipt :
    ∃ omega : BiasedBoolStream,
      omega ∈ informativePrefixCylinder ∧
      omega ∉ informativeFailure ∧
      selectedPosterior omega 32 = truePosterior ∧
      predictableTilt true 0 omega = 0 ∧
      predictableTilt true 1 omega = (1 : ℝ) / 2 ∧
      totalSelectedTilt omega = (31 : ℝ) / 2 ∧
      (∑ k ∈ Finset.range 32,
        predictableTilt true k omega * observedLoss true k omega) = 0 ∧
      klDiv (selectedPosterior omega 32) uniformBoolPrior = Real.log 2 ∧
      forwardPredictableTiltPosteriorQuadraticPenalty
          (selectedPosterior omega 32) observedLoss predictableTilt 32 omega ≤
        (125 : ℝ) / 256 ∧
      selectedPopulationRisk omega < informativeBoundary omega ∧
      informativeBoundary omega < (2 : ℝ) / 5 := by
  obtain ⟨omega, hcylinder, hgood⟩ := informative_goodCylinderPath_exists
  have hposterior := selectedPosterior_of_mem_informativePrefixCylinder hcylinder
  have htilt := true_predictableTilt_of_mem hcylinder
  refine ⟨omega, hcylinder, hgood, hposterior, ?_, ?_,
    totalSelectedTilt_eq_thirtyOne_halves_of_mem hcylinder,
    selected_weightedEmpiricalLoss_eq_zero_of_mem hcylinder, ?_, ?_,
    selectedPopulationRisk_lt_boundary_of_not_mem hcylinder hgood,
    informativeBoundary_lt_two_fifths_of_mem hcylinder⟩
  · simpa using htilt 0
  · simpa using htilt 1
  · rw [hposterior]
    exact truePosterior_kl_eq_log_two
  · rw [hposterior]
    exact selected_point_quadraticPenalty_le_125_256_of_mem hcylinder

/-! ## Exact post-data model--strategy selection receipt -/

/-- A second predeclared strategy.  It skips the first loss and then uses the
fixed conservative tilt `1 / 4`. -/
def conservativePredictableTilt (_h : Bool) (k : ℕ)
    (_omega : BiasedBoolStream) : ℝ :=
  if k = 0 then 0 else 1 / 4

theorem conservativePredictableTilt_stronglyAdapted (h : Bool) :
    StronglyAdapted streamFiltration (conservativePredictableTilt h) := by
  intro k
  change StronglyMeasurable[streamFiltration k]
    (fun _ : BiasedBoolStream ↦ if k = 0 then (0 : ℝ) else 1 / 4)
  exact stronglyMeasurable_const

theorem conservativePredictableTilt_range (h : Bool) (k : ℕ)
    (omega : BiasedBoolStream) :
    0 ≤ conservativePredictableTilt h k omega ∧
      conservativePredictableTilt h k omega ≤ (1 / 2 : ℝ) := by
  by_cases hk : k = 0
  · simp [conservativePredictableTilt, hk]
  · norm_num [conservativePredictableTilt, hk]

/-- Two strategies declared before observation: the genuinely path-dependent
rule from the first receipt and a conservative constant-after-first rule. -/
def informativeStrategyCatalog (j h : Bool) (k : ℕ)
    (omega : BiasedBoolStream) : ℝ :=
  if j then predictableTilt h k omega else conservativePredictableTilt h k omega

theorem informativeStrategyCatalog_stronglyAdapted (j h : Bool) :
    StronglyAdapted streamFiltration (informativeStrategyCatalog j h) := by
  cases j
  · intro k
    change StronglyMeasurable[streamFiltration k]
      (conservativePredictableTilt h k)
    exact conservativePredictableTilt_stronglyAdapted h k
  · intro k
    change StronglyMeasurable[streamFiltration k] (predictableTilt h k)
    exact predictableTilt_stronglyAdapted h k

theorem informativeStrategyCatalog_range (j h : Bool) (k : ℕ)
    (omega : BiasedBoolStream) :
    0 ≤ informativeStrategyCatalog j h k omega ∧
      informativeStrategyCatalog j h k omega ≤ (1 / 2 : ℝ) := by
  cases j
  · simpa [informativeStrategyCatalog] using
      conservativePredictableTilt_range h k omega
  · simpa [informativeStrategyCatalog] using predictableTilt_range h k omega

/-- The strategy posterior is selected after observing the path.  Reusing the
same Boolean selector keeps the receipt small; the strategy catalog above is
separate from the model catalog. -/
def selectedStrategyPosterior (omega : BiasedBoolStream) (n : ℕ) : Bool → ℝ :=
  selectedPosterior omega n

theorem selectedStrategyPosterior_isPMF (omega : BiasedBoolStream) (n : ℕ) :
    IsPMF (selectedStrategyPosterior omega n) := by
  exact selectedPosterior_isPMF omega n

/-- The post-data strategy selector is not a fixed posterior. -/
theorem selectedStrategyPosterior_pathDependent_witness :
    selectedStrategyPosterior oneFalseThirtyOneTrueStream 32 = truePosterior ∧
      selectedStrategyPosterior allTrueStream 32 = falsePosterior := by
  constructor <;>
    simp [selectedStrategyPosterior, selectedPosterior,
      biasedBoolCoordinateSample, oneFalseThirtyOneTrueStream, allTrueStream]

/-- The two predeclared strategies make different bets on the receipt path. -/
theorem informativeStrategyCatalog_distinct_witness :
    informativeStrategyCatalog true true 1 oneFalseThirtyOneTrueStream =
        (1 : ℝ) / 2 ∧
      informativeStrategyCatalog false true 1 oneFalseThirtyOneTrueStream =
        (1 : ℝ) / 4 := by
  norm_num [informativeStrategyCatalog, predictableTilt,
    conservativePredictableTilt, afterFirstTilt, biasedBoolCoordinateSample,
    oneFalseThirtyOneTrueStream]

theorem selectedStrategyPosterior_of_mem_informativePrefixCylinder
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    selectedStrategyPosterior omega 32 = truePosterior := by
  simpa [selectedStrategyPosterior] using
    selectedPosterior_of_mem_informativePrefixCylinder homega

theorem selectedStrategy_kl_eq_log_two_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    klDiv (selectedStrategyPosterior omega 32) uniformBoolPrior = Real.log 2 := by
  rw [selectedStrategyPosterior_of_mem_informativePrefixCylinder homega]
  exact truePosterior_kl_eq_log_two

/-- Factorized selected posterior on model--strategy pairs. -/
def selectedModelStrategyPosterior (omega : BiasedBoolStream) (n : ℕ) :
    Bool × Bool → ℝ :=
  modelStrategyProductPrior
    (selectedPosterior omega n) (selectedStrategyPosterior omega n)

theorem selectedModelStrategyPosterior_isPMF
    (omega : BiasedBoolStream) (n : ℕ) :
    IsPMF (selectedModelStrategyPosterior omega n) := by
  exact modelStrategyProductPrior_isPMF
    (selectedPosterior_isPMF omega n)
    (selectedStrategyPosterior_isPMF omega n)

theorem selectedModelStrategyPosterior_eq_dirac_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    selectedModelStrategyPosterior omega 32 = diracPosterior (true, true) := by
  unfold selectedModelStrategyPosterior
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega,
    selectedStrategyPosterior_of_mem_informativePrefixCylinder homega]
  funext p
  rcases p with ⟨i, j⟩
  cases i <;> cases j <;>
    simp [modelStrategyProductPrior, truePosterior, diracPosterior]

theorem posteriorAverage_dirac_true_true (g : Bool × Bool → ℝ) :
    posteriorAverage (diracPosterior (true, true)) g = g (true, true) := by
  unfold posteriorAverage diracPosterior
  rw [Fintype.sum_prod_type]
  simp

theorem selectedStrategy_totalWeight_eq_thirtyOne_halves_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableStrategyPosteriorTotalWeight
        (selectedModelStrategyPosterior omega 32)
        informativeStrategyCatalog 32 omega = (31 : ℝ) / 2 := by
  rw [selectedModelStrategyPosterior_eq_dirac_of_mem homega]
  unfold forwardPredictableStrategyPosteriorTotalWeight
    forwardPredictableTiltPosteriorTotalWeight
  rw [posteriorAverage_dirac_true_true]
  simpa [modelStrategyPredictableTilt, informativeStrategyCatalog,
    totalSelectedTilt] using totalSelectedTilt_eq_thirtyOne_halves_of_mem homega

theorem selectedStrategy_normalizedObservation_eq_zero_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableStrategyPosteriorNormalizedObservation
        (selectedModelStrategyPosterior omega 32) observedLoss
        informativeStrategyCatalog 32 omega = 0 := by
  rw [selectedModelStrategyPosterior_eq_dirac_of_mem homega]
  unfold forwardPredictableStrategyPosteriorNormalizedObservation
    forwardPredictableTiltPosteriorNormalizedObservation
    forwardPredictableTiltPosteriorTotalWeight
  rw [posteriorAverage_dirac_true_true, posteriorAverage_dirac_true_true]
  simp only [modelStrategyProcess, modelStrategyPredictableTilt,
    informativeStrategyCatalog, if_true]
  rw [selected_weightedEmpiricalLoss_eq_zero_of_mem homega]
  exact zero_div _

theorem selectedStrategy_normalizedMean_eq_populationRisk_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableStrategyPosteriorNormalizedMean
        (selectedModelStrategyPosterior omega 32) meanLoss
        informativeStrategyCatalog 32 omega = selectedPopulationRisk omega := by
  rw [selectedModelStrategyPosterior_eq_dirac_of_mem homega]
  unfold forwardPredictableStrategyPosteriorNormalizedMean
    forwardPredictableTiltPosteriorNormalizedMean
    forwardPredictableTiltPosteriorTotalWeight
  rw [posteriorAverage_dirac_true_true, posteriorAverage_dirac_true_true]
  simp only [modelStrategyProcess, modelStrategyPredictableTilt,
    informativeStrategyCatalog, if_true]
  have hmean : ∀ k, meanLoss true k omega = (1 : ℝ) / 32 := by
    intro k
    simp [meanLoss, true_populationRisk_eq_one_thirtyTwo]
  simp_rw [hmean]
  have hsum :
      (∑ k ∈ Finset.range 32,
        predictableTilt true k omega * ((1 : ℝ) / 32)) =
        (1 : ℝ) / 32 * totalSelectedTilt omega := by
    unfold totalSelectedTilt
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hdenom :
      (∑ k ∈ Finset.range 32, predictableTilt true k omega) =
        totalSelectedTilt omega := rfl
  rw [hsum, hdenom, totalSelectedTilt_eq_thirtyOne_halves_of_mem homega]
  rw [selectedPopulationRisk_eq_one_thirtyTwo_of_mem homega]
  norm_num

theorem selectedStrategy_quadraticPenalty_le_125_256_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableStrategyPosteriorQuadraticPenalty
        (selectedModelStrategyPosterior omega 32) observedLoss
        informativeStrategyCatalog 32 omega ≤ (125 : ℝ) / 256 := by
  rw [selectedModelStrategyPosterior_eq_dirac_of_mem homega]
  unfold forwardPredictableStrategyPosteriorQuadraticPenalty
    forwardPredictableTiltPosteriorQuadraticPenalty
  rw [posteriorAverage_dirac_true_true]
  simp only [modelStrategyProcess, modelStrategyPredictableTilt,
    informativeStrategyCatalog, if_true]
  have hpenalty := selected_point_quadraticPenalty_le_125_256_of_mem homega
  unfold forwardPredictableTiltPosteriorQuadraticPenalty posteriorAverage at hpenalty
  rw [Fintype.sum_bool] at hpenalty
  simpa [truePosterior] using hpenalty

/-- Exact factorized selected boundary.  The first `KL` is model selection and
the second, separately visible `KL`, is post-data strategy selection. -/
def informativeStrategyBoundary (omega : BiasedBoolStream) : ℝ :=
  (((klDiv (selectedPosterior omega 32) uniformBoolPrior +
        klDiv (selectedStrategyPosterior omega 32) uniformBoolPrior) +
      Real.log (1 / ((1 : ℝ) / 128)) +
      forwardPredictableStrategyPosteriorQuadraticPenalty
        (selectedModelStrategyPosterior omega 32) observedLoss
        informativeStrategyCatalog 32 omega) /
    ((31 : ℝ) / 2))

theorem selectedStrategy_complexity_eq_nine_log_two_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    (klDiv (selectedPosterior omega 32) uniformBoolPrior +
          klDiv (selectedStrategyPosterior omega 32) uniformBoolPrior) +
        Real.log (1 / ((1 : ℝ) / 128)) = 9 * Real.log 2 := by
  rw [selectedPosterior_of_mem_informativePrefixCylinder homega,
    selectedStrategyPosterior_of_mem_informativePrefixCylinder homega,
    truePosterior_kl_eq_log_two]
  norm_num
  rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
  ring

theorem informativeStrategyBoundary_lt_seven_sixteenths_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    informativeStrategyBoundary omega < (7 : ℝ) / 16 := by
  have hcomplexity := selectedStrategy_complexity_eq_nine_log_two_of_mem homega
  have hpenalty := selectedStrategy_quadraticPenalty_le_125_256_of_mem homega
  have hlog : Real.log 2 < (6932 : ℝ) / 10000 :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold informativeStrategyBoundary
  rw [hcomplexity]
  nlinarith

/-- The theorem-produced model--strategy certificate remains nonvacuous after
charging a separate positive `log 2` cost for post-data strategy selection. -/
theorem informative_strategySelection_nonvacuous_receipt :
    ∃ goodEvent : Set BiasedBoolStream, ∃ omega : BiasedBoolStream,
      biasedBoolStreamLaw.real goodEventᶜ ≤ (1 : ℝ) / 128 ∧
      omega ∈ goodEvent ∧
      omega ∈ informativePrefixCylinder ∧
      selectedPosterior omega 32 = truePosterior ∧
      selectedStrategyPosterior omega 32 = truePosterior ∧
      klDiv (selectedPosterior omega 32) uniformBoolPrior = Real.log 2 ∧
      klDiv (selectedStrategyPosterior omega 32) uniformBoolPrior = Real.log 2 ∧
      informativeStrategyCatalog true true 1 omega = (1 : ℝ) / 2 ∧
      informativeStrategyCatalog false true 1 omega = (1 : ℝ) / 4 ∧
      forwardPredictableStrategyPosteriorTotalWeight
          (selectedModelStrategyPosterior omega 32)
          informativeStrategyCatalog 32 omega = (31 : ℝ) / 2 ∧
      forwardPredictableStrategyPosteriorNormalizedObservation
          (selectedModelStrategyPosterior omega 32) observedLoss
          informativeStrategyCatalog 32 omega = 0 ∧
      selectedPopulationRisk omega = (1 : ℝ) / 32 ∧
      forwardPredictableStrategyPosteriorQuadraticPenalty
          (selectedModelStrategyPosterior omega 32) observedLoss
          informativeStrategyCatalog 32 omega ≤ (125 : ℝ) / 256 ∧
      selectedPopulationRisk omega < informativeStrategyBoundary omega ∧
      informativeStrategyBoundary omega < (7 : ℝ) / 16 := by
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_forwardPredictableStrategyPACBayes_factorized_normalized_selected_event
      (μ := biasedBoolStreamLaw) (ℱ := streamFiltration)
      (modelPrior := uniformBoolPrior) uniformBoolPrior_isFullSupportPMF
      (strategyPrior := uniformBoolPrior) uniformBoolPrior_isFullSupportPMF
      (X := observedLoss) (mean := meanLoss)
      (lambda := informativeStrategyCatalog)
      (L := (1 / 2 : ℝ)) (delta := (1 / 128 : ℝ))
      (by norm_num) (by norm_num)
      observedLoss_incrementAdapted meanLoss_stronglyAdapted
      informativeStrategyCatalog_stronglyAdapted observedLoss_unit
      informativeStrategyCatalog_range observedLoss_condExp_eq_meanLoss
      selectedPosterior selectedPosterior_isPMF
      selectedStrategyPosterior selectedStrategyPosterior_isPMF
  have hintersection : ∃ omega : BiasedBoolStream,
      omega ∈ informativePrefixCylinder ∧ omega ∈ goodEvent := by
    by_contra hnone
    have hsubset : informativePrefixCylinder ⊆ goodEventᶜ := by
      intro omega hcylinder
      by_contra hcomplement
      exact hnone ⟨omega, hcylinder, by simpa using hcomplement⟩
    have hmono :
        biasedBoolStreamLaw.real informativePrefixCylinder ≤
          biasedBoolStreamLaw.real goodEventᶜ :=
      measureReal_mono hsubset
    linarith [informativePrefixCylinder_mass_gt_delta]
  obtain ⟨omega, hcylinder, hgoodOmega⟩ := hintersection
  have hmodel := selectedPosterior_of_mem_informativePrefixCylinder hcylinder
  have hstrategy :=
    selectedStrategyPosterior_of_mem_informativePrefixCylinder hcylinder
  have hweight := selectedStrategy_totalWeight_eq_thirtyOne_halves_of_mem hcylinder
  have hweightPos : 0 <
      forwardPredictableStrategyPosteriorTotalWeight
        (selectedModelStrategyPosterior omega 32)
        informativeStrategyCatalog 32 omega := by
    rw [hweight]
    norm_num
  have hbound := hgood omega hgoodOmega 32 hweightPos
  have hriskBound :
      selectedPopulationRisk omega < informativeStrategyBoundary omega := by
    have hposteriorDef :
        modelStrategyProductPrior
            (selectedPosterior omega 32) (selectedStrategyPosterior omega 32) =
          selectedModelStrategyPosterior omega 32 := rfl
    rw [hposteriorDef] at hbound
    rw [selectedStrategy_normalizedMean_eq_populationRisk_of_mem hcylinder,
      selectedStrategy_normalizedObservation_eq_zero_of_mem hcylinder,
      hweight, zero_add] at hbound
    simpa [selectedModelStrategyPosterior, informativeStrategyBoundary] using hbound
  have hselectedTilt := true_predictableTilt_of_mem hcylinder
  refine ⟨goodEvent, omega, hmass, hgoodOmega, hcylinder, hmodel, hstrategy,
    ?_, ?_, ?_, ?_, hweight,
    selectedStrategy_normalizedObservation_eq_zero_of_mem hcylinder,
    selectedPopulationRisk_eq_one_thirtyTwo_of_mem hcylinder,
    selectedStrategy_quadraticPenalty_le_125_256_of_mem hcylinder,
    hriskBound, informativeStrategyBoundary_lt_seven_sixteenths_of_mem hcylinder⟩
  · rw [hmodel]
    exact truePosterior_kl_eq_log_two
  · exact selectedStrategy_kl_eq_log_two_of_mem hcylinder
  · simpa [informativeStrategyCatalog] using hselectedTilt 1
  · simp [informativeStrategyCatalog, conservativePredictableTilt]

/-! ## Shared history-dependent strategies and ordinary risk -/

/-- The same two strategies, now shared across models.  The first strategy is
still genuinely path dependent: it uses the Boolean-`true` hypothesis's first
revealed loss to choose every later tilt. -/
def sharedInformativeStrategyCatalog (j : Bool) (k : ℕ)
    (omega : BiasedBoolStream) : ℝ :=
  informativeStrategyCatalog j true k omega

theorem sharedInformativeStrategyCatalog_stronglyAdapted (j : Bool) :
    StronglyAdapted streamFiltration (sharedInformativeStrategyCatalog j) := by
  exact informativeStrategyCatalog_stronglyAdapted j true

theorem sharedInformativeStrategyCatalog_range (j : Bool) (k : ℕ)
    (omega : BiasedBoolStream) :
    0 ≤ sharedInformativeStrategyCatalog j k omega ∧
      sharedInformativeStrategyCatalog j k omega ≤ (1 / 2 : ℝ) := by
  exact informativeStrategyCatalog_range j true k omega

theorem selectedSharedStrategy_totalWeight_eq_thirtyOne_halves_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableStrategyPosteriorTotalWeight
        (selectedModelStrategyPosterior omega 32)
        (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega =
      (31 : ℝ) / 2 := by
  rw [selectedModelStrategyPosterior_eq_dirac_of_mem homega]
  unfold forwardPredictableStrategyPosteriorTotalWeight
    forwardPredictableTiltPosteriorTotalWeight
  rw [posteriorAverage_dirac_true_true]
  simpa [modelStrategyPredictableTilt, sharedInformativeStrategyCatalog,
    informativeStrategyCatalog, totalSelectedTilt] using
      totalSelectedTilt_eq_thirtyOne_halves_of_mem homega

theorem selectedSharedStrategy_normalizedObservation_eq_zero_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableStrategyPosteriorNormalizedObservation
        (selectedModelStrategyPosterior omega 32) observedLoss
        (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega = 0 := by
  rw [selectedModelStrategyPosterior_eq_dirac_of_mem homega]
  unfold forwardPredictableStrategyPosteriorNormalizedObservation
    forwardPredictableTiltPosteriorNormalizedObservation
    forwardPredictableTiltPosteriorTotalWeight
  rw [posteriorAverage_dirac_true_true, posteriorAverage_dirac_true_true]
  simp only [modelStrategyProcess, modelStrategyPredictableTilt,
    sharedInformativeStrategyCatalog, informativeStrategyCatalog, if_true]
  rw [selected_weightedEmpiricalLoss_eq_zero_of_mem homega]
  exact zero_div _

theorem selectedSharedStrategy_quadraticPenalty_le_125_256_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    forwardPredictableStrategyPosteriorQuadraticPenalty
        (selectedModelStrategyPosterior omega 32) observedLoss
        (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega ≤
      (125 : ℝ) / 256 := by
  rw [selectedModelStrategyPosterior_eq_dirac_of_mem homega]
  unfold forwardPredictableStrategyPosteriorQuadraticPenalty
    forwardPredictableTiltPosteriorQuadraticPenalty
  rw [posteriorAverage_dirac_true_true]
  simp only [modelStrategyProcess, modelStrategyPredictableTilt,
    sharedInformativeStrategyCatalog, informativeStrategyCatalog, if_true]
  have hpenalty := selected_point_quadraticPenalty_le_125_256_of_mem homega
  unfold forwardPredictableTiltPosteriorQuadraticPenalty posteriorAverage at hpenalty
  rw [Fintype.sum_bool] at hpenalty
  simpa [truePosterior] using hpenalty

def informativeSharedStrategyBoundary (omega : BiasedBoolStream) : ℝ :=
  (((klDiv (selectedPosterior omega 32) uniformBoolPrior +
        klDiv (selectedStrategyPosterior omega 32) uniformBoolPrior) +
      Real.log (1 / ((1 : ℝ) / 128)) +
      forwardPredictableStrategyPosteriorQuadraticPenalty
        (selectedModelStrategyPosterior omega 32) observedLoss
        (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega) /
    ((31 : ℝ) / 2))

theorem informativeSharedStrategyBoundary_lt_seven_sixteenths_of_mem
    {omega : BiasedBoolStream} (homega : omega ∈ informativePrefixCylinder) :
    informativeSharedStrategyBoundary omega < (7 : ℝ) / 16 := by
  have hcomplexity := selectedStrategy_complexity_eq_nine_log_two_of_mem homega
  have hpenalty :=
    selectedSharedStrategy_quadraticPenalty_le_125_256_of_mem homega
  have hlog : Real.log 2 < (6932 : ℝ) / 10000 :=
    Real.log_two_lt_d9.trans (by norm_num)
  unfold informativeSharedStrategyBoundary
  rw [hcomplexity]
  nlinarith

/-- Direct exact receipt for the ordinary-risk theorem with a finite catalog
of shared, history-dependent predictable strategies.  Model and strategy
posteriors are both selected from the observed path and each pays `log 2`.
The target `1 / 32` is the posterior average of the supplied constant
conditional model risks. -/
theorem informative_sharedStrategy_ordinaryRisk_nonvacuous_receipt :
    ∃ goodEvent : Set BiasedBoolStream, ∃ omega : BiasedBoolStream,
      biasedBoolStreamLaw.real goodEventᶜ ≤ (1 : ℝ) / 128 ∧
      omega ∈ goodEvent ∧
      omega ∈ informativePrefixCylinder ∧
      selectedPosterior omega 32 = truePosterior ∧
      selectedStrategyPosterior omega 32 = truePosterior ∧
      klDiv (selectedPosterior omega 32) uniformBoolPrior = Real.log 2 ∧
      klDiv (selectedStrategyPosterior omega 32) uniformBoolPrior = Real.log 2 ∧
      sharedInformativeStrategyCatalog true 1 omega = (1 : ℝ) / 2 ∧
      sharedInformativeStrategyCatalog false 1 omega = (1 : ℝ) / 4 ∧
      forwardPredictableStrategyPosteriorTotalWeight
          (selectedModelStrategyPosterior omega 32)
          (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega =
        (31 : ℝ) / 2 ∧
      forwardPredictableStrategyPosteriorNormalizedObservation
          (selectedModelStrategyPosterior omega 32) observedLoss
          (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega = 0 ∧
      selectedPopulationRisk omega = (1 : ℝ) / 32 ∧
      forwardPredictableStrategyPosteriorQuadraticPenalty
          (selectedModelStrategyPosterior omega 32) observedLoss
          (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega ≤
        (125 : ℝ) / 256 ∧
      selectedPopulationRisk omega < informativeSharedStrategyBoundary omega ∧
      informativeSharedStrategyBoundary omega < (7 : ℝ) / 16 := by
  letI := biasedBoolStreamLaw_isProbabilityMeasure
  obtain ⟨goodEvent, hmass, hgood⟩ :=
    exists_forwardPredictableStrategyPACBayes_shared_constantMean_factorized_ordinaryRisk_event
      (μ := biasedBoolStreamLaw) (ℱ := streamFiltration)
      (modelPrior := uniformBoolPrior) uniformBoolPrior_isFullSupportPMF
      (strategyPrior := uniformBoolPrior) uniformBoolPrior_isFullSupportPMF
      (risk := iidLossPopulationRisk biasedBoolLaw disagreementLoss)
      (X := observedLoss) (lambda := sharedInformativeStrategyCatalog)
      (L := (1 / 2 : ℝ)) (delta := (1 / 128 : ℝ))
      (by norm_num) (by norm_num) observedLoss_incrementAdapted
      sharedInformativeStrategyCatalog_stronglyAdapted observedLoss_unit
      sharedInformativeStrategyCatalog_range
      (fun h k ↦ by
        change biasedBoolStreamLaw[observedLoss h k | streamFiltration k]
          =ᵐ[biasedBoolStreamLaw] meanLoss h k
        exact observedLoss_condExp_eq_meanLoss h k)
  have hintersection : ∃ omega : BiasedBoolStream,
      omega ∈ informativePrefixCylinder ∧ omega ∈ goodEvent := by
    by_contra hnone
    have hsubset : informativePrefixCylinder ⊆ goodEventᶜ := by
      intro omega hcylinder
      by_contra hcomplement
      exact hnone ⟨omega, hcylinder, by simpa using hcomplement⟩
    have hmono :
        biasedBoolStreamLaw.real informativePrefixCylinder ≤
          biasedBoolStreamLaw.real goodEventᶜ :=
      measureReal_mono hsubset
    linarith [informativePrefixCylinder_mass_gt_delta]
  obtain ⟨omega, hcylinder, hgoodOmega⟩ := hintersection
  have hmodel := selectedPosterior_of_mem_informativePrefixCylinder hcylinder
  have hstrategy :=
    selectedStrategyPosterior_of_mem_informativePrefixCylinder hcylinder
  have hweight :=
    selectedSharedStrategy_totalWeight_eq_thirtyOne_halves_of_mem hcylinder
  have hweightPos : 0 <
      forwardPredictableStrategyPosteriorTotalWeight
        (selectedModelStrategyPosterior omega 32)
        (fun j _h ↦ sharedInformativeStrategyCatalog j) 32 omega := by
    rw [hweight]
    norm_num
  have hbound := hgood omega hgoodOmega
    (selectedPosterior omega 32) (selectedPosterior_isPMF omega 32)
    (selectedStrategyPosterior omega 32)
    (selectedStrategyPosterior_isPMF omega 32) 32 hweightPos
  have hriskBound :
      selectedPopulationRisk omega < informativeSharedStrategyBoundary omega := by
    rw [show modelStrategyProductPrior
        (selectedPosterior omega 32) (selectedStrategyPosterior omega 32) =
          selectedModelStrategyPosterior omega 32 by rfl] at hbound
    rw [selectedSharedStrategy_normalizedObservation_eq_zero_of_mem hcylinder,
      hweight, zero_add] at hbound
    simpa [selectedPopulationRisk, selectedModelStrategyPosterior,
      informativeSharedStrategyBoundary] using hbound
  refine ⟨goodEvent, omega, hmass, hgoodOmega, hcylinder, hmodel, hstrategy,
    ?_, ?_, ?_, ?_, hweight,
    selectedSharedStrategy_normalizedObservation_eq_zero_of_mem hcylinder,
    selectedPopulationRisk_eq_one_thirtyTwo_of_mem hcylinder,
    selectedSharedStrategy_quadraticPenalty_le_125_256_of_mem hcylinder,
    hriskBound,
    informativeSharedStrategyBoundary_lt_seven_sixteenths_of_mem hcylinder⟩
  · rw [hmodel]
    exact truePosterior_kl_eq_log_two
  · exact selectedStrategy_kl_eq_log_two_of_mem hcylinder
  · simpa [sharedInformativeStrategyCatalog, informativeStrategyCatalog] using
      (true_predictableTilt_of_mem hcylinder 1)
  · simp [sharedInformativeStrategyCatalog, informativeStrategyCatalog,
      conservativePredictableTilt]

/-! ## Public endpoint and axiom receipts -/

#check forwardPredictableTiltMeanEmpiricalBernsteinLowerFactor
#check forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
#check forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#check forwardPredictableTiltMeanEmpiricalBernsteinLower_typeI_control
#check forwardPredictableTiltPACBayesAnyPosteriorFailure_mass_le_delta
#check forwardPredictableTiltPACBayes_allPosteriors_of_not_mem
#check forwardPredictableTiltPosteriorTotalWeight
#check forwardPredictableTiltPosteriorNormalizedMean
#check forwardPredictableTiltPosteriorNormalizedObservation
#check forwardPredictableTiltPACBayes_normalized_of_not_mem
#check forwardPredictableTiltPACBayes_selected_of_not_mem
#check forwardPredictableTiltPACBayes_normalized_selected_of_not_mem
#check exists_forwardPredictableTiltPACBayes_event
#check exists_forwardPredictableTiltPACBayes_normalized_event
#check predictableTilt_nonconstant_prefix_witness
#check informative_exists_allTime_allPosterior_event
#check informative_nonvacuous_receipt
#check exists_forwardPredictableStrategyPACBayes_factorized_normalized_selected_event
#check posteriorAverage_modelStrategyProductPrior_separable
#check forwardPredictableStrategyPosteriorTotalWeight_shared_factorized
#check forwardPredictableStrategyPosteriorNormalizedMean_shared_constant_factorized
#check exists_forwardPredictableStrategyPACBayes_shared_constantMean_factorized_ordinaryRisk_event
#check selectedStrategyPosterior_pathDependent_witness
#check informativeStrategyCatalog_distinct_witness
#check informative_strategySelection_nonvacuous_receipt
#check informative_sharedStrategy_ordinaryRisk_nonvacuous_receipt

#print axioms forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinLower_typeI_control
#print axioms forwardPredictableTiltPACBayesAnyPosteriorFailure_mass_le_delta
#print axioms forwardPredictableTiltPACBayes_allPosteriors_of_not_mem
#print axioms forwardPredictableTiltPosteriorNormalizedMean_sub_observation
#print axioms forwardPredictableTiltPACBayes_normalized_of_not_mem
#print axioms forwardPredictableTiltPACBayes_selected_of_not_mem
#print axioms forwardPredictableTiltPACBayes_normalized_selected_of_not_mem
#print axioms exists_forwardPredictableTiltPACBayes_event
#print axioms exists_forwardPredictableTiltPACBayes_normalized_event
#print axioms predictableTilt_nonconstant_prefix_witness
#print axioms informative_exists_allTime_allPosterior_event
#print axioms informative_nonvacuous_receipt
#print axioms exists_forwardPredictableStrategyPACBayes_factorized_normalized_selected_event
#print axioms posteriorAverage_modelStrategyProductPrior_separable
#print axioms forwardPredictableStrategyPosteriorTotalWeight_shared_factorized
#print axioms forwardPredictableStrategyPosteriorNormalizedMean_shared_constant_factorized
#print axioms exists_forwardPredictableStrategyPACBayes_shared_constantMean_factorized_ordinaryRisk_event
#print axioms selectedStrategyPosterior_pathDependent_witness
#print axioms informativeStrategyCatalog_distinct_witness
#print axioms informative_strategySelection_nonvacuous_receipt
#print axioms informative_sharedStrategy_ordinaryRisk_nonvacuous_receipt

end

end FormalSLT.Examples.CheckForwardPredictableTiltPACBayesInformative
