import FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
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
-/

namespace FormalSLT.Examples.CheckForwardPredictableTiltPACBayesInformative

open Finset MeasureTheory ProbabilityTheory Real BigOperators
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniformIID
open FormalSLT.PACBayes.ForwardBesselPACBayesIID
open FormalSLT.PACBayes.ForwardPredictableTiltPACBayes
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

theorem selectedPopulationRisk_lt_boundary_of_not_mem
    {omega : BiasedBoolStream} (hcylinder : omega ∈ informativePrefixCylinder)
    (hgood : omega ∉ informativeFailure) :
    selectedPopulationRisk omega < informativeBoundary omega := by
  have hbound := forwardPredictableTiltPACBayes_selected_of_not_mem
    (prior := uniformBoolPrior) (X := observedLoss) (mean := meanLoss)
    (lambda := predictableTilt) (delta := (1 / 128 : ℝ))
    (by simpa [informativeFailure] using hgood)
    selectedPosterior selectedPosterior_isPMF 32
  have hgap := selected_point_meanGap_eq_thirtyOne_sixtyFour_of_mem hcylinder
  have hposterior := selectedPosterior_of_mem_informativePrefixCylinder hcylinder
  have hrisk := selectedPopulationRisk_eq_one_thirtyTwo_of_mem hcylinder
  rw [hposterior, hgap] at hbound
  rw [hrisk]
  unfold informativeBoundary
  rw [hposterior]
  nlinarith

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

/-! ## Public endpoint and axiom receipts -/

#check forwardPredictableTiltMeanEmpiricalBernsteinLowerFactor
#check forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess
#check forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#check forwardPredictableTiltMeanEmpiricalBernsteinLower_typeI_control
#check forwardPredictableTiltPACBayesAnyPosteriorFailure_mass_le_delta
#check forwardPredictableTiltPACBayes_allPosteriors_of_not_mem
#check forwardPredictableTiltPACBayes_selected_of_not_mem
#check exists_forwardPredictableTiltPACBayes_event
#check predictableTilt_nonconstant_prefix_witness
#check informative_exists_allTime_allPosterior_event
#check informative_nonvacuous_receipt

#print axioms forwardPredictableTiltMeanEmpiricalBernsteinLowerProcess_eProcess_of_bounded
#print axioms forwardPredictableTiltMeanEmpiricalBernsteinLower_typeI_control
#print axioms forwardPredictableTiltPACBayesAnyPosteriorFailure_mass_le_delta
#print axioms forwardPredictableTiltPACBayes_allPosteriors_of_not_mem
#print axioms forwardPredictableTiltPACBayes_selected_of_not_mem
#print axioms exists_forwardPredictableTiltPACBayes_event
#print axioms predictableTilt_nonconstant_prefix_witness
#print axioms informative_exists_allTime_allPosterior_event
#print axioms informative_nonvacuous_receipt

end

end FormalSLT.Examples.CheckForwardPredictableTiltPACBayesInformative
