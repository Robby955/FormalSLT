import FormalSLT.StochasticDynamics.TrajectoryForwardBesselPACBayesOracle
import FormalSLT.StochasticDynamics.FiniteTrajectorySleepingOrdinaryRiskPACBayes

/-!
# Informative countable-tilt trajectory empirical-Bernstein receipt

This checker instantiates the all-time trajectory endpoint on a genuinely
prefix-dependent Boolean process.  A fixed two-rule catalog contains a static
predictor and an online last-label predictor.  The observed first transition
selects a point posterior, so both posterior branches occur on positive-mass
supported cylinders and the selected posterior pays `KL = log 2`.

At confidence `1 - 1/160`, the online branch has positive Bessel variance
`1/512`.  Its checked selected boundary lies in `(0.2738, 0.2744)`, while the
same path at time `2048` selects the next countable atom and has boundary in
`(0.1432, 0.1434)`.  The latter is strictly smaller.

Claim boundary: the predictor catalog is fixed before observing data, though
one catalog member is prefix-adaptive.  The countable theorem confidence-
allocates over singleton atom events; it does not construct a master selected
e-process.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.AnytimeValid.AllocationLogLog
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open FormalSLT.PACBayes.ForwardBesselPACBayesOracle
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative

open FormalSLT.StochasticDynamics

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def oneThenZero (k : ℕ) : ℝ := if k = 0 then 1 else 0

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def firstMonitoredState (n : ℕ) (u : (i : Finset.Iic n) → Bool) : Bool :=
  if h : 1 ≤ n then u ⟨1, Finset.mem_Iic.mpr h⟩ else false

def informativeNextState (n : ℕ) (u : (i : Finset.Iic n) → Bool) : Bool :=
  if firstMonitoredState n u then
    u ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  else
    !(u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

def informativeDynamicPMF (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) : PMF Bool :=
  PMF.ofFintype
    (fun y ↦ if n = 0 then
      if y then ((3 / 4 : NNReal) : ENNReal)
      else ((1 / 4 : NNReal) : ENNReal)
    else if y = informativeNextState n u then 1 else 0)
    (by
      by_cases hn : n = 0
      · have hsumNN : (3 / 4 : NNReal) + 1 / 4 = 1 := by norm_num
        have hsum : ((3 / 4 : NNReal) : ENNReal) +
            ((1 / 4 : NNReal) : ENNReal) = 1 := by
          rw [← ENNReal.coe_add, hsumNN]
          rfl
        simpa [hn, Fintype.sum_bool] using hsum
      · cases hnext : informativeNextState n u <;> simp [hn])

def informativeDynamicKernel (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Bool) Bool :=
  Kernel.ofFunOfCountable fun u ↦ (informativeDynamicPMF n u).toMeasure

instance informativeDynamicKernel.instIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (informativeDynamicKernel n) :=
  ⟨fun u ↦ by
    change IsProbabilityMeasure (informativeDynamicPMF n u).toMeasure
    infer_instance⟩

def persistentTruePath (n : ℕ) : Bool := decide (0 < n)
def firstFalseThenAlternatingPath (n : ℕ) : Bool := decide (0 < n ∧ Even n)

/-- At time two, two reachable histories have the same initial and current
state but induce opposite next-step laws through their first monitored state. -/
theorem informativeDynamicKernel_history_witness :
    persistentTruePath 2 = firstFalseThenAlternatingPath 2 ∧
    informativeDynamicPMF 2 (Preorder.frestrictLe 2 persistentTruePath) true = 1 ∧
    informativeDynamicPMF 2
        (Preorder.frestrictLe 2 firstFalseThenAlternatingPath) true = 0 := by
  norm_num [persistentTruePath, firstFalseThenAlternatingPath,
    informativeDynamicPMF, informativeNextState, firstMonitoredState,
    PMF.ofFintype_apply, Preorder.frestrictLe_apply]

def informativeScore (i : Bool) : FormalSLT.StochasticDynamics.TrajectoryScore Bool :=
  fun n u y ↦
    if i then
      if n = 0 then (if y then 1 else 0)
      else if y = u ⟨n, Finset.mem_Iic.mpr le_rfl⟩ then 0 else 1
    else if y then 1 else 0

theorem informativeScore_mem_Icc :
    ∀ i n u y, informativeScore i n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i n u y
  fin_cases i <;> simp [informativeScore] <;> split_ifs <;> norm_num

/-- The online rule changes its prediction with the observed prefix, while the
static rule does not.  Both displayed prefixes lead to the same next label. -/
theorem informativeScore_online_update_witness :
    informativeScore true 1
        (Preorder.frestrictLe 1 persistentTruePath) true = 0 ∧
      informativeScore true 1
        (Preorder.frestrictLe 1 firstFalseThenAlternatingPath) true = 1 ∧
      informativeScore false 1
        (Preorder.frestrictLe 1 persistentTruePath) true = 1 ∧
      informativeScore false 1
        (Preorder.frestrictLe 1 firstFalseThenAlternatingPath) true = 1 := by
  norm_num [informativeScore, persistentTruePath,
    firstFalseThenAlternatingPath, Preorder.frestrictLe_apply]

def transitionViolationScore : FormalSLT.StochasticDynamics.TrajectoryScore Bool :=
  fun n u y ↦
    if 1 ≤ n then if y = informativeNextState n u then 0 else 1 else 0

theorem transitionViolationScore_mem_Icc :
    ∀ n u y, transitionViolationScore n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro n u y
  simp [transitionViolationScore]
  split_ifs <;> norm_num

theorem transitionViolation_conditionalRisk_eq_zero
    (n : ℕ) (hn : 1 ≤ n) (x : ℕ → Bool) :
    FormalSLT.StochasticDynamics.conditionalTrajectoryRisk
        informativeDynamicKernel transitionViolationScore n x = 0 := by
  unfold FormalSLT.StochasticDynamics.conditionalTrajectoryRisk informativeDynamicKernel
  change ∫ y, transitionViolationScore n (Preorder.frestrictLe n x) y
    ∂(informativeDynamicPMF n (Preorder.frestrictLe n x)).toMeasure = 0
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  cases hnext : informativeNextState n (Preorder.frestrictLe n x) <;>
    simp [transitionViolationScore, informativeDynamicPMF, hn, hn0, hnext]

def informativePathMeasure : Measure (ℕ → Bool) :=
  FormalSLT.StochasticDynamics.trajectoryMeasure informativeDynamicKernel false

instance informativePathMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure informativePathMeasure := by
  unfold informativePathMeasure
  infer_instance

theorem transitionViolation_observed_ae_zero (n : ℕ) (hn : 1 ≤ n) :
    FormalSLT.StochasticDynamics.observedTrajectoryScore
        transitionViolationScore n =ᵐ[informativePathMeasure] 0 := by
  have hcond :=
    FormalSLT.StochasticDynamics.observedTrajectoryScore_condExp
      informativeDynamicKernel false transitionViolationScore
      transitionViolationScore_mem_Icc
      n
  have hcond0 :
      informativePathMeasure[
          FormalSLT.StochasticDynamics.observedTrajectoryScore
            transitionViolationScore n |
          Filtration.piLE (X := fun _ : ℕ ↦ Bool) n] =ᵐ[informativePathMeasure]
        (0 : (ℕ → Bool) → ℝ) := by
    refine hcond.trans (Filter.Eventually.of_forall fun x ↦ ?_)
    exact transitionViolation_conditionalRisk_eq_zero n hn x
  have hcondIntegral :
      ∫ x, informativePathMeasure[
          FormalSLT.StochasticDynamics.observedTrajectoryScore
            transitionViolationScore n |
          Filtration.piLE (X := fun _ : ℕ ↦ Bool) n] x
        ∂informativePathMeasure = 0 := by
    simpa using integral_congr_ae hcond0
  have hintegral :
      ∫ x, FormalSLT.StochasticDynamics.observedTrajectoryScore
          transitionViolationScore n x ∂informativePathMeasure = 0 := by
    rw [← integral_condExp
      ((Filtration.piLE (X := fun _ : ℕ ↦ Bool)).le n)]
    exact hcondIntegral
  exact (integral_eq_zero_iff_of_nonneg
      (fun x ↦
        (FormalSLT.StochasticDynamics.observedTrajectoryScore_mem_Icc
          transitionViolationScore_mem_Icc n x).1)
      (FormalSLT.StochasticDynamics.integrable_observedTrajectoryScore
        (κ := informativeDynamicKernel) (x0 := false)
        (score := transitionViolationScore)
        transitionViolationScore_mem_Icc
        n)).1 hintegral

theorem informative_recurrence_ae (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ x ∂informativePathMeasure,
      x (n + 1) = informativeNextState n (Preorder.frestrictLe n x) := by
  filter_upwards [transitionViolation_observed_ae_zero n hn] with x hx
  unfold FormalSLT.StochasticDynamics.observedTrajectoryScore at hx
  simp [transitionViolationScore, hn] at hx
  exact hx

def informativeSupportEvent : Set (ℕ → Bool) :=
  {x | ∀ n, 1 ≤ n →
    x (n + 1) = informativeNextState n (Preorder.frestrictLe n x)}

theorem informativeSupportEvent_ae :
    ∀ᵐ x ∂informativePathMeasure, x ∈ informativeSupportEvent := by
  change ∀ᵐ x ∂informativePathMeasure, ∀ n, 1 ≤ n →
    x (n + 1) = informativeNextState n (Preorder.frestrictLe n x)
  rw [ae_all_iff]
  intro n
  by_cases hn : 1 ≤ n
  · exact (informative_recurrence_ae n hn).mono fun x hx _ ↦ hx
  · exact Filter.Eventually.of_forall fun _ hx ↦ (hn hx).elim

def firstTrueEvent : Set (ℕ → Bool) := {x | x 1 = true}

theorem informativePathMeasure_firstTrueEvent :
    informativePathMeasure firstTrueEvent = (3 : ENNReal) / 4 := by
  let u0 : (i : Finset.Iic 0) → Bool := fun _ ↦ false
  have hmap := FormalSLT.StochasticDynamics.map_trajectory_next
    informativeDynamicKernel 0 u0
  have happly :
      Measure.map (fun x : ℕ → Bool ↦ x 1)
          informativePathMeasure =
        informativeDynamicKernel 0 u0 := by
    simpa [informativePathMeasure,
      FormalSLT.StochasticDynamics.trajectoryMeasure, u0] using hmap
  calc
    informativePathMeasure firstTrueEvent =
        (Measure.map (fun x : ℕ → Bool ↦ x 1)
          informativePathMeasure) {true} := by
      rw [Measure.map_apply (measurable_pi_apply 1) (MeasurableSet.singleton true)]
      rfl
    _ = informativeDynamicKernel 0 u0 {true} := by rw [happly]
    _ = (3 : ENNReal) / 4 := by
      change (informativeDynamicPMF 0 u0).toMeasure {true} = _
      rw [(informativeDynamicPMF 0 u0).toMeasure_apply_singleton true
        (MeasurableSet.singleton true)]
      norm_num [informativeDynamicPMF, PMF.ofFintype_apply]

def informativeCylinder : Set (ℕ → Bool) :=
  informativeSupportEvent ∩ firstTrueEvent

theorem informativePathMeasure_informativeCylinder :
    informativePathMeasure informativeCylinder = (3 : ENNReal) / 4 := by
  rw [informativeCylinder,
    Measure.measure_inter_eq_of_ae informativeSupportEvent_ae,
    informativePathMeasure_firstTrueEvent]

theorem path_eq_true_of_mem_informativeCylinder
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder)
    {n : ℕ} (hn : 1 ≤ n) : x n = true := by
  have hx1 : x 1 = true := by
    simpa [informativeCylinder, firstTrueEvent] using hx.2
  induction n, hn using Nat.le_induction with
  | base => exact hx1
  | succ n hn ih =>
      have hrec := hx.1 n hn
      rw [hrec]
      simp [informativeNextState, firstMonitoredState, hn,
        Preorder.frestrictLe_apply, hx1, ih]

def uniformPrior (_i : Bool) : ℝ := 1 / 2

theorem uniformPrior_isFullSupportPMF : IsFullSupportPMF uniformPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [uniformPrior]
  · norm_num [uniformPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [uniformPrior]

def pointPosterior (selected i : Bool) : ℝ := if i = selected then 1 else 0

theorem pointPosterior_isPMF (selected : Bool) : IsPMF (pointPosterior selected) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases selected <;> fin_cases i <;> norm_num [pointPosterior]
  · fin_cases selected <;> norm_num [pointPosterior, Fintype.sum_bool]

/-- `true` selects the online last-label predictor; `false` selects the static
false predictor. -/
def selectedPosterior (x : ℕ → Bool) (_n : ℕ) : Bool → ℝ :=
  pointPosterior (x 1)

theorem selectedPosterior_isPMF (x : ℕ → Bool) (n : ℕ) :
    IsPMF (selectedPosterior x n) := pointPosterior_isPMF _

theorem selectedPosterior_explicit_branches :
    selectedPosterior persistentTruePath 512 = pointPosterior true ∧
      selectedPosterior firstFalseThenAlternatingPath 512 = pointPosterior false := by
  constructor <;> rfl

theorem pointPosterior_kl_eq_log_two (selected : Bool) :
    klDiv (pointPosterior selected) uniformPrior = Real.log 2 := by
  fin_cases selected <;> simp [klDiv, pointPosterior, uniformPrior]

theorem selectedPosterior_kl_eq_log_two (x : ℕ → Bool) (n : ℕ) :
    klDiv (selectedPosterior x n) uniformPrior = Real.log 2 :=
  pointPosterior_kl_eq_log_two _

theorem selectedPosterior_kl_pos (x : ℕ → Bool) (n : ℕ) :
    0 < klDiv (selectedPosterior x n) uniformPrior := by
  rw [selectedPosterior_kl_eq_log_two]
  exact Real.log_pos (by norm_num)

theorem observed_onlineScore_eq_oneThenZero_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) (k : ℕ) :
    FormalSLT.StochasticDynamics.observedTrajectoryScore
        (informativeScore true) k x = oneThenZero k := by
  have hx1 : x 1 = true := by
    simpa [informativeCylinder, firstTrueEvent] using hx.2
  by_cases hk : k = 0
  · subst k
    simp [FormalSLT.StochasticDynamics.observedTrajectoryScore,
      informativeScore, oneThenZero, hx1]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hkTrue := path_eq_true_of_mem_informativeCylinder hx hk1
    have hksTrue := path_eq_true_of_mem_informativeCylinder hx (by omega : 1 ≤ k + 1)
    simp [FormalSLT.StochasticDynamics.observedTrajectoryScore,
      informativeScore, oneThenZero, hk, Preorder.frestrictLe_apply,
      hkTrue, hksTrue]

theorem selected_empiricalRisk_eq_one_512_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    FormalSLT.StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
        informativeScore (selectedPosterior x 512) 512 x = (1 : ℝ) / 512 := by
  have hposterior : selectedPosterior x 512 = pointPosterior true := by
    unfold selectedPosterior
    have hx1 : x 1 = true := by
      simpa [informativeCylinder, firstTrueEvent] using hx.2
    rw [hx1]
  rw [hposterior]
  unfold FormalSLT.StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
    posteriorAverage FormalSLT.StochasticDynamics.trajectoryEmpiricalPrequentialRisk
    runningMean runningSum
  rw [Fintype.sum_bool]
  simp only [pointPosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  have hsum :
      ∑ k ∈ Finset.range 512,
        FormalSLT.StochasticDynamics.observedTrajectoryScore
          (informativeScore true) k x = 1 := by
    calc
      _ = ∑ k ∈ Finset.range 512, oneThenZero k := by
        apply Finset.sum_congr rfl
        intro k _
        exact observed_onlineScore_eq_oneThenZero_of_mem hx k
      _ = 1 := by norm_num [oneThenZero, Finset.sum_range_succ]
  rw [hsum]
  norm_num

theorem online_forwardBesselQ_512_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    forwardBesselQ
        (fun k ↦ FormalSLT.StochasticDynamics.observedTrajectoryScore
          (informativeScore true) k x) 512 = (511 : ℝ) / 512 := by
  have hmean : forwardPrefixMean
      (fun k ↦ FormalSLT.StochasticDynamics.observedTrajectoryScore
        (informativeScore true) k x) 512 = forwardPrefixMean oneThenZero 512 := by
    unfold forwardPrefixMean
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact observed_onlineScore_eq_oneThenZero_of_mem hx k
  unfold forwardBesselQ
  rw [hmean]
  calc
    (∑ i ∈ Finset.range 512,
        (FormalSLT.StochasticDynamics.observedTrajectoryScore
          (informativeScore true) i x - forwardPrefixMean oneThenZero 512) ^ 2) =
        ∑ i ∈ Finset.range 512,
          (oneThenZero i - forwardPrefixMean oneThenZero 512) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [observed_onlineScore_eq_oneThenZero_of_mem hx i]
    _ = (511 : ℝ) / 512 := by
      norm_num [forwardPrefixMean, oneThenZero, Finset.sum_range_succ]

theorem online_besselVariance_eq_one_512_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin 512 ↦
          FormalSLT.StochasticDynamics.observedTrajectoryScore
            (informativeScore true) i x) = (1 : ℝ) / 512 := by
  have h := forwardBesselQ_eq_card_sub_one_mul_sampleVarianceBessel
    (fun k ↦ FormalSLT.StochasticDynamics.observedTrajectoryScore
      (informativeScore true) k x) (n := 512) (by norm_num)
  rw [online_forwardBesselQ_512_eq_of_mem hx] at h
  norm_num at h ⊢
  linarith

theorem online_besselVariance_mem_Ioo_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
        (fun i : Fin 512 ↦
          FormalSLT.StochasticDynamics.observedTrajectoryScore
            (informativeScore true) i x) ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
  rw [online_besselVariance_eq_one_512_of_mem hx]
  norm_num

theorem online_hybridPenalty_512_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    forwardHybridBesselPenalty
        (fun k ↦ FormalSLT.StochasticDynamics.observedTrajectoryScore
          (informativeScore true) k x) 512 = (2045 : ℝ) / 1024 := by
  unfold forwardHybridBesselPenalty
  rw [online_forwardBesselQ_512_eq_of_mem hx]
  norm_num [harmonic]

theorem selected_posteriorHybridPenalty_512_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    FormalSLT.StochasticDynamics.trajectoryPosteriorHybridBesselPenalty
        (selectedPosterior x 512) informativeScore 512 x =
      (2045 : ℝ) / 1024 := by
  have hposterior : selectedPosterior x 512 = pointPosterior true := by
    unfold selectedPosterior
    have hx1 : x 1 = true := by
      simpa [informativeCylinder, firstTrueEvent] using hx.2
    rw [hx1]
  rw [hposterior]
  unfold FormalSLT.StochasticDynamics.trajectoryPosteriorHybridBesselPenalty
    posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul, add_zero]
  exact online_hybridPenalty_512_eq_of_mem hx

theorem online_forwardBesselQ_2048_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    forwardBesselQ
        (fun k ↦ FormalSLT.StochasticDynamics.observedTrajectoryScore
          (informativeScore true) k x) 2048 = (2047 : ℝ) / 2048 := by
  have hmean : forwardPrefixMean
      (fun k ↦ FormalSLT.StochasticDynamics.observedTrajectoryScore
        (informativeScore true) k x) 2048 = forwardPrefixMean oneThenZero 2048 := by
    unfold forwardPrefixMean
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact observed_onlineScore_eq_oneThenZero_of_mem hx k
  unfold forwardBesselQ
  rw [hmean]
  calc
    (∑ i ∈ Finset.range 2048,
        (FormalSLT.StochasticDynamics.observedTrajectoryScore
          (informativeScore true) i x - forwardPrefixMean oneThenZero 2048) ^ 2) =
        ∑ i ∈ Finset.range 2048,
          (oneThenZero i - forwardPrefixMean oneThenZero 2048) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [observed_onlineScore_eq_oneThenZero_of_mem hx i]
    _ = (2047 : ℝ) / 2048 := by
      norm_num [forwardPrefixMean, oneThenZero, Finset.sum_range_succ]

theorem online_hybridPenalty_2048_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    forwardHybridBesselPenalty
        (fun k ↦ FormalSLT.StochasticDynamics.observedTrajectoryScore
          (informativeScore true) k x) 2048 = (8189 : ℝ) / 4096 := by
  unfold forwardHybridBesselPenalty
  rw [online_forwardBesselQ_2048_eq_of_mem hx]
  norm_num [harmonic]

theorem selected_posteriorHybridPenalty_2048_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    FormalSLT.StochasticDynamics.trajectoryPosteriorHybridBesselPenalty
        (selectedPosterior x 2048) informativeScore 2048 x =
      (8189 : ℝ) / 4096 := by
  have hposterior : selectedPosterior x 2048 = pointPosterior true := by
    unfold selectedPosterior
    have hx1 : x 1 = true := by
      simpa [informativeCylinder, firstTrueEvent] using hx.2
    rw [hx1]
  rw [hposterior]
  unfold FormalSLT.StochasticDynamics.trajectoryPosteriorHybridBesselPenalty
    posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul, add_zero]
  exact online_hybridPenalty_2048_eq_of_mem hx

def highConfidenceBoundary (n : ℕ) (x : ℕ → Bool) : ℝ :=
  FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayesBoundary
    uniformPrior informativeScore (selectedPosterior x n) (1 / 160)
      (geometricForwardTiltIndex n) n x

theorem selected_tilt_index_512 : geometricForwardTiltIndex 512 = 3 := by
  norm_num [geometricForwardTiltIndex, Nat.log]

theorem selected_tilt_index_2048 : geometricForwardTiltIndex 2048 = 4 := by
  norm_num [geometricForwardTiltIndex, Nat.log]

theorem selected_tilt_weight_3 :
    polynomialForwardTiltWeight 3 = (1 : ℝ) / 20 := by
  norm_num [polynomialForwardTiltWeight,
    FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight]

theorem selected_tilt_weight_4 :
    polynomialForwardTiltWeight 4 = (1 : ℝ) / 30 := by
  norm_num [polynomialForwardTiltWeight,
    FormalSLT.PACBayes.InfiniteEmpiricalBernsteinStitch.reverseDyadicEpochWeight]

theorem selected_tilt_log_cost_512 :
    Real.log (1 / (((1 : ℝ) / 160) * polynomialForwardTiltWeight 3)) =
      7 * Real.log 2 + 2 * Real.log 5 := by
  rw [selected_tilt_weight_3]
  norm_num
  have hlog3200 : Real.log 3200 = 7 * Real.log 2 + 2 * Real.log 5 := by
    calc
      Real.log 3200 = Real.log ((2 : ℝ) ^ 7 * 5 ^ 2) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 7) + Real.log ((5 : ℝ) ^ 2) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = 7 * Real.log 2 + 2 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
  exact hlog3200

theorem selected_tilt_log_cost_2048 :
    Real.log (1 / (((1 : ℝ) / 160) * polynomialForwardTiltWeight 4)) =
      6 * Real.log 2 + Real.log 3 + 2 * Real.log 5 := by
  rw [selected_tilt_weight_4]
  norm_num
  have hlog4800 :
      Real.log 4800 = 6 * Real.log 2 + Real.log 3 + 2 * Real.log 5 := by
    calc
      Real.log 4800 = Real.log (((2 : ℝ) ^ 6 * 3) * 5 ^ 2) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 6 * 3) + Real.log ((5 : ℝ) ^ 2) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log ((2 : ℝ) ^ 6) + Real.log 3) +
          Real.log ((5 : ℝ) ^ 2) := by
        rw [Real.log_mul (by positivity) (by norm_num)]
      _ = 6 * Real.log 2 + Real.log 3 + 2 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        ring
  exact hlog4800

theorem highConfidenceBoundary_512_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    highConfidenceBoundary 512 x =
      (8 * Real.log 2 + 2 * Real.log 5 +
          forwardEmpiricalBernsteinPsi (1 / 16) * (2045 / 1024)) / 32 := by
  unfold highConfidenceBoundary
  rw [selected_tilt_index_512,
    FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
      uniformPrior informativeScore (selectedPosterior x 512) (by norm_num)
      3 512 x,
    selectedPosterior_kl_eq_log_two,
    selected_posteriorHybridPenalty_512_eq_of_mem hx]
  norm_num [geometricForwardTilt]
  rw [show Real.log 3200 = 7 * Real.log 2 + 2 * Real.log 5 by
    calc
      Real.log 3200 = Real.log ((2 : ℝ) ^ 7 * 5 ^ 2) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 7) + Real.log ((5 : ℝ) ^ 2) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = 7 * Real.log 2 + 2 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        norm_num]
  ring

theorem highConfidenceBoundary_2048_eq_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    highConfidenceBoundary 2048 x =
      (7 * Real.log 2 + Real.log 3 + 2 * Real.log 5 +
          forwardEmpiricalBernsteinPsi (1 / 32) * (8189 / 4096)) / 64 := by
  unfold highConfidenceBoundary
  rw [selected_tilt_index_2048,
    FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayesBoundary_eq_explicit
      uniformPrior informativeScore (selectedPosterior x 2048) (by norm_num)
      4 2048 x,
    selectedPosterior_kl_eq_log_two,
    selected_posteriorHybridPenalty_2048_eq_of_mem hx]
  norm_num [geometricForwardTilt]
  rw [show Real.log 4800 = 6 * Real.log 2 + Real.log 3 + 2 * Real.log 5 by
    calc
      Real.log 4800 = Real.log (((2 : ℝ) ^ 6 * 3) * 5 ^ 2) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 6 * 3) + Real.log ((5 : ℝ) ^ 2) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log ((2 : ℝ) ^ 6) + Real.log 3) +
          Real.log ((5 : ℝ) ^ 2) := by
        rw [Real.log_mul (by positivity) (by norm_num)]
      _ = 6 * Real.log 2 + Real.log 3 + 2 * Real.log 5 := by
        rw [Real.log_pow, Real.log_pow]
        ring]
  ring

theorem highConfidenceBoundary_512_enclosure
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    (2738 : ℝ) / 10000 < highConfidenceBoundary 512 x ∧
      highConfidenceBoundary 512 x < (2744 : ℝ) / 10000 := by
  rw [highConfidenceBoundary_512_eq_of_mem hx]
  have hpsi0 := forwardEmpiricalBernsteinPsi_nonneg
    (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 : ℝ) / 16 < 1)
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq
    (by norm_num : (1 : ℝ) / 16 ≤ 1 / 2)
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9,
      Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem highConfidenceBoundary_2048_enclosure
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    (1432 : ℝ) / 10000 < highConfidenceBoundary 2048 x ∧
      highConfidenceBoundary 2048 x < (1434 : ℝ) / 10000 := by
  rw [highConfidenceBoundary_2048_eq_of_mem hx]
  have hpsi0 := forwardEmpiricalBernsteinPsi_nonneg
    (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 : ℝ) / 32 < 1)
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq
    (by norm_num : (1 : ℝ) / 32 ≤ 1 / 2)
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, Real.log_two_lt_d9,
      Real.log_three_lt_d9, Real.log_five_lt_d9]

theorem highConfidenceBoundary_2048_lt_512_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    highConfidenceBoundary 2048 x < highConfidenceBoundary 512 x := by
  have hsmall := (highConfidenceBoundary_2048_enclosure hx).2
  have hlarge := (highConfidenceBoundary_512_enclosure hx).1
  linarith

theorem highConfidence_rhs_512_lt_seven_twenty_fifths_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    FormalSLT.StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
        informativeScore (selectedPosterior x 512) 512 x +
        highConfidenceBoundary 512 x < (7 : ℝ) / 25 := by
  rw [selected_empiricalRisk_eq_one_512_of_mem hx]
  have hboundary := (highConfidenceBoundary_512_enclosure hx).2
  linarith

def informativeExceptionalEvent : Set (ℕ → Bool) :=
  FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent
    informativeDynamicKernel uniformPrior informativeScore (1 / 160)

theorem informativeExceptionalEvent_mass_le_delta :
    informativePathMeasure.real informativeExceptionalEvent ≤ (1 : ℝ) / 160 := by
  simpa [informativePathMeasure, informativeExceptionalEvent] using
    (FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayesExceptionalEvent_mass_le
      (K := informativeDynamicKernel) false
      (score := informativeScore)
      informativeScore_mem_Icc
      uniformPrior_isFullSupportPMF
      (delta := (1 / 160 : ℝ)) (by norm_num))

theorem informativeCylinder_real_mass :
    informativePathMeasure.real informativeCylinder = (3 : ℝ) / 4 := by
  rw [measureReal_def, informativePathMeasure_informativeCylinder]
  norm_num

theorem informative_goodCylinderPath_exists :
    ∃ x : ℕ → Bool,
      x ∈ informativeCylinder ∧ x ∉ informativeExceptionalEvent := by
  by_contra h
  have hsubset : informativeCylinder ⊆ informativeExceptionalEvent := by
    intro x hx
    by_contra hgood
    exact h ⟨x, hx, hgood⟩
  have hmono : informativePathMeasure.real informativeCylinder ≤
      informativePathMeasure.real informativeExceptionalEvent :=
    measureReal_mono hsubset
  rw [informativeCylinder_real_mass] at hmono
  have hbad := informativeExceptionalEvent_mass_le_delta
  linarith

def firstFalseEvent : Set (ℕ → Bool) := {x | x 1 = false}

theorem informativePathMeasure_firstFalseEvent :
    informativePathMeasure firstFalseEvent = (1 : ENNReal) / 4 := by
  let u0 : (i : Finset.Iic 0) → Bool := fun _ ↦ false
  have hmap := FormalSLT.StochasticDynamics.map_trajectory_next
    informativeDynamicKernel 0 u0
  have happly :
      Measure.map (fun x : ℕ → Bool ↦ x 1)
          informativePathMeasure =
        informativeDynamicKernel 0 u0 := by
    simpa [informativePathMeasure,
      FormalSLT.StochasticDynamics.trajectoryMeasure, u0] using hmap
  calc
    informativePathMeasure firstFalseEvent =
        (Measure.map (fun x : ℕ → Bool ↦ x 1)
          informativePathMeasure) {false} := by
      rw [Measure.map_apply (measurable_pi_apply 1) (MeasurableSet.singleton false)]
      rfl
    _ = informativeDynamicKernel 0 u0 {false} := by rw [happly]
    _ = (1 : ENNReal) / 4 := by
      change (informativeDynamicPMF 0 u0).toMeasure {false} = _
      rw [(informativeDynamicPMF 0 u0).toMeasure_apply_singleton false
        (MeasurableSet.singleton false)]
      norm_num [informativeDynamicPMF, PMF.ofFintype_apply]

def alternateCylinder : Set (ℕ → Bool) :=
  informativeSupportEvent ∩ firstFalseEvent

theorem alternateCylinder_real_mass :
    informativePathMeasure.real alternateCylinder = (1 : ℝ) / 4 := by
  have hmeasure : informativePathMeasure alternateCylinder = (1 : ENNReal) / 4 := by
    rw [alternateCylinder,
      Measure.measure_inter_eq_of_ae informativeSupportEvent_ae,
      informativePathMeasure_firstFalseEvent]
  rw [measureReal_def, hmeasure]
  norm_num

theorem alternate_goodCylinderPath_exists :
    ∃ x : ℕ → Bool,
      x ∈ alternateCylinder ∧ x ∉ informativeExceptionalEvent := by
  by_contra h
  have hsubset : alternateCylinder ⊆ informativeExceptionalEvent := by
    intro x hx
    by_contra hgood
    exact h ⟨x, hx, hgood⟩
  have hmono : informativePathMeasure.real alternateCylinder ≤
      informativePathMeasure.real informativeExceptionalEvent :=
    measureReal_mono hsubset
  rw [alternateCylinder_real_mass] at hmono
  have hbad := informativeExceptionalEvent_mass_le_delta
  linarith

theorem selector_branches_on_positive_mass_good_cylinders :
    (∃ x : ℕ → Bool, x ∈ informativeCylinder ∧
      x ∉ informativeExceptionalEvent ∧
      selectedPosterior x 512 = pointPosterior true) ∧
    (∃ x : ℕ → Bool, x ∈ alternateCylinder ∧
      x ∉ informativeExceptionalEvent ∧
      selectedPosterior x 512 = pointPosterior false) := by
  constructor
  · obtain ⟨x, hx, hgood⟩ := informative_goodCylinderPath_exists
    refine ⟨x, hx, hgood, ?_⟩
    unfold selectedPosterior
    have hx1 : x 1 = true := by
      simpa [informativeCylinder, firstTrueEvent] using hx.2
    rw [hx1]
  · obtain ⟨x, hx, hgood⟩ := alternate_goodCylinderPath_exists
    refine ⟨x, hx, hgood, ?_⟩
    unfold selectedPosterior
    have hx1 : x 1 = false := by
      simpa [alternateCylinder, firstFalseEvent] using hx.2
    rw [hx1]

theorem informative_allTime_vanishing_capstone :
    ∃ goodEvent : Set (ℕ → Bool),
      informativePathMeasure.real goodEventᶜ ≤ (1 : ℝ) / 160 ∧
      (∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
        FormalSLT.StochasticDynamics.trajectoryPosteriorAverageConditionalRisk
            informativeDynamicKernel informativeScore (selectedPosterior x n) n x <
          FormalSLT.StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
              informativeScore (selectedPosterior x n) n x +
            FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayesBoundary
              uniformPrior informativeScore (selectedPosterior x n) (1 / 160)
                (geometricForwardTiltIndex n) n x) ∧
      (∀ x ∈ goodEvent,
        Filter.Tendsto
          (fun n ↦
            FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayesBoundary
              uniformPrior informativeScore (selectedPosterior x n) (1 / 160)
                (geometricForwardTiltIndex n) n x)
          Filter.atTop (nhds 0)) := by
  simpa [informativePathMeasure] using
    (FormalSLT.StochasticDynamics.exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event
      (K := informativeDynamicKernel) false
      (score := informativeScore)
      informativeScore_mem_Icc
      uniformPrior_isFullSupportPMF
      (delta := (1 / 160 : ℝ)) (by norm_num) (by norm_num)
      selectedPosterior selectedPosterior_isPMF)

theorem selected_risk_bound_of_not_mem
    {x : ℕ → Bool} (hx : x ∉ informativeExceptionalEvent) :
    FormalSLT.StochasticDynamics.trajectoryPosteriorAverageConditionalRisk
        informativeDynamicKernel informativeScore (selectedPosterior x 512) 512 x <
      FormalSLT.StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
          informativeScore (selectedPosterior x 512) 512 x +
        highConfidenceBoundary 512 x := by
  have hbound :=
    FormalSLT.StochasticDynamics.trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
      informativeDynamicKernel
      (score := informativeScore)
      informativeScore_mem_Icc
      uniformPrior_isFullSupportPMF
      (delta := (1 / 160 : ℝ)) (by norm_num)
      (by simpa [informativeExceptionalEvent] using hx)
      (geometricForwardTiltIndex 512) (selectedPosterior x 512)
      (selectedPosterior_isPMF x 512) 512 (by norm_num)
  simpa [highConfidenceBoundary] using hbound

theorem informative_nonvacuous_receipt :
    ∃ x : ℕ → Bool,
      x ∈ informativeCylinder ∧
      x ∉ informativeExceptionalEvent ∧
      selectedPosterior x 512 = pointPosterior true ∧
      klDiv (selectedPosterior x 512) uniformPrior = Real.log 2 ∧
      0 < klDiv (selectedPosterior x 512) uniformPrior ∧
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin 512 ↦
            FormalSLT.StochasticDynamics.observedTrajectoryScore
              (informativeScore true) i x) = (1 : ℝ) / 512 ∧
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel
          (fun i : Fin 512 ↦
            FormalSLT.StochasticDynamics.observedTrajectoryScore
              (informativeScore true) i x) ∈ Set.Ioo (0 : ℝ) (1 / 4) ∧
      geometricForwardTiltIndex 512 = 3 ∧
      Real.log (1 / (((1 : ℝ) / 160) * polynomialForwardTiltWeight 3)) =
        7 * Real.log 2 + 2 * Real.log 5 ∧
      geometricForwardTiltIndex 2048 = 4 ∧
      Real.log (1 / (((1 : ℝ) / 160) * polynomialForwardTiltWeight 4)) =
        6 * Real.log 2 + Real.log 3 + 2 * Real.log 5 ∧
      FormalSLT.StochasticDynamics.trajectoryPosteriorAverageConditionalRisk
          informativeDynamicKernel informativeScore (selectedPosterior x 512) 512 x <
        FormalSLT.StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
            informativeScore (selectedPosterior x 512) 512 x +
          highConfidenceBoundary 512 x ∧
      FormalSLT.StochasticDynamics.trajectoryPosteriorEmpiricalPrequentialRisk
            informativeScore (selectedPosterior x 512) 512 x +
          highConfidenceBoundary 512 x < (7 : ℝ) / 25 ∧
      (2738 : ℝ) / 10000 < highConfidenceBoundary 512 x ∧
      highConfidenceBoundary 512 x < (2744 : ℝ) / 10000 ∧
      (1432 : ℝ) / 10000 < highConfidenceBoundary 2048 x ∧
      highConfidenceBoundary 2048 x < (1434 : ℝ) / 10000 ∧
      highConfidenceBoundary 2048 x < highConfidenceBoundary 512 x := by
  obtain ⟨x, hx, hgood⟩ := informative_goodCylinderPath_exists
  refine ⟨x, hx, hgood, ?_, selectedPosterior_kl_eq_log_two x 512,
    selectedPosterior_kl_pos x 512, online_besselVariance_eq_one_512_of_mem hx,
    online_besselVariance_mem_Ioo_of_mem hx, selected_tilt_index_512,
    selected_tilt_log_cost_512, selected_tilt_index_2048,
    selected_tilt_log_cost_2048, selected_risk_bound_of_not_mem hgood,
    highConfidence_rhs_512_lt_seven_twenty_fifths_of_mem hx,
    (highConfidenceBoundary_512_enclosure hx).1,
    (highConfidenceBoundary_512_enclosure hx).2,
    (highConfidenceBoundary_2048_enclosure hx).1,
    (highConfidenceBoundary_2048_enclosure hx).2,
    highConfidenceBoundary_2048_lt_512_of_mem hx⟩
  unfold selectedPosterior
  have hx1 : x 1 = true := by
    simpa [informativeCylinder, firstTrueEvent] using hx.2
  rw [hx1]

/-! ## Observable growing-prefix oracle receipt -/

/-- Exact trajectory boundary after minimizing over the geometric prefix
available at reporting time `n`. -/
def observableOracleBoundary (n : ℕ) (x : ℕ → Bool) : ℝ :=
  trajectoryGrowingPrefixForwardBesselPACBayesBoundary
    uniformPrior informativeScore (selectedPosterior x n) (1 / 160) n x

/-- The observable oracle retains the previously audited all-time atom as a
candidate, so its exact boundary can only improve on that boundary. -/
theorem observableOracleBoundary_le_highConfidenceBoundary
    (n : ℕ) (x : ℕ → Bool) :
    observableOracleBoundary n x ≤ highConfidenceBoundary n x := by
  apply trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_atom
  simp [growingPrefixForwardBesselPACBayesMaxIndex]

/-- On every path outside the allocated exceptional event, the ordinary
posterior-averaged conditional trajectory risk is controlled by empirical
prequential risk plus the exact post-data oracle boundary. -/
theorem observableOracle_risk_bound_of_not_mem
    {x : ℕ → Bool} (hx : x ∉ informativeExceptionalEvent) :
    trajectoryPosteriorAverageConditionalRisk
        informativeDynamicKernel informativeScore (selectedPosterior x 512) 512 x <
      trajectoryPosteriorEmpiricalPrequentialRisk
          informativeScore (selectedPosterior x 512) 512 x +
        observableOracleBoundary 512 x := by
  have hbound :=
    trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
      informativeDynamicKernel
      (score := informativeScore)
      informativeScore_mem_Icc
      uniformPrior_isFullSupportPMF
      (delta := (1 / 160 : ℝ)) (by norm_num)
      (by simpa [informativeExceptionalEvent] using hx)
      (trajectoryGrowingPrefixForwardBesselPACBayesArgmin
        uniformPrior informativeScore (selectedPosterior x 512)
          (1 / 160) 512 x)
      (selectedPosterior x 512) (selectedPosterior_isPMF x 512)
      512 (by norm_num)
  simpa [observableOracleBoundary,
    trajectoryGrowingPrefixForwardBesselPACBayesBoundary] using hbound

/-- The exact selected boundary is controlled by the explicit observable
variance-adaptive envelope on the same path. -/
theorem observableOracleBoundary_512_le_LILEnvelope (x : ℕ → Bool) :
    observableOracleBoundary 512 x ≤
      trajectoryGrowingPrefixForwardBesselPACBayesLILEnvelope
        uniformPrior informativeScore (selectedPosterior x 512)
          (1 / 160) 512 x := by
  exact trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
    uniformPrior_isFullSupportPMF (selectedPosterior_isPMF x 512)
    informativeScore_mem_Icc (by norm_num) (by norm_num) (by norm_num) x

/-- At the two audited reporting times, exact post-data minimization preserves
the previous strict numerical upper bounds without evaluating the classical
argmin witness. -/
theorem observableOracleBoundary_numeric_receipt
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    observableOracleBoundary 512 x < (2744 : ℝ) / 10000 ∧
      observableOracleBoundary 2048 x < (1434 : ℝ) / 10000 := by
  constructor
  · exact (observableOracleBoundary_le_highConfidenceBoundary 512 x).trans_lt
      (highConfidenceBoundary_512_enclosure hx).2
  · exact (observableOracleBoundary_le_highConfidenceBoundary 2048 x).trans_lt
      (highConfidenceBoundary_2048_enclosure hx).2

/-- The complete empirical-plus-oracle right-hand side remains strictly below
`7/25` on the audited positive-mass cylinder. -/
theorem observableOracle_rhs_512_lt_seven_twenty_fifths_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    trajectoryPosteriorEmpiricalPrequentialRisk
          informativeScore (selectedPosterior x 512) 512 x +
        observableOracleBoundary 512 x < (7 : ℝ) / 25 := by
  have horacle := observableOracleBoundary_le_highConfidenceBoundary 512 x
  have hold := highConfidence_rhs_512_lt_seven_twenty_fifths_of_mem hx
  linarith

/-- Replayable end-to-end receipt: a positive-mass supported trajectory lies
outside the allocated exceptional event, its path-selected posterior has the
ordinary conditional-risk guarantee, and the exact post-data tilt oracle is
both nonvacuous and bounded by the observable LIL-order envelope. -/
theorem informative_observableOracle_receipt :
    ∃ x : ℕ → Bool,
      x ∈ informativeCylinder ∧
      x ∉ informativeExceptionalEvent ∧
      selectedPosterior x 512 = pointPosterior true ∧
      trajectoryPosteriorAverageConditionalRisk
          informativeDynamicKernel informativeScore
            (selectedPosterior x 512) 512 x <
        trajectoryPosteriorEmpiricalPrequentialRisk
            informativeScore (selectedPosterior x 512) 512 x +
          observableOracleBoundary 512 x ∧
      observableOracleBoundary 512 x < (2744 : ℝ) / 10000 ∧
      observableOracleBoundary 2048 x < (1434 : ℝ) / 10000 ∧
      trajectoryPosteriorEmpiricalPrequentialRisk
            informativeScore (selectedPosterior x 512) 512 x +
          observableOracleBoundary 512 x < (7 : ℝ) / 25 ∧
      observableOracleBoundary 512 x ≤
        trajectoryGrowingPrefixForwardBesselPACBayesLILEnvelope
          uniformPrior informativeScore (selectedPosterior x 512)
            (1 / 160) 512 x := by
  obtain ⟨x, hx, hgood⟩ := informative_goodCylinderPath_exists
  have hposterior : selectedPosterior x 512 = pointPosterior true := by
    unfold selectedPosterior
    have hx1 : x 1 = true := by
      simpa [informativeCylinder, firstTrueEvent] using hx.2
    rw [hx1]
  exact ⟨x, hx, hgood, hposterior,
    observableOracle_risk_bound_of_not_mem hgood,
    (observableOracleBoundary_numeric_receipt hx).1,
    (observableOracleBoundary_numeric_receipt hx).2,
    observableOracle_rhs_512_lt_seven_twenty_fifths_of_mem hx,
    observableOracleBoundary_512_le_LILEnvelope x⟩

/-! ## Same-event wake-selected soft-Brier receipt -/

/-- Numeric encoding of a Boolean outcome. -/
def softBrierOutcome : Bool → ℝ
  | false => 0
  | true => 1

/-- A genuinely probabilistic forecast.  The `true` hypothesis always predicts
`3/4`.  The `false` hypothesis predicts `1/4` at time zero and thereafter puts
probability `3/4` on the prefix-determined next state. -/
def softInformativeForecast (h : Bool) (n : ℕ)
    (u : (i : Finset.Iic n) → Bool) : ℝ :=
  if h then 3 / 4
  else if n = 0 then 1 / 4
  else if informativeNextState n u then 3 / 4 else 1 / 4

/-- Squared probabilistic loss for the soft informative forecast. -/
def softInformativeBrierScore (h : Bool) : TrajectoryScore Bool :=
  fun n u y ↦
    (softInformativeForecast h n u - softBrierOutcome y) ^ 2

theorem softInformativeBrierScore_mem_Icc :
    ∀ h n u y,
      softInformativeBrierScore h n u y ∈ Set.Icc (0 : ℝ) 1 := by
  intro h n u y
  constructor
  · exact sq_nonneg _
  · fin_cases h <;> fin_cases y <;>
      norm_num [softInformativeBrierScore, softInformativeForecast,
        softBrierOutcome] <;>
      split_ifs <;> norm_num

/-- The wake is selected from the observed first transition. -/
def selectedSoftBrierWake (x : ℕ → Bool) : ℕ :=
  if x 1 then 0 else 1

def eighthTilt (_j : ℕ) : ℝ := 1 / 8

theorem eighthTilt_pos (j : ℕ) : 0 < eighthTilt j := by
  norm_num [eighthTilt]

theorem eighthTilt_le (j : ℕ) : eighthTilt j ≤ (1 / 8 : ℝ) := by
  norm_num [eighthTilt]

theorem selectedSoftBrierWake_eq_zero_of_mem
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    selectedSoftBrierWake x = 0 := by
  have hx1 : x 1 = true := by
    simpa [informativeCylinder, firstTrueEvent] using hx.2
  simp [selectedSoftBrierWake, hx1]

theorem selectedSoftBrierWake_eq_one_of_mem
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) :
    selectedSoftBrierWake x = 1 := by
  have hx1 : x 1 = false := by
    simpa [alternateCylinder, firstFalseEvent] using hx.2
  simp [selectedSoftBrierWake, hx1]

theorem selectedPosterior_eq_true_of_mem_informativeCylinder
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) (n : ℕ) :
    selectedPosterior x n = pointPosterior true := by
  unfold selectedPosterior
  have hx1 : x 1 = true := by
    simpa [informativeCylinder, firstTrueEvent] using hx.2
  rw [hx1]

theorem selectedPosterior_eq_false_of_mem_alternateCylinder
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) (n : ℕ) :
    selectedPosterior x n = pointPosterior false := by
  unfold selectedPosterior
  have hx1 : x 1 = false := by
    simpa [alternateCylinder, firstFalseEvent] using hx.2
  rw [hx1]

theorem observed_softBrier_true_eq
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) (k : ℕ) :
    observedTrajectoryScore (softInformativeBrierScore true) k x =
      (1 : ℝ) / 16 := by
  have hxnext := path_eq_true_of_mem_informativeCylinder hx
    (show 1 ≤ k + 1 by omega)
  norm_num [observedTrajectoryScore, softInformativeBrierScore,
    softInformativeForecast, softBrierOutcome, hxnext]

theorem observed_softBrier_false_eq
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) (k : ℕ) :
    observedTrajectoryScore (softInformativeBrierScore false) k x =
      (1 : ℝ) / 16 := by
  by_cases hk : k = 0
  · subst k
    have hx1 : x 1 = false := by
      simpa [alternateCylinder, firstFalseEvent] using hx.2
    norm_num [observedTrajectoryScore, softInformativeBrierScore,
      softInformativeForecast, softBrierOutcome, hx1]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hrec := hx.1 k hk1
    unfold observedTrajectoryScore
    rw [hrec]
    cases hnext : informativeNextState k (Preorder.frestrictLe k x) <;>
      norm_num [softInformativeBrierScore,
        softInformativeForecast, softBrierOutcome, hk, hnext]

theorem softBrier_true_conditionalRisk_timeZero (x : ℕ → Bool) :
    conditionalTrajectoryRisk informativeDynamicKernel
        (softInformativeBrierScore true) 0 x =
      (3 : ℝ) / 16 := by
  unfold conditionalTrajectoryRisk informativeDynamicKernel
  change ∫ y, softInformativeBrierScore true 0
      (Preorder.frestrictLe 0 x) y
    ∂(informativeDynamicPMF 0
      (Preorder.frestrictLe 0 x)).toMeasure = _
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  norm_num [informativeDynamicPMF, PMF.ofFintype_apply,
    softInformativeBrierScore, softInformativeForecast, softBrierOutcome]

theorem softBrier_true_conditionalRisk_succ
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder)
    {k : ℕ} (hk : 1 ≤ k) :
    conditionalTrajectoryRisk informativeDynamicKernel
        (softInformativeBrierScore true) k x = (1 : ℝ) / 16 := by
  unfold conditionalTrajectoryRisk informativeDynamicKernel
  change ∫ y, softInformativeBrierScore true k
      (Preorder.frestrictLe k x) y
    ∂(informativeDynamicPMF k (Preorder.frestrictLe k x)).toMeasure = _
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hxnext := path_eq_true_of_mem_informativeCylinder hx
    (show 1 ≤ k + 1 by omega)
  have hrec := hx.1 k hk
  have hnext : informativeNextState k (Preorder.frestrictLe k x) = true := by
    rw [← hrec]
    exact hxnext
  norm_num [informativeDynamicPMF, PMF.ofFintype_apply,
    softInformativeBrierScore, softInformativeForecast, softBrierOutcome,
    hk0, hnext]

theorem softBrier_false_conditionalRisk_succ
    {x : ℕ → Bool}
    {k : ℕ} (hk : 1 ≤ k) :
    conditionalTrajectoryRisk informativeDynamicKernel
        (softInformativeBrierScore false) k x = (1 : ℝ) / 16 := by
  unfold conditionalTrajectoryRisk informativeDynamicKernel
  change ∫ y, softInformativeBrierScore false k
      (Preorder.frestrictLe k x) y
    ∂(informativeDynamicPMF k (Preorder.frestrictLe k x)).toMeasure = _
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  cases hnext : informativeNextState k (Preorder.frestrictLe k x) <;>
    norm_num [informativeDynamicPMF, PMF.ofFintype_apply,
      softInformativeBrierScore, softInformativeForecast, softBrierOutcome,
      hk0, hnext]

theorem softBrier_true_conditionalSuffixRisk_eq
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    finiteTrajectoryPosteriorAverageConditionalSuffixRisk
        informativeDynamicKernel softInformativeBrierScore
        (selectedPosterior x 512) 0 512 x = (257 : ℝ) / 4096 := by
  have hposterior :=
    selectedPosterior_eq_true_of_mem_informativeCylinder hx 512
  rw [hposterior]
  unfold finiteTrajectoryPosteriorAverageConditionalSuffixRisk posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  have hsum :
      ∑ k ∈ Finset.Ico 0 512,
          conditionalTrajectoryRisk informativeDynamicKernel
            (softInformativeBrierScore true) k x = (257 : ℝ) / 8 := by
    rw [Nat.Ico_zero_eq_range]
    calc
      _ = ∑ k ∈ Finset.range 512,
          if k = 0 then (3 : ℝ) / 16 else 1 / 16 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hk0 : k = 0
        · subst k
          simp [softBrier_true_conditionalRisk_timeZero]
        · rw [if_neg hk0]
          exact softBrier_true_conditionalRisk_succ hx
            (Nat.one_le_iff_ne_zero.mpr hk0)
      _ = (257 : ℝ) / 8 := by
        norm_num [Finset.sum_range_succ]
  rw [hsum]
  norm_num

theorem softBrier_false_conditionalSuffixRisk_eq
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) :
    finiteTrajectoryPosteriorAverageConditionalSuffixRisk
        informativeDynamicKernel softInformativeBrierScore
        (selectedPosterior x 512) 1 512 x = (1 : ℝ) / 16 := by
  have hposterior :=
    selectedPosterior_eq_false_of_mem_alternateCylinder hx 512
  rw [hposterior]
  unfold finiteTrajectoryPosteriorAverageConditionalSuffixRisk posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, if_true, one_mul, Bool.true_eq_false,
    if_false, zero_mul]
  have hsum :
      ∑ k ∈ Finset.Ico 1 512,
          conditionalTrajectoryRisk informativeDynamicKernel
            (softInformativeBrierScore false) k x = (511 : ℝ) / 16 := by
    calc
      _ = ∑ _k ∈ Finset.Ico 1 512, (1 : ℝ) / 16 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact softBrier_false_conditionalRisk_succ
          (Finset.mem_Ico.mp hk).1
      _ = (511 : ℝ) / 16 := by norm_num
  rw [hsum]
  norm_num

theorem softBrier_true_empiricalSuffixRisk_eq
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        softInformativeBrierScore (selectedPosterior x 512) 0 512 x =
      (1 : ℝ) / 16 := by
  have hposterior :=
    selectedPosterior_eq_true_of_mem_informativeCylinder hx 512
  rw [hposterior]
  unfold finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  simp_rw [observed_softBrier_true_eq hx]
  norm_num

theorem softBrier_false_empiricalSuffixRisk_eq
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) :
    finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk
        softInformativeBrierScore (selectedPosterior x 512) 1 512 x =
      (1 : ℝ) / 16 := by
  have hposterior :=
    selectedPosterior_eq_false_of_mem_alternateCylinder hx 512
  rw [hposterior]
  unfold finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, if_true, one_mul, Bool.true_eq_false,
    if_false, zero_mul]
  simp_rw [observed_softBrier_false_eq hx]
  norm_num

theorem softBrier_true_forwardPredictor_eq
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder)
    {k : ℕ} (hk : 0 < k) :
    forwardPredictorProcess
        (observedTrajectoryScore (softInformativeBrierScore true)) k x =
      (1 : ℝ) / 16 := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg hk.ne']
  simp_rw [observed_softBrier_true_eq hx]
  simp [hk.ne']

theorem softBrier_false_forwardPredictor_eq
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder)
    {k : ℕ} (hk : 0 < k) :
    forwardPredictorProcess
        (observedTrajectoryScore (softInformativeBrierScore false)) k x =
      (1 : ℝ) / 16 := by
  unfold forwardPredictorProcess forwardPredictor forwardPrefixMean
  rw [if_neg hk.ne']
  simp_rw [observed_softBrier_false_eq hx]
  simp [hk.ne']

theorem softBrier_true_predictorPenalty_eq
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        softInformativeBrierScore (selectedPosterior x 512)
        eighthTilt 0 512 x =
      forwardEmpiricalBernsteinPsi (1 / 8) * (49 / 256) := by
  have hposterior :=
    selectedPosterior_eq_true_of_mem_informativeCylinder hx 512
  rw [hposterior]
  unfold finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, Bool.false_eq_true, if_false, zero_mul,
    if_true, one_mul]
  simp only [add_zero]
  rw [Nat.Ico_zero_eq_range]
  calc
    _ = ∑ k ∈ Finset.range 512,
        if k = 0 then
          forwardEmpiricalBernsteinPsi (1 / 8) * (49 / 256)
        else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        norm_num [eighthTilt, observed_softBrier_true_eq hx,
          forwardPredictorProcess, forwardPredictor]
      · rw [if_neg hk0, observed_softBrier_true_eq hx,
          softBrier_true_forwardPredictor_eq hx
            (Nat.pos_of_ne_zero hk0)]
        ring
    _ = forwardEmpiricalBernsteinPsi (1 / 8) * (49 / 256) := by
      norm_num [Finset.sum_range_succ]

theorem softBrier_false_predictorPenalty_eq
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) :
    finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
        softInformativeBrierScore (selectedPosterior x 512)
        eighthTilt 1 512 x = 0 := by
  have hposterior :=
    selectedPosterior_eq_false_of_mem_alternateCylinder hx 512
  rw [hposterior]
  unfold finiteTrajectoryPosteriorConstantTiltSuffixPredictorQuadraticPenalty
    posteriorAverage
  rw [Fintype.sum_bool]
  simp only [pointPosterior, if_true, one_mul, Bool.true_eq_false,
    if_false, zero_mul]
  simp only [zero_add]
  apply Finset.sum_eq_zero
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
  rw [observed_softBrier_false_eq hx,
    softBrier_false_forwardPredictor_eq hx hkpos]
  ring

def selectedSoftBrierBoundary (x : ℕ → Bool) : ℝ :=
  finiteTrajectorySleepingConstantTiltSuffixBoundary
    uniformPrior (selectedPosterior x 512) softInformativeBrierScore
    eighthTilt (1 / 160) (selectedSoftBrierWake x) 512 x

theorem softBrier_log_budget :
    Real.log (1 / ((1 : ℝ) / 160)) =
      5 * Real.log 2 + Real.log 5 := by
  norm_num
  calc
    Real.log (160 : ℝ) = Real.log ((2 : ℝ) ^ 5 * 5) := by norm_num
    _ = Real.log ((2 : ℝ) ^ 5) + Real.log 5 := by
      rw [Real.log_mul (by positivity) (by norm_num)]
    _ = 5 * Real.log 2 + Real.log 5 := by
      rw [Real.log_pow]
      ring

theorem softBrier_wake_zero_cost :
    -Real.log (polynomialEpochWeight 0) = Real.log 2 := by
  rw [polynomialSleepingSelectionCost]
  norm_num

theorem softBrier_wake_one_cost :
    -Real.log (polynomialEpochWeight 1) = Real.log 2 + Real.log 3 := by
  rw [polynomialSleepingSelectionCost]
  norm_num

theorem selectedSoftBrierBoundary_true_eq
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    selectedSoftBrierBoundary x =
      (1 : ℝ) / 16 +
        (7 * Real.log 2 + Real.log 5 +
          forwardEmpiricalBernsteinPsi (1 / 8) * (49 / 256)) / 64 := by
  unfold selectedSoftBrierBoundary
  unfold finiteTrajectorySleepingConstantTiltSuffixBoundary
  rw [selectedSoftBrierWake_eq_zero_of_mem hx,
    softBrier_true_empiricalSuffixRisk_eq hx,
    selectedPosterior_kl_eq_log_two,
    softBrier_log_budget,
    softBrier_true_predictorPenalty_eq hx]
  rw [sub_eq_add_neg, softBrier_wake_zero_cost]
  norm_num [eighthTilt]
  ring

theorem selectedSoftBrierBoundary_false_eq
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) :
    selectedSoftBrierBoundary x =
      (1 : ℝ) / 16 +
        8 * (7 * Real.log 2 + Real.log 3 + Real.log 5) / 511 := by
  unfold selectedSoftBrierBoundary
  unfold finiteTrajectorySleepingConstantTiltSuffixBoundary
  rw [selectedSoftBrierWake_eq_one_of_mem hx,
    softBrier_false_empiricalSuffixRisk_eq hx,
    selectedPosterior_kl_eq_log_two,
    softBrier_log_budget,
    softBrier_false_predictorPenalty_eq hx]
  rw [sub_eq_add_neg, softBrier_wake_one_cost]
  norm_num [eighthTilt]
  ring

theorem selectedSoftBrierBoundary_true_lt_quarter
    {x : ℕ → Bool} (hx : x ∈ informativeCylinder) :
    selectedSoftBrierBoundary x < (1 : ℝ) / 4 := by
  rw [selectedSoftBrierBoundary_true_eq hx]
  have hpsi := forwardEmpiricalBernsteinPsi_le_two_mul_sq
    (show (1 : ℝ) / 8 ≤ 1 / 2 by norm_num)
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem selectedSoftBrierBoundary_false_lt_quarter
    {x : ℕ → Bool} (hx : x ∈ alternateCylinder) :
    selectedSoftBrierBoundary x < (1 : ℝ) / 4 := by
  rw [selectedSoftBrierBoundary_false_eq hx]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9]

/-- One theorem-generated event contains witnesses from both supported
positive-mass cylinders.  On that same event, the observed first transition
selects both the posterior and the wake time.  Each explicitly evaluated
encountered conditional suffix risk is below a checked boundary smaller than
`1/4`.

The target is conditional risk encountered on the monitored suffix.  This
receipt does not reinterpret it as future, stationary, population, or
deployment risk.  The kernel, prior, score family, and tilt schedule are
predeclared; only the posterior and wake time are selected from the path. -/
theorem informative_twoWake_softBrier_sameEvent_receipt :
    ∃ goodEvent : Set (ℕ → Bool),
      informativePathMeasure.real goodEventᶜ ≤ (1 : ℝ) / 160 ∧
      informativePathMeasure.real informativeCylinder = (3 : ℝ) / 4 ∧
      informativePathMeasure.real alternateCylinder = (1 : ℝ) / 4 ∧
      (∃ x : ℕ → Bool,
        x ∈ informativeCylinder ∧ x ∈ goodEvent ∧
        selectedPosterior x 512 = pointPosterior true ∧
        selectedSoftBrierWake x = 0 ∧
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x =
          (257 : ℝ) / 4096 ∧
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x <
          selectedSoftBrierBoundary x ∧
        selectedSoftBrierBoundary x < (1 : ℝ) / 4) ∧
      (∃ x : ℕ → Bool,
        x ∈ alternateCylinder ∧ x ∈ goodEvent ∧
        selectedPosterior x 512 = pointPosterior false ∧
        selectedSoftBrierWake x = 1 ∧
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x =
          (1 : ℝ) / 16 ∧
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x <
          selectedSoftBrierBoundary x ∧
        selectedSoftBrierBoundary x < (1 : ℝ) / 4) := by
  rcases
      exists_finiteTrajectorySleepingConstantTiltPACBayes_suffixRisk_event
        informativeDynamicKernel false softInformativeBrierScore
        softInformativeBrierScore_mem_Icc eighthTilt
        (L := (1 / 8 : ℝ)) eighthTilt_pos eighthTilt_le (by norm_num)
        uniformPrior_isFullSupportPMF
        (delta := (1 / 160 : ℝ)) (by norm_num) with
    ⟨goodEvent, hmassRaw, hgood⟩
  have hmass : informativePathMeasure.real goodEventᶜ ≤ (1 : ℝ) / 160 := by
    simpa [informativePathMeasure] using hmassRaw
  have htrueExists :
      ∃ x : ℕ → Bool, x ∈ informativeCylinder ∧ x ∈ goodEvent := by
    by_contra hnone
    have hsubset : informativeCylinder ⊆ goodEventᶜ := by
      intro x hx
      show x ∉ goodEvent
      intro hxgood
      exact hnone ⟨x, hx, hxgood⟩
    have hmono : informativePathMeasure.real informativeCylinder ≤
        informativePathMeasure.real goodEventᶜ :=
      measureReal_mono hsubset
    rw [informativeCylinder_real_mass] at hmono
    linarith
  have hfalseExists :
      ∃ x : ℕ → Bool, x ∈ alternateCylinder ∧ x ∈ goodEvent := by
    by_contra hnone
    have hsubset : alternateCylinder ⊆ goodEventᶜ := by
      intro x hx
      show x ∉ goodEvent
      intro hxgood
      exact hnone ⟨x, hx, hxgood⟩
    have hmono : informativePathMeasure.real alternateCylinder ≤
        informativePathMeasure.real goodEventᶜ :=
      measureReal_mono hsubset
    rw [alternateCylinder_real_mass] at hmono
    linarith
  refine ⟨goodEvent, hmass, informativeCylinder_real_mass,
    alternateCylinder_real_mass, ?_, ?_⟩
  · obtain ⟨x, hxcyl, hxgood⟩ := htrueExists
    have hwake := selectedSoftBrierWake_eq_zero_of_mem hxcyl
    have hposterior :=
      selectedPosterior_eq_true_of_mem_informativeCylinder hxcyl 512
    have hboundRaw := hgood x hxgood (selectedPosterior x 512)
      (selectedPosterior_isPMF x 512) 0 512 (by norm_num)
    have htarget :
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x =
          (257 : ℝ) / 4096 := by
      rw [hwake]
      exact softBrier_true_conditionalSuffixRisk_eq hxcyl
    have hbound :
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x <
          selectedSoftBrierBoundary x := by
      simpa [selectedSoftBrierBoundary, hwake] using hboundRaw
    exact ⟨x, hxcyl, hxgood, hposterior, hwake, htarget, hbound,
      selectedSoftBrierBoundary_true_lt_quarter hxcyl⟩
  · obtain ⟨x, hxcyl, hxgood⟩ := hfalseExists
    have hwake := selectedSoftBrierWake_eq_one_of_mem hxcyl
    have hposterior :=
      selectedPosterior_eq_false_of_mem_alternateCylinder hxcyl 512
    have hboundRaw := hgood x hxgood (selectedPosterior x 512)
      (selectedPosterior_isPMF x 512) 1 512 (by norm_num)
    have htarget :
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x =
          (1 : ℝ) / 16 := by
      rw [hwake]
      exact softBrier_false_conditionalSuffixRisk_eq hxcyl
    have hbound :
        finiteTrajectoryPosteriorAverageConditionalSuffixRisk
            informativeDynamicKernel softInformativeBrierScore
            (selectedPosterior x 512) (selectedSoftBrierWake x) 512 x <
          selectedSoftBrierBoundary x := by
      simpa [selectedSoftBrierBoundary, hwake] using hboundRaw
    exact ⟨x, hxcyl, hxgood, hposterior, hwake, htarget, hbound,
      selectedSoftBrierBoundary_false_lt_quarter hxcyl⟩

/-! Public endpoint and complete local axiom receipt. -/

#check trajectoryCountableEmpiricalBernsteinPACBayes_allPosteriors_of_not_mem
#check exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event
#check informativeDynamicKernel_history_witness
#check informativeScore_online_update_witness
#check selectedPosterior_explicit_branches
#check selector_branches_on_positive_mass_good_cylinders
#check informative_allTime_vanishing_capstone
#check informative_nonvacuous_receipt
#check trajectoryGrowingPrefixForwardBesselPACBayesArgmin
#check trajectoryGrowingPrefixForwardBesselPACBayesBoundary
#check trajectoryGrowingPrefixForwardBesselPACBayesLILEnvelope
#check trajectoryGrowingPrefixForwardBesselPACBayesArgmin_mem
#check trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_atom
#check trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
#check trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
#check trajectoryGrowingPrefixForwardBesselPACBayesBoundary_tendsto_zero
#check exists_trajectoryGrowingPrefixForwardBesselPACBayesOracle_event
#check informative_observableOracle_receipt
#check softInformativeBrierScore_mem_Icc
#check softBrier_true_conditionalSuffixRisk_eq
#check softBrier_false_conditionalSuffixRisk_eq
#check selectedSoftBrierBoundary_true_lt_quarter
#check selectedSoftBrierBoundary_false_lt_quarter
#check informative_twoWake_softBrier_sameEvent_receipt

#print axioms informativeDynamicKernel_history_witness
#print axioms informativeScore_mem_Icc
#print axioms informativeScore_online_update_witness
#print axioms transitionViolationScore_mem_Icc
#print axioms transitionViolation_conditionalRisk_eq_zero
#print axioms transitionViolation_observed_ae_zero
#print axioms informative_recurrence_ae
#print axioms informativeSupportEvent_ae
#print axioms informativePathMeasure_firstTrueEvent
#print axioms informativePathMeasure_informativeCylinder
#print axioms path_eq_true_of_mem_informativeCylinder
#print axioms uniformPrior_isFullSupportPMF
#print axioms pointPosterior_isPMF
#print axioms selectedPosterior_isPMF
#print axioms selectedPosterior_explicit_branches
#print axioms pointPosterior_kl_eq_log_two
#print axioms selectedPosterior_kl_eq_log_two
#print axioms selectedPosterior_kl_pos
#print axioms observed_onlineScore_eq_oneThenZero_of_mem
#print axioms selected_empiricalRisk_eq_one_512_of_mem
#print axioms online_forwardBesselQ_512_eq_of_mem
#print axioms online_besselVariance_eq_one_512_of_mem
#print axioms online_besselVariance_mem_Ioo_of_mem
#print axioms online_hybridPenalty_512_eq_of_mem
#print axioms selected_posteriorHybridPenalty_512_eq_of_mem
#print axioms online_forwardBesselQ_2048_eq_of_mem
#print axioms online_hybridPenalty_2048_eq_of_mem
#print axioms selected_posteriorHybridPenalty_2048_eq_of_mem
#print axioms selected_tilt_index_512
#print axioms selected_tilt_index_2048
#print axioms selected_tilt_weight_3
#print axioms selected_tilt_weight_4
#print axioms selected_tilt_log_cost_512
#print axioms selected_tilt_log_cost_2048
#print axioms highConfidenceBoundary_512_eq_of_mem
#print axioms highConfidenceBoundary_2048_eq_of_mem
#print axioms highConfidenceBoundary_512_enclosure
#print axioms highConfidenceBoundary_2048_enclosure
#print axioms highConfidenceBoundary_2048_lt_512_of_mem
#print axioms highConfidence_rhs_512_lt_seven_twenty_fifths_of_mem
#print axioms informativeExceptionalEvent_mass_le_delta
#print axioms informativeCylinder_real_mass
#print axioms informative_goodCylinderPath_exists
#print axioms informativePathMeasure_firstFalseEvent
#print axioms alternateCylinder_real_mass
#print axioms alternate_goodCylinderPath_exists
#print axioms selector_branches_on_positive_mass_good_cylinders
#print axioms informative_allTime_vanishing_capstone
#print axioms selected_risk_bound_of_not_mem
#print axioms informative_nonvacuous_receipt
#print axioms trajectoryGrowingPrefixForwardBesselPACBayesArgmin_mem
#print axioms trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_atom
#print axioms trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_LILEnvelope
#print axioms trajectoryGrowingPrefixForwardBesselPACBayesBoundary_le_allTimeRate
#print axioms trajectoryGrowingPrefixForwardBesselPACBayesBoundary_tendsto_zero
#print axioms exists_trajectoryGrowingPrefixForwardBesselPACBayesOracle_event
#print axioms observableOracleBoundary_le_highConfidenceBoundary
#print axioms observableOracle_risk_bound_of_not_mem
#print axioms observableOracleBoundary_512_le_LILEnvelope
#print axioms observableOracleBoundary_numeric_receipt
#print axioms observableOracle_rhs_512_lt_seven_twenty_fifths_of_mem
#print axioms informative_observableOracle_receipt
#print axioms softInformativeBrierScore_mem_Icc
#print axioms softBrier_true_conditionalSuffixRisk_eq
#print axioms softBrier_false_conditionalSuffixRisk_eq
#print axioms selectedSoftBrierBoundary_true_lt_quarter
#print axioms selectedSoftBrierBoundary_false_lt_quarter
#print axioms informative_twoWake_softBrier_sameEvent_receipt

end
end FormalSLT.Examples.CheckTrajectoryEmpiricalBernsteinPACBayesCountableInformative
