/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes
import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes

/-!
# Two-sided singular-fraction PAC-Bayes on measurable trajectory spaces

This module specializes the continuous two-sided singular-fraction theorem to
bounded trajectory scores on arbitrary measurable hypothesis and state spaces.
The joint trajectory-score contract discharges the parameter, path, and
singular-fraction process measurability obligations in both orientations.

One outer-probability event controls every reporting time `n >= 2` and every
eligible posterior chosen after observing the path.  The conclusion concerns
posterior-averaged conditional loss along the encountered prefixes, not
future, population, stationary, or deployment risk.  Its radius is
observable and LIL-order; no sharpness, minimax, or universal
predictable-strategy claim is made.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open FormalSLT.PACBayes.ContinuousSingularFractionBesselPACBayes
open FormalSLT.PACBayes.ContinuousTwoSidedSingularFractionBesselPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

variable {Theta Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]

private lemma stronglyMeasurable_forwardPredictableMeanLowerProcess_variableTilt
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X mean : Alpha -> Nat -> Real) (lam : Alpha -> Real) (n : Nat)
    (hX : forall k, k < n -> StronglyMeasurable (fun a => X a k))
    (hmean : forall k, k < n -> StronglyMeasurable (fun a => mean a k))
    (hlam : StronglyMeasurable lam) :
    StronglyMeasurable (fun a =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (fun k a => X a k) (fun k a => mean a k) (lam a) n a) := by
  have hprefix (k : Nat) (hk : k <= n) : StronglyMeasurable (fun a =>
      forwardPrefixMean (fun r => X a r) k) := by
    unfold forwardPrefixMean
    have hsum : StronglyMeasurable
        (∑ r ∈ Finset.range k, fun a => X a r) :=
      Finset.stronglyMeasurable_sum (Finset.range k) fun r hr =>
        hX r ((Finset.mem_range.mp hr).trans_le hk)
    have heq : (fun a => (∑ r ∈ Finset.range k, X a r) / (k : Real)) =
        fun a => (∑ r ∈ Finset.range k, fun a => X a r) a *
          (k : Real)⁻¹ := by
      funext a
      simp [div_eq_mul_inv]
    rw [heq]
    exact hsum.mul_const (k : Real)⁻¹
  have hpredictor (k : Nat) (hk : k < n) : StronglyMeasurable (fun a =>
      forwardPredictor (fun r => X a r) k) := by
    by_cases hk0 : k = 0
    · subst k
      simpa [forwardPredictor] using
        (stronglyMeasurable_const :
          StronglyMeasurable (fun _ : Alpha => (1 / 2 : Real)))
    · simpa [forwardPredictor, hk0] using
        hprefix k (Nat.le_of_lt hk)
  have hgap : StronglyMeasurable (fun a =>
      ∑ k ∈ Finset.range n, (mean a k - X a k)) := by
    have hgap' := Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
      (hmean k (Finset.mem_range.mp hk)).sub
        (hX k (Finset.mem_range.mp hk))
    convert hgap' using 1
    funext a
    simp
  have hquad : StronglyMeasurable (fun a =>
      forwardPredictableQuadratic (fun k => X a k) n) := by
    unfold forwardPredictableQuadratic
    have hquad' := Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
      ((hX k (Finset.mem_range.mp hk)).sub
        (hpredictor k (Finset.mem_range.mp hk))).pow 2
    convert hquad' using 1
    funext a
    simp
  have hpsi : StronglyMeasurable (fun a =>
      forwardEmpiricalBernsteinPsi (lam a)) := by
    unfold forwardEmpiricalBernsteinPsi
    have harg : StronglyMeasurable (fun a => 1 - lam a) :=
      stronglyMeasurable_const.sub hlam
    have hlog : StronglyMeasurable (fun a => Real.log (1 - lam a)) :=
      (Real.measurable_log.comp harg.measurable).stronglyMeasurable
    exact hlog.neg.sub hlam
  have hscore : StronglyMeasurable (fun a =>
      lam a * (∑ k ∈ Finset.range n, (mean a k - X a k)) -
        forwardEmpiricalBernsteinPsi (lam a) *
          forwardPredictableQuadratic (fun k => X a k) n) :=
    (hlam.mul hgap).sub (hpsi.mul hquad)
  have hexp := Real.continuous_exp.comp_stronglyMeasurable hscore
  have heq : (fun a =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (fun k a => X a k) (fun k a => mean a k) (lam a) n a) =
      fun a => Real.exp
        (lam a * (∑ k ∈ Finset.range n, (mean a k - X a k)) -
          forwardEmpiricalBernsteinPsi (lam a) *
            forwardPredictableQuadratic (fun k => X a k) n) := by
    funext a
    exact forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq
      (fun k a => X a k) (fun k a => mean a k) (lam a) n a
  rw [heq]
  exact hexp

set_option maxHeartbeats 800000 in
/-- Joint measurability of the score family derives filtered joint
measurability of the singular-fraction lower process. -/
theorem stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (n : Nat) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
      (fun q : (Nat -> Z) × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2.2))
          (conditionalTrajectoryRisk K (score q.2.2))
          (singularFraction q.2.1) n q.1) := by
  let mProd : MeasurableSpace ((Nat -> Z) × (Real × Theta)) :=
    MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance
  letI : MeasurableSpace ((Nat -> Z) × (Real × Theta)) := mProd
  change StronglyMeasurable (fun q : (Nat -> Z) × (Real × Theta) =>
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (observedTrajectoryScore (score q.2.2))
      (conditionalTrajectoryRisk K (score q.2.2))
      (singularFraction q.2.1) n q.1)
  refine stronglyMeasurable_forwardPredictableMeanLowerProcess_variableTilt
    (fun (q : (Nat -> Z) × (Real × Theta)) k =>
      observedTrajectoryScore (score q.2.2) k q.1)
    (fun (q : (Nat -> Z) × (Real × Theta)) k =>
      conditionalTrajectoryRisk K (score q.2.2) k q.1)
    (fun q => singularFraction q.2.1) n ?_ ?_ ?_
  · intro k hk
    have hbase := stronglyMeasurable_observedTrajectoryScore_joint_filtered
      hscore (Nat.succ_le_iff.mpr hk)
    exact hbase.comp_measurable
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  · intro k hk
    have hbase := stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered
      K hscore (Nat.le_of_lt hk)
    exact hbase.comp_measurable
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  · exact (measurable_singularFraction.comp
      (measurable_fst.comp measurable_snd)).stronglyMeasurable

set_option maxHeartbeats 800000 in
/-- The same score contract derives filtered joint measurability for the
complemented trajectory process used for the opposite tail. -/
theorem stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (n : Nat) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
      (fun q : (Nat -> Z) × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (fun k x => 1 - observedTrajectoryScore (score q.2.2) k x)
          (fun k x => 1 - conditionalTrajectoryRisk K (score q.2.2) k x)
          (singularFraction q.2.1) n q.1) := by
  let mProd : MeasurableSpace ((Nat -> Z) × (Real × Theta)) :=
    MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance
  letI : MeasurableSpace ((Nat -> Z) × (Real × Theta)) := mProd
  change StronglyMeasurable (fun q : (Nat -> Z) × (Real × Theta) =>
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (fun k x => 1 - observedTrajectoryScore (score q.2.2) k x)
      (fun k x => 1 - conditionalTrajectoryRisk K (score q.2.2) k x)
      (singularFraction q.2.1) n q.1)
  refine stronglyMeasurable_forwardPredictableMeanLowerProcess_variableTilt
    (fun (q : (Nat -> Z) × (Real × Theta)) k =>
      1 - observedTrajectoryScore (score q.2.2) k q.1)
    (fun (q : (Nat -> Z) × (Real × Theta)) k =>
      1 - conditionalTrajectoryRisk K (score q.2.2) k q.1)
    (fun q => singularFraction q.2.1) n ?_ ?_ ?_
  · intro k hk
    have hbase := stronglyMeasurable_observedTrajectoryScore_joint_filtered
      hscore (Nat.succ_le_iff.mpr hk)
    exact stronglyMeasurable_const.sub (hbase.comp_measurable
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  · intro k hk
    have hbase := stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered
      K hscore (Nat.le_of_lt hk)
    exact stronglyMeasurable_const.sub (hbase.comp_measurable
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  · exact (measurable_singularFraction.comp
      (measurable_fst.comp measurable_snd)).stronglyMeasurable

/-- Filtered measurability gives ambient joint measurability of the original
singular-fraction trajectory process. -/
theorem stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_ambient
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2.2))
          (conditionalTrajectoryRisk K (score q.2.2))
          (singularFraction q.2.1) n q.1) := by
  exact stronglyMeasurable_trajectory_ambient_of_filtered_prod
    (Theta := Real × Theta) (Z := Z) n
    (stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_filtered
      K hscore n)

/-- Filtered measurability gives ambient joint measurability of the
complemented singular-fraction trajectory process. -/
theorem stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_ambient
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × (Real × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (fun k x => 1 - observedTrajectoryScore (score q.2.2) k x)
          (fun k x => 1 - conditionalTrajectoryRisk K (score q.2.2) k x)
          (singularFraction q.2.1) n q.1) := by
  exact stronglyMeasurable_trajectory_ambient_of_filtered_prod
    (Theta := Real × Theta) (Z := Z) n
    (stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_filtered
      K hscore n)

/-- For bounded jointly measurable scores on arbitrary measurable state and
hypothesis spaces, a single event of complement outer mass at most `delta`
controls the absolute posterior-averaged conditional-minus-observed
trajectory-prefix gap.  The event precedes the path, every eligible posterior
selected from that path, and every reporting time `n >= 2`.  The two tails use
equal confidence budgets.  The conclusion concerns encountered-prefix risk
only and makes no sharpness or strategy-uniformity claim. -/
theorem exists_continuousMeasurableTrajectoryTwoSidedSingularFractionBesselPACBayesLIL_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n ->
              |continuousTrajectoryPosteriorAverageConditionalRisk
                    K score posterior n x -
                continuousTrajectoryPosteriorEmpiricalPrequentialRisk
                    score posterior n x| <
                singularFractionObservableLILBoundary
                    (continuousTrajectoryPosteriorHybridBesselPenalty
                      score posterior n x)
                    (continuousSingularFractionBesselEffectiveConfidence
                      prior posterior (delta / 2)) /
                  (n : Real) := by
  rcases exists_continuousTwoSidedSingularFractionBesselPACBayesLIL_event
      (mu := trajectoryMeasure K x0)
      (F := Filtration.piLE (X := fun _ : Nat => Z)) prior
      hdelta hdelta_one
      (fun theta =>
        observedTrajectoryScore_incrementAdapted_parameterized_of_joint
          hscore_joint theta)
      (fun theta =>
        conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
          K hscore_joint theta)
      (fun theta k x => observedTrajectoryScore_mem_Icc
        (hscore_unit theta) k x)
      (fun theta k x => conditionalTrajectoryRisk_mem_Icc_of_joint
        K (jointlyStronglyMeasurableTrajectoryScore_section
          hscore_joint theta) (hscore_unit theta) k x)
      (fun theta k => observedTrajectoryScore_condExp_parameterized_of_joint
        K x0 hscore_joint hscore_unit theta k)
      (fun k x =>
        stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
          hscore_joint k x)
      (fun k x =>
        stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint
          K hscore_joint k x)
      (stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_ambient
        K hscore_joint)
      (stronglyMeasurable_continuousMeasurableTrajectorySingularFractionLowerProcess_filtered
        K hscore_joint)
      (stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_ambient
        K hscore_joint)
      (stronglyMeasurable_continuousMeasurableTrajectoryComplementSingularFractionLowerProcess_filtered
        K hscore_joint) with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx posterior hposterior hposterior_prior hllr n hn
  have hbound := hgood x hx posterior hposterior hposterior_prior hllr n hn
  simpa only [continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic,
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic,
    continuousTrajectoryPosteriorHybridBesselPenalty_eq_generic] using hbound

end

end FormalSLT.StochasticDynamics
