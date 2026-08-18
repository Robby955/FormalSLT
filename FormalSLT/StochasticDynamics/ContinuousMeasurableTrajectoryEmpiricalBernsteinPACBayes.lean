/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.ContinuousTrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.MeasurableTrajectoryRisk

/-!
# Continuous-hypothesis PAC-Bayes on arbitrary measurable trajectory spaces

This module combines the arbitrary-measurable-state trajectory semantics with
the continuous-hypothesis forward empirical-Bernstein PAC-Bayes engine.  Both
the hypothesis space and the state space may be arbitrary measurable spaces.
The continuation kernel may depend on the complete observed prefix.

The score-family measurability contract is joint in the hypothesis, complete
prefix, and next state.  From that single score contract, this file derives:

* joint measurability of every fixed-hypothesis trajectory score;
* parameter measurability and posterior integrability of the kernel risk;
* increment adaptedness of the observed score;
* predictability of the conditional risk; and
* the exact trajectory conditional-expectation identity.

The final theorem then invokes the actual continuous-prior
predictable-mean empirical-Bernstein e-process.  Measurability of the complete
parameterized finite-time process in the product of the time filtration with
the hypothesis sigma algebra is derived from the same joint score contract;
ambient product measurability follows by monotonicity.  No separate
concentration, MGF, expectation, or process-measurability premise is assumed.

The resulting single outer-probability event is simultaneous over every
`n >= 2`, every declared finite tilt, and every posterior absolutely
continuous with respect to the prior whose log-likelihood ratio is
integrable.  No finite-state or finite-hypothesis assumption is used.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

local instance continuousMeasurableTrajectoryPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {Theta Tau Z : Type*} [MeasurableSpace Theta] [MeasurableSpace Z]
  [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]

/-- Joint measurability of a parameterized trajectory score in the
hypothesis, complete prefix, and next state. -/
def JointlyStronglyMeasurableParameterizedTrajectoryScore
    (score : Theta -> TrajectoryScore Z) : Prop :=
  forall n, StronglyMeasurable
    (fun q : Theta × (((i : Finset.Iic n) -> Z) × Z) =>
      score q.1 n q.2.1 q.2.2)

/-- Every fixed-hypothesis section of a jointly measurable parameterized
score satisfies the arbitrary-state trajectory measurability contract. -/
lemma jointlyStronglyMeasurableTrajectoryScore_section
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (theta : Theta) :
    JointlyStronglyMeasurableTrajectoryScore (score theta) := by
  intro n
  have hmap : Measurable
      (fun p : (((i : Finset.Iic n) -> Z) × Z) => (theta, p)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using (hscore n).comp_measurable hmap

/-- At a fixed path coordinate, the observed score is strongly measurable in
the hypothesis parameter. -/
lemma stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (n : Nat) (x : Nat -> Z) :
    StronglyMeasurable (fun theta =>
      observedTrajectoryScore (score theta) n x) := by
  have hmap : Measurable (fun theta : Theta =>
      (theta, (Preorder.frestrictLe n x, x (n + 1)))) :=
    measurable_id.prodMk (measurable_const.prodMk measurable_const)
  simpa only [observedTrajectoryScore, Function.comp_def] using
    (hscore n).comp_measurable hmap

/-- At a fixed encountered prefix, the kernel-conditional risk is strongly
measurable in the hypothesis parameter. -/
lemma stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (n : Nat) (x : Nat -> Z) :
    StronglyMeasurable (fun theta =>
      conditionalTrajectoryRisk K (score theta) n x) := by
  let u := Preorder.frestrictLe n x
  have hmap : Measurable (fun q : Theta × Z =>
      (q.1, (u, q.2))) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  have hjoint : StronglyMeasurable (fun q : Theta × Z =>
      score q.1 n u q.2) := by
    simpa only [Function.comp_def] using (hscore n).comp_measurable hmap
  unfold conditionalTrajectoryRisk
  change StronglyMeasurable (fun theta =>
    ∫ y, score theta n u y ∂K n u)
  exact StronglyMeasurable.integral_prod_right' (ν := K n u) hjoint

/-- Under a probability posterior, the parameterized conditional risk is
integrable.  Boundedness and the joint score contract discharge the analytic
obligation rather than assuming posterior integrability separately. -/
lemma integrable_conditionalTrajectoryRisk_parameter_of_joint
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (n : Nat) (x : Nat -> Z) :
    Integrable (fun theta =>
      conditionalTrajectoryRisk K (score theta) n x) posterior := by
  refine Integrable.of_bound
    (stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint
      K hscore n x).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall fun theta => by
    have hsection := jointlyStronglyMeasurableTrajectoryScore_section
      hscore theta
    have hrisk := conditionalTrajectoryRisk_mem_Icc_of_joint
      K hsection (hscore_unit theta) n x
    rw [Real.norm_eq_abs, abs_of_nonneg hrisk.1]
    exact hrisk.2

/-- Thin arbitrary-state wrapper: the observed parameterized score is
increment-adapted for every fixed hypothesis. -/
lemma observedTrajectoryScore_incrementAdapted_parameterized_of_joint
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (theta : Theta) :
    IncrementAdapted (Filtration.piLE (X := fun _ : Nat => Z))
      (observedTrajectoryScore (score theta)) := by
  intro n
  exact stronglyMeasurable_observedTrajectoryScore_succ_of_joint
    (jointlyStronglyMeasurableTrajectoryScore_section hscore theta) n

/-- Thin arbitrary-state wrapper: the kernel-conditional risk is predictable
for every fixed hypothesis. -/
lemma conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (theta : Theta) :
    StronglyAdapted (Filtration.piLE (X := fun _ : Nat => Z))
      (conditionalTrajectoryRisk K (score theta)) := by
  intro n
  exact stronglyMeasurable_conditionalTrajectoryRisk_of_joint K
    (jointlyStronglyMeasurableTrajectoryScore_section hscore theta) n

/-- Thin arbitrary-state wrapper around the general `Kernel.traj`
conditional-expectation bridge. -/
theorem observedTrajectoryScore_condExp_parameterized_of_joint
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (theta : Theta) (n : Nat) :
    (trajectoryMeasure K x0)[observedTrajectoryScore (score theta) n |
        Filtration.piLE (X := fun _ : Nat => Z) n] =ᵐ[trajectoryMeasure K x0]
      conditionalTrajectoryRisk K (score theta) n := by
  exact observedTrajectoryScore_condExp_of_joint K x0 (score theta)
    (jointlyStronglyMeasurableTrajectoryScore_section hscore theta)
    (hscore_unit theta) n

private lemma stronglyMeasurable_piLE_prod_of_prefix_parameter
    (n : Nat) (g : (((i : Finset.Iic n) -> Z) × Theta) -> Real)
    (hg : StronglyMeasurable g) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
      (fun q : ((Nat -> Z) × Theta) =>
        g (Preorder.frestrictLe n q.1, q.2)) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact hg.comp_measurable
    (((comap_measurable _).comp measurable_fst).prodMk measurable_snd)

private lemma stronglyMeasurable_trajectory_filtered_prod_mono
    {a b : Nat} (hab : a <= b) {f : ((Nat -> Z) × Theta) -> Real}
    (hf : StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) a) inferInstance] f) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) b) inferInstance] f := by
  apply hf.mono
  unfold MeasurableSpace.prod
  exact sup_le_sup
    (MeasurableSpace.comap_mono
      ((Filtration.piLE (X := fun _ : Nat => Z)).mono hab))
    le_rfl

/-- Joint score measurability implies joint path-parameter measurability of
every observation under every later path filtration. -/
lemma stronglyMeasurable_observedTrajectoryScore_joint_filtered
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    {k n : Nat} (hkn : k + 1 <= n) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
      (fun q : ((Nat -> Z) × Theta) =>
        observedTrajectoryScore (score q.2) k q.1) := by
  let g : (((i : Finset.Iic (k + 1)) -> Z) × Theta) -> Real := fun p =>
    score p.2 k
      (Preorder.frestrictLe₂ (π := fun _ : Nat => Z) (Nat.le_succ k) p.1)
      (p.1 ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩)
  have hmap : Measurable (fun p :
      (((i : Finset.Iic (k + 1)) -> Z) × Theta) =>
      (p.2,
        (Preorder.frestrictLe₂ (π := fun _ : Nat => Z) (Nat.le_succ k) p.1,
          p.1 ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩))) :=
    measurable_snd.prodMk
      (((Preorder.measurable_frestrictLe₂
        (X := fun _ : Nat => Z) (Nat.le_succ k)).comp measurable_fst).prodMk
        ((measurable_pi_apply
          (⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ :
            Finset.Iic (k + 1))).comp measurable_fst))
  have hg : StronglyMeasurable g := by
    simpa only [g, Function.comp_def] using (hscore k).comp_measurable hmap
  have hbase := stronglyMeasurable_piLE_prod_of_prefix_parameter
    (Theta := Theta) (Z := Z) (k + 1) g hg
  have hbase' : StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) (k + 1)) inferInstance]
      (fun q : ((Nat -> Z) × Theta) =>
        observedTrajectoryScore (score q.2) k q.1) := by
    convert hbase using 1
    funext q
    rfl
  exact stronglyMeasurable_trajectory_filtered_prod_mono hkn hbase'

private lemma stronglyMeasurable_conditionalTrajectoryRisk_prefix_parameter
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (k : Nat) :
    StronglyMeasurable (fun p : (((i : Finset.Iic k) -> Z) × Theta) =>
      ∫ y, score p.2 k p.1 y ∂K k p.1) := by
  let Kparameter : Kernel ((((i : Finset.Iic k) -> Z) × Theta)) Z :=
    (K k).comap Prod.fst measurable_fst
  have hmap : Measurable (fun r :
      ((((i : Finset.Iic k) -> Z) × Theta) × Z) =>
      (r.1.2, (r.1.1, r.2))) :=
    (measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hjoint : StronglyMeasurable (fun r :
      ((((i : Finset.Iic k) -> Z) × Theta) × Z) =>
      score r.1.2 k r.1.1 r.2) := by
    simpa only [Function.comp_def] using (hscore k).comp_measurable hmap
  have hint := StronglyMeasurable.integral_kernel_prod_right'
    (κ := Kparameter) hjoint
  simpa only [Kparameter, Kernel.comap_apply] using hint

/-- Joint score measurability implies joint path-parameter measurability of
the kernel-conditional risk under every later path filtration. -/
lemma stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    {k n : Nat} (hkn : k <= n) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
      (fun q : ((Nat -> Z) × Theta) =>
        conditionalTrajectoryRisk K (score q.2) k q.1) := by
  have hg := stronglyMeasurable_conditionalTrajectoryRisk_prefix_parameter
    K hscore k
  have hbase := stronglyMeasurable_piLE_prod_of_prefix_parameter
    (Theta := Theta) (Z := Z) k
    (fun p : (((i : Finset.Iic k) -> Z) × Theta) =>
      ∫ y, score p.2 k p.1 y ∂K k p.1) hg
  have hbase' : StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) k) inferInstance]
      (fun q : ((Nat -> Z) × Theta) =>
        conditionalTrajectoryRisk K (score q.2) k q.1) := by
    simpa only [conditionalTrajectoryRisk] using hbase
  exact stronglyMeasurable_trajectory_filtered_prod_mono hkn hbase'

private lemma stronglyMeasurable_forwardPredictableMeanLowerProcess_of_coordinates
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X mean : Alpha -> Nat -> Real) (lam : Real) (n : Nat)
    (hX : forall k, k < n -> StronglyMeasurable (fun a => X a k))
    (hmean : forall k, k < n -> StronglyMeasurable (fun a => mean a k)) :
    StronglyMeasurable (fun a =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (fun k a => X a k) (fun k a => mean a k) lam n a) := by
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
        (stronglyMeasurable_const : StronglyMeasurable (fun _ : Alpha => (1 / 2 : Real)))
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
  have hscore : StronglyMeasurable (fun a =>
      lam * (∑ k ∈ Finset.range n, (mean a k - X a k)) -
        forwardEmpiricalBernsteinPsi lam *
          forwardPredictableQuadratic (fun k => X a k) n) :=
    hgap.const_mul lam |>.sub
      (hquad.const_mul (forwardEmpiricalBernsteinPsi lam))
  have hexp := Real.continuous_exp.comp_stronglyMeasurable hscore
  have heq : (fun a =>
      forwardPredictableMeanEmpiricalBernsteinLowerProcess
        (fun k a => X a k) (fun k a => mean a k) lam n a) =
      fun a => Real.exp
        (lam * (∑ k ∈ Finset.range n, (mean a k - X a k)) -
          forwardEmpiricalBernsteinPsi lam *
            forwardPredictableQuadratic (fun k => X a k) n) := by
    funext a
    exact forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq
      (fun k a => X a k) (fun k a => mean a k) lam n a
  rw [heq]
  exact hexp

set_option maxHeartbeats 800000 in
/-- The single joint score contract and kernel measurability derive the
filtered joint measurability of the complete finite-time actual e-process.
Thus the arbitrary-state continuous-posterior endpoint needs no opaque
process-measurability premise. -/
theorem stronglyMeasurable_continuousMeasurableTrajectoryLowerProcess_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)]
    {score : Theta -> TrajectoryScore Z}
    (hscore : JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (lam : Real) (n : Nat) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
      (fun q : ((Nat -> Z) × Theta) =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2)) lam n q.1) := by
  let mProd : MeasurableSpace (((Nat -> Z) × Theta)) :=
    MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance
  letI : MeasurableSpace (((Nat -> Z) × Theta)) := mProd
  change StronglyMeasurable (fun q : ((Nat -> Z) × Theta) =>
    forwardPredictableMeanEmpiricalBernsteinLowerProcess
      (observedTrajectoryScore (score q.2))
      (conditionalTrajectoryRisk K (score q.2)) lam n q.1)
  refine stronglyMeasurable_forwardPredictableMeanLowerProcess_of_coordinates
    (fun (q : ((Nat -> Z) × Theta)) k =>
      observedTrajectoryScore (score q.2) k q.1)
    (fun (q : ((Nat -> Z) × Theta)) k =>
      conditionalTrajectoryRisk K (score q.2) k q.1)
    lam n ?_ ?_
  · intro k hk
    exact stronglyMeasurable_observedTrajectoryScore_joint_filtered
      hscore (Nat.succ_le_iff.mpr hk)
  · intro k hk
    exact stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered
      K hscore (Nat.le_of_lt hk)

/-- Filtered product measurability implies ambient product measurability.
This discharges the duplicate ambient-process interface required by the
generic continuous-mixture engine. -/
lemma stronglyMeasurable_trajectory_ambient_of_filtered_prod
    (n : Nat) {f : ((Nat -> Z) × Theta) -> Real}
    (hf : StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance] f) :
    StronglyMeasurable f := by
  apply hf.mono
  unfold MeasurableSpace.prod
  exact sup_le_sup
    (MeasurableSpace.comap_mono
      ((Filtration.piLE (X := fun _ : Nat => Z)).le n))
    le_rfl

omit [Nonempty Tau] in
/-- One outer-mass event controls continuous-posterior trajectory
empirical-Bernstein PAC-Bayes simultaneously on arbitrary measurable
hypothesis and state spaces.  The event is common to every `n >= 2`, every
declared finite tilt, and every eligible post-data posterior. -/
theorem exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_joint :
      JointlyStronglyMeasurableParameterizedTrajectoryScore score)
    (prior : Measure Theta) [IsProbabilityMeasure prior]
    {weight : Tau -> Real} (hweight_pos : forall j, 0 < weight j)
    (hweight_sum : ∑ j, weight j = 1)
    {lam : Tau -> Real} {delta : Real} (hdelta : 0 < delta)
    (hlam : forall j, 0 < lam j) (hlam_one : forall j, lam j < 1) :
    ∃ goodEvent : Set (Nat -> Z),
      (trajectoryMeasure K x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, forall j : Tau,
          forall posterior : Measure Theta,
            IsProbabilityMeasure posterior -> posterior ≪ prior ->
            Integrable (llr posterior prior) posterior ->
            forall n : Nat, 2 <= n ->
              continuousTrajectoryPosteriorAverageConditionalRisk
                  K score posterior n x <
                continuousTrajectoryPosteriorEmpiricalPrequentialRisk
                    score posterior n x +
                  continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
                    prior weight lam score posterior delta j n x := by
  have hprocess_filtered (j : Tau) (n : Nat) :
      StronglyMeasurable[MeasurableSpace.prod
        ((Filtration.piLE (X := fun _ : Nat => Z)) n) inferInstance]
        (fun q : (Nat -> Z) × Theta =>
          forwardPredictableMeanEmpiricalBernsteinLowerProcess
            (observedTrajectoryScore (score q.2))
            (conditionalTrajectoryRisk K (score q.2))
            (lam j) n q.1) :=
    stronglyMeasurable_continuousMeasurableTrajectoryLowerProcess_filtered
      K hscore_joint (lam j) n
  have hprocess_ambient (j : Tau) (n : Nat) : StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2))
          (lam j) n q.1) :=
    stronglyMeasurable_trajectory_ambient_of_filtered_prod
      n (hprocess_filtered j n)
  rcases exists_continuousForwardPredictableMeanBesselPACBayes_event
      (mu := trajectoryMeasure K x0)
      (F := Filtration.piLE (X := fun _ : Nat => Z))
      prior hweight_pos hweight_sum hdelta hlam hlam_one
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
      hprocess_ambient hprocess_filtered with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j posterior hposterior hposterior_prior hllr n hn
  have hbound := hgood x hx j posterior hposterior
    hposterior_prior hllr n hn
  simpa only [continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic,
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic,
    continuousTrajectoryEmpiricalBernsteinPACBayesBoundary_eq_generic] using hbound

end

end FormalSLT.StochasticDynamics
