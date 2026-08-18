/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes

/-!
# Continuous-hypothesis trajectory empirical-Bernstein PAC-Bayes

This module specializes the continuous predictable-mean forward-Bessel
PAC-Bayes theorem to arbitrary prefix-dependent finite-state trajectory
kernels.  The hypothesis parameter may be any measurable space, the prior is
an arbitrary probability measure, and every probability posterior absolutely
continuous with respect to the prior and with integrable log-likelihood ratio
is supported on the same outer-probability event.

The supplied trajectory score family is pointwise `[0,1]`-valued and
measurable in the hypothesis parameter at every finite prefix and next state.
Because the state space and every observed prefix are finite, this
coordinatewise hypothesis implies joint path-parameter measurability of the
observed score, the kernel-conditional risk, and the actual pathwise
e-process.  Thus the trajectory endpoint has no separate joint-process
measurability assumption.  The filtered joint result also implies ambient
product measurability by monotonicity of the product sigma algebra.

The state space remains finite and discrete and the declared tilt catalog
remains finite.  This file makes no continuous-state claim.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayes.ContinuousForwardPredictableMeanBesselPACBayes
open scoped BigOperators ENNReal

namespace FormalSLT.StochasticDynamics

noncomputable section

local instance continuousTrajectoryPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {Theta Tau Z : Type*} [MeasurableSpace Theta]
  [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- A real-valued function on a product with finite discrete right factor is
strongly measurable when each left section is strongly measurable. -/
theorem stronglyMeasurable_uncurry_of_finite_discrete_right
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    [Fintype Beta] [MeasurableSingletonClass Beta]
    (f : Alpha -> Beta -> Real)
    (hf : forall b, StronglyMeasurable (fun a => f a b)) :
    StronglyMeasurable (fun q : Alpha × Beta => f q.1 q.2) := by
  classical
  have heq : (fun q : Alpha × Beta => f q.1 q.2) =
      ∑ b : Beta, fun q => if q.2 = b then f q.1 b else 0 := by
    funext q
    simp
  rw [heq]
  exact Finset.stronglyMeasurable_sum Finset.univ fun b _ =>
    StronglyMeasurable.ite
      (measurable_snd (measurableSet_singleton b))
      ((hf b).comp_measurable measurable_fst) stronglyMeasurable_const

/-- Parameter measurability of the finite-kernel conditional trajectory risk
follows from coordinatewise parameter measurability of the score. -/
theorem stronglyMeasurable_conditionalTrajectoryRisk_parameter
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (n : Nat) (x : Nat -> Z) :
    StronglyMeasurable (fun theta =>
      conditionalTrajectoryRisk K (score theta) n x) := by
  let u := Preorder.frestrictLe n x
  have hjoint : StronglyMeasurable (fun q : Theta × Z =>
      score q.1 n u q.2) :=
    stronglyMeasurable_uncurry_of_finite_discrete_right
      (fun theta y => score theta n u y)
      (fun y => hscore_parameter n u y)
  unfold conditionalTrajectoryRisk
  change StronglyMeasurable (fun theta =>
    ∫ y, score theta n u y ∂K n u)
  exact StronglyMeasurable.integral_prod_right' (ν := K n u) hjoint

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSingletonClass Z] in
/-- The product of a finite-prefix path sigma algebra with the parameter sigma
algebra is contained in the ambient path-parameter product sigma algebra. -/
theorem measurableSpace_prod_piLE_le_ambient (n : Nat) :
    MeasurableSpace.prod
        ((Filtration.piLE (X := fun _ : Nat => Z)) n)
        (inferInstance : MeasurableSpace Theta) <=
      MeasurableSpace.prod
        (MeasurableSpace.pi : MeasurableSpace (Nat -> Z))
        (inferInstance : MeasurableSpace Theta) := by
  unfold MeasurableSpace.prod
  exact sup_le_sup
    (MeasurableSpace.comap_mono
      ((Filtration.piLE (X := fun _ : Nat => Z)).le n)) le_rfl

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSingletonClass Z] in
private theorem measurable_prefix_parameter_pair
    {k n : Nat} (hkn : k <= n) :
    Measurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
      (fun q : (Nat -> Z) × Theta =>
        (Preorder.frestrictLe k q.1, q.2)) := by
  have hpref_k : Measurable[Filtration.piLE (X := fun _ : Nat => Z) k]
      (Preorder.frestrictLe k :
        (Nat -> Z) -> ((i : Finset.Iic k) -> Z)) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact comap_measurable _
  have hpref_n : Measurable[Filtration.piLE (X := fun _ : Nat => Z) n]
      (Preorder.frestrictLe k :
        (Nat -> Z) -> ((i : Finset.Iic k) -> Z)) :=
    hpref_k.mono
      ((Filtration.piLE (X := fun _ : Nat => Z)).mono hkn) le_rfl
  exact (hpref_n.comp measurable_fst).prodMk measurable_snd

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- For a score measurable in the hypothesis at each finite state-prefix
coordinate, its observed path score is jointly measurable in the path through
time `n` and the hypothesis whenever the observation has been revealed. -/
theorem stronglyMeasurable_observedTrajectoryScore_parameter_prod
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    {k n : Nat} (hkn : k + 1 <= n) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
      (fun q : (Nat -> Z) × Theta =>
        observedTrajectoryScore (score q.2) k q.1) := by
  let f : Theta -> ((i : Finset.Iic (k + 1)) -> Z) -> Real :=
    fun theta u =>
      score theta k
        (Preorder.frestrictLe₂
          (π := fun _ : Nat => Z) (Nat.le_succ k) u)
        (u ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩)
  have hf : StronglyMeasurable
      (fun q : Theta × ((i : Finset.Iic (k + 1)) -> Z) =>
        f q.1 q.2) :=
    stronglyMeasurable_uncurry_of_finite_discrete_right
      (Alpha := Theta) (Beta := ((i : Finset.Iic (k + 1)) -> Z)) f
      (fun u => by
        dsimp [f]
        exact hscore_parameter k _ _)
  have hswap : StronglyMeasurable
      (fun q : ((i : Finset.Iic (k + 1)) -> Z) × Theta =>
        f q.2 q.1) :=
    hf.comp_measurable measurable_swap
  have hmap := measurable_prefix_parameter_pair
    (Theta := Theta) (Z := Z) hkn
  have hcomp := hswap.comp_measurable hmap
  change StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
    (fun q : (Nat -> Z) × Theta =>
      score q.2 k (Preorder.frestrictLe k q.1) (q.1 (k + 1)))
  convert hcomp using 1
  funext q
  simp only [f]
  congr 1

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
private theorem stronglyMeasurable_conditionalTrajectoryRisk_prefix_parameter
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (k : Nat) (u : (i : Finset.Iic k) -> Z) :
    StronglyMeasurable
      (fun theta => ∫ y, score theta k u y ∂K k u) := by
  have hjoint : StronglyMeasurable
      (fun q : Theta × Z => score q.1 k u q.2) :=
    stronglyMeasurable_uncurry_of_finite_discrete_right
      (Alpha := Theta) (Beta := Z)
      (fun theta y => score theta k u y)
      (fun y => hscore_parameter k u y)
  exact StronglyMeasurable.integral_prod_right' (ν := K k u) hjoint

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- Coordinatewise parameter measurability of a finite-state trajectory score
also makes its kernel-conditional risk jointly measurable in the finite path
prefix and the hypothesis. -/
theorem stronglyMeasurable_conditionalTrajectoryRisk_parameter_prod
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    {k n : Nat} (hkn : k <= n) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
      (fun q : (Nat -> Z) × Theta =>
        conditionalTrajectoryRisk K (score q.2) k q.1) := by
  let f : Theta -> ((i : Finset.Iic k) -> Z) -> Real :=
    fun theta u => ∫ y, score theta k u y ∂K k u
  have hf : StronglyMeasurable
      (fun q : Theta × ((i : Finset.Iic k) -> Z) => f q.1 q.2) :=
    stronglyMeasurable_uncurry_of_finite_discrete_right
      (Alpha := Theta) (Beta := ((i : Finset.Iic k) -> Z)) f
      (fun u => by
        dsimp [f]
        exact stronglyMeasurable_conditionalTrajectoryRisk_prefix_parameter
          K score hscore_parameter k u)
  have hswap : StronglyMeasurable
      (fun q : ((i : Finset.Iic k) -> Z) × Theta => f q.2 q.1) :=
    hf.comp_measurable measurable_swap
  have hmap := measurable_prefix_parameter_pair
    (Theta := Theta) (Z := Z) hkn
  have hcomp := hswap.comp_measurable hmap
  change StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
    (fun q : (Nat -> Z) × Theta =>
      ∫ y, score q.2 k (Preorder.frestrictLe k q.1) y
        ∂K k (Preorder.frestrictLe k q.1))
  exact hcomp

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem stronglyMeasurable_forwardPredictorProcess_of_prefix
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X : Nat -> Alpha -> Real) {k : Nat}
    (hX : forall i, i < k -> StronglyMeasurable (X i)) :
    StronglyMeasurable (forwardPredictorProcess X k) := by
  unfold forwardPredictorProcess forwardPredictor
  split_ifs
  · exact stronglyMeasurable_const
  · unfold forwardPrefixMean
    have hsum : StronglyMeasurable (∑ i ∈ Finset.range k, X i) :=
      Finset.stronglyMeasurable_sum (Finset.range k) fun i hi =>
        hX i (Finset.mem_range.mp hi)
    simpa only [Finset.sum_apply, div_eq_mul_inv] using
      hsum.mul_const ((k : Real)⁻¹)

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem stronglyMeasurable_forwardPredictableQuadratic_of_prefix
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X : Nat -> Alpha -> Real) {n : Nat}
    (hX : forall k, k < n -> StronglyMeasurable (X k)) :
    StronglyMeasurable
      (fun a => forwardPredictableQuadratic (fun k => X k a) n) := by
  unfold forwardPredictableQuadratic
  have hsum : StronglyMeasurable
      (∑ k ∈ Finset.range n, fun a =>
        (X k a - forwardPredictor (fun i => X i a) k) ^ 2) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
      ((hX k (Finset.mem_range.mp hk)).sub
        (by
          change StronglyMeasurable (forwardPredictorProcess X k)
          exact stronglyMeasurable_forwardPredictorProcess_of_prefix X
            (fun i hi =>
              hX i (hi.trans (Finset.mem_range.mp hk))))).pow 2
  convert hsum using 1
  funext a
  simp only [Finset.sum_apply]

omit [MeasurableSpace Theta] [Fintype Tau] [DecidableEq Tau]
  [Nonempty Tau] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z] in
private theorem stronglyMeasurable_forwardPredictableMeanLowerProcess_of_prefix
    {Alpha : Type*} [MeasurableSpace Alpha]
    (X mean : Nat -> Alpha -> Real) (lam : Real) {n : Nat}
    (hX : forall k, k < n -> StronglyMeasurable (X k))
    (hmean : forall k, k < n -> StronglyMeasurable (mean k)) :
    StronglyMeasurable
      (forwardPredictableMeanEmpiricalBernsteinLowerProcess
        X mean lam n) := by
  have hsum : StronglyMeasurable
      (∑ k ∈ Finset.range n, fun a => mean k a - X k a) :=
    Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
      (hmean k (Finset.mem_range.mp hk)).sub
        (hX k (Finset.mem_range.mp hk))
  have hquad := stronglyMeasurable_forwardPredictableQuadratic_of_prefix X hX
  have hexponent :=
    (hsum.const_mul lam).sub
      (hquad.const_mul (forwardEmpiricalBernsteinPsi lam))
  have hexp := Real.continuous_exp.comp_stronglyMeasurable hexponent
  convert hexp using 1
  funext a
  rw [forwardPredictableMeanEmpiricalBernsteinLowerProcess_eq]
  simp only [Finset.sum_apply]
  rfl

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- The actual lower-tail trajectory e-process is jointly measurable for the
time-`n` path filtration and an arbitrary measurable hypothesis space.  This
is derived solely from coordinatewise score measurability and finite state. -/
theorem stronglyMeasurable_continuousTrajectoryLowerProcess_filtered
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (lam : Real) (n : Nat) :
    StronglyMeasurable[MeasurableSpace.prod
      ((Filtration.piLE (X := fun _ : Nat => Z)) n)
      (inferInstance : MeasurableSpace Theta)]
      (fun q : (Nat -> Z) × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2)) lam n q.1) := by
  let X : Nat -> ((Nat -> Z) × Theta) -> Real := fun k q =>
    observedTrajectoryScore (score q.2) k q.1
  let mean : Nat -> ((Nat -> Z) × Theta) -> Real := fun k q =>
    conditionalTrajectoryRisk K (score q.2) k q.1
  let mPathTheta := MeasurableSpace.prod
    ((Filtration.piLE (X := fun _ : Nat => Z)) n)
    (inferInstance : MeasurableSpace Theta)
  letI : MeasurableSpace ((Nat -> Z) × Theta) := mPathTheta
  have hX : forall k, k < n -> StronglyMeasurable (X k) := by
    intro k hk
    dsimp [X]
    exact stronglyMeasurable_observedTrajectoryScore_parameter_prod
      score hscore_parameter (by omega)
  have hmean : forall k, k < n -> StronglyMeasurable (mean k) := by
    intro k hk
    dsimp [mean]
    exact stronglyMeasurable_conditionalTrajectoryRisk_parameter_prod
      K score hscore_parameter (by omega)
  have hprocess :=
    stronglyMeasurable_forwardPredictableMeanLowerProcess_of_prefix
      X mean lam hX hmean
  change StronglyMeasurable
    (forwardPredictableMeanEmpiricalBernsteinLowerProcess X mean lam n)
  exact hprocess

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau] in
/-- Filtered joint measurability of the trajectory e-process implies its
ambient path-parameter measurability. -/
theorem stronglyMeasurable_continuousTrajectoryLowerProcess_ambient
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
    (lam : Real) (n : Nat) :
    StronglyMeasurable
      (fun q : (Nat -> Z) × Theta =>
        forwardPredictableMeanEmpiricalBernsteinLowerProcess
          (observedTrajectoryScore (score q.2))
          (conditionalTrajectoryRisk K (score q.2)) lam n q.1) := by
  have hfiltered :=
    stronglyMeasurable_continuousTrajectoryLowerProcess_filtered
      K score hscore_parameter lam n
  exact (hfiltered.measurable.mono
    (measurableSpace_prod_piLE_le_ambient
      (Theta := Theta) (Z := Z) n) le_rfl).stronglyMeasurable

/-- Posterior-integrated average conditional risk along the encountered
trajectory prefixes. -/
def continuousTrajectoryPosteriorAverageConditionalRisk
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta, trajectoryAverageConditionalRisk K (score theta) n x ∂posterior

/-- Posterior-integrated observed prequential trajectory risk. -/
def continuousTrajectoryPosteriorEmpiricalPrequentialRisk
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta, trajectoryEmpiricalPrequentialRisk (score theta) n x ∂posterior

/-- Posterior integral of the observed per-hypothesis hybrid-Bessel penalty. -/
def continuousTrajectoryPosteriorHybridBesselPenalty
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) : Real :=
  ∫ theta, forwardHybridBesselPenalty
    (fun k => observedTrajectoryScore (score theta) k x) n ∂posterior

/-- Exact continuous-posterior trajectory empirical-Bernstein boundary at one
declared tilt. -/
def continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
    (prior : Measure Theta) (weight : Tau -> Real) (lam : Tau -> Real)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (delta : Real) (j : Tau) (n : Nat) (x : Nat -> Z) : Real :=
  ((InformationTheory.klDiv posterior prior).toReal +
      Real.log (1 / (delta * weight j)) +
      forwardEmpiricalBernsteinPsi (lam j) *
        continuousTrajectoryPosteriorHybridBesselPenalty
          score posterior n x) /
    ((n : Real) * lam j)

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The trajectory boundary is definitionally the generic continuous
predictable-mean boundary specialized to observed trajectory scores. -/
theorem continuousTrajectoryEmpiricalBernsteinPACBayesBoundary_eq_generic
    (prior : Measure Theta) (weight : Tau -> Real) (lam : Tau -> Real)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (delta : Real) (j : Tau) (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
        prior weight lam score posterior delta j n x =
      continuousForwardPredictableMeanBesselBoundary
        prior weight lam
        (fun theta => observedTrajectoryScore (score theta))
        posterior delta j n x := by
  rfl

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSingletonClass Z] in
/-- The posterior-integrated trajectory risk is the posterior integral of the
generic predictable prefix mean. -/
theorem continuousTrajectoryPosteriorAverageConditionalRisk_eq_generic
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorAverageConditionalRisk
        K score posterior n x =
      ∫ theta, forwardPrefixMean
        (fun k => conditionalTrajectoryRisk K (score theta) k x) n
        ∂posterior := by
  rfl

omit [Fintype Tau] [DecidableEq Tau] [Nonempty Tau]
  [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The posterior-integrated empirical trajectory risk is the posterior
integral of the generic observed prefix mean. -/
theorem continuousTrajectoryPosteriorEmpiricalPrequentialRisk_eq_generic
    (score : Theta -> TrajectoryScore Z) (posterior : Measure Theta)
    (n : Nat) (x : Nat -> Z) :
    continuousTrajectoryPosteriorEmpiricalPrequentialRisk
        score posterior n x =
      ∫ theta, forwardPrefixMean
        (fun k => observedTrajectoryScore (score theta) k x) n
        ∂posterior := by
  rfl

omit [Nonempty Tau] in
/-- One outer-mass event controls continuous-posterior trajectory
empirical-Bernstein PAC-Bayes at every `n >= 2` and every declared finite
tilt.  The posterior may be selected after observing the path because the
event is already uniform over every eligible posterior measure. -/
theorem exists_continuousTrajectoryEmpiricalBernsteinPACBayes_event
    (K : (n : Nat) -> Kernel ((i : Finset.Iic n) -> Z) Z)
    [forall n, IsMarkovKernel (K n)] (x0 : Z)
    (score : Theta -> TrajectoryScore Z)
    (hscore_unit : forall theta n u y,
      score theta n u y ∈ Set.Icc (0 : Real) 1)
    (hscore_parameter : forall n u y,
      StronglyMeasurable (fun theta => score theta n u y))
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
  rcases exists_continuousForwardPredictableMeanBesselPACBayes_event
      (mu := trajectoryMeasure K x0)
      (F := Filtration.piLE (X := fun _ : Nat => Z))
      prior hweight_pos hweight_sum hdelta hlam hlam_one
      (fun theta => observedTrajectoryScore_incrementAdapted (score theta))
      (fun theta => conditionalTrajectoryRisk_stronglyAdapted K (score theta))
      (fun theta k x => observedTrajectoryScore_mem_Icc
        (hscore_unit theta) k x)
      (fun theta k x => conditionalTrajectoryRisk_mem_Icc
        K (hscore_unit theta) k x)
      (fun theta k => observedTrajectoryScore_condExp
        K x0 (score theta) (hscore_unit theta) k)
      (fun k x => hscore_parameter k
        (Preorder.frestrictLe k x) (x (k + 1)))
      (fun k x => stronglyMeasurable_conditionalTrajectoryRisk_parameter
        K score hscore_parameter k x)
      (fun j n =>
        stronglyMeasurable_continuousTrajectoryLowerProcess_ambient
          K score hscore_parameter (lam j) n)
      (fun j n =>
        stronglyMeasurable_continuousTrajectoryLowerProcess_filtered
          K score hscore_parameter (lam j) n) with
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
