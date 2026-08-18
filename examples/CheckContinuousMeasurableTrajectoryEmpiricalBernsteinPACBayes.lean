import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform

/-!
# Arbitrary-state, continuous-hypothesis trajectory PAC-Bayes checks

This audit fixes both the hypothesis and trajectory state types to `Real`.
The score genuinely depends on both real arguments, so this is not a finite
surrogate hidden behind an unused type parameter.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.StochasticDynamics

noncomputable section

#synth Infinite Real

/-- A genuinely real-parameter, real-state bounded trajectory score. -/
def realParameterizedClippedTrajectoryScore : Real -> TrajectoryScore Real :=
  fun theta _n _u y => max 0 (min 1 (theta + y))

lemma realParameterizedClippedTrajectoryScore_joint :
    JointlyStronglyMeasurableParameterizedTrajectoryScore
      realParameterizedClippedTrajectoryScore := by
  intro n
  change StronglyMeasurable
    (fun q : Real × (((i : Finset.Iic n) -> Real) × Real) =>
      max 0 (min 1 (q.1 + q.2.2)))
  fun_prop

lemma realParameterizedClippedTrajectoryScore_unit
    (theta : Real) (n : Nat) (u : (i : Finset.Iic n) -> Real) (y : Real) :
    realParameterizedClippedTrajectoryScore theta n u y ∈
      Set.Icc (0 : Real) 1 := by
  constructor
  · exact le_max_left 0 (min 1 (theta + y))
  · exact max_le (by norm_num) (min_le_left 1 (theta + y))

/-! A stochastic real-state receipt with nonzero conditional variance. -/

def realRademacherValue (b : Bool) : Real := if b then 1 else -1

def realRademacherPMF : PMF Real :=
  (PMF.uniformOfFintype Bool).map realRademacherValue

def stochasticRealPrefixKernel (n : Nat) :
    Kernel ((i : Finset.Iic n) -> Real) Real :=
  Kernel.const _ realRademacherPMF.toMeasure

instance stochasticRealPrefixKernel.instIsMarkovKernel (n : Nat) :
    IsMarkovKernel (stochasticRealPrefixKernel n) := by
  unfold stochasticRealPrefixKernel
  infer_instance

/-- At parameter zero the clipped score is Bernoulli on the two real atoms,
so its exact conditional variance is positive and equals `1/4`. -/
lemma stochasticRealPrefixKernel_positive_variance
    (u : (i : Finset.Iic 0) -> Real) :
    ∫ y, (realParameterizedClippedTrajectoryScore 0 0 u y - (1 / 2 : Real)) ^ 2
        ∂stochasticRealPrefixKernel 0 u = (1 / 4 : Real) := by
  unfold stochasticRealPrefixKernel realRademacherPMF
  change ∫ y,
      (realParameterizedClippedTrajectoryScore 0 0 u y - (1 / 2 : Real)) ^ 2
        ∂((PMF.uniformOfFintype Bool).map realRademacherValue).toMeasure =
    (1 / 4 : Real)
  rw [← PMF.toMeasure_map (p := PMF.uniformOfFintype Bool)
    (f := realRademacherValue) (by fun_prop)]
  have hintegrand : StronglyMeasurable (fun y : Real =>
      (realParameterizedClippedTrajectoryScore 0 0 u y -
        (1 / 2 : Real)) ^ 2) := by
    unfold realParameterizedClippedTrajectoryScore
    fun_prop
  rw [integral_map (by fun_prop) hintegrand.aestronglyMeasurable]
  rw [PMF.integral_eq_sum]
  norm_num [realParameterizedClippedTrajectoryScore,
    realRademacherValue, PMF.uniformOfFintype_apply]

#check stochasticRealPrefixKernel
#check stochasticRealPrefixKernel_positive_variance

/-- The parameterized kernel-risk integration lemma instantiated with an
infinite hypothesis space and an infinite trajectory state space. -/
example (posterior : Measure Real) [IsProbabilityMeasure posterior]
    (n : Nat) (x : Nat -> Real) :
    Integrable (fun theta => conditionalTrajectoryRisk
      affineRealPrefixKernel (realParameterizedClippedTrajectoryScore theta)
      n x) posterior :=
  integrable_conditionalTrajectoryRisk_parameter_of_joint
    affineRealPrefixKernel
    realParameterizedClippedTrajectoryScore_joint
    realParameterizedClippedTrajectoryScore_unit posterior n x

#check JointlyStronglyMeasurableParameterizedTrajectoryScore
#check jointlyStronglyMeasurableTrajectoryScore_section
#check stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
#check stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint
#check integrable_conditionalTrajectoryRisk_parameter_of_joint
#check observedTrajectoryScore_incrementAdapted_parameterized_of_joint
#check conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
#check observedTrajectoryScore_condExp_parameterized_of_joint
#check stronglyMeasurable_observedTrajectoryScore_joint_filtered
#check stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered
#check stronglyMeasurable_continuousMeasurableTrajectoryLowerProcess_filtered
#check stronglyMeasurable_trajectory_ambient_of_filtered_prod
#check continuousTrajectoryPosteriorAverageConditionalRisk
#check continuousTrajectoryPosteriorEmpiricalPrequentialRisk
#check continuousTrajectoryPosteriorHybridBesselPenalty
#check continuousTrajectoryEmpiricalBernsteinPACBayesBoundary
#check exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event

#check (exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event
  (Theta := Real) (Z := Real) (Tau := Bool))

#print axioms jointlyStronglyMeasurableTrajectoryScore_section
#print axioms stronglyMeasurable_observedTrajectoryScore_parameter_of_joint
#print axioms stronglyMeasurable_conditionalTrajectoryRisk_parameter_of_joint
#print axioms integrable_conditionalTrajectoryRisk_parameter_of_joint
#print axioms observedTrajectoryScore_incrementAdapted_parameterized_of_joint
#print axioms conditionalTrajectoryRisk_stronglyAdapted_parameterized_of_joint
#print axioms observedTrajectoryScore_condExp_parameterized_of_joint
#print axioms stronglyMeasurable_observedTrajectoryScore_joint_filtered
#print axioms stronglyMeasurable_conditionalTrajectoryRisk_joint_filtered
#print axioms stronglyMeasurable_continuousMeasurableTrajectoryLowerProcess_filtered
#print axioms stronglyMeasurable_trajectory_ambient_of_filtered_prod
#print axioms exists_continuousMeasurableTrajectoryEmpiricalBernsteinPACBayes_event
#print axioms realParameterizedClippedTrajectoryScore_joint
#print axioms stochasticRealPrefixKernel_positive_variance

end
