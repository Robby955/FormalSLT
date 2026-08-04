import FormalSLT.Concentration.HeterogeneousMcDiarmid
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory
open scoped BigOperators ENNReal NNReal

#check FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_hetero
#check FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_hetero_lower
#check FormalSLT.Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp_hetero
#check FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_of_hetero

#print axioms FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_hetero
#print axioms FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_hetero_lower
#print axioms FormalSLT.Concentration.mcdiarmid_twoSided_of_hasBoundedDifferences_sharp_hetero
#print axioms FormalSLT.Concentration.mcdiarmid_of_hasBoundedDifferences_sharp_of_hetero

noncomputable def boolLawOneThird : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false
    ⟨(1 : ℝ) / 3, by norm_num, by norm_num⟩

noncomputable def boolLawOneHalf : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false
    ⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩

noncomputable def heteroBoolLaw : Fin 2 → Measure Bool :=
  fun k => if (k : ℕ) = 0 then boolLawOneThird else boolLawOneHalf

example : ∀ k : Fin 2, IsProbabilityMeasure (heteroBoolLaw k) := by
  intro k
  fin_cases k
  · dsimp [heteroBoolLaw, boolLawOneThird]
    infer_instance
  · dsimp [heteroBoolLaw, boolLawOneHalf]
    infer_instance

example : heteroBoolLaw 0 Set.univ = 1 := by
  haveI : IsProbabilityMeasure (heteroBoolLaw 0) := by
    dsimp [heteroBoolLaw, boolLawOneThird]
    infer_instance
  rw [measure_univ]

example : heteroBoolLaw 1 Set.univ = 1 := by
  haveI : IsProbabilityMeasure (heteroBoolLaw 1) := by
    dsimp [heteroBoolLaw, boolLawOneHalf]
    infer_instance
  rw [measure_univ]

example : boolLawOneThird ≠ boolLawOneHalf := by
  intro h
  have htrue := congrArg (fun m : Measure Bool => m.real ({true} : Set Bool)) h
  norm_num [boolLawOneThird, boolLawOneHalf,
    ProbabilityTheory.bernoulliMeasure_real_apply] at htrue

example :
    Real.exp (-2 * ((1 / 2 : ℝ) ^ 2) / (((1 : ℝ) ^ 2) + ((1 : ℝ) ^ 2))) < 1 := by
  have hneg :
      -2 * ((1 / 2 : ℝ) ^ 2) / (((1 : ℝ) ^ 2) + ((1 : ℝ) ^ 2)) < 0 := by
    norm_num
  exact Real.exp_lt_one_iff.mpr hneg
