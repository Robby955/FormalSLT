import FormalSLT.PACBayesSeeger

open FormalSLT.PACBayesSeeger

#check BernoulliKLMomentTypeCountingBound
#print axioms bernoulliSuccessCount_fiber_card
#print axioms bernoulliSuccessCount_le
#print axioms sum_boolSamples_by_bernoulliSuccessCount
#print axioms bernoulliEmpiricalMean_eq_successCount_div
#print axioms finiteProductSampleWeight_bernoulliSuccessMass_eq
#print axioms bernoulliKLMomentTypeMass_nonneg_of_le
#print axioms bernoulliKLMomentTypeMass_cancel_interior
#print axioms bernoulliKLMomentSampleTerm_eq_typeMass_of_q_interior
#print axioms bernoulliKLMoment_typeReduction_of_sampleTerm_le_typeMass
#print axioms bernoulliKLMomentTypeReduction_of_q_interior
#print axioms bernoulliKLMomentTypeReduction_of_q_mem_Icc
#print axioms BernoulliKLMomentTypeCountingBound_of_64_le
#print axioms BernoulliKLMomentTypeCountingBound_of_pos
#print axioms bernoulliKLMoment_le_two_sqrt_of_typeCountingBound
#print axioms bernoulliKLMoment_le_two_sqrt_of_q_interior_and_typeCountingBound
#print axioms bernoulliKLMoment_le_two_sqrt_of_q_mem_Icc_and_typeCountingBound
#print axioms bernoulliKLMoment_le_two_sqrt_of_q_interior
#print axioms bernoulliKLMoment_le_two_sqrt_of_q_mem_Icc
#print axioms expectedPriorSeegerKLMoment_bernoulli_le_two_sqrt
#print axioms pacbayes_seeger_klForm_of_bernoulliPriorMoment_and_binaryKLJensen

example : bernoulliSuccessCount (fun _ : Fin 2 => true) = 2 := by
  norm_num [bernoulliSuccessCount, bernoulliSuccessSet]

example : Fintype.card {S : Fin 2 → Bool // bernoulliSuccessCount S = 1} = 2 := by
  simpa using (bernoulliSuccessCount_fiber_card (n := 2) (k := 1))

example :
    (∑ S : Fin 2 → Bool, (bernoulliSuccessCount S : ℝ)) = 4 := by
  rw [sum_boolSamples_by_bernoulliSuccessCount (n := 2) (fun k => (k : ℝ))]
  norm_num [Finset.sum_range_succ]

example : bernoulliSuccessMass (1 / 2) true = 1 / 2 := by
  norm_num [bernoulliSuccessMass]

example : bernoulliEmpiricalMean (fun _ : Fin 2 => true) = 1 := by
  norm_num [bernoulliEmpiricalMean]

example : BernoulliKLMomentTypeCountingBound 1 := by
  exact BernoulliKLMomentTypeCountingBound_of_pos (by norm_num)

example :
    bernoulliKLMoment (n := 2) (1 / 2) ≤ 2 * Real.sqrt (2 : ℝ) := by
  exact bernoulliKLMoment_le_two_sqrt_of_q_mem_Icc
    (n := 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
