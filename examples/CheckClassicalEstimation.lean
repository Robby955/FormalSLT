import FormalSLT.Statistics.ClassicalEstimation

open FormalSLT.Statistics
open FormalSLT.Statistics.ClassicalEstimation
open scoped BigOperators

#check sampleMean_const
#check sampleMean_add
#check sampleMean_sub
#check sampleMean_smul
#check sampleMean_add_const
#check sampleMean_eq_finiteMean_uniform
#check sampleMean_unbiased_finite
#check sampleMean_unbiased_identically_distributed_finite
#check sampleVarianceBessel
#check sampleVarianceBessel_two
#check sampleVarianceBessel_eq_centered_secondMoment_sub_meanSq
#check sampleVarianceBessel_unbiased_finite
#check bernoulliLogLikelihoodFromCount
#check bernoulliScoreAtSampleMean_eq_zero
#check bernoulliScore_mle_from_count
#check bernoulliLogLikelihood_global_argmax_from_count
#check gaussianKnownVarianceLogLikelihood
#check gaussianScoreAtSampleMean_eq_zero
#check gaussianKnownVarianceLogLikelihood_mle
#check horvitzThompsonEstimator
#check finitePopulationTotal_add
#check finitePopulationTotal_smul
#check horvitzThompsonEstimator_eq_total_of_inclusion_eq_pi
#check horvitzThompson_design_unbiased
#check bootstrapMean
#check bootstrapMean_eq_sampleMean
#check bootstrapMean_const

/-- Concrete Bernoulli MLE witness: one success in two trials has MLE `1/2`. -/
example :
    bernoulliScoreFromCount 2 1 ((1 : ℝ) / 2) = 0 := by
  norm_num [bernoulliScoreFromCount]

/-- Concrete Bernoulli global-MLE witness: for one success in two trials,
the log-likelihood is maximized at `1/2` over the open unit interval. -/
example {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    bernoulliLogLikelihoodFromCount 2 1 θ
      ≤ bernoulliLogLikelihoodFromCount 2 1 ((1 : ℝ) / 2) := by
  have h := bernoulliLogLikelihood_global_argmax_from_count
    (n := 2) (k := 1) (by norm_num) (by norm_num) hθ0 hθ1
  norm_num at h ⊢
  exact h

/-- Concrete Bessel-unbiasedness witness for two centered Rademacher draws. -/
example :
    weightedExpectation (fun _ : Bool × Bool => (1 : ℝ) / 4)
        (fun ω => sampleVarianceBessel
          (fun i : Fin 2 => if i = 0 then (if ω.1 then 1 else -1)
            else (if ω.2 then 1 else -1)))
      = 1 := by
  exact sampleVarianceBessel_unbiased_finite
    (n := 2) (w := fun _ : Bool × Bool => (1 : ℝ) / 4)
    (X := fun i ω => if i = 0 then (if ω.1 then 1 else -1)
      else (if ω.2 then 1 else -1))
    (μ := 0) (sigma2 := 1)
    (by norm_num)
    (by
      intro i
      fin_cases i <;> norm_num [weightedExpectation])
    (by
      unfold weightedExpectation sampleMean
      rw [Fintype.sum_prod_type]
      norm_num)

/-- Concrete Gaussian known-variance witness: the score vanishes at the sample mean. -/
example :
    gaussianKnownVarianceScore ![1, 3] 2 (sampleMean ![1, 3]) = 0 := by
  norm_num [gaussianKnownVarianceScore, sampleMean]

/-- Concrete Horvitz-Thompson witness under deterministic unit inclusion. -/
example :
    horvitzThompsonEstimator
        (fun i : Fin 2 => (i.1 : ℝ) + 1)
        (fun _ : Fin 2 => 1)
        (fun _ : Fin 2 => 1)
      = finitePopulationTotal (fun i : Fin 2 => (i.1 : ℝ) + 1) := by
  norm_num [horvitzThompsonEstimator, finitePopulationTotal]

/-- Concrete bootstrap witness: the mean of the empirical resampling distribution
equals the observed sample mean. -/
example :
    bootstrapMean ![2, 4, 6] = sampleMean ![2, 4, 6] := by
  simpa using bootstrapMean_eq_sampleMean ![2, 4, 6]

#print axioms sampleMean_unbiased_finite
#print axioms bernoulliScore_mle_from_count
#print axioms bernoulliLogLikelihood_global_argmax_from_count
#print axioms sampleVarianceBessel_unbiased_finite
#print axioms gaussianKnownVarianceLogLikelihood_mle
#print axioms horvitzThompson_design_unbiased
#print axioms bootstrapMean_eq_sampleMean
