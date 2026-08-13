import FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

/-!
# Concrete finite joint mean/variance PAC-Bayes catalog checker

A fair Boolean law, two complementary indicator loss functions with equal
population risk `1/2` and population variance `1/4`, a fair
full-support prior, and a skewed posterior instantiate the one-event joint
catalog at `n = 2`.  The two catalog entries carry unequal positive weights
`1/2` and `1/4` with total `3/4`, active tilts `t, eta ∈ {1/2, 1/4}`, and
strictly positive variance coefficients `kappa = 1/2` and `kappa = 3/8`.
The receipt recomputes every reported number, exhibits a nonconstant sample
score, shows the single bad set has mass at most `1/2` so a good sample
exists, and instantiates the selector endpoints with a selector whose two
values are both attained on concrete samples.
-/

namespace FormalSLT.Examples.CheckFiniteJointMeanVariancePACBayes

open Finset BigOperators Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes

noncomputable section

/-- Fair law on a two-point data domain. -/
def dataLaw : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    norm_num [dataLaw]
  · norm_num [dataLaw]

/-- Complementary indicator losses: hypothesis `h` pays loss one exactly when
the observation equals `h`. -/
def matchLoss (h z : Bool) : ℝ := if z = h then 1 else 0

theorem matchLoss_mem_Icc (h z : Bool) :
    matchLoss h z ∈ Set.Icc (0 : ℝ) 1 := by
  cases h <;> cases z <;> norm_num [matchLoss]

/-- Fair full-support prior over the two hypotheses. -/
def fairPrior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem fairPrior_isFullSupportPMF : IsFullSupportPMF fairPrior := by
  constructor
  · constructor
    · intro h
      norm_num [fairPrior]
    · norm_num [fairPrior]
  · intro h
    norm_num [fairPrior]

/-- Skewed posterior, distinct from the prior, so the KL term is active. -/
def skewedPosterior : Bool → ℝ := fun h => if h then 3 / 4 else 1 / 4

theorem skewedPosterior_isPMF : IsPMF skewedPosterior := by
  constructor
  · intro h
    cases h <;> norm_num [skewedPosterior]
  · norm_num [skewedPosterior, Fintype.sum_bool]

/-! ### The two-entry joint catalog -/

/-- Mean tilts `1/2` and `1/4`. -/
def catT : Bool → ℝ := fun c => if c then 1 / 2 else 1 / 4

/-- Variance tilts `1/2` and `1/4`. -/
def catEta : Bool → ℝ := fun c => if c then 1 / 2 else 1 / 4

/-- Unequal positive weights `1/2` and `1/4`. -/
def catW : Bool → ℝ := fun c => if c then 1 / 2 else 1 / 4

theorem catT_nonneg : ∀ c, 0 ≤ catT c := by
  intro c
  cases c <;> norm_num [catT]

theorem catT_pos : ∀ c, 0 < catT c := by
  intro c
  cases c <;> norm_num [catT]

theorem catEta_nonneg : ∀ c, 0 ≤ catEta c := by
  intro c
  cases c <;> norm_num [catEta]

theorem catEta_pos : ∀ c, 0 < catEta c := by
  intro c
  cases c <;> norm_num [catEta]

theorem catW_pos : ∀ c, 0 < catW c := by
  intro c
  cases c <;> norm_num [catW]

theorem catW_nonneg : ∀ c, 0 ≤ catW c := fun c => (catW_pos c).le

/-- The two weights are genuinely unequal. -/
theorem catW_unequal : catW true ≠ catW false := by
  norm_num [catW]

theorem catW_sum_eq : (∑ c : Bool, catW c) = 3 / 4 := by
  norm_num [catW, Fintype.sum_bool]

theorem catW_sum_le_one : (∑ c : Bool, catW c) ≤ 1 := by
  rw [catW_sum_eq]
  norm_num

/-- Recomputed variance coefficient at the strong entry:
`kappa = (1/2)*2 - (1/2)^2*2^2/(2*(2-1)) = 1 - 1/2 = 1/2`. -/
theorem kappa_true_eq :
    finiteJointMeanVarianceKappa 2 (catEta true) = 1 / 2 := by
  norm_num [catEta, finiteJointMeanVarianceKappa]

/-- Recomputed variance coefficient at the weak entry:
`kappa = (1/4)*2 - (1/4)^2*2^2/(2*(2-1)) = 1/2 - 1/8 = 3/8`. -/
theorem kappa_false_eq :
    finiteJointMeanVarianceKappa 2 (catEta false) = 3 / 8 := by
  norm_num [catEta, finiteJointMeanVarianceKappa]

theorem kappa_pos : ∀ c, 0 < finiteJointMeanVarianceKappa 2 (catEta c) := by
  intro c
  cases c
  · rw [kappa_false_eq]
    norm_num
  · rw [kappa_true_eq]
    norm_num

theorem kappa_nonneg : ∀ c, 0 ≤ finiteJointMeanVarianceKappa 2 (catEta c) :=
  fun c => (kappa_pos c).le

/-! ### Recomputed population quantities -/

theorem matchLoss_populationRisk (h : Bool) :
    finitePopulationRisk dataLaw matchLoss h = 1 / 2 := by
  cases h <;>
    norm_num [finitePopulationRisk, dataLaw, matchLoss, Fintype.sum_bool]

theorem matchLoss_populationVariance (h : Bool) :
    finitePopulationVariance dataLaw matchLoss h = 1 / 4 := by
  cases h <;>
    norm_num [finitePopulationVariance, finitePopulationRisk, dataLaw,
      matchLoss, Fintype.sum_bool]

/-! ### Nonconstant sample score -/

/-- The constant sample avoiding hypothesis `true`. -/
def allFalseSample : Fin 2 → Bool := fun _ => false

/-- The mixed sample with one hit and one miss. -/
def mixedSample : Fin 2 → Bool := fun k => if k = 0 then false else true

theorem allFalse_empiricalRisk :
    finiteEmpiricalRisk matchLoss true allFalseSample = 0 := by
  norm_num [finiteEmpiricalRisk, matchLoss, allFalseSample, Fin.sum_univ_two]

theorem mixed_empiricalRisk :
    finiteEmpiricalRisk matchLoss true mixedSample = 1 / 2 := by
  norm_num [finiteEmpiricalRisk, matchLoss, mixedSample, Fin.sum_univ_two]

theorem allFalse_empiricalVariance :
    finiteEmpiricalVariance matchLoss true allFalseSample = 0 := by
  norm_num [finiteEmpiricalVariance,
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, matchLoss, allFalseSample,
    Fin.sum_univ_two]

theorem mixed_empiricalVariance :
    finiteEmpiricalVariance matchLoss true mixedSample = 1 / 2 := by
  norm_num [finiteEmpiricalVariance,
    FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
    FormalSLT.Statistics.sampleMean, matchLoss, mixedSample,
    Fin.sum_univ_two]

/-- The strong-entry score separates the constant sample from the mixed
sample by exactly `t + eta = 1`; the sample-independent Bennett and
transported-variance terms cancel in the difference. -/
theorem score_gap_eq_one :
    finiteJointMeanVarianceScore 2 dataLaw matchLoss (catT true) (catEta true)
        true allFalseSample -
      finiteJointMeanVarianceScore 2 dataLaw matchLoss (catT true) (catEta true)
        true mixedSample = 1 := by
  unfold finiteJointMeanVarianceScore
  rw [allFalse_empiricalRisk, mixed_empiricalRisk,
    allFalse_empiricalVariance, mixed_empiricalVariance]
  norm_num [catT, catEta]
  ring

/-- The per-hypothesis sample score is not constant in the sample. -/
theorem score_nonconstant :
    finiteJointMeanVarianceScore 2 dataLaw matchLoss (catT true) (catEta true)
        true allFalseSample ≠
      finiteJointMeanVarianceScore 2 dataLaw matchLoss (catT true) (catEta true)
        true mixedSample := by
  intro heq
  have hgap := score_gap_eq_one
  rw [heq, sub_self] at hgap
  norm_num at hgap

/-! ### One bad event of mass at most delta -/

/-- The single catalog bad-sample set at confidence budget `delta = 1/2`. -/
def jointBadSamples : Finset (Fin 2 → Bool) :=
  finiteJointMeanVarianceCatalogBadSamples
    2 dataLaw fairPrior matchLoss catT catEta catW (1 / 2)

theorem jointBadSamples_mass_le_half :
    (∑ S ∈ jointBadSamples, finiteProductSampleWeight dataLaw S) ≤
      (1 : ℝ) / 2 := by
  have hmass :=
    finiteJointMeanVariance_catalogBadSamples_mass_le_delta
      (n := 2) (t := catT) (eta := catEta) (w := catW) (delta := 1 / 2)
      (by norm_num) dataLaw dataLaw_isPMF
      fairPrior_isFullSupportPMF.toIsPMF matchLoss matchLoss_mem_Icc
      catT_nonneg catEta_nonneg kappa_nonneg catW_nonneg catW_sum_le_one
      (by norm_num)
  simpa [jointBadSamples] using hmass

/-- The bad event does not exhaust the sample space, so a good sample
exists. -/
theorem goodSample_exists : ∃ S : Fin 2 → Bool, S ∉ jointBadSamples := by
  by_contra hgood
  push Not at hgood
  have hbad : jointBadSamples = Finset.univ := by
    ext S
    simp [hgood S]
  have htotal :
      (∑ S : Fin 2 → Bool, finiteProductSampleWeight dataLaw S) = 1 :=
    (finiteProductSampleWeight_isPMF (n := 2) dataLaw_isPMF).sum_one
  have hmass := jointBadSamples_mass_le_half
  rw [hbad, htotal] at hmass
  norm_num at hmass

/-! ### A selector that genuinely exercises distinct entries -/

/-- The selector inspects the sample: constant samples pick the strong entry,
mixed samples pick the weak entry. -/
def sampleSelector (S : Fin 2 → Bool) (_rho : Bool → ℝ) : Bool :=
  S 0 == S 1

theorem sampleSelector_allFalse :
    sampleSelector allFalseSample skewedPosterior = true := by
  norm_num [sampleSelector, allFalseSample]

theorem sampleSelector_mixed :
    sampleSelector mixedSample skewedPosterior = false := by
  norm_num [sampleSelector, mixedSample]

/-- The two selector values are attained on concrete samples, so the selector
genuinely uses distinct catalog entries. -/
theorem sampleSelector_exercises_both :
    sampleSelector allFalseSample skewedPosterior ≠
      sampleSelector mixedSample skewedPosterior := by
  rw [sampleSelector_allFalse, sampleSelector_mixed]
  simp

/-! ### Selector endpoints on the good event

The skewed posterior exercises the empirical terms; the per-hypothesis
population risks and variances coincide in this receipt. -/

/-- The selected raw retained-variance certificate at the skewed posterior. -/
def selectedJointCertificate (S : Fin 2 → Bool) : Prop :=
  catT (sampleSelector S skewedPosterior) * (2 : ℝ) *
      (posteriorAverage skewedPosterior (finitePopulationRisk dataLaw matchLoss) -
        posteriorAverage skewedPosterior
          (fun i => finiteEmpiricalRisk matchLoss i S)) ≤
    klDiv skewedPosterior fairPrior +
      Real.log (1 / ((1 / 2) * catW (sampleSelector S skewedPosterior))) +
      catEta (sampleSelector S skewedPosterior) * (2 : ℝ) *
        posteriorAverage skewedPosterior
          (fun i => finiteEmpiricalVariance matchLoss i S) +
      (2 : ℝ) *
        Real.log
          (1 + (Real.exp (catT (sampleSelector S skewedPosterior)) - 1 -
              catT (sampleSelector S skewedPosterior)) *
            posteriorAverage skewedPosterior
              (finitePopulationVariance dataLaw matchLoss)) -
      Real.exp (-catT (sampleSelector S skewedPosterior)) *
        finiteJointMeanVarianceKappa 2 (catEta (sampleSelector S skewedPosterior)) *
        posteriorAverage skewedPosterior
          (finitePopulationVariance dataLaw matchLoss)

/-- On the good event the selected certificate holds with one shared
confidence event and one KL term. -/
theorem jointCatalog_selected_witness :
    ∃ S : Fin 2 → Bool, S ∉ jointBadSamples ∧ selectedJointCertificate S := by
  rcases goodSample_exists with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  exact finiteJointMeanVariance_posteriorGap_le_selected_of_not_mem
    2 dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF matchLoss catW_pos
    sampleSelector S (by simpa [jointBadSamples] using hS)
    skewedPosterior_isPMF

/-- The selected division-form certificate at the skewed posterior. -/
def selectedJointDivCertificate (S : Fin 2 → Bool) : Prop :=
  posteriorAverage skewedPosterior (finitePopulationRisk dataLaw matchLoss) -
      posteriorAverage skewedPosterior
        (fun i => finiteEmpiricalRisk matchLoss i S) ≤
    (klDiv skewedPosterior fairPrior +
        Real.log (1 / ((1 / 2) * catW (sampleSelector S skewedPosterior))) +
        catEta (sampleSelector S skewedPosterior) * (2 : ℝ) *
          posteriorAverage skewedPosterior
            (fun i => finiteEmpiricalVariance matchLoss i S) +
        (2 : ℝ) *
          Real.log
            (1 + (Real.exp (catT (sampleSelector S skewedPosterior)) - 1 -
                catT (sampleSelector S skewedPosterior)) *
              posteriorAverage skewedPosterior
                (finitePopulationVariance dataLaw matchLoss)) -
        Real.exp (-catT (sampleSelector S skewedPosterior)) *
          finiteJointMeanVarianceKappa 2
            (catEta (sampleSelector S skewedPosterior)) *
          posteriorAverage skewedPosterior
            (finitePopulationVariance dataLaw matchLoss)) /
      (catT (sampleSelector S skewedPosterior) * (2 : ℝ))

/-- The division form also holds on the good event because every catalog mean
tilt is strictly positive. -/
theorem jointCatalog_selected_div_witness :
    ∃ S : Fin 2 → Bool, S ∉ jointBadSamples ∧ selectedJointDivCertificate S := by
  rcases goodSample_exists with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  exact finiteJointMeanVariance_posteriorGap_div_le_selected_of_not_mem
    (by norm_num) dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF matchLoss
    catW_pos catT_pos sampleSelector S (by simpa [jointBadSamples] using hS)
    skewedPosterior_isPMF

#check finiteJointMeanVarianceScore
#check finiteJointMeanVarianceScore_expectation_le_one
#check finiteJointMeanVariancePriorMoment
#check finiteJointMeanVariancePriorMoment_nonneg
#check finiteJointMeanVariancePriorMoment_pos
#check finiteJointMeanVariance_priorMoment_expectation_le_one
#check finiteJointMeanVarianceMasterMixture
#check finiteJointMeanVarianceMasterMixture_nonneg
#check finiteJointMeanVariance_masterMixture_expectation_le_weightSum
#check finiteJointMeanVariance_masterMixture_expectation_le_one
#check finiteJointMeanVarianceCatalogBadSamples
#check finiteJointMeanVariance_not_mem_catalogBadSamples_iff
#check finiteJointMeanVariance_catalogBadSamples_mass_le_delta
#check finiteJointMeanVariance_priorMoment_le_of_not_mem
#check finiteJointMeanVariance_posteriorScore_le_of_not_mem
#check finiteJointMeanVariance_posteriorGap_le_of_not_mem
#check finiteJointMeanVariance_posteriorGap_div_le_of_not_mem
#check finiteJointMeanVariance_posteriorGap_le_selected_of_not_mem
#check finiteJointMeanVariance_posteriorGap_div_le_selected_of_not_mem
#check catW_sum_eq
#check kappa_true_eq
#check kappa_false_eq
#check matchLoss_populationRisk
#check matchLoss_populationVariance
#check score_gap_eq_one
#check sampleSelector_allFalse
#check sampleSelector_mixed

#print axioms finiteJointMeanVarianceScore_expectation_le_one
#print axioms finiteJointMeanVariancePriorMoment_nonneg
#print axioms finiteJointMeanVariancePriorMoment_pos
#print axioms finiteJointMeanVariance_priorMoment_expectation_le_one
#print axioms finiteJointMeanVarianceMasterMixture_nonneg
#print axioms finiteJointMeanVariance_masterMixture_expectation_le_weightSum
#print axioms finiteJointMeanVariance_masterMixture_expectation_le_one
#print axioms finiteJointMeanVariance_not_mem_catalogBadSamples_iff
#print axioms finiteJointMeanVariance_catalogBadSamples_mass_le_delta
#print axioms finiteJointMeanVariance_priorMoment_le_of_not_mem
#print axioms finiteJointMeanVariance_posteriorScore_le_of_not_mem
#print axioms finiteJointMeanVariance_posteriorGap_le_of_not_mem
#print axioms finiteJointMeanVariance_posteriorGap_div_le_of_not_mem
#print axioms finiteJointMeanVariance_posteriorGap_le_selected_of_not_mem
#print axioms finiteJointMeanVariance_posteriorGap_div_le_selected_of_not_mem
#print axioms catW_sum_eq
#print axioms kappa_true_eq
#print axioms kappa_false_eq
#print axioms matchLoss_populationRisk
#print axioms matchLoss_populationVariance
#print axioms score_gap_eq_one
#print axioms sampleSelector_allFalse
#print axioms sampleSelector_mixed
#print axioms score_nonconstant
#print axioms jointBadSamples_mass_le_half
#print axioms goodSample_exists
#print axioms sampleSelector_exercises_both
#print axioms jointCatalog_selected_witness
#print axioms jointCatalog_selected_div_witness

end

end FormalSLT.Examples.CheckFiniteJointMeanVariancePACBayes
