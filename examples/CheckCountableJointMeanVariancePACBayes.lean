import FormalSLT.PACBayes.CountableJointMeanVariancePACBayes
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Concrete countable joint mean/variance mixture receipt

This checker uses a fair Boolean data law and prior, a genuinely infinite
geometric catalog with weights `1 / 2 / 2^c`, distinct mean tilts
`1 / (c + 1)`, and variance tilt `1 / 2`.  The weights are positive and sum
to one.  At `n = 2`, every variance coefficient is `1 / 2`.

The receipt instantiates the one-event mass theorem at `delta = 1 / 2`, proves
that a good sample exists, and on that same sample extracts the prior-moment
bound for every natural-number catalog entry.
-/

namespace FormalSLT.Examples.CheckCountableJointMeanVariancePACBayes

open Finset BigOperators Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteJointMeanVarianceMGF
open FormalSLT.PACBayes.FiniteJointMeanVariancePACBayes
open FormalSLT.PACBayes.CountableJointMeanVariancePACBayes

noncomputable section

/-- Fair law on a two-point data domain. -/
def dataLaw : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    norm_num [dataLaw]
  · norm_num [dataLaw]

/-- Complementary indicator losses. -/
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

/-- Distinct positive mean tilts indexed by the natural numbers. -/
def countableT (c : ℕ) : ℝ := 1 / (c + 1 : ℝ)

/-- Constant admissible variance tilt. -/
def countableEta (_c : ℕ) : ℝ := 1 / 2

/-- Geometric probability weights on the countable catalog. -/
def countableW (c : ℕ) : ℝ := 1 / 2 / 2 ^ c

theorem countableT_pos (c : ℕ) : 0 < countableT c := by
  unfold countableT
  exact one_div_pos.mpr (by positivity)

theorem countableT_nonneg (c : ℕ) : 0 ≤ countableT c :=
  (countableT_pos c).le

theorem countableEta_nonneg (c : ℕ) : 0 ≤ countableEta c := by
  norm_num [countableEta]

theorem countableKappa_eq (c : ℕ) :
    finiteJointMeanVarianceKappa 2 (countableEta c) = 1 / 2 := by
  norm_num [countableEta, finiteJointMeanVarianceKappa]

theorem countableKappa_nonneg (c : ℕ) :
    0 ≤ finiteJointMeanVarianceKappa 2 (countableEta c) := by
  rw [countableKappa_eq]
  norm_num

theorem countableW_pos (c : ℕ) : 0 < countableW c := by
  unfold countableW
  exact div_pos (by norm_num) (pow_pos (by norm_num) c)

theorem countableW_nonneg (c : ℕ) : 0 ≤ countableW c :=
  (countableW_pos c).le

theorem countableW_summable : Summable countableW := by
  unfold countableW
  exact summable_geometric_two' (1 : ℝ)

theorem countableW_tsum_eq_one : (∑' c, countableW c) = 1 := by
  unfold countableW
  exact tsum_geometric_two' (1 : ℝ)

/-- The catalog is not a disguised constant sequence. -/
theorem countable_catalog_distinct :
    countableT 0 ≠ countableT 1 ∧ countableW 0 ≠ countableW 1 := by
  norm_num [countableT, countableW]

/-- The support-aware bad set at confidence budget `delta = 1 / 2`. -/
def countableBadSamples : Finset (Fin 2 → Bool) :=
  countableJointMeanVarianceCatalogBadSamples
    2 dataLaw fairPrior matchLoss countableT countableEta countableW (1 / 2)

theorem countableBadSamples_mass_le_half :
    (∑ S ∈ countableBadSamples, finiteProductSampleWeight dataLaw S) ≤
      (1 : ℝ) / 2 := by
  have hmass :=
    countableJointMeanVariance_catalogBadSamples_mass_le_delta
      (n := 2) (t := countableT) (eta := countableEta) (w := countableW)
      (delta := (1 : ℝ) / 2) (by norm_num)
      dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF.toIsPMF
      matchLoss matchLoss_mem_Icc countableT_nonneg countableEta_nonneg
      countableKappa_nonneg countableW_nonneg countableW_summable
      (by rw [countableW_tsum_eq_one]) (by norm_num)
  simpa [countableBadSamples] using hmass

/-- The bad event does not exhaust the finite sample space. -/
theorem countableGoodSample_exists :
    ∃ S : Fin 2 → Bool, S ∉ countableBadSamples := by
  by_contra hgood
  push Not at hgood
  have hbad : countableBadSamples = Finset.univ := by
    ext S
    simp [hgood S]
  have htotal :
      (∑ S : Fin 2 → Bool, finiteProductSampleWeight dataLaw S) = 1 :=
    (finiteProductSampleWeight_isPMF (n := 2) dataLaw_isPMF).sum_one
  have hmass := countableBadSamples_mass_le_half
  rw [hbad, htotal] at hmass
  norm_num at hmass

/-- Every entry can be extracted on the same good sample. -/
def allCountableEntryMomentsControlled (S : Fin 2 → Bool) : Prop :=
  ∀ c : ℕ,
    finiteJointMeanVariancePriorMoment
        2 dataLaw fairPrior matchLoss (countableT c) (countableEta c) S ≤
      1 / (((1 : ℝ) / 2) * countableW c)

theorem countableGoodSample_all_entries_controlled :
    ∃ S : Fin 2 → Bool,
      S ∉ countableBadSamples ∧ allCountableEntryMomentsControlled S := by
  rcases countableGoodSample_exists with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  intro c
  exact countableJointMeanVariance_priorMoment_le_of_not_mem
    (n := 2) (t := countableT) (eta := countableEta) (w := countableW)
    (delta := (1 : ℝ) / 2) (by norm_num)
    dataLaw dataLaw_isPMF fairPrior_isFullSupportPMF.toIsPMF
    matchLoss matchLoss_mem_Icc countableT_nonneg countableEta_nonneg
    countableKappa_nonneg countableW_pos countableW_summable S
    (by simpa [countableBadSamples] using hS) c

/-- The first two genuinely distinct entries have explicit confidence shares
on the same good sample. -/
theorem countableGoodSample_firstTwoEntries_controlled :
    ∃ S : Fin 2 → Bool,
      S ∉ countableBadSamples ∧
        finiteJointMeanVariancePriorMoment
            2 dataLaw fairPrior matchLoss (countableT 0) (countableEta 0) S ≤ 4 ∧
        finiteJointMeanVariancePriorMoment
            2 dataLaw fairPrior matchLoss (countableT 1) (countableEta 1) S ≤ 8 := by
  rcases countableGoodSample_all_entries_controlled with ⟨S, hS, hall⟩
  refine ⟨S, hS, ?_, ?_⟩
  · have h0 := hall 0
    norm_num [countableW] at h0
    exact h0
  · have h1 := hall 1
    norm_num [countableW] at h1
    exact h1

/-! The support guard is active, not decorative: a sample outside the support
of a degenerate product law is included in the bad set at zero probability
cost. -/

def pointMassFalse : Bool → ℝ := fun z => if z then 0 else 1

theorem pointMassFalse_isPMF : IsPMF pointMassFalse := by
  constructor
  · intro z
    cases z <;> norm_num [pointMassFalse]
  · norm_num [pointMassFalse]

def allTrueSample : Fin 2 → Bool := fun _ => true

theorem allTrueSample_weight_eq_zero :
    finiteProductSampleWeight pointMassFalse allTrueSample = 0 := by
  norm_num [finiteProductSampleWeight, pointMassFalse, allTrueSample]

theorem allTrueSample_mem_countableSupportGuard :
    allTrueSample ∈ countableJointMeanVarianceCatalogBadSamples
      2 pointMassFalse fairPrior matchLoss countableT countableEta countableW (1 / 2) := by
  rw [countableJointMeanVarianceCatalogBadSamples]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inl allTrueSample_weight_eq_zero⟩

#check countableJointMeanVarianceMasterMixture
#check countableJointMeanVarianceMasterMixture_nonneg
#check countableJointMeanVariance_weightedPriorMoments_summable_of_sampleWeight_pos
#check countableJointMeanVariance_masterMixture_expectation_le_weightTsum
#check countableJointMeanVariance_masterMixture_expectation_le_one
#check countableJointMeanVarianceCatalogBadSamples
#check countableJointMeanVariance_not_mem_catalogBadSamples_iff
#check countableJointMeanVariance_catalogBadSamples_mass_le_delta
#check countableJointMeanVariance_priorMoment_le_of_not_mem
#check countableW_tsum_eq_one
#check countableGoodSample_all_entries_controlled
#check countableGoodSample_firstTwoEntries_controlled
#check allTrueSample_mem_countableSupportGuard

#print axioms countableJointMeanVariance_weightedPriorMoments_summable_of_sampleWeight_pos
#print axioms countableJointMeanVarianceMasterMixture_nonneg
#print axioms countableJointMeanVariance_masterMixture_expectation_le_weightTsum
#print axioms countableJointMeanVariance_masterMixture_expectation_le_one
#print axioms countableJointMeanVariance_not_mem_catalogBadSamples_iff
#print axioms countableJointMeanVariance_catalogBadSamples_mass_le_delta
#print axioms countableJointMeanVariance_priorMoment_le_of_not_mem
#print axioms countableGoodSample_all_entries_controlled
#print axioms countableGoodSample_firstTwoEntries_controlled
#print axioms allTrueSample_mem_countableSupportGuard

end

end FormalSLT.Examples.CheckCountableJointMeanVariancePACBayes
