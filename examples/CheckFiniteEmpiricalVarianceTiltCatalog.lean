import FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concrete finite weighted empirical-variance tilt catalog checker

The finite law has two unequal atoms and two hypotheses with distinct
bounded-loss population variances.  The catalog has two entries with unequal
positive weights `1/2` and `1/4` summing to `3/4 <= 1`, and two distinct
admissible tilts `eta = 11/17` and `eta = 33/34` at `n = 34`, so
`eta * n = 22` and `eta * n = 33` against the admissibility ceiling
`2 * (n - 1) = 66`.

At `delta = 1/8` the two entry budgets are `1/16` and `1/32`.  Both the
posterior and the tilt are selected after seeing the sample, the tilt selector
reads the posterior as well, and the selector provably takes both catalog
values on samples of strictly positive product mass.  Each branch instantiates
the actual simultaneous selector theorem and lands strictly below the trivial
variance ceiling `1/4`: entry `false` at most `1/5`, entry `true` at most
`11/50`.
-/

namespace FormalSLT.Examples.CheckFiniteEmpiricalVarianceTiltCatalog

open Finset BigOperators Real
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayesFiniteProductMGF
open FormalSLT.PACBayes.FiniteProductBernstein
open FormalSLT.PACBayes.FiniteEmpiricalVariance
open FormalSLT.PACBayes.FiniteEmpiricalVarianceMGF
open FormalSLT.PACBayes.FiniteEmpiricalVariancePACBayes
open FormalSLT.PACBayes.FiniteEmpiricalVarianceTiltCatalog

noncomputable section

/-! ## The finite instance -/

/-- Unequal two-point data law: `P(false)=4/5`, `P(true)=1/5`. -/
def dataLaw : Bool → ℝ := fun z => if z then (1 : ℝ) / 5 else 4 / 5

theorem dataLaw_isPMF : IsPMF dataLaw := by
  constructor
  · intro z
    cases z <;> norm_num [dataLaw]
  · norm_num [dataLaw]

/-- Uniform full-support prior on the two hypotheses. -/
def prior : Bool → ℝ := fun _ => (1 : ℝ) / 2

theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  constructor
  · constructor
    · intro i
      norm_num [prior]
    · norm_num [prior]
  · intro i
    norm_num [prior]

/-- Two bounded, deliberately asymmetric losses.  Hypothesis `false` incurs
unit loss only on a `true` observation; hypothesis `true` incurs half loss only
on a `false` observation.  Their population variances are therefore distinct. -/
def loss (h z : Bool) : ℝ :=
  if h = false then (if z = true then 1 else 0)
  else (if z = false then (1 : ℝ) / 2 else 0)

theorem loss_mem_Icc (h z : Bool) : loss h z ∈ Set.Icc (0 : ℝ) 1 := by
  cases h <;> cases z <;> norm_num [loss]

/-! ## The catalog: two unequal weights, two distinct admissible tilts -/

/-- Catalog tilts.  Entry `false` uses `eta = 11/17`, entry `true` uses
`eta = 33/34`.  At `n = 34` these give `eta * n = 22` and `eta * n = 33`. -/
def etaCat : Bool → ℝ := fun j => if j then (33 : ℝ) / 34 else 11 / 17

/-- Catalog weights.  Unequal, positive, and summing to `3/4 <= 1`. -/
def weightCat : Bool → ℝ := fun j => if j then (1 : ℝ) / 4 else 1 / 2

theorem etaCat_pos (j : Bool) : 0 < etaCat j := by
  cases j <;> norm_num [etaCat]

theorem etaCat_distinct : etaCat false ≠ etaCat true := by
  norm_num [etaCat]

/-- Both catalog tilts satisfy the explicit admissibility condition
`eta j * n < 2 * (n - 1)` at `n = 34`. -/
theorem etaCat_admissible (j : Bool) :
    etaCat j * (34 : ℝ) < 2 * ((34 : ℝ) - 1) := by
  cases j <;> norm_num [etaCat]

theorem weightCat_pos (j : Bool) : 0 < weightCat j := by
  cases j <;> norm_num [weightCat]

theorem weightCat_unequal : weightCat false ≠ weightCat true := by
  norm_num [weightCat]

theorem weightCat_sum_le_one : ∑ j : Bool, weightCat j ≤ 1 := by
  norm_num [weightCat]

/-- The two entry budgets at `delta = 1/8` are `1/16` and `1/32`. -/
theorem entryBudget_false : (1 : ℝ) / 8 * weightCat false = 1 / 16 := by
  norm_num [weightCat]

theorem entryBudget_true : (1 : ℝ) / 8 * weightCat true = 1 / 32 := by
  norm_num [weightCat]

/-! ## Sample-dependent posterior and sample-and-posterior-dependent selector -/

/-- Posterior giving weight `3/5` to `favored` and `2/5` to the other. -/
def nearPosterior (favored : Bool) : Bool → ℝ := fun h =>
  if h = favored then (3 : ℝ) / 5 else 2 / 5

theorem nearPosterior_isPMF (favored : Bool) : IsPMF (nearPosterior favored) := by
  constructor
  · intro h
    cases favored <;> cases h <;> norm_num [nearPosterior]
  · cases favored <;> norm_num [nearPosterior]

/-- Sample-dependent posterior: favor the first observed label. -/
def postSelect (S : Fin 34 → Bool) : Bool → ℝ := nearPosterior (S 0)

theorem postSelect_isPMF (S : Fin 34 → Bool) : IsPMF (postSelect S) :=
  nearPosterior_isPMF (S 0)

/-- Tilt selector reading **both** the sample and the posterior: take the
`eta = 33/34` entry only when the first observation is `true` and the posterior
actually favors that first observation. -/
def tiltSelect (S : Fin 34 → Bool) (ρ : Bool → ℝ) : Bool :=
  (S 0) && decide (ρ (!(S 0)) < ρ (S 0))

def allFalse : Fin 34 → Bool := fun _ => false
def allTrue : Fin 34 → Bool := fun _ => true

theorem postSelect_allFalse : postSelect allFalse = nearPosterior false := rfl
theorem postSelect_allTrue : postSelect allTrue = nearPosterior true := rfl

/-- The selector picks catalog entry `false` on the all-`false` sample. -/
theorem tiltSelect_allFalse : tiltSelect allFalse (postSelect allFalse) = false := by
  norm_num [tiltSelect, allFalse, postSelect, nearPosterior]

/-- The selector picks catalog entry `true` on the all-`true` sample. -/
theorem tiltSelect_allTrue : tiltSelect allTrue (postSelect allTrue) = true := by
  norm_num [tiltSelect, allTrue, postSelect, nearPosterior]

/-- The selector takes **both** catalog values across the two samples. -/
theorem tiltSelect_takes_both_values :
    tiltSelect allFalse (postSelect allFalse) ≠
      tiltSelect allTrue (postSelect allTrue) := by
  rw [tiltSelect_allFalse, tiltSelect_allTrue]
  exact Bool.false_ne_true

/-- At a **fixed** sample the selected catalog entry still genuinely depends on
the posterior, so the two-argument selector is not secretly sample-only. -/
theorem tiltSelect_depends_on_posterior :
    tiltSelect allTrue (nearPosterior false) ≠
      tiltSelect allTrue (nearPosterior true) := by
  norm_num [tiltSelect, allTrue, nearPosterior]

/-- The sample-dependent posterior is genuinely sample-dependent. -/
theorem postSelect_takes_two_values : postSelect allFalse ≠ postSelect allTrue := by
  intro h
  have hfalse := congrFun h false
  norm_num [postSelect, allFalse, allTrue, nearPosterior] at hfalse

/-! ## Variances of the instance -/

theorem populationVariance_false_eq_four_twentyFive :
    finitePopulationVariance dataLaw loss false = (4 : ℝ) / 25 := by
  norm_num [finitePopulationVariance, finitePopulationRisk, dataLaw, loss]

theorem populationVariance_true_eq_one_twentyFive :
    finitePopulationVariance dataLaw loss true = (1 : ℝ) / 25 := by
  norm_num [finitePopulationVariance, finitePopulationRisk, dataLaw, loss]

theorem populationVariance_le_four_twentyFive (h : Bool) :
    finitePopulationVariance dataLaw loss h ≤ (4 : ℝ) / 25 := by
  cases h
  · rw [populationVariance_false_eq_four_twentyFive]
  · rw [populationVariance_true_eq_one_twentyFive]
    norm_num

theorem posterior_populationVariance_le_four_twentyFive
    (ρ : Bool → ℝ) (hρ : IsPMF ρ) :
    posteriorAverage ρ (fun h => finitePopulationVariance dataLaw loss h) ≤
      (4 : ℝ) / 25 := by
  unfold posteriorAverage
  calc
    (∑ h : Bool, ρ h * finitePopulationVariance dataLaw loss h) ≤
        ∑ h : Bool, ρ h * ((4 : ℝ) / 25) := by
      exact Finset.sum_le_sum (fun h _ =>
        mul_le_mul_of_nonneg_left
          (populationVariance_le_four_twentyFive h) (hρ.nonneg h))
    _ = (4 : ℝ) / 25 := by
      rw [← Finset.sum_mul, hρ.sum_one]
      norm_num

/-- A constant sample gives zero Bessel empirical variance for either
hypothesis. -/
theorem empiricalVariance_allFalse_eq_zero (h : Bool) :
    finiteEmpiricalVariance loss h allFalse = 0 := by
  cases h <;>
    norm_num [finiteEmpiricalVariance,
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
      FormalSLT.Statistics.sampleMean, loss, allFalse]

theorem empiricalVariance_allTrue_eq_zero (h : Bool) :
    finiteEmpiricalVariance loss h allTrue = 0 := by
  cases h <;>
    norm_num [finiteEmpiricalVariance,
      FormalSLT.Statistics.ClassicalEstimation.sampleVarianceBessel,
      FormalSLT.Statistics.sampleMean, loss, allTrue]

theorem posterior_empiricalVariance_allFalse_eq_zero (ρ : Bool → ℝ) :
    posteriorAverage ρ (fun h => finiteEmpiricalVariance loss h allFalse) = 0 := by
  unfold posteriorAverage
  simp_rw [empiricalVariance_allFalse_eq_zero]
  simp

theorem posterior_empiricalVariance_allTrue_eq_zero (ρ : Bool → ℝ) :
    posteriorAverage ρ (fun h => finiteEmpiricalVariance loss h allTrue) = 0 := by
  unfold posteriorAverage
  simp_rw [empiricalVariance_allTrue_eq_zero]
  simp

theorem posteriorVarianceProxy33_eq (ρ : Bool → ℝ) :
    posteriorMarginVarianceProxy ρ
        (fun h => finitePopulationVariance dataLaw loss h / (33 : ℝ)) =
      posteriorAverage ρ (finitePopulationVariance dataLaw loss) / 33 := by
  unfold posteriorMarginVarianceProxy posteriorAverage
  norm_num
  ring

/-! ## Numeric log bounds

Both directions are needed.  Lower bounds drive the bad-set nonmembership
proofs; upper bounds drive the certificates.  The crude estimate `log 2 <= 1`
is not sufficient for the `log 32` certificate, so `Real.log_two_lt_d9` is
used for the upper bounds. -/

theorem log_sixteen_eq : Real.log (1 / ((1 : ℝ) / 16)) = 4 * Real.log 2 := by
  norm_num only [one_div, inv_div, inv_one]
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
  norm_num

theorem log_thirtyTwo_eq : Real.log (1 / ((1 : ℝ) / 32)) = 5 * Real.log 2 := by
  norm_num only [one_div, inv_div, inv_one]
  rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
  norm_num

/-- Nonmembership margin for catalog entry `false`: needs `176/75 ≈ 2.3467`. -/
theorem log_sixteen_gt : (176 : ℝ) / 75 < Real.log (1 / ((1 : ℝ) / 16)) := by
  rw [log_sixteen_eq]
  have h := Real.log_two_gt_d9
  nlinarith

/-- Nonmembership margin for catalog entry `true`: needs `66/25 = 2.64`. -/
theorem log_thirtyTwo_gt : (66 : ℝ) / 25 < Real.log (1 / ((1 : ℝ) / 32)) := by
  rw [log_thirtyTwo_eq]
  have h := Real.log_two_gt_d9
  nlinarith

theorem log_sixteen_lt : Real.log (1 / ((1 : ℝ) / 16)) < (2773 : ℝ) / 1000 := by
  rw [log_sixteen_eq]
  have h := Real.log_two_lt_d9
  nlinarith

theorem log_thirtyTwo_lt : Real.log (1 / ((1 : ℝ) / 32)) < (3466 : ℝ) / 1000 := by
  rw [log_thirtyTwo_eq]
  have h := Real.log_two_lt_d9
  nlinarith

/-- Tangent-line estimate for both posterior branches: `KL <= 1/25`. -/
theorem nearPosterior_kl_le_one_twentyFive (favored : Bool) :
    klDiv (nearPosterior favored) prior ≤ (1 : ℝ) / 25 := by
  have hlogSixFifths : Real.log ((6 : ℝ) / 5) ≤ 1 / 5 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 / 5 by norm_num)
    norm_num at h
    exact h
  have hlogFourFifths : Real.log ((4 : ℝ) / 5) ≤ -(1 / 5) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)
    norm_num at h
    exact h
  have hSixScaled : (3 : ℝ) / 5 * Real.log (6 / 5) ≤ (3 : ℝ) / 25 := by
    nlinarith
  have hFourScaled : (2 : ℝ) / 5 * Real.log (4 / 5) ≤ -(2 : ℝ) / 25 := by
    nlinarith
  cases favored <;> simp [klDiv, nearPosterior, prior] <;> linarith

theorem postSelect_kl_le_one_twentyFive (S : Fin 34 → Bool) :
    klDiv (postSelect S) prior ≤ (1 : ℝ) / 25 :=
  nearPosterior_kl_le_one_twentyFive (S 0)

/-! ## Entrywise bad-set nonmembership -/

set_option maxRecDepth 4096 in
/-- Entry `false` (`eta * n = 22`, budget `1/16`) does not exclude `allFalse`. -/
theorem allFalse_not_mem_entry_false :
    allFalse ∉ finiteEmpiricalVariancePACBayesBadSamples
      34 dataLaw prior loss ((11 : ℝ) / 17) ((1 : ℝ) / 16) := by
  intro hmem
  simp only [finiteEmpiricalVariancePACBayesBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨ρ, hρ, hbad⟩
  have hV := posterior_populationVariance_le_four_twentyFive ρ hρ
  have hkl : 0 ≤ klDiv ρ prior := klDiv_nonneg hρ prior_isFullSupportPMF
  have hlog := log_sixteen_gt
  have hB := posterior_empiricalVariance_allFalse_eq_zero ρ
  have hproxy := posteriorVarianceProxy33_eq ρ
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hbad
  rw [hB] at hbad
  norm_num at hbad
  rw [hproxy] at hbad
  linarith

set_option maxRecDepth 4096 in
/-- Entry `true` (`eta * n = 33`, budget `1/32`) does not exclude `allFalse`. -/
theorem allFalse_not_mem_entry_true :
    allFalse ∉ finiteEmpiricalVariancePACBayesBadSamples
      34 dataLaw prior loss ((33 : ℝ) / 34) ((1 : ℝ) / 32) := by
  intro hmem
  simp only [finiteEmpiricalVariancePACBayesBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨ρ, hρ, hbad⟩
  have hV := posterior_populationVariance_le_four_twentyFive ρ hρ
  have hkl : 0 ≤ klDiv ρ prior := klDiv_nonneg hρ prior_isFullSupportPMF
  have hlog := log_thirtyTwo_gt
  have hB := posterior_empiricalVariance_allFalse_eq_zero ρ
  have hproxy := posteriorVarianceProxy33_eq ρ
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hbad
  rw [hB] at hbad
  norm_num at hbad
  rw [hproxy] at hbad
  linarith

set_option maxRecDepth 4096 in
theorem allTrue_not_mem_entry_false :
    allTrue ∉ finiteEmpiricalVariancePACBayesBadSamples
      34 dataLaw prior loss ((11 : ℝ) / 17) ((1 : ℝ) / 16) := by
  intro hmem
  simp only [finiteEmpiricalVariancePACBayesBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨ρ, hρ, hbad⟩
  have hV := posterior_populationVariance_le_four_twentyFive ρ hρ
  have hkl : 0 ≤ klDiv ρ prior := klDiv_nonneg hρ prior_isFullSupportPMF
  have hlog := log_sixteen_gt
  have hB := posterior_empiricalVariance_allTrue_eq_zero ρ
  have hproxy := posteriorVarianceProxy33_eq ρ
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hbad
  rw [hB] at hbad
  norm_num at hbad
  rw [hproxy] at hbad
  linarith

set_option maxRecDepth 4096 in
theorem allTrue_not_mem_entry_true :
    allTrue ∉ finiteEmpiricalVariancePACBayesBadSamples
      34 dataLaw prior loss ((33 : ℝ) / 34) ((1 : ℝ) / 32) := by
  intro hmem
  simp only [finiteEmpiricalVariancePACBayesBadSamples,
    finitePACBayesBernsteinFixedLambdaBadSamples, Finset.mem_filter,
    Finset.mem_univ, true_and] at hmem
  rcases hmem with ⟨ρ, hρ, hbad⟩
  have hV := posterior_populationVariance_le_four_twentyFive ρ hρ
  have hkl : 0 ≤ klDiv ρ prior := klDiv_nonneg hρ prior_isFullSupportPMF
  have hlog := log_thirtyTwo_gt
  have hB := posterior_empiricalVariance_allTrue_eq_zero ρ
  have hproxy := posteriorVarianceProxy33_eq ρ
  unfold posteriorGeneralizationGap posteriorRisk posteriorEmpiricalRisk at hbad
  rw [hB] at hbad
  norm_num at hbad
  rw [hproxy] at hbad
  linarith

/-! ## Catalog nonmembership -/

/-- `allFalse` is outside the single catalog exceptional set. -/
theorem allFalse_not_mem_catalog :
    allFalse ∉ finiteEmpiricalVarianceWeightedCatalogBadSamples
      34 dataLaw prior loss etaCat weightCat ((1 : ℝ) / 8) := by
  refine (finiteEmpiricalVariance_not_mem_weightedCatalog_iff
    34 dataLaw prior loss etaCat weightCat ((1 : ℝ) / 8) allFalse).2 ?_
  intro j
  cases j
  · have h : (1 : ℝ) / 8 * weightCat false = 1 / 16 := entryBudget_false
    rw [show etaCat false = (11 : ℝ) / 17 from rfl, h]
    exact allFalse_not_mem_entry_false
  · have h : (1 : ℝ) / 8 * weightCat true = 1 / 32 := entryBudget_true
    rw [show etaCat true = (33 : ℝ) / 34 from rfl, h]
    exact allFalse_not_mem_entry_true

/-- `allTrue` is outside the single catalog exceptional set. -/
theorem allTrue_not_mem_catalog :
    allTrue ∉ finiteEmpiricalVarianceWeightedCatalogBadSamples
      34 dataLaw prior loss etaCat weightCat ((1 : ℝ) / 8) := by
  refine (finiteEmpiricalVariance_not_mem_weightedCatalog_iff
    34 dataLaw prior loss etaCat weightCat ((1 : ℝ) / 8) allTrue).2 ?_
  intro j
  cases j
  · have h : (1 : ℝ) / 8 * weightCat false = 1 / 16 := entryBudget_false
    rw [show etaCat false = (11 : ℝ) / 17 from rfl, h]
    exact allTrue_not_mem_entry_false
  · have h : (1 : ℝ) / 8 * weightCat true = 1 / 32 := entryBudget_true
    rw [show etaCat true = (33 : ℝ) / 34 from rfl, h]
    exact allTrue_not_mem_entry_true

/-! ## Catalog mass -/

/-- The single weighted catalog exceptional set has product mass at most
`delta = 1/8`, covering both tilts at once. -/
theorem catalog_badEventMass_le_eighth :
    (∑ S ∈ finiteEmpiricalVarianceWeightedCatalogBadSamples
        34 dataLaw prior loss etaCat weightCat ((1 : ℝ) / 8),
      finiteProductSampleWeight dataLaw S) ≤ (1 : ℝ) / 8 :=
  finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta
    (κ := Bool) (n := 34) (Z := Bool) (ι := Bool)
    (by norm_num) dataLaw dataLaw_isPMF prior_isFullSupportPMF loss
    (fun i z => loss_mem_Icc i z)
    etaCat weightCat ((1 : ℝ) / 8)
    etaCat_pos weightCat_pos weightCat_sum_le_one (by norm_num)

/-! ## Positive-mass samples -/

theorem allFalse_productWeight_pos :
    0 < finiteProductSampleWeight dataLaw allFalse := by
  simp [finiteProductSampleWeight, dataLaw, allFalse]

theorem allTrue_productWeight_pos :
    0 < finiteProductSampleWeight dataLaw allTrue := by
  simp [finiteProductSampleWeight, dataLaw, allTrue]

/-! ## The selector certificate -/

/-- The exact right-hand side produced by the simultaneous selector theorem. -/
def catalogCertificate (S : Fin 34 → Bool) (ρ : Bool → ℝ) : ℝ :=
  (posteriorAverage ρ (fun h => finiteEmpiricalVariance loss h S) +
      (klDiv ρ prior +
          Real.log (1 / ((1 : ℝ) / 8 * weightCat (tiltSelect S ρ)))) /
        (etaCat (tiltSelect S ρ) * (34 : ℝ))) /
    (1 - etaCat (tiltSelect S ρ) * (34 : ℝ) / (2 * ((34 : ℝ) - 1)))

/-- Instantiation of the **actual** simultaneous selector theorem on the
all-`false` branch, where the selector picks catalog entry `false`. -/
theorem allFalse_posteriorVariance_le_catalogCertificate :
    posteriorAverage (postSelect allFalse)
        (finitePopulationVariance dataLaw loss) ≤
      catalogCertificate allFalse (postSelect allFalse) :=
  posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem
    (κ := Bool) (n := 34) (Z := Bool) (ι := Bool)
    (by norm_num) dataLaw prior loss etaCat weightCat ((1 : ℝ) / 8)
    etaCat_pos (fun j => etaCat_admissible j)
    tiltSelect allFalse allFalse_not_mem_catalog
    (postSelect allFalse) (postSelect_isPMF allFalse)

/-- Instantiation of the **actual** simultaneous selector theorem on the
all-`true` branch, where the selector picks catalog entry `true`. -/
theorem allTrue_posteriorVariance_le_catalogCertificate :
    posteriorAverage (postSelect allTrue)
        (finitePopulationVariance dataLaw loss) ≤
      catalogCertificate allTrue (postSelect allTrue) :=
  posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem
    (κ := Bool) (n := 34) (Z := Bool) (ι := Bool)
    (by norm_num) dataLaw prior loss etaCat weightCat ((1 : ℝ) / 8)
    etaCat_pos (fun j => etaCat_admissible j)
    tiltSelect allTrue allTrue_not_mem_catalog
    (postSelect allTrue) (postSelect_isPMF allTrue)

/-- Entry `false` branch: `eta * n = 22`, denominator `2/3`, budget `1/16`. -/
theorem allFalse_catalogCertificate_le_one_fifth :
    catalogCertificate allFalse (postSelect allFalse) ≤ (1 : ℝ) / 5 := by
  unfold catalogCertificate
  rw [tiltSelect_allFalse]
  rw [posterior_empiricalVariance_allFalse_eq_zero]
  rw [show etaCat false = (11 : ℝ) / 17 from rfl,
    show (1 : ℝ) / 8 * weightCat false = 1 / 16 from entryBudget_false]
  have hkl := postSelect_kl_le_one_twentyFive allFalse
  have hlog := log_sixteen_lt
  have hkl0 : 0 ≤ klDiv (postSelect allFalse) prior :=
    klDiv_nonneg (postSelect_isPMF allFalse) prior_isFullSupportPMF
  norm_num
  linarith

/-- Entry `true` branch: `eta * n = 33`, denominator `1/2`, budget `1/32`. -/
theorem allTrue_catalogCertificate_le_eleven_fiftieths :
    catalogCertificate allTrue (postSelect allTrue) ≤ (11 : ℝ) / 50 := by
  unfold catalogCertificate
  rw [tiltSelect_allTrue]
  rw [posterior_empiricalVariance_allTrue_eq_zero]
  rw [show etaCat true = (33 : ℝ) / 34 from rfl,
    show (1 : ℝ) / 8 * weightCat true = 1 / 32 from entryBudget_true]
  have hkl := postSelect_kl_le_one_twentyFive allTrue
  have hlog := log_thirtyTwo_lt
  have hkl0 : 0 ≤ klDiv (postSelect allTrue) prior :=
    klDiv_nonneg (postSelect_isPMF allTrue) prior_isFullSupportPMF
  norm_num
  linarith

/-! ## Left-hand-side values, so the certificates are visibly not vacuous -/

theorem selectedPosterior_populationVariance_allFalse_eq_14_125 :
    posteriorAverage (postSelect allFalse)
        (fun h => finitePopulationVariance dataLaw loss h) = (14 : ℝ) / 125 := by
  norm_num [posteriorAverage, postSelect, allFalse, nearPosterior,
    populationVariance_false_eq_four_twentyFive,
    populationVariance_true_eq_one_twentyFive]

theorem selectedPosterior_populationVariance_allTrue_eq_11_125 :
    posteriorAverage (postSelect allTrue)
        (fun h => finitePopulationVariance dataLaw loss h) = (11 : ℝ) / 125 := by
  norm_num [posteriorAverage, postSelect, allTrue, nearPosterior,
    populationVariance_false_eq_four_twentyFive,
    populationVariance_true_eq_one_twentyFive]

theorem selectedPosterior_populationVariance_differs :
    posteriorAverage (postSelect allFalse)
        (fun h => finitePopulationVariance dataLaw loss h) ≠
      posteriorAverage (postSelect allTrue)
        (fun h => finitePopulationVariance dataLaw loss h) := by
  rw [selectedPosterior_populationVariance_allFalse_eq_14_125,
    selectedPosterior_populationVariance_allTrue_eq_11_125]
  norm_num

/-- The two branches genuinely use different catalog tilts and different
confidence budgets, so the union bound is doing real work. -/
theorem selected_entries_use_distinct_tilt_and_weight :
    etaCat (tiltSelect allFalse (postSelect allFalse)) ≠
        etaCat (tiltSelect allTrue (postSelect allTrue)) ∧
      weightCat (tiltSelect allFalse (postSelect allFalse)) ≠
        weightCat (tiltSelect allTrue (postSelect allTrue)) := by
  rw [tiltSelect_allFalse, tiltSelect_allTrue]
  exact ⟨etaCat_distinct, weightCat_unequal⟩

/-- **Receipt.**  On both positive-mass samples the selector fires a different
catalog entry, the actual simultaneous theorem applies, and both certificates
are strictly below the trivial variance ceiling `1/4`. -/
theorem catalog_selected_branches_nonvacuous :
    (tiltSelect allFalse (postSelect allFalse) ≠
        tiltSelect allTrue (postSelect allTrue)) ∧
    (0 < finiteProductSampleWeight dataLaw allFalse ∧
      posteriorAverage (postSelect allFalse)
          (finitePopulationVariance dataLaw loss) ≤
        catalogCertificate allFalse (postSelect allFalse) ∧
      catalogCertificate allFalse (postSelect allFalse) < (1 : ℝ) / 4) ∧
    (0 < finiteProductSampleWeight dataLaw allTrue ∧
      posteriorAverage (postSelect allTrue)
          (finitePopulationVariance dataLaw loss) ≤
        catalogCertificate allTrue (postSelect allTrue) ∧
      catalogCertificate allTrue (postSelect allTrue) < (1 : ℝ) / 4) :=
  ⟨tiltSelect_takes_both_values,
    ⟨allFalse_productWeight_pos,
      allFalse_posteriorVariance_le_catalogCertificate,
      allFalse_catalogCertificate_le_one_fifth.trans_lt (by norm_num)⟩,
    ⟨allTrue_productWeight_pos,
      allTrue_posteriorVariance_le_catalogCertificate,
      allTrue_catalogCertificate_le_eleven_fiftieths.trans_lt (by norm_num)⟩⟩

#check FormalSLT.Probability.FiniteUnionBound.finiteWeightedUnionBound_sum_le_of_exists_mem
#check finiteEmpiricalVarianceWeightedCatalogBadSamples
#check finiteEmpiricalVariance_mem_weightedCatalog_iff
#check finiteEmpiricalVariance_not_mem_weightedCatalog_iff
#check finiteEmpiricalVarianceFixedTiltBadSamples_subset_weightedCatalog
#check finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta
#check finiteEmpiricalVariance_posteriorGap_le_weightedCatalog_of_not_mem
#check posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_of_not_mem
#check posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem
#check dataLaw_isPMF
#check prior_isFullSupportPMF
#check loss_mem_Icc
#check etaCat_pos
#check etaCat_distinct
#check etaCat_admissible
#check weightCat_pos
#check weightCat_unequal
#check weightCat_sum_le_one
#check postSelect_isPMF
#check postSelect_takes_two_values
#check tiltSelect_allFalse
#check tiltSelect_allTrue
#check tiltSelect_takes_both_values
#check tiltSelect_depends_on_posterior
#check allFalse_not_mem_catalog
#check allTrue_not_mem_catalog
#check catalog_badEventMass_le_eighth
#check allFalse_productWeight_pos
#check allTrue_productWeight_pos
#check allFalse_posteriorVariance_le_catalogCertificate
#check allTrue_posteriorVariance_le_catalogCertificate
#check allFalse_catalogCertificate_le_one_fifth
#check allTrue_catalogCertificate_le_eleven_fiftieths
#check selectedPosterior_populationVariance_allFalse_eq_14_125
#check selectedPosterior_populationVariance_allTrue_eq_11_125
#check selectedPosterior_populationVariance_differs
#check selected_entries_use_distinct_tilt_and_weight
#check catalog_selected_branches_nonvacuous

#print axioms FormalSLT.Probability.FiniteUnionBound.finiteWeightedUnionBound_sum_le_of_exists_mem
#print axioms finiteEmpiricalVariance_mem_weightedCatalog_iff
#print axioms finiteEmpiricalVariance_not_mem_weightedCatalog_iff
#print axioms finiteEmpiricalVarianceFixedTiltBadSamples_subset_weightedCatalog
#print axioms finiteEmpiricalVariance_weightedCatalog_badEventMass_le_delta
#print axioms finiteEmpiricalVariance_posteriorGap_le_weightedCatalog_of_not_mem
#print axioms posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_of_not_mem
#print axioms posteriorPopulationVariance_le_empiricalVariance_weightedCatalog_selected_of_not_mem
#print axioms dataLaw_isPMF
#print axioms prior_isFullSupportPMF
#print axioms loss_mem_Icc
#print axioms etaCat_pos
#print axioms etaCat_distinct
#print axioms etaCat_admissible
#print axioms weightCat_pos
#print axioms weightCat_unequal
#print axioms weightCat_sum_le_one
#print axioms postSelect_isPMF
#print axioms postSelect_takes_two_values
#print axioms tiltSelect_allFalse
#print axioms tiltSelect_allTrue
#print axioms tiltSelect_takes_both_values
#print axioms tiltSelect_depends_on_posterior
#print axioms allFalse_not_mem_catalog
#print axioms allTrue_not_mem_catalog
#print axioms catalog_badEventMass_le_eighth
#print axioms allFalse_productWeight_pos
#print axioms allTrue_productWeight_pos
#print axioms allFalse_posteriorVariance_le_catalogCertificate
#print axioms allTrue_posteriorVariance_le_catalogCertificate
#print axioms allFalse_catalogCertificate_le_one_fifth
#print axioms allTrue_catalogCertificate_le_eleven_fiftieths
#print axioms selectedPosterior_populationVariance_allFalse_eq_14_125
#print axioms selectedPosterior_populationVariance_allTrue_eq_11_125
#print axioms selectedPosterior_populationVariance_differs
#print axioms selected_entries_use_distinct_tilt_and_weight
#print axioms catalog_selected_branches_nonvacuous

end

end FormalSLT.Examples.CheckFiniteEmpiricalVarianceTiltCatalog
