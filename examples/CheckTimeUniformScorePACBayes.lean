import FormalSLT.PACBayes.TimeUniformScorePACBayes

/-!
# Generic time-uniform score PAC-Bayes audit

The receipt uses a finite two-hypothesis class and a delayed-reveal Bool
filtration. At time one, each hypothesis has wealth `3/2` on one outcome and
`1/2` on the other, then freezes. Thus each exponentiated score is a genuine
nonconstant martingale/e-process. A nonuniform full-support prior makes their
mixture nonconstant too: it equals `5/4` on `true` and `3/4` on `false`, so the
positive-mass `true` outcome crosses the `5/4` Ville threshold. The generic
compiler bounds its all-time/all-posterior failure event by `4/5`; the explicit
`false` outcome is good, and the regret adapter fires on target `score + 1/5`.
-/

open MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid
open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.TimeUniformScore
open scoped ENNReal BigOperators

noncomputable section

namespace FormalSLT.PACBayes.TimeUniformScoreWitness

/-- Uniform probability measure on the two Bool outcomes. -/
def muBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure muBool := by
  refine ⟨?_⟩
  simp only [muBool, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  exact ENNReal.add_halves 1

/-- The sample is hidden at time zero and fully revealed from time one onward. -/
def boolDelayFiltration : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq := fun n => if n = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp only [hi, hj]
        exact bot_le
    · have hj : j ≠ 0 := by
        rintro rfl
        exact hi (Nat.le_zero.mp hij)
      simp [hi, hj]
  le' := by
    intro n
    by_cases hn : n = 0
    · simp only [hn]
      exact bot_le
    · simp [hn]

/-- Nonuniform full-support prior on two hypotheses. -/
def twoHypPrior : Fin 2 → ℝ := fun i => if i = 0 then (3 : ℝ) / 4 else 1 / 4

theorem twoHypPrior_isFullSupportPMF : IsFullSupportPMF twoHypPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [twoHypPrior]
  · norm_num [twoHypPrior, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> norm_num [twoHypPrior]

/--
Two complementary betting wealth processes. They start at one; from time one,
hypothesis zero pays `3/2` on `true` and `1/2` on `false`, while hypothesis one
pays the reverse.
-/
def twoHypWealth (i : Fin 2) (n : ℕ) (ω : Bool) : ℝ :=
  if n = 0 then 1
  else if i = 0 then (if ω then 3 / 2 else 1 / 2)
  else (if ω then 1 / 2 else 3 / 2)

theorem twoHypWealth_pos (i : Fin 2) (n : ℕ) (ω : Bool) :
    0 < twoHypWealth i n ω := by
  by_cases hn : n = 0
  · simp [twoHypWealth, hn]
  · fin_cases i <;> cases ω <;> norm_num [twoHypWealth, hn]

/-- Log-wealth score whose exponential is exactly the betting wealth. -/
def twoHypScore (i : Fin 2) (n : ℕ) (ω : Bool) : ℝ :=
  Real.log (twoHypWealth i n ω)

theorem exp_twoHypScore (i : Fin 2) (n : ℕ) (ω : Bool) :
    Real.exp (twoHypScore i n ω) = twoHypWealth i n ω := by
  exact Real.exp_log (twoHypWealth_pos i n ω)

theorem twoHypWealth_stronglyAdapted (i : Fin 2) :
    StronglyAdapted boolDelayFiltration (twoHypWealth i) := by
  intro n
  by_cases hn : n = 0
  · subst n
    have hconst : twoHypWealth i 0 = fun _ => (1 : ℝ) := by
      funext ω
      simp [twoHypWealth]
    rw [hconst]
    exact stronglyMeasurable_const
  · have hfiltration : boolDelayFiltration n = ⊤ := by
      simp [boolDelayFiltration, hn]
    rw [show StronglyMeasurable[boolDelayFiltration n] (twoHypWealth i n) =
        StronglyMeasurable[⊤] (twoHypWealth i n) from by rw [hfiltration]]
    exact measurable_from_top.stronglyMeasurable

theorem twoHypWealth_supermartingale (i : Fin 2) :
    Supermartingale (twoHypWealth i) boolDelayFiltration muBool := by
  refine supermartingale_nat (twoHypWealth_stronglyAdapted i)
    (fun _ => Integrable.of_finite) ?_
  intro n
  by_cases hn : n = 0
  · subst n
    have hfiltration : boolDelayFiltration 0 = ⊥ := by
      simp [boolDelayFiltration]
    rw [hfiltration, condExp_bot]
    have hint : ∫ ω, twoHypWealth i 1 ω ∂muBool = 1 := by
      haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (true : Bool)) :=
        Measure.smul_finite _ (by norm_num)
      haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (false : Bool)) :=
        Measure.smul_finite _ (by norm_num)
      rw [muBool, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
        integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
      fin_cases i <;> norm_num [twoHypWealth, smul_eq_mul]
    rw [hint]
    exact Filter.Eventually.of_forall fun ω => by simp [twoHypWealth]
  · have hfiltration : boolDelayFiltration n = ⊤ := by
      simp [boolDelayFiltration, hn]
    have hmeas : StronglyMeasurable[boolDelayFiltration n] (twoHypWealth i (n + 1)) := by
      rw [hfiltration]
      exact measurable_from_top.stronglyMeasurable
    rw [condExp_of_stronglyMeasurable
      (boolDelayFiltration.le n) hmeas Integrable.of_finite]
    exact Filter.Eventually.of_forall fun ω => by
      simp [twoHypWealth, hn]

/-- Every exponentiated score is a genuine e-process. -/
theorem twoHypScore_eProcess (i : Fin 2) :
    EProcess muBool boolDelayFiltration
      (fun n ω => Real.exp (twoHypScore i n ω)) := by
  have hfun : (fun n ω => Real.exp (twoHypScore i n ω)) = twoHypWealth i := by
    funext n ω
    exact exp_twoHypScore i n ω
  rw [hfun]
  exact
    { nonneg := fun n ω => (twoHypWealth_pos i n ω).le
      start_one := fun ω => by simp [twoHypWealth]
      supermartingale := twoHypWealth_supermartingale i }

/-- The receipt score is nonconstant on the two positive-mass outcomes. -/
theorem twoHypScore_nonconstant :
    twoHypScore 0 1 true ≠ twoHypScore 0 1 false := by
  intro h
  have hexp := congrArg Real.exp h
  rw [exp_twoHypScore, exp_twoHypScore] at hexp
  norm_num [twoHypWealth] at hexp

/-- Closed numeric all-time/all-posterior certificate at failure level `4/5`. -/
theorem twoHypScore_failure_mass_le_fourFifths :
    muBool.real
      (timeUniformScorePACBayesAnyPosteriorFailure
        twoHypPrior twoHypScore (4 / 5)) ≤ (4 / 5 : ℝ) := by
  exact timeUniformScorePACBayes_allPosteriors_bound
    twoHypPrior_isFullSupportPMF twoHypScore_eProcess (by norm_num)

/-- A target separated from the score by the deterministic regret `1/5`. -/
def twoHypTarget (i : Fin 2) (n : ℕ) (ω : Bool) : ℝ :=
  twoHypScore i n ω + 1 / 5

def oneFifthRegret (_n : ℕ) : ℝ := 1 / 5

/-- The pathwise deterministic-regret adapter fires on every good outcome. -/
theorem twoHypTarget_certificate (ω : Bool)
    (hgood :
      ω ∉ timeUniformScorePACBayesAnyPosteriorFailure
        twoHypPrior twoHypScore (4 / 5)) :
    posteriorAverage twoHypPrior (fun i => twoHypTarget i 1 ω)
      ≤ klDiv twoHypPrior twoHypPrior + Real.log (1 / (4 / 5 : ℝ)) + 1 / 5 := by
  exact posteriorTarget_le_of_not_mem_timeUniformScorePACBayesFailure
    (regret := oneFifthRegret) hgood twoHypPrior_isFullSupportPMF.toIsPMF 1
    (fun _ => le_rfl)

/-- Exact values of the nonconstant prior mixture. -/
theorem twoHypScore_priorMixture_value (n : ℕ) (ω : Bool) :
    scorePriorMixtureProcess twoHypPrior twoHypScore n ω =
      if n = 0 then 1 else if ω then 5 / 4 else 3 / 4 := by
  unfold scorePriorMixtureProcess
  simp_rw [exp_twoHypScore]
  by_cases hn : n = 0 <;> cases ω <;>
    norm_num [twoHypPrior, twoHypWealth, hn, Fin.sum_univ_two]

/-- The common prior-mixture e-process is itself nonconstant. -/
theorem twoHypScore_priorMixture_nonconstant :
    scorePriorMixtureProcess twoHypPrior twoHypScore 1 true ≠
      scorePriorMixtureProcess twoHypPrior twoHypScore 1 false := by
  rw [twoHypScore_priorMixture_value, twoHypScore_priorMixture_value]
  norm_num

/-- The positive-mass `true` outcome crosses the `5/4` Ville threshold. -/
theorem twoHypScore_true_crosses_fiveFourths :
    true ∈ atTopCrossingEvent
      (scorePriorMixtureProcess twoHypPrior twoHypScore) (1 / (4 / 5 : ℝ)) := by
  refine ⟨1, ?_⟩
  rw [twoHypScore_priorMixture_value]
  norm_num

/-- The explicit outcome `false` lies on the compiler's common good event. -/
theorem twoHypScore_false_good :
    false ∉ timeUniformScorePACBayesAnyPosteriorFailure
      twoHypPrior twoHypScore (4 / 5) := by
  intro hfailure
  have hcross :=
    timeUniformScorePACBayesAnyPosteriorFailure_subset_crossing
      twoHypPrior_isFullSupportPMF (by norm_num) hfailure
  rcases hcross with ⟨n, hn⟩
  rw [twoHypScore_priorMixture_value] at hn
  by_cases hzero : n = 0 <;> norm_num [hzero] at hn

/-- The regret adapter gives a closed certificate on the explicit good outcome. -/
theorem twoHypTarget_false_certificate :
    posteriorAverage twoHypPrior (fun i => twoHypTarget i 1 false)
      ≤ klDiv twoHypPrior twoHypPrior + Real.log (1 / (4 / 5 : ℝ)) + 1 / 5 :=
  twoHypTarget_certificate false twoHypScore_false_good

#check @scorePriorMixture_eProcess
#check @timeUniformScorePACBayesAnyPosteriorFailure_subset_crossing
#check @timeUniformScorePACBayes_allPosteriors_bound
#check @posteriorTarget_le_of_not_mem_timeUniformScorePACBayesFailure

#print axioms scorePriorMixture_eProcess
#print axioms timeUniformScorePACBayesAnyPosteriorFailure_subset_crossing
#print axioms timeUniformScorePACBayes_allPosteriors_bound
#print axioms posteriorTarget_le_of_not_mem_timeUniformScorePACBayesFailure

#print axioms twoHypScore_eProcess
#print axioms twoHypScore_failure_mass_le_fourFifths
#print axioms twoHypTarget_certificate
#print axioms twoHypScore_nonconstant
#print axioms twoHypScore_priorMixture_nonconstant
#print axioms twoHypScore_true_crosses_fiveFourths
#print axioms twoHypScore_false_good
#print axioms twoHypTarget_false_certificate

end FormalSLT.PACBayes.TimeUniformScoreWitness
