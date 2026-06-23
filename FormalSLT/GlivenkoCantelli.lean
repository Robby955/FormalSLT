import Mathlib.Probability.CDF
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Order.Basic
import FormalSLT.UniformConvergence
import FormalSLT.Rademacher.ERMGeneralization
import FormalSLT.PACBayes.VCHybrid

/-!
# Glivenko-Cantelli bridge

This module adds the named Glivenko-Cantelli surface missing from the current
FormalSLT library and connects it to the existing finite-class
uniform-convergence, Rademacher, VC, and PAC-Bayes theorem surfaces.

The imported mathlib snapshot has `ProbabilityTheory.cdf` and strong-law
infrastructure, but no theorem named Glivenko-Cantelli and no empirical-CDF API.
Accordingly, this file makes the bridge explicit: the classical empirical-CDF
uniform-deviation process is the lower-ray indicator-class empirical process.
-/

open scoped BigOperators Function Topology ENNReal NNReal
open Filter MeasureTheory ProbabilityTheory
open FormalSLT.ERM
open FormalSLT.GhostSample (piMeasure)
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesBernstein
open FormalSLT.PACBayes.VCHybrid
open FormalSLT.Rademacher.FiniteSample (empiricalRademacherComplexity)
open FormalSLT.Risk
open FormalSLT.VC.Rademacher (effectiveClass)

namespace FormalSLT.GlivenkoCantelli

noncomputable section

/-- Lower-ray indicator `1{z <= x}`, as a real-valued loss/function class member. -/
def lowerRayIndicator (x z : ℝ) : ℝ :=
  if z ≤ x then 1 else 0

/-- Strict lower-ray indicator `1{z < x}`, used for atom-aware upper brackets. -/
def strictLowerRayIndicator (x z : ℝ) : ℝ :=
  if z < x then 1 else 0

/-- Lower-ray indicators are `[0,1]`-valued. -/
theorem lowerRayIndicator_mem_Icc (x z : ℝ) :
    lowerRayIndicator x z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold lowerRayIndicator
  split_ifs <;> norm_num

/-- Strict lower-ray indicators are `[0,1]`-valued. -/
theorem strictLowerRayIndicator_mem_Icc (x z : ℝ) :
    strictLowerRayIndicator x z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold strictLowerRayIndicator
  split_ifs <;> norm_num

/-- Lower-ray indicators are measurable. -/
lemma measurable_lowerRayIndicator (x : ℝ) :
    Measurable (lowerRayIndicator x) := by
  unfold lowerRayIndicator
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/-- Strict lower-ray indicators are measurable. -/
lemma measurable_strictLowerRayIndicator (x : ℝ) :
    Measurable (strictLowerRayIndicator x) := by
  unfold strictLowerRayIndicator
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

/-- Left limit of the CDF, i.e. the population mass of `(-∞, x)`. -/
def cdfLeftLimit (μ : Measure ℝ) (x : ℝ) : ℝ :=
  Function.leftLim (ProbabilityTheory.cdf μ) x

lemma cdfLeftLimit_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ cdfLeftLimit μ x := by
  have hlim :
      Tendsto (ProbabilityTheory.cdf μ) (𝓝[<] x) (𝓝 (cdfLeftLimit μ x)) := by
    simpa [cdfLeftLimit] using (ProbabilityTheory.monotone_cdf μ).tendsto_leftLim x
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with y _
  exact ProbabilityTheory.cdf_nonneg μ y

lemma integrable_lowerRayIndicator_comp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X0 : Ω → ℝ}
    (hX0 : Measurable X0) (x : ℝ) :
    Integrable (fun ω => lowerRayIndicator x (X0 ω)) P := by
  refine Integrable.of_mem_Icc 0 1 ?_ ?_
  · exact ((measurable_lowerRayIndicator x).comp hX0).aemeasurable
  · exact Filter.Eventually.of_forall fun ω => lowerRayIndicator_mem_Icc x (X0 ω)

lemma integrable_strictLowerRayIndicator_comp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X0 : Ω → ℝ}
    (hX0 : Measurable X0) (x : ℝ) :
    Integrable (fun ω => strictLowerRayIndicator x (X0 ω)) P := by
  refine Integrable.of_mem_Icc 0 1 ?_ ?_
  · exact ((measurable_strictLowerRayIndicator x).comp hX0).aemeasurable
  · exact Filter.Eventually.of_forall fun ω => strictLowerRayIndicator_mem_Icc x (X0 ω)

lemma integral_lowerRayIndicator_comp_eq_cdf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X0 : Ω → ℝ} (hX0 : Measurable X0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hLaw : Measure.map X0 P = μ) (x : ℝ) :
    ∫ ω, lowerRayIndicator x (X0 ω) ∂P = ProbabilityTheory.cdf μ x := by
  let A : Set Ω := {ω | X0 ω ≤ x}
  have hA : MeasurableSet A := measurableSet_le hX0 measurable_const
  have hfun :
      (fun ω => lowerRayIndicator x (X0 ω)) =
        A.indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    simp [A, lowerRayIndicator, Set.indicator]
  rw [hfun]
  have hint :
      ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P = P.real A := by
    simpa using (integral_indicator_one (μ := P) hA)
  rw [hint]
  rw [ProbabilityTheory.cdf_eq_real]
  have hmap : (Measure.map X0 P) (Set.Iic x) = P A := by
    rw [Measure.map_apply hX0 measurableSet_Iic]
    rfl
  have hmeasure : P A = μ (Set.Iic x) := by
    rw [← hmap, hLaw]
  exact congrArg ENNReal.toReal hmeasure

lemma integral_strictLowerRayIndicator_comp_eq_cdfLeftLimit
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X0 : Ω → ℝ} (hX0 : Measurable X0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hLaw : Measure.map X0 P = μ) (x : ℝ) :
    ∫ ω, strictLowerRayIndicator x (X0 ω) ∂P = cdfLeftLimit μ x := by
  let A : Set Ω := {ω | X0 ω < x}
  have hA : MeasurableSet A := measurableSet_lt hX0 measurable_const
  have hfun :
      (fun ω => strictLowerRayIndicator x (X0 ω)) =
        A.indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    simp [A, strictLowerRayIndicator, Set.indicator]
  rw [hfun]
  have hint :
      ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P = P.real A := by
    simpa using (integral_indicator_one (μ := P) hA)
  rw [hint]
  have hmap : (Measure.map X0 P) (Set.Iio x) = P A := by
    rw [Measure.map_apply hX0 measurableSet_Iio]
    rfl
  have hmeasure : P A = μ (Set.Iio x) := by
    rw [← hmap, hLaw]
  have hreal : P.real A = (μ (Set.Iio x)).toReal := congrArg ENNReal.toReal hmeasure
  rw [hreal]
  have hμIio : μ (Set.Iio x) = ENNReal.ofReal (cdfLeftLimit μ x) := by
    have hst :=
      StieltjesFunction.measure_Iio (ProbabilityTheory.cdf μ)
        (ProbabilityTheory.tendsto_cdf_atBot μ) x
    rw [ProbabilityTheory.measure_cdf μ] at hst
    simpa [cdfLeftLimit] using hst
  rw [hμIio]
  exact ENNReal.toReal_ofReal (cdfLeftLimit_nonneg μ x)

/-- Generalized inverse of a CDF at level `p`. -/
def cdfQuantile (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ ProbabilityTheory.cdf μ x}

lemma cdfQuantile_set_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : p < 1) :
    ({x : ℝ | p ≤ ProbabilityTheory.cdf μ x} : Set ℝ).Nonempty := by
  rcases (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hp) |>.exists
    with ⟨x, hx⟩
  exact ⟨x, le_of_lt hx⟩

lemma cdfQuantile_set_bddBelow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 0 < p) :
    BddBelow ({x : ℝ | p ≤ ProbabilityTheory.cdf μ x} : Set ℝ) := by
  rcases (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hp) |>.exists
    with ⟨x0, hx0⟩
  refine ⟨x0, ?_⟩
  intro y hy
  by_contra hxy
  have hyx : y ≤ x0 := le_of_not_ge hxy
  have hmono : ProbabilityTheory.cdf μ y ≤ ProbabilityTheory.cdf μ x0 :=
    ProbabilityTheory.monotone_cdf μ hyx
  exact not_lt_of_ge (hy.trans hmono) hx0

lemma cdfQuantile_le_of_le_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p x : ℝ} (hp0 : 0 < p) (hpx : p ≤ ProbabilityTheory.cdf μ x) :
    cdfQuantile μ p ≤ x := by
  exact csInf_le (cdfQuantile_set_bddBelow μ hp0) hpx

lemma le_cdfQuantile_of_cdf_lt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p x : ℝ} (hp1 : p < 1) (hxp : ProbabilityTheory.cdf μ x < p) :
    x ≤ cdfQuantile μ p := by
  refine le_csInf (cdfQuantile_set_nonempty μ hp1) ?_
  intro y hy
  by_contra hxy
  have hyx : y ≤ x := le_of_not_ge hxy
  have hmono : ProbabilityTheory.cdf μ y ≤ ProbabilityTheory.cdf μ x :=
    ProbabilityTheory.monotone_cdf μ hyx
  exact not_lt_of_ge (hy.trans hmono) hxp

lemma cdfQuantile_cdf_ge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ ProbabilityTheory.cdf μ (cdfQuantile μ p) := by
  by_contra hpq
  have hlt : ProbabilityTheory.cdf μ (cdfQuantile μ p) < p := lt_of_not_ge hpq
  have hright : {y : ℝ | ProbabilityTheory.cdf μ y < p} ∈ 𝓝[≥] cdfQuantile μ p :=
    (ProbabilityTheory.cdf μ).right_continuous (cdfQuantile μ p) (Iio_mem_nhds hlt)
  rcases (mem_nhdsGE_iff_exists_Ico_subset.mp hright) with ⟨u, huq, hsub⟩
  rcases exists_lt_of_csInf_lt (cdfQuantile_set_nonempty μ hp1) huq with ⟨y, hyS, hyu⟩
  have hqy : cdfQuantile μ p ≤ y :=
    csInf_le (cdfQuantile_set_bddBelow μ hp0) hyS
  have hylt : ProbabilityTheory.cdf μ y < p := hsub ⟨hqy, hyu⟩
  exact not_lt_of_ge hyS hylt

lemma cdfLeftLimit_quantile_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℝ} (hp0 : 0 < p) :
    cdfLeftLimit μ (cdfQuantile μ p) ≤ p := by
  have hlim :
      Tendsto (ProbabilityTheory.cdf μ) (𝓝[<] cdfQuantile μ p)
        (𝓝 (cdfLeftLimit μ (cdfQuantile μ p))) := by
    simpa [cdfLeftLimit] using
      (ProbabilityTheory.monotone_cdf μ).tendsto_leftLim (cdfQuantile μ p)
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  by_contra hpy
  have hpy' : p ≤ ProbabilityTheory.cdf μ y := le_of_not_ge hpy
  have hqy := cdfQuantile_le_of_le_cdf μ hp0 hpy'
  exact not_lt_of_ge hqy hy

/--
Finite atom-aware bracketing grid for real lower rays.

For every real probability law and positive mesh `ε`, there is a finite set of
thresholds such that each lower ray is bracketed either by a lower tail, an
upper tail, or by a closed lower grid ray and a strict upper grid ray. The
strict upper side is necessary at atoms: the population gap is measured with
the CDF left limit at the upper threshold.
-/
theorem finiteLowerRayBracketingGrid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set ℝ, G.Finite ∧ G.Nonempty ∧
      ∀ x : ℝ,
        (∃ b ∈ G, x < b ∧ cdfLeftLimit μ b ≤ ε) ∨
        (∃ a ∈ G, a ≤ x ∧ 1 - ProbabilityTheory.cdf μ a ≤ ε) ∨
        (∃ a ∈ G, ∃ b ∈ G,
          a ≤ x ∧ x < b ∧ cdfLeftLimit μ b - ProbabilityTheory.cdf μ a ≤ ε) := by
  classical
  rcases exists_nat_one_div_lt hε with ⟨n, hnε⟩
  let N : ℕ := n + 1
  let D : ℝ := (N + 1 : ℕ)
  let G : Set ℝ :=
    {q : ℝ | ∃ k : ℕ, k < N ∧
      q = cdfQuantile μ (((k + 1 : ℕ) : ℝ) / D)}
  have hDpos : 0 < D := by positivity
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hdeltaε : 1 / D < ε := by
    have hdenpos : 0 < ((n : ℝ) + 1) := by positivity
    have hdenle : ((n : ℝ) + 1) ≤ D := by
      dsimp [D, N]
      norm_num
    exact lt_of_le_of_lt (one_div_le_one_div_of_le hdenpos hdenle) hnε
  have hdelta_pos : 0 < 1 / D := by positivity
  have hdelta_lt_one : 1 / D < 1 := by
    have hDgt1 : (1 : ℝ) < D := by
      dsimp [D, N]
      norm_num
      positivity
    exact (div_lt_iff₀ hDpos).2 (by simpa using hDgt1)
  refine ⟨G, ?_, ?_, ?_⟩
  · have hG :
        G = (fun k : ℕ => cdfQuantile μ (((k + 1 : ℕ) : ℝ) / D)) ''
          {k : ℕ | k < N} := by
      ext q
      constructor
      · rintro ⟨k, hk, hq⟩
        exact ⟨k, hk, hq.symm⟩
      · rintro ⟨k, hk, hq⟩
        exact ⟨k, hk, hq.symm⟩
    rw [hG]
    exact (Set.finite_lt_nat N).image _
  · refine ⟨cdfQuantile μ (1 / D), ?_⟩
    refine ⟨0, by simp [N], ?_⟩
    simp
  · intro x
    let y : ℝ := ProbabilityTheory.cdf μ x
    have hy0 : 0 ≤ y := by simpa [y] using ProbabilityTheory.cdf_nonneg μ x
    by_cases hlow : y < 1 / D
    · left
      let b : ℝ := cdfQuantile μ (1 / D)
      have hbG : b ∈ G := by
        refine ⟨0, by simp [N], ?_⟩
        simp [b]
      have hb_cdf : (1 / D) ≤ ProbabilityTheory.cdf μ b :=
        cdfQuantile_cdf_ge μ hdelta_pos hdelta_lt_one
      have hxle : x ≤ b := by
        simpa [b, y] using le_cdfQuantile_of_cdf_lt μ hdelta_lt_one hlow
      have hxlt : x < b := by
        refine lt_of_le_of_ne hxle ?_
        intro hxb
        have hxlow : ProbabilityTheory.cdf μ x < 1 / D := by simpa [y] using hlow
        exact not_lt_of_ge (hxb ▸ hb_cdf) hxlow
      have hb_left : cdfLeftLimit μ b ≤ 1 / D := by
        simpa [b] using cdfLeftLimit_quantile_le μ hdelta_pos
      exact ⟨b, hbG, hxlt, hb_left.trans hdeltaε.le⟩
    · by_cases hhigh : 1 - 1 / D ≤ y
      · right
        left
        let a : ℝ := cdfQuantile μ (((n + 1 : ℕ) : ℝ) / D)
        have haG : a ∈ G := by
          refine ⟨n, by simp [N], ?_⟩
          simp [a]
        have hp_eq : (((n + 1 : ℕ) : ℝ) / D) = 1 - 1 / D := by
          dsimp [D, N]
          field_simp [hDne]
          norm_num
        have hp_pos : 0 < (((n + 1 : ℕ) : ℝ) / D) := by positivity
        have hp_lt_one : (((n + 1 : ℕ) : ℝ) / D) < 1 := by
          rw [hp_eq]
          linarith [hdelta_pos]
        have hpa : (((n + 1 : ℕ) : ℝ) / D) ≤ ProbabilityTheory.cdf μ a :=
          cdfQuantile_cdf_ge μ hp_pos hp_lt_one
        have hpx : (((n + 1 : ℕ) : ℝ) / D) ≤ ProbabilityTheory.cdf μ x := by
          rw [hp_eq]
          simpa [y] using hhigh
        have hax : a ≤ x := cdfQuantile_le_of_le_cdf μ hp_pos hpx
        have htail : 1 - ProbabilityTheory.cdf μ a ≤ 1 / D := by
          linarith [hpa, hp_eq]
        exact ⟨a, haG, hax, htail.trans hdeltaε.le⟩
      · right
        right
        have hlow_le : 1 / D ≤ y := le_of_not_gt hlow
        have hhigh_lt : y < 1 - 1 / D := lt_of_not_ge hhigh
        let k : ℕ := Nat.floor (y * D)
        have hyD_nonneg : 0 ≤ y * D := mul_nonneg hy0 hDpos.le
        have hyD_ge_one : ((1 : ℕ) : ℝ) ≤ y * D := by
          have hmul := mul_le_mul_of_nonneg_right hlow_le hDpos.le
          have hmul' : (1 : ℝ) ≤ y * D := by
            rwa [one_div_mul_cancel hDne] at hmul
          simpa using hmul'
        have hk_ge_one : 1 ≤ k := Nat.le_floor hyD_ge_one
        have hyD_lt_N : y * D < (N : ℝ) := by
          have hlt : y < ((N : ℝ) / D) := by
            have hNeq : ((N : ℝ) / D) = 1 - 1 / D := by
              dsimp [D]
              field_simp [hDne]
              norm_num
            simpa [hNeq] using hhigh_lt
          rwa [lt_div_iff₀ hDpos] at hlt
        have hk_lt_N : k < N := (Nat.floor_lt hyD_nonneg).2 hyD_lt_N
        let a : ℝ := cdfQuantile μ ((k : ℝ) / D)
        let b : ℝ := cdfQuantile μ (((k + 1 : ℕ) : ℝ) / D)
        have haG : a ∈ G := by
          refine ⟨k - 1, ?_, ?_⟩
          · omega
          · have hcast : (((k - 1 : ℕ) : ℝ) + 1) / D = (k : ℝ) / D := by
              rw [← Nat.cast_add_one, Nat.sub_add_cancel hk_ge_one]
            simp [a, hcast]
        have hbG : b ∈ G := by
          refine ⟨k, hk_lt_N, ?_⟩
          simp [b]
        have hk_div_pos : 0 < (k : ℝ) / D := by positivity
        have hk_div_lt_one : (k : ℝ) / D < 1 := by
          have hkD : (k : ℝ) < D := by
            have : (k : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hk_lt_N
            dsimp [D]
            exact this.trans_le (by norm_num)
          exact (div_lt_one hDpos).2 hkD
        have hka_cdf : (k : ℝ) / D ≤ ProbabilityTheory.cdf μ a :=
          cdfQuantile_cdf_ge μ hk_div_pos hk_div_lt_one
        have hk_le_yD : (k : ℝ) ≤ y * D := by
          simpa [k] using Nat.floor_le hyD_nonneg
        have hk_div_le_y : (k : ℝ) / D ≤ y := by
          rwa [div_le_iff₀ hDpos]
        have hax : a ≤ x := by
          exact cdfQuantile_le_of_le_cdf μ hk_div_pos (by simpa [a, y] using hk_div_le_y)
        have hkp1_div_pos : 0 < (((k + 1 : ℕ) : ℝ) / D) := by positivity
        have hkp1_div_lt_one : (((k + 1 : ℕ) : ℝ) / D) < 1 := by
          have hkp1_le_N : k + 1 ≤ N := Nat.succ_le_iff.mpr hk_lt_N
          have hltD : (((k + 1 : ℕ) : ℝ)) < D := by
            have hleN : (((k + 1 : ℕ) : ℝ)) ≤ (N : ℝ) :=
              Nat.cast_le.mpr hkp1_le_N
            dsimp [D]
            exact hleN.trans_lt (by norm_num)
          exact (div_lt_one hDpos).2 hltD
        have hb_cdf : (((k + 1 : ℕ) : ℝ) / D) ≤ ProbabilityTheory.cdf μ b :=
          cdfQuantile_cdf_ge μ hkp1_div_pos hkp1_div_lt_one
        have hyD_lt_kp1 : y * D < ((k + 1 : ℕ) : ℝ) := by
          simpa [k, Nat.cast_add_one] using Nat.lt_floor_add_one (y * D)
        have hy_lt_kp1_div : y < (((k + 1 : ℕ) : ℝ) / D) := by
          rwa [lt_div_iff₀ hDpos]
        have hxle_b : x ≤ b := by
          exact le_cdfQuantile_of_cdf_lt μ hkp1_div_lt_one
            (by simpa [b, y] using hy_lt_kp1_div)
        have hxlt_b : x < b := by
          refine lt_of_le_of_ne hxle_b ?_
          intro hxb
          have hxy : ProbabilityTheory.cdf μ x < (((k + 1 : ℕ) : ℝ) / D) := by
            simpa [y] using hy_lt_kp1_div
          exact not_lt_of_ge (hxb ▸ hb_cdf) hxy
        have hb_left : cdfLeftLimit μ b ≤ (((k + 1 : ℕ) : ℝ) / D) := by
          simpa [b] using cdfLeftLimit_quantile_le μ hkp1_div_pos
        have hgap_mesh :
            cdfLeftLimit μ b - ProbabilityTheory.cdf μ a ≤ 1 / D := by
          have hsub := sub_le_sub hb_left hka_cdf
          have hmesh : (((k + 1 : ℕ) : ℝ) / D) - (k : ℝ) / D = 1 / D := by
            rw [Nat.cast_add_one]
            ring
          exact hsub.trans (by rw [hmesh])
        exact ⟨a, haG, b, hbG, hax, hxlt_b, hgap_mesh.trans hdeltaε.le⟩

/-- Finite empirical average over a supplied sample-index finset. -/
def empiricalAverage {ι Ω : Type*} (s : Finset ι) (f : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ s, f i ω) / (s.card : ℝ)

/-- Empirical average of a function class member along a sample map. -/
def classEmpiricalAverage {ι Ω Z : Type*}
    (X : ι → Ω → Z) (s : Finset ι) (f : Z → ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ s, f (X i ω)) / (s.card : ℝ)

/-- Empirical CDF for a finite sample indexed by `s`. -/
def empiricalCDF {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (x : ℝ) : ℝ :=
  classEmpiricalAverage X s (lowerRayIndicator x) ω

/-- Strict empirical CDF for a finite sample indexed by `s`. -/
def strictEmpiricalCDF {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (x : ℝ) : ℝ :=
  classEmpiricalAverage X s (strictLowerRayIndicator x) ω

/-- The empirical CDF is exactly the empirical average of lower-ray indicators. -/
theorem empiricalCDF_eq_lowerRayEmpiricalAverage {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (x : ℝ) :
    empiricalCDF X s ω x =
      classEmpiricalAverage X s (lowerRayIndicator x) ω := rfl

/-- The strict empirical CDF is exactly the strict lower-ray empirical average. -/
theorem strictEmpiricalCDF_eq_strictLowerRayEmpiricalAverage {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (x : ℝ) :
    strictEmpiricalCDF X s ω x =
      classEmpiricalAverage X s (strictLowerRayIndicator x) ω := rfl

lemma lowerRayIndicator_mono {x y z : ℝ} (hxy : x ≤ y) :
    lowerRayIndicator x z ≤ lowerRayIndicator y z := by
  unfold lowerRayIndicator
  by_cases hx : z ≤ x
  · have hy : z ≤ y := hx.trans hxy
    simp [hx, hy]
  · simp [hx]
    split_ifs <;> norm_num

lemma lowerRayIndicator_le_strictLowerRayIndicator {x y z : ℝ} (hxy : x < y) :
    lowerRayIndicator x z ≤ strictLowerRayIndicator y z := by
  unfold lowerRayIndicator strictLowerRayIndicator
  by_cases hx : z ≤ x
  · have hy : z < y := lt_of_le_of_lt hx hxy
    simp [hx, hy]
  · simp [hx]
    split_ifs <;> norm_num

lemma strictLowerRayIndicator_mono {x y z : ℝ} (hxy : x ≤ y) :
    strictLowerRayIndicator x z ≤ strictLowerRayIndicator y z := by
  unfold strictLowerRayIndicator
  by_cases hx : z < x
  · have hy : z < y := hx.trans_le hxy
    simp [hx, hy]
  · simp [hx]
    split_ifs <;> norm_num

lemma empiricalCDF_mono {ι Ω : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (ω : Ω) {x y : ℝ} (hxy : x ≤ y) :
    empiricalCDF X s ω x ≤ empiricalCDF X s ω y := by
  unfold empiricalCDF classEmpiricalAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun i _ => lowerRayIndicator_mono hxy))
    (Nat.cast_nonneg s.card)

lemma empiricalCDF_le_strictEmpiricalCDF {ι Ω : Type*} (X : ι → Ω → ℝ)
    (s : Finset ι) (ω : Ω) {x y : ℝ} (hxy : x < y) :
    empiricalCDF X s ω x ≤ strictEmpiricalCDF X s ω y := by
  unfold empiricalCDF strictEmpiricalCDF classEmpiricalAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun i _ => lowerRayIndicator_le_strictLowerRayIndicator hxy))
    (Nat.cast_nonneg s.card)

lemma strictEmpiricalCDF_mono {ι Ω : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (ω : Ω) {x y : ℝ} (hxy : x ≤ y) :
    strictEmpiricalCDF X s ω x ≤ strictEmpiricalCDF X s ω y := by
  unfold strictEmpiricalCDF classEmpiricalAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun i _ => strictLowerRayIndicator_mono hxy))
    (Nat.cast_nonneg s.card)

lemma empiricalCDF_nonneg {ι Ω : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (ω : Ω) (x : ℝ) : 0 ≤ empiricalCDF X s ω x := by
  unfold empiricalCDF classEmpiricalAverage
  exact div_nonneg
    (Finset.sum_nonneg (fun i _ => (lowerRayIndicator_mem_Icc x (X i ω)).1))
    (Nat.cast_nonneg s.card)

lemma empiricalCDF_le_one {ι Ω : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (ω : Ω) (x : ℝ) : empiricalCDF X s ω x ≤ 1 := by
  unfold empiricalCDF classEmpiricalAverage
  by_cases hs : s.card = 0
  · simp [hs]
  · have hspos : 0 < (s.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hsum :
        ∑ i ∈ s, lowerRayIndicator x (X i ω) ≤ (s.card : ℝ) := by
      calc
        ∑ i ∈ s, lowerRayIndicator x (X i ω) ≤ ∑ i ∈ s, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => (lowerRayIndicator_mem_Icc x (X i ω)).2)
        _ = (s.card : ℝ) := by simp
    rw [div_le_iff₀ hspos]
    simpa using hsum

lemma strictEmpiricalCDF_nonneg {ι Ω : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (ω : Ω) (x : ℝ) : 0 ≤ strictEmpiricalCDF X s ω x := by
  unfold strictEmpiricalCDF classEmpiricalAverage
  exact div_nonneg
    (Finset.sum_nonneg (fun i _ => (strictLowerRayIndicator_mem_Icc x (X i ω)).1))
    (Nat.cast_nonneg s.card)

lemma strictEmpiricalCDF_le_one {ι Ω : Type*} (X : ι → Ω → ℝ) (s : Finset ι)
    (ω : Ω) (x : ℝ) : strictEmpiricalCDF X s ω x ≤ 1 := by
  unfold strictEmpiricalCDF classEmpiricalAverage
  by_cases hs : s.card = 0
  · simp [hs]
  · have hspos : 0 < (s.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
    have hsum :
        ∑ i ∈ s, strictLowerRayIndicator x (X i ω) ≤ (s.card : ℝ) := by
      calc
        ∑ i ∈ s, strictLowerRayIndicator x (X i ω) ≤ ∑ i ∈ s, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => (strictLowerRayIndicator_mem_Icc x (X i ω)).2)
        _ = (s.card : ℝ) := by simp
    rw [div_le_iff₀ hspos]
    simpa using hsum

/--
Deterministic bracketing bound for lower rays.

If every point in a finite atom-aware grid has closed- and strict-lower-ray
empirical deviation at most `η`, then every lower ray has empirical-CDF
deviation at most `2 * η`.
-/
theorem lowerRayBracketing_uniformDeviation_bound {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {G : Set ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hBrackets :
      ∀ x : ℝ,
        (∃ b ∈ G, x < b ∧ cdfLeftLimit μ b ≤ η) ∨
        (∃ a ∈ G, a ≤ x ∧ 1 - ProbabilityTheory.cdf μ a ≤ η) ∨
        (∃ a ∈ G, ∃ b ∈ G,
          a ≤ x ∧ x < b ∧ cdfLeftLimit μ b - ProbabilityTheory.cdf μ a ≤ η))
    (hClosed :
      ∀ a ∈ G, |empiricalCDF X s ω a - ProbabilityTheory.cdf μ a| ≤ η)
    (hStrict :
      ∀ b ∈ G, |strictEmpiricalCDF X s ω b - cdfLeftLimit μ b| ≤ η) :
    ∀ x : ℝ, |empiricalCDF X s ω x - ProbabilityTheory.cdf μ x| ≤ 2 * η := by
  intro x
  have hE_nonneg : 0 ≤ empiricalCDF X s ω x := empiricalCDF_nonneg X s ω x
  have hE_le_one : empiricalCDF X s ω x ≤ 1 := empiricalCDF_le_one X s ω x
  have hF_nonneg : 0 ≤ ProbabilityTheory.cdf μ x := ProbabilityTheory.cdf_nonneg μ x
  have hF_le_one : ProbabilityTheory.cdf μ x ≤ 1 := ProbabilityTheory.cdf_le_one μ x
  refine abs_le.2 ?_
  rcases hBrackets x with hlow | hupper | hmiddle
  · rcases hlow with ⟨b, hbG, hxb, hbLeft⟩
    have hF_le_left : ProbabilityTheory.cdf μ x ≤ cdfLeftLimit μ b := by
      simpa [cdfLeftLimit] using (ProbabilityTheory.monotone_cdf μ).le_leftLim hxb
    have hE_le_strict : empiricalCDF X s ω x ≤ strictEmpiricalCDF X s ω b :=
      empiricalCDF_le_strictEmpiricalCDF X s ω hxb
    have hStrict_b := abs_le.mp (hStrict b hbG)
    have hStrict_upper : strictEmpiricalCDF X s ω b - cdfLeftLimit μ b ≤ η :=
      hStrict_b.2
    constructor <;> linarith
  · rcases hupper with ⟨a, haG, hax, haTail⟩
    have hFa_le_Fx : ProbabilityTheory.cdf μ a ≤ ProbabilityTheory.cdf μ x :=
      ProbabilityTheory.monotone_cdf μ hax
    have hEa_le_Ex : empiricalCDF X s ω a ≤ empiricalCDF X s ω x :=
      empiricalCDF_mono X s ω hax
    have hClosed_a := abs_le.mp (hClosed a haG)
    constructor <;> linarith
  · rcases hmiddle with ⟨a, haG, b, hbG, hax, hxb, hgap⟩
    have hF_le_left : ProbabilityTheory.cdf μ x ≤ cdfLeftLimit μ b := by
      simpa [cdfLeftLimit] using (ProbabilityTheory.monotone_cdf μ).le_leftLim hxb
    have hFa_le_Fx : ProbabilityTheory.cdf μ a ≤ ProbabilityTheory.cdf μ x :=
      ProbabilityTheory.monotone_cdf μ hax
    have hEa_le_Ex : empiricalCDF X s ω a ≤ empiricalCDF X s ω x :=
      empiricalCDF_mono X s ω hax
    have hEx_le_Sb : empiricalCDF X s ω x ≤ strictEmpiricalCDF X s ω b :=
      empiricalCDF_le_strictEmpiricalCDF X s ω hxb
    have hClosed_a := abs_le.mp (hClosed a haG)
    have hStrict_b := abs_le.mp (hStrict b hbG)
    constructor <;> linarith

/--
Uniform deviation of an abstract empirical process over a class `F`, using an
explicit population functional. This avoids baking integrability into the
definition and matches the way the existing finite-class probability wrappers
accept externally supplied risks.
-/
def gcClassUniformDeviation {ι Ω Z H : Type*}
    (F : H → Z → ℝ) (population : H → ℝ)
    (X : ι → Ω → Z) (s : Finset ι) (ω : Ω) : ℝ :=
  sSup {r : ℝ | ∃ h : H, r = |classEmpiricalAverage X s (F h) ω - population h|}

/-- Uniform empirical-CDF deviation, written as a lower-ray class deviation. -/
def empiricalCDFUniformDeviation {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (μ : Measure ℝ) : ℝ :=
  gcClassUniformDeviation lowerRayIndicator (fun x : ℝ => ProbabilityTheory.cdf μ x) X s ω

/-- The empirical-CDF uniform deviation is nonnegative. -/
lemma empiricalCDFUniformDeviation_nonneg {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    0 ≤ empiricalCDFUniformDeviation X s ω μ := by
  let S : Set ℝ :=
    {r : ℝ | ∃ x : ℝ,
      r = |classEmpiricalAverage X s (lowerRayIndicator x) ω -
        ProbabilityTheory.cdf μ x|}
  have hBdd : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro r ⟨x, rfl⟩
    have hE0 : 0 ≤ empiricalCDF X s ω x := empiricalCDF_nonneg X s ω x
    have hE1 : empiricalCDF X s ω x ≤ 1 := empiricalCDF_le_one X s ω x
    have hF0 : 0 ≤ ProbabilityTheory.cdf μ x := ProbabilityTheory.cdf_nonneg μ x
    have hF1 : ProbabilityTheory.cdf μ x ≤ 1 := ProbabilityTheory.cdf_le_one μ x
    have hAbs :
        |empiricalCDF X s ω x - ProbabilityTheory.cdf μ x| ≤ 1 := by
      exact abs_le.2 (by constructor <;> linarith)
    simpa [empiricalCDF] using hAbs
  have hmem :
      |classEmpiricalAverage X s (lowerRayIndicator 0) ω -
        ProbabilityTheory.cdf μ 0| ∈ S := by
    exact ⟨0, rfl⟩
  have hnonneg :
      0 ≤ |classEmpiricalAverage X s (lowerRayIndicator 0) ω -
        ProbabilityTheory.cdf μ 0| := abs_nonneg _
  exact hnonneg.trans (le_csSup hBdd hmem)

/-- A pointwise empirical-CDF deviation bound bounds the `sSup` uniform deviation. -/
lemma empiricalCDFUniformDeviation_le_of_forall {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (μ : Measure ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hPointwise :
      ∀ x : ℝ, |empiricalCDF X s ω x - ProbabilityTheory.cdf μ x| ≤ C) :
    empiricalCDFUniformDeviation X s ω μ ≤ C := by
  unfold empiricalCDFUniformDeviation gcClassUniformDeviation
  exact Real.sSup_le (by
    rintro r ⟨x, rfl⟩
    simpa using hPointwise x) hC

/-- Empirical-CDF uniform deviation is the lower-ray GC-class deviation. -/
theorem empiricalCDFUniformDeviation_eq_gcClassUniformDeviation {ι Ω : Type*}
    (X : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) (μ : Measure ℝ) :
    empiricalCDFUniformDeviation X s ω μ =
      gcClassUniformDeviation lowerRayIndicator
        (fun x : ℝ => ProbabilityTheory.cdf μ x) X s ω := rfl

/--
An indexed class is Glivenko-Cantelli along `X` when the uniform empirical
process over `Finset.range n` converges almost surely to zero.
-/
def IsGCClass {Ω Z H : Type*} [MeasurableSpace Ω]
    (F : H → Z → ℝ) (population : H → ℝ)
    (X : ℕ → Ω → Z) (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P,
    Tendsto
      (fun n : ℕ => gcClassUniformDeviation F population X (Finset.range n) ω)
      atTop (𝓝 0)

/-- Classical empirical-CDF Glivenko-Cantelli statement in this module's notation. -/
def ClassicalGlivenkoCantelli {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) (μ : Measure ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    Tendsto
      (fun n : ℕ => empiricalCDFUniformDeviation X (Finset.range n) ω μ)
      atTop (𝓝 0)

/--
The classical empirical-CDF GC statement is exactly the GC-class statement for
the lower-ray indicator class. This is the measure-theory/statistics-to-SLT
bridge: the index `x : ℝ` in the CDF is the hypothesis/class index in uniform
convergence.
-/
theorem lowerRayGC_iff_classicalGlivenkoCantelli {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) (μ : Measure ℝ) :
    IsGCClass lowerRayIndicator (fun x : ℝ => ProbabilityTheory.cdf μ x) X P ↔
      ClassicalGlivenkoCantelli X P μ := by
  rfl

/--
Classical Glivenko-Cantelli uniformization from pointwise convergence on closed
and strict lower rays.

The proof uses `finiteLowerRayBracketingGrid` at countably many mesh sizes,
intersects the corresponding a.s. events, and then applies the deterministic
bracketing bound. The strict lower-ray hypotheses are the atom-safe upper
brackets.
-/
theorem classicalGlivenkoCantelli_of_pointwise_lowerRay {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : ℕ → Ω → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hClosed :
      ∀ x : ℝ,
        ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ => empiricalCDF X (Finset.range n) ω x)
            atTop (𝓝 (ProbabilityTheory.cdf μ x)))
    (hStrict :
      ∀ x : ℝ,
        ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ => strictEmpiricalCDF X (Finset.range n) ω x)
            atTop (𝓝 (cdfLeftLimit μ x))) :
    ClassicalGlivenkoCantelli X P μ := by
  have hBasis :
      ∀ m : ℕ,
        ∀ᵐ ω ∂P,
          ∀ᶠ n : ℕ in atTop,
            empiricalCDFUniformDeviation X (Finset.range n) ω μ <
              1 / ((m : ℝ) + 1) := by
    intro m
    let α : ℝ := 1 / ((m : ℝ) + 1)
    let η : ℝ := α / 4
    have hα_pos : 0 < α := by
      dsimp [α]
      positivity
    have hη_pos : 0 < η := by
      dsimp [η]
      positivity
    rcases finiteLowerRayBracketingGrid μ hη_pos with ⟨G, hGfinite, _, hBrackets⟩
    have hClosedAE :
        ∀ᵐ ω ∂P,
          ∀ a ∈ G,
            Tendsto (fun n : ℕ => empiricalCDF X (Finset.range n) ω a)
              atTop (𝓝 (ProbabilityTheory.cdf μ a)) :=
      hGfinite.eventually_all.2 fun a _ => hClosed a
    have hStrictAE :
        ∀ᵐ ω ∂P,
          ∀ b ∈ G,
            Tendsto (fun n : ℕ => strictEmpiricalCDF X (Finset.range n) ω b)
              atTop (𝓝 (cdfLeftLimit μ b)) :=
      hGfinite.eventually_all.2 fun b _ => hStrict b
    filter_upwards [hClosedAE, hStrictAE] with ω hClosedω hStrictω
    have hClosedEventually :
        ∀ a ∈ G,
          ∀ᶠ n : ℕ in atTop,
            |empiricalCDF X (Finset.range n) ω a - ProbabilityTheory.cdf μ a| ≤ η := by
      intro a haG
      exact ((Metric.tendsto_nhds.mp (hClosedω a haG)) η hη_pos).mono
        (fun n hn => by
          simpa [Real.dist_eq] using le_of_lt hn)
    have hStrictEventually :
        ∀ b ∈ G,
          ∀ᶠ n : ℕ in atTop,
            |strictEmpiricalCDF X (Finset.range n) ω b - cdfLeftLimit μ b| ≤ η := by
      intro b hbG
      exact ((Metric.tendsto_nhds.mp (hStrictω b hbG)) η hη_pos).mono
        (fun n hn => by
          simpa [Real.dist_eq] using le_of_lt hn)
    have hClosedAll :
        ∀ᶠ n : ℕ in atTop,
          ∀ a ∈ G,
            |empiricalCDF X (Finset.range n) ω a - ProbabilityTheory.cdf μ a| ≤ η :=
      hGfinite.eventually_all.2 hClosedEventually
    have hStrictAll :
        ∀ᶠ n : ℕ in atTop,
          ∀ b ∈ G,
            |strictEmpiricalCDF X (Finset.range n) ω b - cdfLeftLimit μ b| ≤ η :=
      hGfinite.eventually_all.2 hStrictEventually
    filter_upwards [hClosedAll, hStrictAll] with n hClosedN hStrictN
    have hPointwise :
        ∀ x : ℝ,
          |empiricalCDF X (Finset.range n) ω x - ProbabilityTheory.cdf μ x| ≤ 2 * η :=
      lowerRayBracketing_uniformDeviation_bound X (Finset.range n) ω μ hη_pos.le
        hBrackets hClosedN hStrictN
    have hUniform :
        empiricalCDFUniformDeviation X (Finset.range n) ω μ ≤ 2 * η :=
      empiricalCDFUniformDeviation_le_of_forall X (Finset.range n) ω μ
        (by positivity) hPointwise
    have hTwoEta_lt : 2 * η < α := by
      dsimp [η]
      linarith [hα_pos]
    exact lt_of_le_of_lt hUniform hTwoEta_lt
  exact (ae_all_iff.2 hBasis).mono fun ω hω =>
    tendsto_order.2
      ⟨fun a ha =>
        Filter.Eventually.of_forall fun n =>
          lt_of_lt_of_le ha
            (empiricalCDFUniformDeviation_nonneg X (Finset.range n) ω μ),
       fun a ha => by
        rcases exists_nat_one_div_lt ha with ⟨m, hm⟩
        exact (hω m).mono fun n hn => lt_trans hn (by simpa using hm)⟩

/--
Pointwise empirical-CDF strong law for a fixed lower ray.

This is the classical-statistics input available directly from mathlib's
strong law: for each fixed threshold `x`, the empirical CDF at `x` converges
almost surely to the population mass of that lower ray. The uncountable
uniformization over all `x` is the remaining full Glivenko-Cantelli step.
-/
theorem lowerRayPointwiseStrongLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : ℕ → Ω → ℝ) (x : ℝ)
    (hIntegrable : Integrable (fun ω => lowerRayIndicator x (X 0 ω)) P)
    (hIndep :
      Pairwise
        ((· ⟂ᵢ[P] ·) on
          (fun n : ℕ => fun ω : Ω => lowerRayIndicator x (X n ω))))
    (hIdent :
      ∀ i,
        IdentDistrib
          (fun ω : Ω => lowerRayIndicator x (X i ω))
          (fun ω : Ω => lowerRayIndicator x (X 0 ω)) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => empiricalCDF X (Finset.range n) ω x)
        atTop (𝓝 (∫ ω, lowerRayIndicator x (X 0 ω) ∂P)) := by
  simpa [empiricalCDF, classEmpiricalAverage, Finset.card_range] using
    ProbabilityTheory.strong_law_ae_real
      (μ := P)
      (X := fun n : ℕ => fun ω : Ω => lowerRayIndicator x (X n ω))
      hIntegrable hIndep hIdent

/--
Pointwise strong law for a fixed strict lower ray.

This is the open-upper-bracket companion to `lowerRayPointwiseStrongLaw`;
atoms force the full Glivenko-Cantelli uniformization to use these strict
upper rays and CDF left limits.
-/
theorem strictLowerRayPointwiseStrongLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : ℕ → Ω → ℝ) (x : ℝ)
    (hIntegrable : Integrable (fun ω => strictLowerRayIndicator x (X 0 ω)) P)
    (hIndep :
      Pairwise
        ((· ⟂ᵢ[P] ·) on
          (fun n : ℕ => fun ω : Ω => strictLowerRayIndicator x (X n ω))))
    (hIdent :
      ∀ i,
        IdentDistrib
          (fun ω : Ω => strictLowerRayIndicator x (X i ω))
          (fun ω : Ω => strictLowerRayIndicator x (X 0 ω)) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => strictEmpiricalCDF X (Finset.range n) ω x)
        atTop (𝓝 (∫ ω, strictLowerRayIndicator x (X 0 ω) ∂P)) := by
  simpa [strictEmpiricalCDF, classEmpiricalAverage, Finset.card_range] using
    ProbabilityTheory.strong_law_ae_real
      (μ := P)
      (X := fun n : ℕ => fun ω : Ω => strictLowerRayIndicator x (X n ω))
      hIntegrable hIndep hIdent

/--
Classical Glivenko-Cantelli theorem for i.i.d. real samples.

If the sample coordinates are independent and identically distributed with
common law `μ`, then the empirical CDF converges uniformly almost surely to the
CDF of `μ`.
-/
theorem classicalGlivenkoCantelli_iid {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hX : ∀ n : ℕ, Measurable (X n))
    (hLaw : Measure.map (X 0) P = μ)
    (hIndep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hIdent : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P) :
    ClassicalGlivenkoCantelli X P μ := by
  refine classicalGlivenkoCantelli_of_pointwise_lowerRay X μ ?_ ?_
  · intro x
    have hIntegrable : Integrable (fun ω => lowerRayIndicator x (X 0 ω)) P :=
      integrable_lowerRayIndicator_comp (P := P) (hX 0) x
    have hIndepClosed :
        Pairwise
          ((· ⟂ᵢ[P] ·) on
            (fun n : ℕ => fun ω : Ω => lowerRayIndicator x (X n ω))) := by
      intro i j hij
      simpa [Function.comp_def] using
        (hIndep hij).comp (measurable_lowerRayIndicator x) (measurable_lowerRayIndicator x)
    have hIdentClosed :
        ∀ i,
          IdentDistrib
            (fun ω : Ω => lowerRayIndicator x (X i ω))
            (fun ω : Ω => lowerRayIndicator x (X 0 ω)) P P := by
      intro i
      simpa [Function.comp_def] using (hIdent i).comp (measurable_lowerRayIndicator x)
    have hIntEq :
        ∫ ω, lowerRayIndicator x (X 0 ω) ∂P = ProbabilityTheory.cdf μ x :=
      integral_lowerRayIndicator_comp_eq_cdf (P := P) (X0 := X 0) (hX 0) μ hLaw x
    exact (lowerRayPointwiseStrongLaw X x hIntegrable hIndepClosed hIdentClosed).mono
      fun _ hω => by
        simpa [hIntEq] using hω
  · intro x
    have hIntegrable : Integrable (fun ω => strictLowerRayIndicator x (X 0 ω)) P :=
      integrable_strictLowerRayIndicator_comp (P := P) (hX 0) x
    have hIndepStrict :
        Pairwise
          ((· ⟂ᵢ[P] ·) on
            (fun n : ℕ => fun ω : Ω => strictLowerRayIndicator x (X n ω))) := by
      intro i j hij
      simpa [Function.comp_def] using
        (hIndep hij).comp
          (measurable_strictLowerRayIndicator x) (measurable_strictLowerRayIndicator x)
    have hIdentStrict :
        ∀ i,
          IdentDistrib
            (fun ω : Ω => strictLowerRayIndicator x (X i ω))
            (fun ω : Ω => strictLowerRayIndicator x (X 0 ω)) P P := by
      intro i
      simpa [Function.comp_def] using (hIdent i).comp (measurable_strictLowerRayIndicator x)
    have hIntEq :
        ∫ ω, strictLowerRayIndicator x (X 0 ω) ∂P = cdfLeftLimit μ x :=
      integral_strictLowerRayIndicator_comp_eq_cdfLeftLimit (P := P) (X0 := X 0)
        (hX 0) μ hLaw x
    exact (strictLowerRayPointwiseStrongLaw X x hIntegrable hIndepStrict hIdentStrict).mono
      fun _ hω => by
        simpa [hIntEq] using hω

/--
Finite-class uniform-convergence bridge: pointwise two-sided deviation tails
imply a simultaneous finite-class empirical-process bad-event bound.
-/
theorem finiteClassUniformConvergenceBridge
    {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype H]
    (deviation : H → Ω → ℝ) {ε : ℝ} {pointwiseTail : ℝ≥0∞}
    (hPointwiseTail : ∀ h, μ {ω | ε ≤ |deviation h ω|} ≤ pointwiseTail) :
    μ (⋃ h, {ω | ε ≤ |deviation h ω|}) ≤ Fintype.card H • pointwiseTail :=
  FormalSLT.UniformConvergence.finiteClassTwoSidedUniformDeviationUnionBound
    deviation hPointwiseTail

/-- VC/Hoeffding finite-class zero-one bridge already proved in `UniformConvergence`. -/
theorem vcHoeffdingBridge_for_gcClass
    {Ω ι H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ} [Fintype H] [Nonempty H]
    {loss : Fin T → H → ι → Ω → ℝ}
    (hIndep : ∀ t h, iIndepFun (loss t h) μ)
    {s : Finset ι}
    {risk : Fin T → H → ℝ} {δ_real : ℝ}
    (hMeas :
      ∀ t h i, i ∈ s → AEMeasurable (loss t h i) μ)
    (hBound01 :
      ∀ t h i, i ∈ s →
        ∀ᵐ ω ∂μ, loss t h i ω ∈ Set.Icc (0 : ℝ) 1)
    (hRisk : ∀ t h, risk t h = ∑ i ∈ s, μ[loss t h i])
    (hNonemptySample : 0 < s.card)
    (hδ_real_pos : 0 < δ_real)
    (hδ_real_lt :
      δ_real < (2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) :
    μ (⋃ p : Fin T × H,
        {ω |
          √(Real.log
              (((2 : ℝ) ^ (T + 1) * (Fintype.card H : ℝ)) /
                δ_real) /
            (2 * (s.card : ℝ))) ≤
            |risk p.1 p.2 / (s.card : ℝ) -
              (∑ i ∈ s, loss p.1 p.2 i ω) / (s.card : ℝ)|}) ≤
      ENNReal.ofReal δ_real :=
  FormalSLT.UniformConvergence.finitePrefixFiniteClassDeviationFromHoeffding_zeroOneRange_explicitRadius
    hIndep hMeas hBound01 hRisk hNonemptySample hδ_real_pos hδ_real_lt

/-- Rademacher ERM learnability bridge already proved in the finite-class Rademacher lane. -/
theorem rademacherERMBridge_for_gcClass
    {ι Z : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Z] {μ : Measure Z}
    [Nonempty Z] [StandardBorelSpace Z] [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ} {B : ℝ} (hB : 0 < B)
    (hℓ_meas : ∀ i, Measurable (ℓ i))
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    {n : ℕ} (hn : 0 < n)
    (hCard : 1 < Fintype.card ι)
    (hhat : (Fin n → Z) → ι)
    (hERM : ∀ S : Fin n → Z, IsERM (empiricalRisk S ℓ) (hhat S))
    (i_star : ι)
    (hOracle : ∀ i : ι, risk μ ℓ i_star ≤ risk μ ℓ i)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (piMeasure μ n).real
        {S | 4 * B * Real.sqrt (2 * Real.log (Fintype.card ι : ℝ) / (n : ℝ))
              + 2 * ε
            ≤ risk μ ℓ (hhat S) - risk μ ℓ i_star}
      ≤ 2 * Real.exp (- ε ^ 2 * ↑n / (2 * B ^ 2)) :=
  FormalSLT.Rademacher.ERMGeneralization.rademacher_erm_excessRisk_tail
    hB hℓ_meas hℓ_bdd hn hCard hhat hERM i_star hOracle hε

/-- VC/PAC-Bayes hybrid learnability bridge already proved in the PAC-Bayes lane. -/
theorem vcPacBayesHybridBridge_for_gcClass
    {Ω ι Z : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype ι] [Nonempty ι]
    {ρ π : ι → ℝ} (hρ : IsPMF ρ)
    (vcBad : Finset Ω)
    {lambda scale delta B : ℝ} {n d : ℕ}
    {ℓ : ι → Z → ℝ} (sample : Ω → Fin n → Z)
    (hB : 0 < B) (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hGrowth : ∀ ω', (effectiveClass ℓ (sample ω')).card ≤
      ∑ k ∈ Finset.range (d + 1), n.choose k)
    (empiricalAnchor : Ω → ℝ)
    (riskFn : ι → ℝ) (empiricalRiskFn : Ω → ι → ℝ)
    (varianceProxy : ι → ℝ) (ω : Ω)
    (hRadGood : ∀ ω', ω' ∉ vcBad →
      posteriorEmpiricalRisk ρ (empiricalRiskFn ω') ≤ empiricalAnchor ω' +
        2 * empiricalRademacherComplexity ℓ (sample ω'))
    (hω :
      ω ∉ vcPacBayesHybridBadSamples vcBad π lambda scale delta
        riskFn empiricalRiskFn varianceProxy) :
    posteriorRisk ρ riskFn ≤
      empiricalAnchor ω +
        vcCapacityTerm B n d +
        (klDiv ρ π + Real.log (1 / delta)) / lambda +
        lambda * posteriorMarginVarianceProxy ρ varianceProxy /
          (2 * (1 - scale * lambda)) :=
  FormalSLT.PACBayes.VCHybrid.vcPacBayesBernsteinPosteriorRisk_bound_from_vcRademacher
    hρ vcBad sample hB hℓ_bdd hn hd hdn hGrowth empiricalAnchor
    riskFn empiricalRiskFn varianceProxy ω hRadGood hω

/-! ## Concrete Bernoulli witness -/

/-- CDF of the Bernoulli distribution with mass `1/2` at `0` and `1/2` at `1`. -/
def bernoulliHalfCDF (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x < 1 then (1 / 2 : ℝ) else 1

/-- Empirical CDF of the concrete four-point sample `[0, 0, 0, 1]`. -/
def bernoulliThreeZerosOneOneSampleCDF (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x < 1 then (3 / 4 : ℝ) else 1

/--
The concrete Bernoulli sample `[0, 0, 0, 1]` has uniform CDF deviation at most
`1/4` from the Bernoulli-`1/2` CDF.
-/
theorem bernoulliThreeZerosOneOne_uniformDeviation_le_quarter :
    ∀ x : ℝ,
      |bernoulliThreeZerosOneOneSampleCDF x - bernoulliHalfCDF x| ≤ (1 / 4 : ℝ) := by
  intro x
  unfold bernoulliThreeZerosOneOneSampleCDF bernoulliHalfCDF
  by_cases hx0 : x < 0
  · simp [hx0]
  · by_cases hx1 : x < 1
    · simp [hx0, hx1]
      norm_num
    · simp [hx0, hx1]

end

end FormalSLT.GlivenkoCantelli
