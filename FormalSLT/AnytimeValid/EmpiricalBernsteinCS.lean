/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.MixtureCS
import FormalSLT.Concentration.SubGamma.CondExpProduct

/-!
# Empirical-Bernstein confidence sequences

This file adds the variance-adaptive exponential process

`M_n = exp (lambda * S_n - psi(lambda) * V_n)`,

where `S_n` is the running sum of centered increments and `V_n` is a
predictable running conditional-second-moment proxy.  The one-step ingredient is
a Bernstein conditional MGF bound with a random predictable variance proxy.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- Bernstein cumulant multiplier for a predictable variance proxy. -/
def empiricalBernsteinCgf (b lam : ℝ) : ℝ :=
  lam ^ 2 / (2 * (1 - b * lam / 3))

/-- Running predictable variance proxy. -/
def runningVarianceProxy {Ω : Type*} (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.range n) fun i => V i ω

/-- Fixed-tilt empirical-Bernstein exponential process. -/
def empiricalBernsteinExponentialProcess {Ω : Type*}
    (X V : ℕ → Ω → ℝ) (b lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp
    (lam * runningSum X n ω - empiricalBernsteinCgf b lam * runningVarianceProxy V n ω)

/-- Prior mixture of empirical-Bernstein exponential processes. -/
def empiricalBernsteinMixtureProcess {Ω : Type*} [MeasurableSpace Ω]
    (X V : ℕ → Ω → ℝ) (b : ℝ) (ρ : Measure ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ lam, empiricalBernsteinExponentialProcess X V b lam n ω ∂ρ

/--
Closed fixed-tilt upper boundary written with a generic log-budget `ell`.

The usual confidence form uses `ell = Real.log (1 / delta)`.
-/
def empiricalBernsteinClosedFormBoundary
    (varianceSum cgf ell n lam : ℝ) : ℝ :=
  cgf * varianceSum / (n * lam) + ell / (n * lam)

/-- Fixed-lambda empirical-Bernstein upper failure event. -/
def empiricalBernsteinUpperFailure {Ω : Type*}
    (X V : ℕ → Ω → ℝ) (b lam delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧
    empiricalBernsteinCgf b lam * runningVarianceProxy V n ω / ((n : ℝ) * lam)
      + Real.log (1 / delta) / ((n : ℝ) * lam)
      ≤ runningMean X n ω}

lemma empiricalBernsteinCgf_nonneg {b lam : ℝ}
    (_hlam : 0 ≤ lam) (hblam : b * lam < 3) :
    0 ≤ empiricalBernsteinCgf b lam := by
  unfold empiricalBernsteinCgf
  have hden : 0 < 2 * (1 - b * lam / 3) := by
    have hpos : 0 < 1 - b * lam / 3 := by linarith
    exact mul_pos (by norm_num) hpos
  exact div_nonneg (sq_nonneg lam) hden.le

lemma runningVarianceProxy_nonneg {Ω : Type*} {V : ℕ → Ω → ℝ}
    (hV_nonneg : ∀ k, 0 ≤ V k) (n : ℕ) (ω : Ω) :
    0 ≤ runningVarianceProxy V n ω := by
  unfold runningVarianceProxy
  exact Finset.sum_nonneg fun i _ => hV_nonneg i ω

/-- Product measurability of the parameterized empirical-Bernstein process. -/
theorem measurable_empiricalBernsteinExponentialProcess_prod {Ω : Type*} [MeasurableSpace Ω]
    (X V : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ)
    (hX_meas : ∀ k, Measurable (X k)) (hV_meas : ∀ k, Measurable (V k)) :
    Measurable
      (fun p : ℝ × Ω => empiricalBernsteinExponentialProcess X V b p.1 n p.2) := by
  unfold empiricalBernsteinExponentialProcess runningSum runningVarianceProxy empiricalBernsteinCgf
  fun_prop
    (disch := first
      | intro i _; exact (hX_meas i).comp measurable_snd
      | intro i _; exact (hV_meas i).comp measurable_snd)

/-- Each fixed-tilt empirical-Bernstein process is adapted once `X` and `V` are adapted. -/
theorem stronglyAdapted_empiricalBernsteinExponentialProcess_of_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} (b lam : ℝ)
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V) :
    StronglyAdapted ℱ (empiricalBernsteinExponentialProcess X V b lam) := by
  intro n
  have hsumX : StronglyMeasurable[ℱ n] (fun ω => runningSum X n ω) := by
    have hrw : (fun ω => runningSum X n ω) = ∑ i ∈ Finset.range n, X i := by
      funext ω
      simp [runningSum, Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact (hX_adapted i).mono (ℱ.mono (le_of_lt hi))
  have hsumV : StronglyMeasurable[ℱ n] (fun ω => runningVarianceProxy V n ω) := by
    have hrw : (fun ω => runningVarianceProxy V n ω) = ∑ i ∈ Finset.range n, V i := by
      funext ω
      simp [runningVarianceProxy, Finset.sum_apply]
    rw [hrw]
    apply Finset.stronglyMeasurable_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact (hV_adapted i).mono (ℱ.mono (le_of_lt hi))
  have hbody : StronglyMeasurable[ℱ n]
      (fun ω =>
        lam * runningSum X n ω - empiricalBernsteinCgf b lam * runningVarianceProxy V n ω) :=
    (hsumX.const_mul lam).sub (hsumV.const_mul (empiricalBernsteinCgf b lam))
  exact Real.continuous_exp.comp_stronglyMeasurable hbody

/--
Random-proxy conditional Bernstein MGF.

If the conditional second moment is bounded by a predictable proxy `V`, then
the conditional MGF is bounded by `exp (psi(lambda) * V)`.
-/
theorem condBernsteinMGF_of_bounded_centered_condVarianceProxy
    {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}
    {X V : Ω → ℝ}
    {b : ℝ}
    (hb_pos : 0 < b)
    (hX_meas : Measurable[m₀] X)
    (hX_int : Integrable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hcenter : μ[X | m] =ᵐ[μ] 0)
    (hvar : μ[fun ω => X ω ^ 2 | m] ≤ᵐ[μ] V) :
    ∀ lam, 0 ≤ lam → b * lam < 3 →
      μ[fun ω => Real.exp (lam * X ω) | m]
        ≤ᵐ[μ]
      fun ω => Real.exp (empiricalBernsteinCgf b lam * V ω) := by
  intro lam hlam hblam
  set K : ℝ := 2 * (1 - b * lam / 3) with hK_def
  have hK_pos : 0 < K := by
    have hpos : 0 < 1 - b * lam / 3 := by linarith
    exact mul_pos (by norm_num) hpos
  by_cases hm : m ≤ m₀
  swap
  · rw [condExp_of_not_le hm]
    exact ae_of_all _ fun _ => (Real.exp_pos _).le
  have h_pw :
      (fun ω => Real.exp (lam * X ω))
        ≤ᵐ[μ]
      (fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K) := by
    filter_upwards [hbound] with ω hω
    have hxlo : -b ≤ X ω := (abs_le.mp hω).1
    have hxhi : X ω ≤ b := (abs_le.mp hω).2
    have h := FormalSLT.Concentration.SubGamma.bennett_taylor_bound
      (x := X ω) (b := b) (lam := lam) hb_pos hlam hblam hxlo hxhi
    simpa [hK_def] using h
  have h_exp_int : Integrable (fun ω => Real.exp (lam * X ω)) μ :=
    FormalSLT.Concentration.SubGamma.integrable_exp_mul_of_bounded hX_meas hbound
  have hXsq_int : Integrable (fun ω => X ω ^ 2) μ := by
    refine MeasureTheory.Integrable.mono' (g := fun _ => b ^ 2)
      (integrable_const _) (hX_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, ← sq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hRHS_int :
      Integrable (fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K) μ := by
    have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
    have h2 : Integrable (fun ω => lam * X ω) μ := hX_int.const_mul lam
    have h3 : Integrable (fun ω => lam ^ 2 * X ω ^ 2 / K) μ := by
      have := (hXsq_int.const_mul (lam ^ 2)).div_const K
      simpa [mul_div_assoc] using this
    exact (h1.add h2).add h3
  have h_mono :
      μ[fun ω => Real.exp (lam * X ω) | m]
        ≤ᵐ[μ]
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m] :=
    condExp_mono h_exp_int hRHS_int h_pw
  have hrewrite :
      (fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K) =
      ((fun _ : Ω => (1 : ℝ)) + fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2) := by
    funext ω
    simp only [Pi.add_apply]
    ring_nf
  have h_const_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  have h_lin_int : Integrable (fun ω => lam * X ω) μ := hX_int.const_mul lam
  have h_quad_int : Integrable (fun ω => lam ^ 2 / K * X ω ^ 2) μ :=
    hXsq_int.const_mul _
  have h_lin_plus_quad_int :
      Integrable (fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2) μ :=
    h_lin_int.add h_quad_int
  have h_step1 := condExp_add (μ := μ) h_const_int h_lin_plus_quad_int m
  have h_step2 := condExp_add (μ := μ) h_lin_int h_quad_int m
  have h_const : μ[(fun _ : Ω => (1 : ℝ)) | m] = fun _ => 1 := condExp_const hm 1
  have h_smul_lin := condExp_smul (𝕜 := ℝ) (μ := μ) (m := m) lam X
  have h_smul_quad :=
    condExp_smul (𝕜 := ℝ) (μ := μ) (m := m) (lam ^ 2 / K) (fun ω => X ω ^ 2)
  have h_lin_eq : μ[fun ω => lam * X ω | m] =ᵐ[μ] fun ω => lam * (μ[X | m]) ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using h_smul_lin
  have h_quad_eq :
      μ[fun ω => lam ^ 2 / K * X ω ^ 2 | m]
        =ᵐ[μ] fun ω => lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using h_smul_quad
  have h_sum_eq :
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m]
        =ᵐ[μ]
      μ[(fun _ : Ω => (1 : ℝ)) | m] + μ[fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2 | m] := by
    rw [hrewrite]
    exact h_step1
  have h_sum_eq2 :
      μ[fun ω => lam * X ω + lam ^ 2 / K * X ω ^ 2 | m]
        =ᵐ[μ]
      μ[fun ω => lam * X ω | m] + μ[fun ω => lam ^ 2 / K * X ω ^ 2 | m] := h_step2
  have h_lin :
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m]
        =ᵐ[μ]
      fun ω => 1 + lam * (μ[X | m]) ω + lam ^ 2 / K * (μ[fun ω => X ω ^ 2 | m]) ω := by
    filter_upwards [h_sum_eq, h_sum_eq2, h_lin_eq, h_quad_eq] with ω hs1 hs2 hle hqe
    simp only [Pi.add_apply] at hs1 hs2
    rw [hs1, hs2, h_const, hle, hqe]
    ring
  have hlamK_nonneg : 0 ≤ lam ^ 2 / K := div_nonneg (sq_nonneg _) hK_pos.le
  have h_bound :
      μ[fun ω => 1 + lam * X ω + lam ^ 2 * X ω ^ 2 / K | m]
        ≤ᵐ[μ]
      fun ω => 1 + lam ^ 2 / K * V ω := by
    filter_upwards [h_lin, hcenter, hvar] with ω h_lin' h_ctr' h_var'
    rw [h_lin']
    have h_ctr'' : (μ[X | m]) ω = 0 := by simpa using h_ctr'
    rw [h_ctr'', mul_zero, add_zero]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_left h_var' hlamK_nonneg) 1
  refine (h_mono.trans h_bound).trans ?_
  refine ae_of_all _ fun ω => ?_
  have hsame : lam ^ 2 / K * V ω = empiricalBernsteinCgf b lam * V ω := by
    simp [empiricalBernsteinCgf, hK_def]
  calc
    (fun ω => 1 + lam ^ 2 / K * V ω) ω
        ≤ Real.exp (lam ^ 2 / K * V ω) := by
          simpa [add_comm] using Real.add_one_le_exp (lam ^ 2 / K * V ω)
    _ = (fun ω => Real.exp (empiricalBernsteinCgf b lam * V ω)) ω := by rw [hsame]

/-- Pointwise upper bound for the variance-adapted exponential process. -/
theorem empiricalBernsteinExponentialProcess_le_of_bound {Ω : Type*}
    (X V : ℕ → Ω → ℝ) (b lam : ℝ) (n : ℕ) (ω : Ω)
    (hlam : 0 ≤ lam) (hblam : b * lam < 3)
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ i ∈ Finset.range n, |X i ω| ≤ b) :
    empiricalBernsteinExponentialProcess X V b lam n ω ≤ Real.exp (lam * (n : ℝ) * b) := by
  unfold empiricalBernsteinExponentialProcess
  apply Real.exp_le_exp.2
  have hsum_le : runningSum X n ω ≤ (n : ℝ) * b := by
    have hle : ∀ i ∈ Finset.range n, X i ω ≤ b := fun i hi => (abs_le.mp (hbound i hi)).2
    calc runningSum X n ω = Finset.sum (Finset.range n) (fun i => X i ω) := rfl
      _ ≤ Finset.sum (Finset.range n) (fun _ => b) := Finset.sum_le_sum hle
      _ = (n : ℝ) * b := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcgf_nonneg : 0 ≤ empiricalBernsteinCgf b lam :=
    empiricalBernsteinCgf_nonneg hlam hblam
  have hvar_nonneg : 0 ≤ runningVarianceProxy V n ω :=
    runningVarianceProxy_nonneg hV_nonneg n ω
  have hpenalty : 0 ≤ empiricalBernsteinCgf b lam * runningVarianceProxy V n ω :=
    mul_nonneg hcgf_nonneg hvar_nonneg
  have hlS : lam * runningSum X n ω ≤ lam * ((n : ℝ) * b) :=
    mul_le_mul_of_nonneg_left hsum_le hlam
  nlinarith

/-- Integrability of the fixed-tilt empirical-Bernstein process from bounded increments. -/
theorem integrable_empiricalBernsteinExponentialProcess
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X V : ℕ → Ω → ℝ} {b lam : ℝ} (n : ℕ)
    (hlam : 0 ≤ lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hV_meas : ∀ k, Measurable (V k))
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b) :
    Integrable (empiricalBernsteinExponentialProcess X V b lam n) μ := by
  refine Integrable.of_bound ?_ (Real.exp (lam * (n : ℝ) * b)) ?_
  · have hmeas :
        Measurable (fun ω => empiricalBernsteinExponentialProcess X V b lam n ω) := by
      unfold empiricalBernsteinExponentialProcess runningSum runningVarianceProxy empiricalBernsteinCgf
      fun_prop (disch := first | intro i _; exact hX_meas i | intro i _; exact hV_meas i)
    exact hmeas.aestronglyMeasurable
  · have hX : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, |X i ω| ≤ b := by
      have hall : ∀ᵐ ω ∂μ, ∀ k, |X k ω| ≤ b := ae_all_iff.2 hbound
      filter_upwards [hall] with ω hω i _ using hω i
    filter_upwards [hX] with ω hω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold empiricalBernsteinExponentialProcess; exact (Real.exp_pos _).le)]
    exact empiricalBernsteinExponentialProcess_le_of_bound X V b lam n ω
      hlam hblam hV_nonneg hω

/--
The variance-adapted exponential process is a supermartingale under the
bounded, centered, conditional-second-moment model.
-/
theorem empiricalBernstein_exponential_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} {b lam : ℝ}
    (hb : 0 < b) (hlam : 0 ≤ lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hV_meas : ∀ k, Measurable (V k))
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V)
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] V k) :
    Supermartingale (empiricalBernsteinExponentialProcess X V b lam) ℱ μ := by
  refine supermartingale_nat
    (stronglyAdapted_empiricalBernsteinExponentialProcess_of_adapted b lam hX_adapted hV_adapted)
    ?_ ?_
  · intro n
    exact integrable_empiricalBernsteinExponentialProcess
      (μ := μ) (X := X) (V := V) (b := b) (lam := lam) n
      hlam hblam hX_meas hV_meas hV_nonneg hbound
  · intro n
    set cgf : ℝ := empiricalBernsteinCgf b lam with hcgf_def
    set Z : Ω → ℝ :=
      fun ω => empiricalBernsteinExponentialProcess X V b lam n ω * Real.exp (-cgf * V n ω)
      with hZ_def
    set Y : Ω → ℝ := fun ω => Real.exp (lam * X n ω) with hY_def
    have hfact :
        empiricalBernsteinExponentialProcess X V b lam (n + 1) =
          fun ω => Z ω * Y ω := by
      funext ω
      simp only [empiricalBernsteinExponentialProcess, runningSum, runningVarianceProxy,
        Finset.sum_range_succ, hZ_def, hY_def]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hZ_meas : StronglyMeasurable[ℱ n] Z := by
      have hM :=
        (stronglyAdapted_empiricalBernsteinExponentialProcess_of_adapted
          (ℱ := ℱ) b lam hX_adapted hV_adapted n)
      have hVn := hV_adapted n
      have hbody : StronglyMeasurable[ℱ n] (fun ω => -cgf * V n ω) :=
        hVn.const_mul (-cgf)
      exact hM.mul (Real.continuous_exp.comp_stronglyMeasurable hbody)
    have hcgf_nonneg : 0 ≤ cgf := by simpa [hcgf_def] using empiricalBernsteinCgf_nonneg hlam hblam
    set C : ℝ := Real.exp (lam * (n : ℝ) * b) with hC_def
    have hZ_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ C := by
      filter_upwards [ae_all_iff.2 hbound] with ω hω
      have hM_le : empiricalBernsteinExponentialProcess X V b lam n ω ≤
          Real.exp (lam * (n : ℝ) * b) :=
        empiricalBernsteinExponentialProcess_le_of_bound X V b lam n ω
          hlam hblam hV_nonneg (fun i hi => hω i)
      have hexp_le_one : Real.exp (-cgf * V n ω) ≤ 1 := by
        have hnonpos : -cgf * V n ω ≤ 0 := by
          have hmul : 0 ≤ cgf * V n ω := mul_nonneg hcgf_nonneg (hV_nonneg n ω)
          nlinarith
        exact (Real.exp_le_one_iff).2 hnonpos
      have hZnonneg : 0 ≤ Z ω :=
        mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      rw [abs_of_nonneg hZnonneg, hZ_def, hC_def]
      calc
        empiricalBernsteinExponentialProcess X V b lam n ω * Real.exp (-cgf * V n ω)
            ≤ Real.exp (lam * (n : ℝ) * b) * Real.exp (-cgf * V n ω) :=
              mul_le_mul_of_nonneg_right hM_le (Real.exp_pos _).le
        _ ≤ Real.exp (lam * (n : ℝ) * b) * 1 :=
              mul_le_mul_of_nonneg_left hexp_le_one (Real.exp_pos _).le
        _ = Real.exp (lam * (n : ℝ) * b) := by ring
    have hY_int : Integrable Y μ :=
      FormalSLT.Concentration.SubGamma.integrable_exp_mul_of_bounded (hX_meas n) (hbound n)
    have hpull :
        μ[fun ω => Z ω * Y ω | ℱ n] =ᵐ[μ] fun ω => Z ω * (μ[Y | ℱ n]) ω :=
      FormalSLT.Concentration.SubGamma.condExp_mul_bounded_left (ℱ.le n) hZ_meas hZ_bdd hY_int
    have hmgf : μ[Y | ℱ n] ≤ᵐ[μ] fun ω => Real.exp (cgf * V n ω) := by
      have h :=
        condBernsteinMGF_of_bounded_centered_condVarianceProxy
          hb (hX_meas n) (hX_int n) (hbound n) (hcenter n) (hvar n) lam hlam hblam
      simpa [hY_def, hcgf_def] using h
    rw [hfact]
    filter_upwards [hpull, hmgf] with ω hpull' hmgf'
    rw [hpull']
    have hZnonneg : 0 ≤ Z ω :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    calc
      Z ω * (μ[Y | ℱ n]) ω
          ≤ Z ω * Real.exp (cgf * V n ω) :=
            mul_le_mul_of_nonneg_left hmgf' hZnonneg
      _ = empiricalBernsteinExponentialProcess X V b lam n ω := by
        rw [hZ_def]
        rw [mul_assoc, ← Real.exp_add]
        simp

/--
The fixed-lambda empirical-Bernstein failure event is contained in the
corresponding exponential crossing event.
-/
theorem empiricalBernsteinUpperFailure_subset_exponential_crossing
    {Ω : Type*} {X V : ℕ → Ω → ℝ} {b lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam) :
    empiricalBernsteinUpperFailure X V b lam delta
      ⊆
    atTopCrossingEvent (empiricalBernsteinExponentialProcess X V b lam) (1 / delta) := by
  intro ω hω
  rcases hω with ⟨n, hn_pos, hn_boundary⟩
  refine ⟨n, ?_⟩
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hden_pos : 0 < (n : ℝ) * lam := mul_pos (Nat.cast_pos.mpr hn_pos) hlam
  have hmul := mul_le_mul_of_nonneg_left hn_boundary hden_pos.le
  have hlog_le :
      Real.log (1 / delta)
        ≤ lam * runningSum X n ω
          - empiricalBernsteinCgf b lam * runningVarianceProxy V n ω := by
    rw [runningMean] at hmul
    field_simp [hn_ne, hlam_ne] at hmul
    nlinarith
  have hdelta_inv_pos : 0 < 1 / delta := one_div_pos.mpr hδ
  rw [← Real.exp_log hdelta_inv_pos]
  exact Real.exp_le_exp.2 hlog_le

/-- Fixed-lambda anytime-valid empirical-Bernstein confidence sequence. -/
theorem empiricalBernstein_time_uniform_confidence_sequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} {b lam delta : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hV_meas : ∀ k, Measurable (V k))
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V)
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] V k) :
    μ.real (empiricalBernsteinUpperFailure X V b lam delta) ≤ delta := by
  have hsup :=
    empiricalBernstein_exponential_supermartingale
      (μ := μ) (ℱ := ℱ) (X := X) (V := V) (b := b) (lam := lam)
      hb hlam.le hblam hX_meas hX_int hV_meas hX_adapted hV_adapted hV_nonneg
      hbound hcenter hvar
  have hnonneg : 0 ≤ empiricalBernsteinExponentialProcess X V b lam :=
    fun _ _ => (Real.exp_pos _).le
  have ha : 0 < 1 / delta := one_div_pos.mpr hδ
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ)
      (M := empiricalBernsteinExponentialProcess X V b lam)
      hsup hnonneg ha
  have hM0 : ∫ ω, empiricalBernsteinExponentialProcess X V b lam 0 ω ∂μ = 1 := by
    have hbody :
        (fun ω => empiricalBernsteinExponentialProcess X V b lam 0 ω) =ᵐ[μ]
          fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => by
        simp [empiricalBernsteinExponentialProcess, runningSum, runningVarianceProxy]
    rw [integral_congr_ae hbody]
    simp [integral_const]
  rw [hM0] at hville
  have h_atTop :
      μ.real
        (atTopCrossingEvent (empiricalBernsteinExponentialProcess X V b lam) (1 / delta))
        ≤ delta := by
    calc
      μ.real
          (atTopCrossingEvent (empiricalBernsteinExponentialProcess X V b lam) (1 / delta))
          = delta *
            ((1 / delta) *
              μ.real
                (atTopCrossingEvent
                  (empiricalBernsteinExponentialProcess X V b lam) (1 / delta))) := by
            field_simp [hδ.ne']
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
      _ = delta := by ring
  exact (measureReal_mono
    (empiricalBernsteinUpperFailure_subset_exponential_crossing
      (X := X) (V := V) (b := b) (lam := lam) (delta := delta) hδ hlam)).trans h_atTop

/-- Product integrability for the empirical-Bernstein process under the uniform tilt prior. -/
theorem integrable_empiricalBernsteinExponentialProcess_prod_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X V : ℕ → Ω → ℝ} {b lam0 lam1 : ℝ} (n : ℕ)
    (hb : 0 < b) (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam1)
    (hlam1 : b * lam1 < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hV_meas : ∀ k, Measurable (V k))
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b) :
    Integrable
      (fun p : ℝ × Ω => empiricalBernsteinExponentialProcess X V b p.1 n p.2)
      ((uniformTiltPrior lam0 lam1).prod μ) := by
  haveI : IsProbabilityMeasure (uniformTiltPrior lam0 lam1) :=
    uniformTiltPrior_isProbabilityMeasure h01
  refine Integrable.of_bound ?_ (Real.exp (lam1 * (n : ℝ) * b)) ?_
  · have hmeas :=
      measurable_empiricalBernsteinExponentialProcess_prod X V b n hX_meas hV_meas
    exact hmeas.aestronglyMeasurable
  · have hlam_mem : ∀ᵐ p : ℝ × Ω ∂((uniformTiltPrior lam0 lam1).prod μ),
        p.1 ∈ Set.Icc lam0 lam1 :=
      (Measure.quasiMeasurePreserving_fst).ae uniformTiltPrior_ae_mem_Icc
    have hX : ∀ᵐ p : ℝ × Ω ∂((uniformTiltPrior lam0 lam1).prod μ),
        ∀ i ∈ Finset.range n, |X i p.2| ≤ b := by
      have h1 : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, |X i ω| ≤ b := by
        have hall : ∀ᵐ ω ∂μ, ∀ k, |X k ω| ≤ b := ae_all_iff.2 hbound
        filter_upwards [hall] with ω hω i _ using hω i
      exact (Measure.quasiMeasurePreserving_snd).ae h1
    filter_upwards [hlam_mem, hX] with p hp hpX
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold empiricalBernsteinExponentialProcess; exact (Real.exp_pos _).le)]
    have hlam0' : 0 ≤ p.1 := hlam0.trans hp.1
    have hlam1' : p.1 ≤ lam1 := hp.2
    have hblam' : b * p.1 < 3 := by
      have hle : b * p.1 ≤ b * lam1 := mul_le_mul_of_nonneg_left hlam1' hb.le
      exact lt_of_le_of_lt hle hlam1
    have hbase := empiricalBernsteinExponentialProcess_le_of_bound X V b p.1 n p.2
      hlam0' hblam' hV_nonneg hpX
    have hcoef : 0 ≤ (n : ℝ) * b := mul_nonneg (Nat.cast_nonneg n) hb.le
    have harg : p.1 * (n : ℝ) * b ≤ lam1 * (n : ℝ) * b := by
      have hmul := mul_le_mul_of_nonneg_right hlam1' hcoef
      nlinarith
    exact hbase.trans (Real.exp_le_exp.2 harg)

/-- Product integrability in the `Ω × ℝ` orientation for the uniform tilt prior. -/
theorem integrable_empiricalBernsteinExponentialProcess_omegaProd_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {X V : ℕ → Ω → ℝ} {b lam0 lam1 : ℝ} (n : ℕ)
    (hb : 0 < b) (hlam0 : 0 ≤ lam0) (h01 : lam0 < lam1)
    (hlam1 : b * lam1 < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hV_meas : ∀ k, Measurable (V k))
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ k, ∀ᵐ ω ∂ν, |X k ω| ≤ b) :
    Integrable
      (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 n p.1)
      (ν.prod (uniformTiltPrior lam0 lam1)) := by
  haveI : IsProbabilityMeasure (uniformTiltPrior lam0 lam1) :=
    uniformTiltPrior_isProbabilityMeasure h01
  refine Integrable.of_bound ?_ (Real.exp (lam1 * (n : ℝ) * b)) ?_
  · have hmeas :
        Measurable
          (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 n p.1) := by
      unfold empiricalBernsteinExponentialProcess runningSum runningVarianceProxy empiricalBernsteinCgf
      fun_prop
        (disch := first
          | intro i _; exact (hX_meas i).comp measurable_fst
          | intro i _; exact (hV_meas i).comp measurable_fst)
    exact hmeas.aestronglyMeasurable
  · have hlam_mem : ∀ᵐ p : Ω × ℝ ∂(ν.prod (uniformTiltPrior lam0 lam1)),
        p.2 ∈ Set.Icc lam0 lam1 :=
      (Measure.quasiMeasurePreserving_snd).ae uniformTiltPrior_ae_mem_Icc
    have hX : ∀ᵐ p : Ω × ℝ ∂(ν.prod (uniformTiltPrior lam0 lam1)),
        ∀ i ∈ Finset.range n, |X i p.1| ≤ b := by
      have h1 : ∀ᵐ ω ∂ν, ∀ i ∈ Finset.range n, |X i ω| ≤ b := by
        have hall : ∀ᵐ ω ∂ν, ∀ k, |X k ω| ≤ b := ae_all_iff.2 hbound
        filter_upwards [hall] with ω hω i _ using hω i
      exact (Measure.quasiMeasurePreserving_fst).ae h1
    filter_upwards [hlam_mem, hX] with p hp hpX
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by unfold empiricalBernsteinExponentialProcess; exact (Real.exp_pos _).le)]
    have hlam0' : 0 ≤ p.2 := hlam0.trans hp.1
    have hlam1' : p.2 ≤ lam1 := hp.2
    have hblam' : b * p.2 < 3 := by
      have hle : b * p.2 ≤ b * lam1 := mul_le_mul_of_nonneg_left hlam1' hb.le
      exact lt_of_le_of_lt hle hlam1
    have hbase := empiricalBernsteinExponentialProcess_le_of_bound X V b p.2 n p.1
      hlam0' hblam' hV_nonneg hpX
    have hcoef : 0 ≤ (n : ℝ) * b := mul_nonneg (Nat.cast_nonneg n) hb.le
    have harg : p.2 * (n : ℝ) * b ≤ lam1 * (n : ℝ) * b := by
      have hmul := mul_le_mul_of_nonneg_right hlam1' hcoef
      nlinarith
    exact hbase.trans (Real.exp_le_exp.2 harg)

/-- Product strong measurability of the parameterized empirical-Bernstein process. -/
theorem stronglyMeasurable_filtration_prod_empiricalBernstein
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} (b : ℝ) (n : ℕ)
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V) :
    StronglyMeasurable[(ℱ n).prod (inferInstance : MeasurableSpace ℝ)]
      (Function.uncurry (fun ω lam => empiricalBernsteinExponentialProcess X V b lam n ω)) := by
  rw [stronglyMeasurable_iff_measurable]
  unfold Function.uncurry empiricalBernsteinExponentialProcess runningSum runningVarianceProxy
    empiricalBernsteinCgf
  have hXmeas : ∀ i ∈ Finset.range n,
      Measurable[(ℱ n).prod (inferInstance : MeasurableSpace ℝ)]
        (fun p : Ω × ℝ => X i p.1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hXi : Measurable[ℱ n] (X i) := by
      rw [← stronglyMeasurable_iff_measurable]
      exact (hX_adapted i).mono (ℱ.mono (le_of_lt hi))
    exact hXi.comp measurable_fst
  have hVmeas : ∀ i ∈ Finset.range n,
      Measurable[(ℱ n).prod (inferInstance : MeasurableSpace ℝ)]
        (fun p : Ω × ℝ => V i p.1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hVi : Measurable[ℱ n] (V i) := by
      rw [← stronglyMeasurable_iff_measurable]
      exact (hV_adapted i).mono (ℱ.mono (le_of_lt hi))
    exact hVi.comp measurable_fst
  apply Measurable.exp
  apply Measurable.sub
  · apply Measurable.mul
    · exact measurable_snd
    · exact Finset.measurable_sum _ hXmeas
  · apply Measurable.mul
    · apply Measurable.div
      · exact measurable_snd.pow_const 2
      · apply Measurable.const_mul
        apply Measurable.const_sub
        apply Measurable.div_const
        apply Measurable.const_mul
        exact measurable_snd
    · exact Finset.measurable_sum _ hVmeas

/-- The prior integral is adapted once `X` and `V` are adapted. -/
theorem stronglyAdapted_empiricalBernsteinMixtureProcess_of_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} (b : ℝ) (ρ : Measure ℝ) [SFinite ρ]
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V) :
    StronglyAdapted ℱ (empiricalBernsteinMixtureProcess X V b ρ) := by
  intro n
  have hjoint :=
    stronglyMeasurable_filtration_prod_empiricalBernstein
      (ℱ := ℱ) (X := X) (V := V) b n hX_adapted hV_adapted
  show StronglyMeasurable[ℱ n]
    (fun ω => ∫ lam, empiricalBernsteinExponentialProcess X V b lam n ω ∂ρ)
  letI : MeasurableSpace Ω := ℱ n
  exact MeasureTheory.StronglyMeasurable.integral_prod_right (ν := ρ) hjoint

/-- One mixture supermartingale step from fixed-tilt empirical-Bernstein steps. -/
theorem empiricalBernstein_mixture_condExp_step_of_fixed_tilt_steps
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} {b : ℝ} {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (h_adapted_mix : StronglyAdapted ℱ (empiricalBernsteinMixtureProcess X V b ρ))
    (h_integrable_mix : ∀ n, Integrable (empiricalBernsteinMixtureProcess X V b ρ n) μ)
    (hM_int_next :
      ∀ n, Integrable
        (fun p : ℝ × Ω => empiricalBernsteinExponentialProcess X V b p.1 (n + 1) p.2)
        (ρ.prod μ))
    (hM_int_next_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 (n + 1) p.1)
          ((μ.restrict s).prod ρ))
    (hM_int_current :
      ∀ n, Integrable
        (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 n p.1)
        (μ.prod ρ))
    (hM_int_current_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 n p.1)
          ((μ.restrict s).prod ρ))
    (hfixed_step :
      ∀ n, ∀ᵐ lam ∂ρ,
        μ[fun ω => empiricalBernsteinExponentialProcess X V b lam (n + 1) ω | ℱ n]
          ≤ᵐ[μ] fun ω => empiricalBernsteinExponentialProcess X V b lam n ω) :
    ∀ n,
      condExp (ℱ n) μ (empiricalBernsteinMixtureProcess X V b ρ (n + 1))
        ≤ᵐ[μ] empiricalBernsteinMixtureProcess X V b ρ n := by
  intro n
  refine ae_le_of_forall_subalgebra_setIntegral_le (ℱ.le n)
    integrable_condExp (h_integrable_mix n) stronglyMeasurable_condExp
    (h_adapted_mix n) ?_
  intro s hs hμs
  have hs₀ : MeasurableSet s := ℱ.le n s hs
  have hnext_restrict := hM_int_next_restrict n hs₀ hμs
  have hcurrent_restrict := hM_int_current_restrict n hs₀ hμs
  have hnext_fiber :
      ∀ᵐ lam ∂ρ,
        Integrable (fun ω => empiricalBernsteinExponentialProcess X V b lam (n + 1) ω) μ := by
    simpa using (hM_int_next n).prod_right_ae
  have hcurrent_fiber :
      ∀ᵐ lam ∂ρ,
        Integrable (fun ω => empiricalBernsteinExponentialProcess X V b lam n ω) μ := by
    simpa using (hM_int_current n).prod_left_ae
  calc
    ∫ ω in s,
        (condExp (ℱ n) μ (empiricalBernsteinMixtureProcess X V b ρ (n + 1))) ω ∂μ
        = ∫ ω in s, empiricalBernsteinMixtureProcess X V b ρ (n + 1) ω ∂μ := by
            exact setIntegral_condExp (ℱ.le n) (h_integrable_mix (n + 1)) hs
    _ = ∫ lam,
          ∫ ω in s, empiricalBernsteinExponentialProcess X V b lam (n + 1) ω ∂μ ∂ρ := by
            simpa [empiricalBernsteinMixtureProcess, Function.uncurry] using
              (integral_integral_swap (μ := μ.restrict s) (ν := ρ)
                (f := fun ω lam => empiricalBernsteinExponentialProcess X V b lam (n + 1) ω)
                hnext_restrict)
    _ ≤ ∫ lam,
          ∫ ω in s, empiricalBernsteinExponentialProcess X V b lam n ω ∂μ ∂ρ := by
            refine integral_mono_ae hnext_restrict.integral_prod_right
              hcurrent_restrict.integral_prod_right ?_
            filter_upwards [hfixed_step n, hnext_fiber, hcurrent_fiber] with
              lam hstep hnext_int hcurrent_int
            calc
              ∫ ω in s, empiricalBernsteinExponentialProcess X V b lam (n + 1) ω ∂μ
                  = ∫ ω in s,
                      (condExp (ℱ n) μ
                        (fun ω => empiricalBernsteinExponentialProcess X V b lam (n + 1) ω)) ω ∂μ := by
                      exact (setIntegral_condExp (ℱ.le n) hnext_int hs).symm
              _ ≤ ∫ ω in s, empiricalBernsteinExponentialProcess X V b lam n ω ∂μ := by
                      exact setIntegral_mono_ae integrable_condExp.integrableOn
                        hcurrent_int.integrableOn hstep
    _ = ∫ ω in s, empiricalBernsteinMixtureProcess X V b ρ n ω ∂μ := by
            simpa [empiricalBernsteinMixtureProcess, Function.uncurry] using
              (integral_integral_swap (μ := μ.restrict s) (ν := ρ)
                (f := fun ω lam => empiricalBernsteinExponentialProcess X V b lam n ω)
                hcurrent_restrict).symm

/-- The empirical-Bernstein mixture process is a nonnegative supermartingale. -/
theorem empiricalBernstein_mixture_is_supermartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} {b : ℝ} {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hb : 0 < b)
    (hsupport : ∀ᵐ lam ∂ρ, lam ∈ Set.Ioo 0 (3 / b))
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hV_meas : ∀ k, Measurable (V k))
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V)
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (h_adapted_mix : StronglyAdapted ℱ (empiricalBernsteinMixtureProcess X V b ρ))
    (h_integrable_mix : ∀ n, Integrable (empiricalBernsteinMixtureProcess X V b ρ n) μ)
    (hM_int :
      ∀ n, Integrable
        (fun p : ℝ × Ω => empiricalBernsteinExponentialProcess X V b p.1 (n + 1) p.2)
        (ρ.prod μ))
    (hM_int_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 (n + 1) p.1)
          ((μ.restrict s).prod ρ))
    (hM_int_step :
      ∀ n, Integrable
        (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 n p.1)
        (μ.prod ρ))
    (hM_int_step_restrict :
      ∀ n, ∀ {s : Set Ω}, MeasurableSet s → μ s < ⊤ →
        Integrable
          (fun p : Ω × ℝ => empiricalBernsteinExponentialProcess X V b p.2 n p.1)
          ((μ.restrict s).prod ρ))
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] V k) :
    Supermartingale (empiricalBernsteinMixtureProcess X V b ρ) ℱ μ
      ∧ ∀ n ω, 0 ≤ empiricalBernsteinMixtureProcess X V b ρ n ω := by
  have hfixed_step :
      ∀ n, ∀ᵐ lam ∂ρ,
        μ[fun ω => empiricalBernsteinExponentialProcess X V b lam (n + 1) ω | ℱ n]
          ≤ᵐ[μ] fun ω => empiricalBernsteinExponentialProcess X V b lam n ω := by
    intro n
    filter_upwards [hsupport] with lam hlam
    have hlam_nonneg : 0 ≤ lam := hlam.1.le
    have hblam : b * lam < 3 := by
      have hmul : b * lam < b * (3 / b) := mul_lt_mul_of_pos_left hlam.2 hb
      have hb_ne : b ≠ 0 := ne_of_gt hb
      have hcancel : b * (3 / b) = 3 := by field_simp [hb_ne]
      linarith
    have hsup :=
      empiricalBernstein_exponential_supermartingale
        (μ := μ) (ℱ := ℱ) (X := X) (V := V) (b := b) (lam := lam)
        hb hlam_nonneg hblam hX_meas hX_int hV_meas hX_adapted hV_adapted hV_nonneg
        hbound hcenter hvar
    exact hsup.condExp_ae_le (Nat.le_succ n)
  have h_cond_step :
      ∀ n,
        condExp (ℱ n) μ (empiricalBernsteinMixtureProcess X V b ρ (n + 1))
          ≤ᵐ[μ] empiricalBernsteinMixtureProcess X V b ρ n :=
    empiricalBernstein_mixture_condExp_step_of_fixed_tilt_steps
      (μ := μ) (ℱ := ℱ) (X := X) (V := V) (b := b) (ρ := ρ)
      h_adapted_mix h_integrable_mix hM_int hM_int_restrict hM_int_step
      hM_int_step_restrict hfixed_step
  refine ⟨supermartingale_nat h_adapted_mix h_integrable_mix h_cond_step, ?_⟩
  intro n ω
  exact integral_nonneg fun lam => (Real.exp_pos _).le

/--
Uniform-prior empirical-Bernstein mixture CS with product measurability and
integrability discharged from the bounded, nonnegative predictable-proxy model.
-/
theorem empiricalBernstein_confidence_sequence_uniformPrior
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X V : ℕ → Ω → ℝ} {b delta lam0 lam1 : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hlam0 : 0 < lam0) (h01 : lam0 < lam1) (hlam1 : lam1 < 3 / b)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (hV_meas : ∀ k, Measurable (V k))
    (hX_adapted : StronglyAdapted ℱ X) (hV_adapted : StronglyAdapted ℱ V)
    (hV_nonneg : ∀ k, 0 ≤ V k)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] V k) :
    μ.real {ω | ∃ n : ℕ, 0 < n ∧
      (1 / delta) ≤ empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1) n ω}
        ≤ delta := by
  haveI : IsProbabilityMeasure (uniformTiltPrior lam0 lam1) :=
    uniformTiltPrior_isProbabilityMeasure h01
  have hblam1 : b * lam1 < 3 := by
    have hmul : b * lam1 < b * (3 / b) := mul_lt_mul_of_pos_left hlam1 hb
    have hb_ne : b ≠ 0 := ne_of_gt hb
    have hcancel : b * (3 / b) = 3 := by field_simp [hb_ne]
    linarith
  have hsupport : ∀ᵐ lam ∂uniformTiltPrior lam0 lam1, lam ∈ Set.Ioo 0 (3 / b) :=
    uniformTiltPrior_valid_tilt_support hlam0 h01 hlam1
  have h_adapted_mix :
      StronglyAdapted ℱ (empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1)) :=
    stronglyAdapted_empiricalBernsteinMixtureProcess_of_adapted b _ hX_adapted hV_adapted
  have h_integrable_mix :
      ∀ n, Integrable (empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1) n) μ := by
    intro n
    have hprod :=
      integrable_empiricalBernsteinExponentialProcess_omegaProd_uniformPrior
        (ν := μ) (X := X) (V := V) (b := b)
        (lam0 := lam0) (lam1 := lam1) n hb hlam0.le h01 hblam1
        hX_meas hV_meas hV_nonneg hbound
    simpa [empiricalBernsteinMixtureProcess] using hprod.integral_prod_left
  have hsup : Supermartingale
      (empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1)) ℱ μ :=
    (empiricalBernstein_mixture_is_supermartingale
      (μ := μ) (ℱ := ℱ) (X := X) (V := V) (b := b)
      (ρ := uniformTiltPrior lam0 lam1)
      hb hsupport hX_meas hX_int hV_meas hX_adapted hV_adapted hV_nonneg
      h_adapted_mix h_integrable_mix
      ?_ ?_ ?_ ?_ hbound hcenter hvar).1
  · have hnonneg : 0 ≤ empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1) := by
      intro n ω
      exact integral_nonneg fun lam => (Real.exp_pos _).le
    have ha : 0 < 1 / delta := one_div_pos.mpr hδ
    have hville :=
      ville_atTop_maximal_ineq
        (μ := μ) (𝒢 := ℱ)
        (M := empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1))
        hsup hnonneg ha
    have hM0 :
        ∫ ω, empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1) 0 ω ∂μ = 1 := by
      have hbody :
          (fun ω => empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1) 0 ω)
            =ᵐ[μ] fun _ => (1 : ℝ) :=
        Filter.Eventually.of_forall fun ω => by
          simp [empiricalBernsteinMixtureProcess, empiricalBernsteinExponentialProcess,
            runningSum, runningVarianceProxy]
      rw [integral_congr_ae hbody]
      simp [integral_const]
    rw [hM0] at hville
    have h_atTop :
        μ.real
          (atTopCrossingEvent
            (empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1)) (1 / delta))
          ≤ delta := by
      calc
        μ.real
            (atTopCrossingEvent
              (empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1)) (1 / delta))
            = delta *
              ((1 / delta) *
                μ.real
                  (atTopCrossingEvent
                    (empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1))
                    (1 / delta))) := by
              field_simp [hδ.ne']
        _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
        _ = delta := by ring
    have hsubset :
        {ω | ∃ n : ℕ, 0 < n ∧
          (1 / delta) ≤ empiricalBernsteinMixtureProcess X V b
            (uniformTiltPrior lam0 lam1) n ω}
          ⊆
        atTopCrossingEvent
          (empiricalBernsteinMixtureProcess X V b (uniformTiltPrior lam0 lam1)) (1 / delta) := by
      intro ω hω
      rcases hω with ⟨n, _hn_pos, hn_cross⟩
      exact ⟨n, hn_cross⟩
    exact (measureReal_mono hsubset).trans h_atTop
  · intro n
    exact integrable_empiricalBernsteinExponentialProcess_prod_uniformPrior
      (μ := μ) (X := X) (V := V) (b := b) (lam0 := lam0) (lam1 := lam1)
      (n + 1) hb hlam0.le h01 hblam1 hX_meas hV_meas hV_nonneg hbound
  · intro n s hs hμs
    haveI : IsFiniteMeasure (μ.restrict s) := by
      rw [isFiniteMeasure_restrict]
      exact ne_of_lt hμs
    exact integrable_empiricalBernsteinExponentialProcess_omegaProd_uniformPrior
      (ν := μ.restrict s) (X := X) (V := V) (b := b)
      (lam0 := lam0) (lam1 := lam1) (n + 1) hb hlam0.le h01 hblam1
      hX_meas hV_meas hV_nonneg (fun k => ae_restrict_of_ae (hbound k))
  · intro n
    exact integrable_empiricalBernsteinExponentialProcess_omegaProd_uniformPrior
      (ν := μ) (X := X) (V := V) (b := b)
      (lam0 := lam0) (lam1 := lam1) n hb hlam0.le h01 hblam1
      hX_meas hV_meas hV_nonneg hbound
  · intro n s hs hμs
    haveI : IsFiniteMeasure (μ.restrict s) := by
      rw [isFiniteMeasure_restrict]
      exact ne_of_lt hμs
    exact integrable_empiricalBernsteinExponentialProcess_omegaProd_uniformPrior
      (ν := μ.restrict s) (X := X) (V := V) (b := b)
      (lam0 := lam0) (lam1 := lam1) n hb hlam0.le h01 hblam1
      hX_meas hV_meas hV_nonneg (fun k => ae_restrict_of_ae (hbound k))

/-- Rational arithmetic witness for the displayed closed-form boundary helper. -/
theorem empiricalBernstein_rational_witness_nonvacuous :
    empiricalBernsteinClosedFormBoundary 0 1 4 2 1 = 2 := by
  norm_num [empiricalBernsteinClosedFormBoundary]

end

end FormalSLT.AnytimeValid
