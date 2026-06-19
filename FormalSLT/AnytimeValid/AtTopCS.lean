/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.SubGaussianCS

/-!
# Countable-time confidence sequences

This file lifts the finite-horizon Ville layer from
`Finset.range (n + 1)` to the countable crossing event
`{omega | exists n, a <= M n omega}`.  The proof applies the existing
optional-stopping finite Ville theorem to the increasing finite crossing
events and passes to the countable union by continuity from below.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- Countable-time crossing event for a real-valued process. -/
def atTopCrossingEvent (M : ℕ → Ω → ℝ) (a : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, a ≤ M n ω}

/-- Finite running-max crossing events exhaust the countable crossing event. -/
theorem finiteRunningMax_event_iUnion_eq_atTopCrossingEvent
    (M : ℕ → Ω → ℝ) (a : ℝ) :
    (⋃ n : ℕ, {ω | a ≤ finiteRunningMax M n ω})
      = atTopCrossingEvent M a := by
  classical
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    dsimp [finiteRunningMax] at hn
    rw [Finset.le_sup'_iff] at hn
    rcases hn with ⟨k, _hk_mem, hk_le⟩
    exact ⟨k, hk_le⟩
  · rintro ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    dsimp [finiteRunningMax]
    exact hn.trans <| Finset.le_sup'
      (f := fun k => M k ω)
      (s := Finset.range (n + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- The finite running-max crossing events are monotone in the horizon. -/
theorem finiteRunningMax_event_mono (M : ℕ → Ω → ℝ) (a : ℝ) :
    Monotone fun n : ℕ => {ω | a ≤ finiteRunningMax M n ω} := by
  classical
  intro n m hnm ω hω
  dsimp [finiteRunningMax] at hω ⊢
  rw [Finset.le_sup'_iff] at hω ⊢
  rcases hω with ⟨k, hk_mem, hk_le⟩
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk_mem
  refine ⟨k, ?_, hk_le⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact hk_mem.trans hnm

/--
Countable-time Ville inequality for a nonnegative supermartingale.

This is the atTop counterpart of `ville_maximal_ineq`: the event is a genuine
countable-time crossing event rather than a finite running maximum.
-/
theorem ville_atTop_maximal_ineq [IsFiniteMeasure μ]
    (hsup : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) {a : ℝ} (ha : 0 < a) :
    a * μ.real (atTopCrossingEvent M a) ≤ ∫ ω, M 0 ω ∂μ := by
  classical
  let E : ℕ → Set Ω := fun n => {ω | a ≤ finiteRunningMax M n ω}
  let I : ℝ := ∫ ω, M 0 ω ∂μ
  have hE_mono : Monotone E := finiteRunningMax_event_mono M a
  have hE_union : (⋃ n : ℕ, E n) = atTopCrossingEvent M a := by
    simpa [E] using finiteRunningMax_event_iUnion_eq_atTopCrossingEvent M a
  have hfinite : ∀ n, a * μ.real (E n) ≤ I := by
    intro n
    simpa [E, I, finiteRunningMax] using
      (ville_maximal_ineq (μ := μ) (𝒢 := 𝒢) (M := M) (a := a) hsup hnonneg n)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg (hnonneg 0)
  have hI_div_nonneg : 0 ≤ I / a := div_nonneg hI_nonneg ha.le
  have hmeasure_le : μ (⋃ n : ℕ, E n) ≤ ENNReal.ofReal (I / a) := by
    rw [hE_mono.measure_iUnion]
    refine iSup_le ?_
    intro n
    have hdiv : μ.real (E n) ≤ I / a := by
      rw [le_div_iff₀ ha]
      simpa [mul_comm] using hfinite n
    rw [← ofReal_measureReal (μ := μ) (s := E n)]
    exact ENNReal.ofReal_le_ofReal hdiv
  have hreal_le : μ.real (⋃ n : ℕ, E n) ≤ I / a := by
    have htop : ENNReal.ofReal (I / a) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h := ENNReal.toReal_mono htop hmeasure_le
    simpa [Measure.real, ENNReal.toReal_ofReal hI_div_nonneg] using h
  calc
    a * μ.real (atTopCrossingEvent M a)
        = a * μ.real (⋃ n : ℕ, E n) := by rw [← hE_union]
    _ ≤ a * (I / a) := mul_le_mul_of_nonneg_left hreal_le ha.le
    _ = ∫ ω, M 0 ω ∂μ := by
      dsimp [I]
      field_simp [ha.ne']

/-- Countable-time fixed-threshold Ville payoff for the sub-Gamma exponential process. -/
theorem ville_atTop_subGamma_exponential_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta)
    (hsup : Supermartingale (subGammaExponentialProcess X sigma2 b lam) ℱ μ) :
    μ.real
      (atTopCrossingEvent (subGammaExponentialProcess X sigma2 b lam) (1 / delta))
      ≤ delta := by
  have hnonneg : 0 ≤ subGammaExponentialProcess X sigma2 b lam :=
    fun _ _ => (Real.exp_pos _).le
  have ha : 0 < 1 / delta := one_div_pos.mpr hδ
  have hville :=
    ville_atTop_maximal_ineq
      (μ := μ) (𝒢 := ℱ)
      (M := subGammaExponentialProcess X sigma2 b lam)
      hsup hnonneg ha
  have hM0 : ∫ ω, subGammaExponentialProcess X sigma2 b lam 0 ω ∂μ = 1 := by
    have hbody :
        (fun ω => subGammaExponentialProcess X sigma2 b lam 0 ω) =ᵐ[μ] fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => by
        simp [subGammaExponentialProcess, runningSum]
    rw [integral_congr_ae hbody]
    simp [integral_const]
  rw [hM0] at hville
  calc
    μ.real
        (atTopCrossingEvent (subGammaExponentialProcess X sigma2 b lam) (1 / delta))
        = delta *
          ((1 / delta) *
            μ.real
              (atTopCrossingEvent
                (subGammaExponentialProcess X sigma2 b lam) (1 / delta))) := by
          field_simp [hδ.ne']
    _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hville hδ.le
    _ = delta := by ring

/-- Fixed-lambda atTop upper boundary for the centered running mean. -/
def atTopSubGammaUpperFailure {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b lam delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧
    subGammaCgf sigma2 b lam / lam
      + Real.log (1 / delta) / ((n : ℝ) * lam)
      ≤ runningMean X n ω}

/--
The fixed-lambda running-mean atTop boundary is contained in the fixed
exponential-process crossing event.
-/
theorem atTopSubGammaUpperFailure_subset_exponential_crossing
    {Ω : Type*} {X : ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam) :
    atTopSubGammaUpperFailure X sigma2 b lam delta
      ⊆
    atTopCrossingEvent (subGammaExponentialProcess X sigma2 b lam) (1 / delta) := by
  intro ω hω
  rcases hω with ⟨n, hn_pos, hn_boundary⟩
  refine ⟨n, ?_⟩
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hden_pos : 0 < (n : ℝ) * lam := mul_pos (Nat.cast_pos.mpr hn_pos) hlam
  have hmul := mul_le_mul_of_nonneg_left hn_boundary hden_pos.le
  have hlog_le :
      Real.log (1 / delta)
        ≤ lam * runningSum X n ω - (n : ℝ) * subGammaCgf sigma2 b lam := by
    rw [runningMean] at hmul
    field_simp [hn_ne, hlam_ne] at hmul
    nlinarith
  have hdelta_inv_pos : 0 < 1 / delta := one_div_pos.mpr hδ
  rw [← Real.exp_log hdelta_inv_pos]
  exact Real.exp_le_exp.2 hlog_le

/--
Countable-time fixed-lambda sub-Gamma confidence boundary from a supplied
exponential supermartingale.
-/
theorem ville_atTop_subGamma_running_mean
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam)
    (hsup : Supermartingale (subGammaExponentialProcess X sigma2 b lam) ℱ μ) :
    μ.real (atTopSubGammaUpperFailure X sigma2 b lam delta) ≤ delta := by
  exact (measureReal_mono
    (atTopSubGammaUpperFailure_subset_exponential_crossing
      (X := X) (sigma2 := sigma2) (b := b) (lam := lam) (delta := delta) hδ hlam)).trans
    (ville_atTop_subGamma_exponential_bound
      (μ := μ) (ℱ := ℱ) (X := X) (sigma2 := sigma2) (b := b) (lam := lam)
      hδ hsup)

/--
End-to-end countable-time fixed-lambda sub-Gamma confidence boundary from the
conditional sub-Gamma increment model.
-/
theorem atTop_time_uniform_confidence_sequence_subGamma
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta)
    (hb : 0 < b) (hσ : 0 ≤ sigma2) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : ∀ k, Measurable (X k)) (hX_int : ∀ k, Integrable (X k) μ)
    (h_adapted : StronglyAdapted ℱ (subGammaExponentialProcess X sigma2 b lam))
    (h_integrable : ∀ k, Integrable (subGammaExponentialProcess X sigma2 b lam k) μ)
    (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ b)
    (hcenter : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0)
    (hvar : ∀ k, μ[fun ω => (X k ω) ^ 2 | ℱ k] ≤ᵐ[μ] fun _ => sigma2) :
    μ.real (atTopSubGammaUpperFailure X sigma2 b lam delta) ≤ delta := by
  exact ville_atTop_subGamma_running_mean hδ hlam
    (nonneg_supermartingale_of_condSubGamma h_adapted h_integrable
      (condSubGamma_supermartingale_step hb hσ hlam.le hblam hX_meas hX_int
        h_adapted hbound hcenter hvar)).1

/--
The fixed-lambda atTop boundary is not vacuous: for the zero process with
zero variance proxy and confidence level `exp (-1)`, the upper failure event is
empty.
-/
theorem atTopSubGammaUpperFailure_zero_process_empty {lam : ℝ} (hlam : 0 < lam) :
    atTopSubGammaUpperFailure
      (fun _ : ℕ => fun _ : Unit => (0 : ℝ)) 0 0 lam (Real.exp (-1))
      = ∅ := by
  classical
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨n, hn_pos, hn_boundary⟩
    have hn_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hden_pos : 0 < (n : ℝ) * lam := mul_pos hn_cast_pos hlam
    have hlog : Real.log (1 / Real.exp (-1)) = 1 := by
      rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    have hpos : 0 < Real.log (1 / Real.exp (-1)) / ((n : ℝ) * lam) :=
      div_pos (by rw [hlog]; norm_num) hden_pos
    have hle :
        Real.log (1 / Real.exp (-1)) / ((n : ℝ) * lam) ≤ 0 := by
      simpa [subGammaCgf, runningMean, runningSum] using hn_boundary
    exact False.elim ((not_lt_of_ge hle) hpos)
  · intro hω
    exact False.elim hω

end

end FormalSLT.AnytimeValid
