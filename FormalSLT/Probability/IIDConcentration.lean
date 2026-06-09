import FormalSLT.Concentration.SharpMcDiarmid

/-!
# IID empirical-mean concentration for online-to-PAC conversion

This module internalizes the iid deviation gate that q055 previously accepted
as a hypothesis.  The finite-time event is written in the exact additive form
needed by `FormalSLT.Concentration.mcdiarmid_additive_independent`:

`T * eps <= sum_t (E[X_t] - X_t(omega))`.

For bounded losses `0 <= X_t <= b`, the lower-tail empirical deviation is proved
by applying the sharp additive McDiarmid theorem to `-X_t`.  This is the q059
bridge from the q049 sharp-McDiarmid backbone to online-to-PAC certificates.

Reference: Cesa-Bianchi, Conconi, Gentile (2004), "On the Generalization
Ability of On-Line Learning Algorithms"; McDiarmid (1989), "On the method of
bounded differences".
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.Probability.IIDConcentration

noncomputable section

/-- Population average of a finite family of loss random variables. -/
def iidPopulationAverage {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin T → Ω → ℝ) : ℝ :=
  (∑ t : Fin T, ∫ ω, X t ω ∂μ) / (T : ℝ)

/-- Empirical average of a finite family of loss random variables at `ω`. -/
def iidEmpiricalAverage {T : ℕ} {Ω : Type*}
    (X : Fin T → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ t : Fin T, X t ω) / (T : ℝ)

/-- Additive lower-tail deviation gap, `sum_t (E[X_t] - X_t(ω))`. -/
def iidPopulationMinusEmpiricalSum {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin T → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ t : Fin T, ((∫ x, X t x ∂μ) - X t ω)

/--
Bad event for the lower-tail empirical deviation used in online-to-PAC:
the empirical average falls below the population average by at least `eps`.
-/
def iidDeviationBadEvent {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin T → Ω → ℝ) (eps : ℝ) : Set Ω :=
  {ω | (T : ℝ) * eps ≤ iidPopulationMinusEmpiricalSum μ X ω}

/-- Algebraic conversion from a finite-sum deviation gap to average losses. -/
theorem iidDeviation_of_not_mem_badEvent
    {T : ℕ} (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin T → Ω → ℝ) (ω : Ω) {eps : ℝ}
    (hnotBad : ω ∉ iidDeviationBadEvent μ X eps) :
    iidPopulationAverage μ X ≤ iidEmpiricalAverage X ω + eps := by
  have hTreal_pos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hTreal_ne : (T : ℝ) ≠ 0 := ne_of_gt hTreal_pos
  have hgap_lt :
      iidPopulationMinusEmpiricalSum μ X ω < (T : ℝ) * eps := by
    exact not_le.mp hnotBad
  have hgap_eq :
      iidPopulationMinusEmpiricalSum μ X ω =
        (∑ t : Fin T, ∫ x, X t x ∂μ) - ∑ t : Fin T, X t ω := by
    simp [iidPopulationMinusEmpiricalSum, Finset.sum_sub_distrib]
  have hmul_eq :
      (T : ℝ) * (iidPopulationAverage μ X - iidEmpiricalAverage X ω) =
        iidPopulationMinusEmpiricalSum μ X ω := by
    rw [hgap_eq]
    unfold iidPopulationAverage iidEmpiricalAverage
    field_simp [hTreal_ne]
  have hscaled_lt :
      (T : ℝ) * (iidPopulationAverage μ X - iidEmpiricalAverage X ω) <
        (T : ℝ) * eps := by
    simpa [hmul_eq] using hgap_lt
  have hdiff_lt : iidPopulationAverage μ X - iidEmpiricalAverage X ω < eps :=
    by nlinarith
  linarith

/--
Sharp-McDiarmid mass bound for the iid lower-tail bad event.

This is the derived q059 deviation gate.  It uses q049's sharp additive
McDiarmid theorem on the independent family `fun t ω => -X t ω`, whose support
is `[-lossBound, 0]` whenever `X t` is almost surely in `[0, lossBound]`.
-/
theorem iidDeviationBadEventMass_le_exp_of_sharpMcDiarmid
    {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Fin T → Ω → ℝ) {lossBound eps : ℝ}
    (hlossBound : 0 ≤ lossBound)
    (hmeas : ∀ t, Measurable (X t))
    (hindep : iIndepFun X μ)
    (hbounded : ∀ t, ∀ᵐ ω ∂μ, X t ω ∈ Set.Icc 0 lossBound)
    (heps : 0 ≤ eps) :
    μ.real (iidDeviationBadEvent μ X eps) ≤
      Real.exp (-2 * ((T : ℝ) * eps) ^ 2 /
        ∑ _ : Fin T, (lossBound - 0) ^ 2) := by
  let Y : Fin T → Ω → ℝ := fun t ω => -X t ω
  have hYmeas : ∀ t, Measurable (Y t) := by
    intro t
    exact (hmeas t).neg
  have hYindep : iIndepFun Y μ := by
    have h := hindep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_id.neg)
    simpa [Y, Function.comp] using h
  have hYrange : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (-lossBound) 0 := by
    intro t
    filter_upwards [hbounded t] with ω hω
    constructor <;> dsimp [Y] <;> linarith [hω.1, hω.2]
  have hrange : ∀ t : Fin T, -lossBound ≤ 0 := by
    intro t
    linarith
  have ht : 0 ≤ (T : ℝ) * eps := by
    exact mul_nonneg (Nat.cast_nonneg T) heps
  have htail :=
    FormalSLT.Concentration.mcdiarmid_additive_independent
      (μ := μ) (X := Y)
      (a := fun _ : Fin T => -lossBound)
      (b := fun _ : Fin T => 0)
      hYmeas hYindep hrange hYrange
      (s := Finset.univ) (t := (T : ℝ) * eps) ht
  have hset :
      {ω : Ω | (T : ℝ) * eps ≤
          ∑ i ∈ Finset.univ, (Y i ω - ∫ x, Y i x ∂μ)}
        = iidDeviationBadEvent μ X eps := by
    ext ω
    simp only [iidDeviationBadEvent, iidPopulationMinusEmpiricalSum, Set.mem_setOf_eq, Y,
      integral_neg]
    have hsum :
        (∑ x : Fin T, (-X x ω - -∫ a, X x a ∂μ)) =
          ∑ x : Fin T, ((∫ a, X x a ∂μ) - X x ω) := by
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hsum]
  rw [hset] at htail
  refine htail.trans (le_of_eq ?_)
  apply congrArg Real.exp
  have hden :
      (∑ i : Fin T, ((fun _ : Fin T => 0) i -
          (fun _ : Fin T => -lossBound) i) ^ 2) =
        ∑ t : Fin T, (lossBound - 0) ^ 2 := by
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hden]

/-- Corollary form that consumes an externally chosen confidence budget `delta`. -/
theorem iidDeviationBadEventMass_le_delta_of_exp_bound
    {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Fin T → Ω → ℝ) {lossBound eps delta : ℝ}
    (hlossBound : 0 ≤ lossBound)
    (hmeas : ∀ t, Measurable (X t))
    (hindep : iIndepFun X μ)
    (hbounded : ∀ t, ∀ᵐ ω ∂μ, X t ω ∈ Set.Icc 0 lossBound)
    (heps : 0 ≤ eps)
    (hexp :
      Real.exp (-2 * ((T : ℝ) * eps) ^ 2 /
        ∑ _ : Fin T, (lossBound - 0) ^ 2) ≤ delta) :
    μ.real (iidDeviationBadEvent μ X eps) ≤ delta := by
  exact (iidDeviationBadEventMass_le_exp_of_sharpMcDiarmid
    (μ := μ) X hlossBound hmeas hindep hbounded heps).trans hexp

end

end FormalSLT.Probability.IIDConcentration
