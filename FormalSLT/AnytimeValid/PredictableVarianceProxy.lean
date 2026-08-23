/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.AnytimeValid.EmpiricalBernsteinCS

/-!
# Predictable variance proxies

This file packages the hypotheses carried by a variance proxy in the
empirical-Bernstein confidence sequence: predictability, pointwise
nonnegativity, square-integrability of the increment, and domination of the
conditional second moment under a finite measure.

Two concrete constructions are supplied. A bounded increment admits the
deterministic proxy `b ^ 2`. A regularized lagged second moment is predictable
because it only reads increments with indices strictly below the current time.
The unconditional lagged construction keeps the deterministic `b ^ 2` floor;
without such a floor, conditional-second-moment domination is a separate model
assumption and is exposed explicitly by
`isPredictableVarianceProxy_regularizedLagged_of_condSecondMoment_le`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

/-- A process `V` is a predictable conditional-second-moment proxy for `X`.

The increment `X k` may be revealed at time `k + 1`, but `V k` is measurable
with respect to the past `F k`. The final field is the load-bearing statistical
condition used by the conditional Bernstein MGF bound. -/
structure IsPredictableVarianceProxy
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] (F : Filtration Nat mOmega)
    (X V : Nat -> Omega -> Real) : Prop where
  stronglyAdapted : StronglyAdapted F V
  nonneg : forall k, 0 <= V k
  sqIntegrable : forall k, Integrable (fun omega => (X k omega) ^ 2) mu
  condSecondMoment_le :
    forall k, mu[fun omega => (X k omega) ^ 2 | F k] ≤ᵐ[mu] V k

/-- The existing fixed-tilt empirical-Bernstein confidence sequence, with all
variance-proxy obligations discharged by `IsPredictableVarianceProxy`. -/
theorem empiricalBernstein_confidence_sequence_of_proxy
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega}
    {X V : Nat -> Omega -> Real} {b lam delta : Real}
    (hdelta : 0 < delta)
    (hb : 0 < b) (hlam : 0 < lam) (hblam : b * lam < 3)
    (hX_meas : forall k, Measurable (X k))
    (hX_int : forall k, Integrable (X k) mu)
    (hX_adapted : IncrementAdapted F X)
    (hbound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= b)
    (hcenter : forall k, mu[X k | F k] =ᵐ[mu] 0)
    (hproxy : IsPredictableVarianceProxy mu F X V) :
    mu.real (empiricalBernsteinUpperFailure X V b lam delta) <= delta := by
  have hV_meas : forall k, Measurable (V k) := by
    intro k
    rw [← stronglyMeasurable_iff_measurable]
    exact (hproxy.stronglyAdapted k).mono (F.le k)
  exact empiricalBernstein_time_uniform_confidence_sequence
    hdelta hb hlam hblam hX_meas hX_int hV_meas hX_adapted
    hproxy.stronglyAdapted hproxy.nonneg hbound hcenter
    hproxy.condSecondMoment_le

/-- The deterministic per-step proxy supplied by an absolute increment bound. -/
def constantVarianceProxy {Omega : Type*} (b : Real) : Nat -> Omega -> Real :=
  fun _ _ => b ^ 2

/-- An absolute bound `|X k| <= b` supplies the predictable proxy `b ^ 2`.

The conditional-second-moment field is proved by conditional-expectation
monotonicity from `X k ^ 2 <= b ^ 2`; it is not an additional premise. -/
theorem isPredictableVarianceProxy_const
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat -> Omega -> Real} {b : Real}
    (hX_meas : forall k, Measurable (X k))
    (hbound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= b) :
    IsPredictableVarianceProxy mu F X (constantVarianceProxy b) := by
  have hXsq_int : forall k,
      Integrable (fun omega => (X k omega) ^ 2) mu := by
    intro k
    refine Integrable.mono' (g := fun _ => b ^ 2)
      (integrable_const _) ((hX_meas k).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hbound k] with omega homega
    rw [Real.norm_eq_abs, ← sq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (abs_nonneg _) homega 2
  refine ⟨?_, ?_, hXsq_int, ?_⟩
  · intro k
    exact stronglyMeasurable_const
  · intro k omega
    exact sq_nonneg b
  · intro k
    have hpoint :
        (fun omega => (X k omega) ^ 2) ≤ᵐ[mu] fun _ => b ^ 2 := by
      filter_upwards [hbound k] with omega homega
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) homega 2
    have hmono := condExp_mono (m := F k)
      (hXsq_int k) (integrable_const (b ^ 2)) hpoint
    rw [condExp_const (F.le k) (b ^ 2)] at hmono
    change mu[fun omega => (X k omega) ^ 2 | F k] ≤ᵐ[mu]
      (fun _ => b ^ 2)
    exact hmono

/-- A regularized lagged second moment with a deterministic floor.

At time `k` this reads only `X 0, ..., X (k - 1)`. The denominator `k + 1`
keeps the definition total at the initial time. -/
def regularizedLaggedSecondMomentProxy {Omega : Type*}
    (X : Nat -> Omega -> Real) (floor : Real) (k : Nat) (omega : Omega) : Real :=
  floor +
    (Finset.sum (Finset.range k) fun i => (X i omega) ^ 2) / (k + 1 : Nat)

/-- A regularized lagged second moment is predictable under increment adaptedness. -/
theorem stronglyAdapted_regularizedLaggedSecondMomentProxy
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    {F : Filtration Nat mOmega} {X : Nat -> Omega -> Real} (floor : Real)
    (hX_adapted : IncrementAdapted F X) :
    StronglyAdapted F (regularizedLaggedSecondMomentProxy X floor) := by
  intro k
  change StronglyMeasurable[F k]
    (fun omega => floor +
      (Finset.sum (Finset.range k) fun i => (X i omega) ^ 2) /
        ((k + 1 : Nat) : Real))
  have hsum : StronglyMeasurable[F k]
      (Finset.sum (Finset.range k) fun i => fun omega => (X i omega) ^ 2) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact ((hX_adapted i).mono (F.mono (Nat.succ_le_of_lt hi))).pow 2
  have hscaled : StronglyMeasurable[F k]
      (fun omega =>
        (Finset.sum (Finset.range k) fun i => (X i omega) ^ 2) /
          ((k + 1 : Nat) : Real)) := by
    simpa only [Finset.sum_apply, div_eq_mul_inv] using
      hsum.mul_const (((k + 1 : Nat) : Real)⁻¹)
  have hfloor_meas : StronglyMeasurable[F k] (fun _ : Omega => floor) :=
    stronglyMeasurable_const
  exact hfloor_meas.add hscaled

/-- Pointwise nonnegativity of the regularized lagged proxy. -/
theorem regularizedLaggedSecondMomentProxy_nonneg
    {Omega : Type*} {X : Nat -> Omega -> Real} {floor : Real}
    (hfloor : 0 <= floor) (k : Nat) (omega : Omega) :
    0 <= regularizedLaggedSecondMomentProxy X floor k omega := by
  unfold regularizedLaggedSecondMomentProxy
  exact add_nonneg hfloor
    (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (X i omega))
      (Nat.cast_nonneg (k + 1)))

/-- Build the regularized lagged proxy from its genuinely statistical premise.

Predictability and nonnegativity are derived. The displayed domination premise
cannot follow from adaptedness alone: past observed squares need not upper-bound
the next conditional second moment for an arbitrary process. -/
theorem isPredictableVarianceProxy_regularizedLagged_of_condSecondMoment_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsFiniteMeasure mu] {F : Filtration Nat mOmega}
    {X : Nat -> Omega -> Real} {floor : Real}
    (hX_adapted : IncrementAdapted F X) (hfloor : 0 <= floor)
    (hXsq_int : forall k, Integrable (fun omega => (X k omega) ^ 2) mu)
    (hvar : forall k,
      mu[fun omega => (X k omega) ^ 2 | F k] ≤ᵐ[mu]
        regularizedLaggedSecondMomentProxy X floor k) :
    IsPredictableVarianceProxy mu F X
      (regularizedLaggedSecondMomentProxy X floor) := by
  exact
    ⟨stronglyAdapted_regularizedLaggedSecondMomentProxy floor hX_adapted,
      fun k omega => regularizedLaggedSecondMomentProxy_nonneg hfloor k omega,
      hXsq_int,
      hvar⟩

/-- A fully discharged regularized lagged proxy for bounded increments.

The `b ^ 2` floor proves conditional-second-moment domination, while the lagged
average records past squares and remains predictable. The floor is
load-bearing, so this construction is at least the constant `b ^ 2` proxy and
is not variance-adaptive. With floor zero, the all-time domination premise
forces the initial squared increment to vanish almost everywhere and then
propagates that degeneracy. This theorem does not claim that a raw past
empirical average dominates the next conditional second moment. -/
theorem isPredictableVarianceProxy_regularizedLagged
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration Nat mOmega} {X : Nat -> Omega -> Real} {b : Real}
    (hX_meas : forall k, Measurable (X k))
    (hX_adapted : IncrementAdapted F X)
    (hbound : forall k, ∀ᵐ omega ∂mu, |X k omega| <= b) :
    IsPredictableVarianceProxy mu F X
      (regularizedLaggedSecondMomentProxy X (b ^ 2)) := by
  have hconst := isPredictableVarianceProxy_const
    (mu := mu) (F := F) (X := X) (b := b) hX_meas hbound
  refine isPredictableVarianceProxy_regularizedLagged_of_condSecondMoment_le
    hX_adapted (sq_nonneg b) hconst.sqIntegrable ?_
  intro k
  filter_upwards [hconst.condSecondMoment_le k] with omega homega
  exact homega.trans (le_add_of_nonneg_right
    (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (X i omega))
      (Nat.cast_nonneg (k + 1))))

end

end FormalSLT.AnytimeValid
