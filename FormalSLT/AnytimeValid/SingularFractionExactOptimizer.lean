/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.AnytimeValid.SingularFractionBesselMixture

/-!
# An exact global minimizer of the original singular-fraction boundary

The all-fraction theorem `singularFractionLowerMixture_all_fraction_boundary`
holds simultaneously for every admissible target fraction outside one Ville
event.  The fraction is therefore free to be chosen after the data, and the
natural choice is the one minimizing the boundary actually produced.

This module minimizes the ORIGINAL boundary

  `B (Q, delta, lam) = lam * Q + (exp 1 / lam) * log (L lam * (L lam + 1) / delta)`

on `0 < lam <= exp (-1)`, where `L lam = -log lam`.  No surrogate is
interposed: `singularFractionForwardBesselBoundary_eq_exactNumerator` is a
definitional identification of `B` with the repository's boundary, so the
optimization is over the same function the mixture argument delivers.

The stationarity condition for `B` is transcendental.  This module does not
derive a closed-form minimizer; it obtains one by compactness instead.
Coercivity comes from the elementary lower bound
`exp 1 * log 2 / lam <= B`, valid because `L >= 1` on the admissible range;
this places every value below the explicit cutoff
`singularFractionExactCutoff` strictly above the value at the cap `exp (-1)`,
so the search may be restricted to a compact interval without losing the
minimum.

The result is an existence and exact-minimization theorem.  It does not prove
uniqueness, and the canonical witness below is chosen classically: no
computable optimizer is claimed.

Optimality here is over the fraction only.  It says nothing about the
uniform singular-fraction mixture, the window, or the variance proxy.
-/

namespace FormalSLT.AnytimeValid

noncomputable section

/-- The original all-fraction boundary numerator as a scalar function of the
observed penalty `Q`, the confidence `delta`, and the target fraction `lam`. -/
def singularFractionExactNumerator (Q delta lam : Real) : Real :=
  lam * Q +
    Real.exp 1 / lam *
      Real.log
        (singularFractionLogScale lam *
          (singularFractionLogScale lam + 1) / delta)

/-- The value of the boundary numerator at the cap `lam = exp (-1)`. -/
def singularFractionExactCapValue (Q delta : Real) : Real :=
  Q / Real.exp 1 + Real.exp 2 * Real.log (2 / delta)

/-- An explicit positive fraction below which the boundary numerator is
strictly worse than its value at the cap. -/
def singularFractionExactCutoff (Q delta : Real) : Real :=
  Real.exp 1 * Real.log 2 / singularFractionExactCapValue Q delta

section Bridge

variable {Omega : Type*}

/-- **The original boundary, not a surrogate.**  The repository's observable
all-fraction boundary is definitionally the scalar numerator at the observed
hybrid-Bessel penalty. -/
theorem singularFractionForwardBesselBoundary_eq_exactNumerator
    (X : Nat → Omega → Real) (lam delta : Real) (n : Nat) (omega : Omega) :
    singularFractionForwardBesselBoundary X lam delta n omega =
      singularFractionExactNumerator
        (forwardHybridBesselPenalty (fun k => X k omega) n) delta lam :=
  rfl

end Bridge

/-- On the admissible range the logarithmic window `L * (L + 1)` is at
least `2`, with equality exactly at the cap. -/
theorem two_le_singularFractionLogWindow
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    2 <= singularFractionLogScale lam * (singularFractionLogScale lam + 1) := by
  have hL : 1 <= singularFractionLogScale lam :=
    one_le_singularFractionLogScale hlam_pos hlam
  nlinarith

/-- The window price is at least `log 2` once `delta <= 1`. -/
theorem log_two_le_singularFractionWindowPrice
    {lam delta : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1))
    (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    Real.log 2 <=
      Real.log
        (singularFractionLogScale lam *
          (singularFractionLogScale lam + 1) / delta) := by
  have hA : 2 <= singularFractionLogScale lam *
      (singularFractionLogScale lam + 1) := two_le_singularFractionLogWindow hlam_pos hlam
  have hle : (2 : Real) <=
      singularFractionLogScale lam *
        (singularFractionLogScale lam + 1) / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  exact Real.log_le_log (by norm_num) hle

/-- **Coercivity.**  The boundary numerator dominates `exp 1 * log 2 / lam`
on the whole admissible range. -/
theorem singularFractionExactNumerator_lower_bound
    {Q delta lam : Real} (hQ : 0 <= Q)
    (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    Real.exp 1 * Real.log 2 / lam <= singularFractionExactNumerator Q delta lam := by
  have hprice := log_two_le_singularFractionWindowPrice hlam_pos hlam hdelta hdelta_one
  have hcoef : 0 <= Real.exp 1 / lam := le_of_lt (div_pos (Real.exp_pos 1) hlam_pos)
  have hsecond : Real.exp 1 / lam * Real.log 2 <=
      Real.exp 1 / lam *
        Real.log
          (singularFractionLogScale lam *
            (singularFractionLogScale lam + 1) / delta) :=
    mul_le_mul_of_nonneg_left hprice hcoef
  have hfirst : 0 <= lam * Q := mul_nonneg (le_of_lt hlam_pos) hQ
  have hrw : Real.exp 1 * Real.log 2 / lam = Real.exp 1 / lam * Real.log 2 := by
    field_simp
  rw [hrw]
  unfold singularFractionExactNumerator
  linarith

/-- The numerator at the cap is the cap value. -/
theorem singularFractionExactNumerator_at_cap (Q delta : Real) :
    singularFractionExactNumerator Q delta (Real.exp (-1)) =
      singularFractionExactCapValue Q delta := by
  have hL : singularFractionLogScale (Real.exp (-1)) = 1 := by
    unfold singularFractionLogScale
    rw [Real.log_exp]
    norm_num
  have hdiv : Real.exp 1 / Real.exp (-1) = Real.exp 2 := by
    rw [← Real.exp_sub]
    norm_num
  have hmul : Real.exp (-1) * Q = Q / Real.exp 1 := by
    rw [Real.exp_neg]
    field_simp
  unfold singularFractionExactNumerator singularFractionExactCapValue
  rw [hL, hdiv, hmul]
  norm_num

/-- The cap value is at least `exp 2 * log 2`, hence strictly positive. -/
theorem singularFractionExactCapValue_lower
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    Real.exp 2 * Real.log 2 <= singularFractionExactCapValue Q delta := by
  have hlog : Real.log 2 <= Real.log (2 / delta) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hexp : (0 : Real) < Real.exp 2 := Real.exp_pos 2
  have hQdiv : 0 <= Q / Real.exp 1 := div_nonneg hQ (le_of_lt (Real.exp_pos 1))
  unfold singularFractionExactCapValue
  nlinarith

/-- The cap value is strictly positive. -/
theorem singularFractionExactCapValue_pos
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    0 < singularFractionExactCapValue Q delta := by
  have hlow := singularFractionExactCapValue_lower hQ hdelta hdelta_one
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : (0 : Real) < Real.exp 2 := Real.exp_pos 2
  nlinarith

/-- The cutoff is strictly positive. -/
theorem singularFractionExactCutoff_pos
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    0 < singularFractionExactCutoff Q delta := by
  have hcap := singularFractionExactCapValue_pos hQ hdelta hdelta_one
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold singularFractionExactCutoff
  positivity

/-- The cutoff never exceeds the cap, so the search interval is nonempty. -/
theorem singularFractionExactCutoff_le_exp_neg_one
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    singularFractionExactCutoff Q delta <= Real.exp (-1) := by
  have hcap_pos := singularFractionExactCapValue_pos hQ hdelta hdelta_one
  have hlow := singularFractionExactCapValue_lower hQ hdelta hdelta_one
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he1 : (0 : Real) < Real.exp 1 := Real.exp_pos 1
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hkey : Real.exp 1 * Real.log 2 <=
      Real.exp (-1) * singularFractionExactCapValue Q delta := by
    have hne : Real.exp (-1) * Real.exp 2 = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [mul_le_mul_of_nonneg_left hlow (le_of_lt (Real.exp_pos (-1)))]
  unfold singularFractionExactCutoff
  rw [div_le_iff₀ hcap_pos]
  linarith

/-- **Every fraction below the cutoff is strictly worse than the cap.** -/
theorem singularFractionExactCapValue_lt_of_lt_cutoff
    {Q delta lam : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (hlam_pos : 0 < lam) (hlam : lam < singularFractionExactCutoff Q delta) :
    singularFractionExactCapValue Q delta < singularFractionExactNumerator Q delta lam := by
  have hcut_le := singularFractionExactCutoff_le_exp_neg_one hQ hdelta hdelta_one
  have hlam_le : lam <= Real.exp (-1) := le_of_lt (lt_of_lt_of_le hlam hcut_le)
  have hlow := singularFractionExactNumerator_lower_bound hQ hdelta hdelta_one hlam_pos hlam_le
  have hcap_pos := singularFractionExactCapValue_pos hQ hdelta hdelta_one
  have hprod : lam * singularFractionExactCapValue Q delta < Real.exp 1 * Real.log 2 := by
    have := (lt_div_iff₀ hcap_pos).1 hlam
    linarith
  have hstrict : singularFractionExactCapValue Q delta < Real.exp 1 * Real.log 2 / lam := by
    rw [lt_div_iff₀ hlam_pos]
    linarith
  linarith

/-- The boundary numerator is continuous on any set of admissible
fractions.  The hypothesis `0 < lam` is essential: at `lam = 0` the Lean
term evaluates to `0`, which is below the cap value. -/
theorem continuousOn_singularFractionExactNumerator
    {Q delta : Real} (hdelta : 0 < delta) {S : Set Real}
    (hS : ∀ lam ∈ S, 0 < lam ∧ lam <= Real.exp (-1)) :
    ContinuousOn (fun lam => singularFractionExactNumerator Q delta lam) S := by
  intro x hx
  obtain ⟨hx_pos, hx_le⟩ := hS x hx
  have hxne : x ≠ 0 := ne_of_gt hx_pos
  have hlogc : ContinuousAt (fun lam : Real => singularFractionLogScale lam) x := by
    unfold singularFractionLogScale
    exact (Real.continuousAt_log hxne).neg
  have hA : ContinuousAt
      (fun lam : Real =>
        singularFractionLogScale lam * (singularFractionLogScale lam + 1) / delta) x :=
    (hlogc.mul (hlogc.add continuousAt_const)).div_const delta
  have hApos : 0 <
      singularFractionLogScale x * (singularFractionLogScale x + 1) / delta := by
    have h2 := two_le_singularFractionLogWindow hx_pos hx_le
    apply div_pos _ hdelta
    linarith
  have hlogA : ContinuousAt
      (fun lam : Real =>
        Real.log
          (singularFractionLogScale lam *
            (singularFractionLogScale lam + 1) / delta)) x :=
    hA.log (ne_of_gt hApos)
  have hterm2 : ContinuousAt
      (fun lam : Real =>
        Real.exp 1 / lam *
          Real.log
            (singularFractionLogScale lam *
              (singularFractionLogScale lam + 1) / delta)) x :=
    (continuousAt_const.div continuousAt_id hxne).mul hlogA
  have hterm1 : ContinuousAt (fun lam : Real => lam * Q) x :=
    continuousAt_id.mul continuousAt_const
  exact (hterm1.add hterm2).continuousWithinAt

/-- A minimizer exists on the compact search interval. -/
theorem exists_isMinOn_singularFractionExactNumerator_Icc
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    ∃ lamStar ∈ Set.Icc (singularFractionExactCutoff Q delta) (Real.exp (-1)),
      IsMinOn (fun lam => singularFractionExactNumerator Q delta lam)
        (Set.Icc (singularFractionExactCutoff Q delta) (Real.exp (-1))) lamStar := by
  have hcut_pos := singularFractionExactCutoff_pos hQ hdelta hdelta_one
  have hcut_le := singularFractionExactCutoff_le_exp_neg_one hQ hdelta hdelta_one
  apply isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hcut_le)
  apply continuousOn_singularFractionExactNumerator hdelta
  intro lam hlam
  exact ⟨lt_of_lt_of_le hcut_pos hlam.1, hlam.2⟩

/-- **PRIMARY.**  The original singular-fraction boundary numerator attains a
global minimum over the full admissible range `0 < lam <= exp (-1)`. -/
theorem exists_admissible_isMinOn_singularFractionExactNumerator
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    ∃ lamStar : Real, 0 < lamStar ∧ lamStar <= Real.exp (-1) ∧
      ∀ lam : Real, 0 < lam → lam <= Real.exp (-1) →
        singularFractionExactNumerator Q delta lamStar <=
          singularFractionExactNumerator Q delta lam := by
  obtain ⟨lamStar, hmem, hmin⟩ :=
    exists_isMinOn_singularFractionExactNumerator_Icc hQ hdelta hdelta_one
  have hcut_pos := singularFractionExactCutoff_pos hQ hdelta hdelta_one
  have hcut_le := singularFractionExactCutoff_le_exp_neg_one hQ hdelta hdelta_one
  refine ⟨lamStar, lt_of_lt_of_le hcut_pos hmem.1, hmem.2, ?_⟩
  intro lam hlam_pos hlam_le
  rcases le_or_gt (singularFractionExactCutoff Q delta) lam with hge | hlt
  · exact hmin (Set.mem_Icc.mpr ⟨hge, hlam_le⟩)
  · have hcap : singularFractionExactNumerator Q delta lamStar <=
        singularFractionExactCapValue Q delta := by
      have h : singularFractionExactNumerator Q delta lamStar <=
          singularFractionExactNumerator Q delta (Real.exp (-1)) :=
        hmin (Set.mem_Icc.mpr ⟨hcut_le, le_rfl⟩)
      rwa [singularFractionExactNumerator_at_cap] at h
    have hstrict :=
      singularFractionExactCapValue_lt_of_lt_cutoff hQ hdelta hdelta_one hlam_pos hlt
    linarith

/-! ### A canonical exact minimizer and the optimized boundary -/

open scoped Classical in
/-- A canonical exact minimizer of the original boundary numerator.  The
guard keeps the definition total; outside the admissible parameter range it
falls back to the cap, which is itself admissible, so the two spec lemmas
`_pos` and `_le_exp_neg_one` hold unconditionally.

This is a `Classical.choose`, so it is not known to be measurable in
`(Q, delta)`.  That is harmless wherever it is eliminated pointwise inside a
universally quantified statement, and it is the reason no process or event in
this development is ever defined in terms of it. -/
def singularFractionExactOptimalLambda (Q delta : Real) : Real :=
  if h : 0 <= Q ∧ 0 < delta ∧ delta <= 1 then
    Classical.choose
      (exists_admissible_isMinOn_singularFractionExactNumerator h.1 h.2.1 h.2.2)
  else Real.exp (-1)

/-- The canonical minimizer is strictly positive. -/
theorem singularFractionExactOptimalLambda_pos (Q delta : Real) :
    0 < singularFractionExactOptimalLambda Q delta := by
  unfold singularFractionExactOptimalLambda
  split_ifs with h
  · exact (Classical.choose_spec
      (exists_admissible_isMinOn_singularFractionExactNumerator h.1 h.2.1 h.2.2)).1
  · exact Real.exp_pos _

/-- The canonical minimizer is admissible. -/
theorem singularFractionExactOptimalLambda_le_exp_neg_one (Q delta : Real) :
    singularFractionExactOptimalLambda Q delta <= Real.exp (-1) := by
  unfold singularFractionExactOptimalLambda
  split_ifs with h
  · exact (Classical.choose_spec
      (exists_admissible_isMinOn_singularFractionExactNumerator h.1 h.2.1 h.2.2)).2.1
  · exact le_rfl

/-- The canonical minimizer really minimizes, over the full admissible range. -/
theorem singularFractionExactOptimalLambda_isMinOn
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    singularFractionExactNumerator Q delta
        (singularFractionExactOptimalLambda Q delta) <=
      singularFractionExactNumerator Q delta lam := by
  have h : 0 <= Q ∧ 0 < delta ∧ delta <= 1 := ⟨hQ, hdelta, hdelta_one⟩
  unfold singularFractionExactOptimalLambda
  rw [dif_pos h]
  exact (Classical.choose_spec
    (exists_admissible_isMinOn_singularFractionExactNumerator h.1 h.2.1 h.2.2)).2.2
    lam hlam_pos hlam

/-- The original boundary numerator evaluated at its own exact minimizer. -/
def singularFractionExactBoundary (Q delta : Real) : Real :=
  singularFractionExactNumerator Q delta (singularFractionExactOptimalLambda Q delta)

/-- **Exact original-boundary optimality, scalar form.**  The optimized
boundary is at most the original boundary numerator at every admissible
fraction. -/
theorem singularFractionExactBoundary_le
    {Q delta : Real} (hQ : 0 <= Q) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    singularFractionExactBoundary Q delta <=
      singularFractionExactNumerator Q delta lam :=
  singularFractionExactOptimalLambda_isMinOn hQ hdelta hdelta_one hlam_pos hlam

/-- The optimized boundary is attained, so it is a minimum and not merely an
infimum.  Attainment is what preserves strict inequalities downstream. -/
theorem singularFractionExactBoundary_eq_numerator (Q delta : Real) :
    singularFractionExactBoundary Q delta =
      singularFractionExactNumerator Q delta
        (singularFractionExactOptimalLambda Q delta) :=
  rfl

section BoundaryComparison

variable {Omega : Type*}

/-- **Exact original-boundary optimality against the repository boundary.**
The optimized boundary is at most the observable all-fraction boundary at
every admissible target fraction.  Together with
`singularFractionForwardBesselBoundary_eq_exactNumerator` this is the
statement that earns the phrase "exact original-boundary optimality". -/
theorem singularFractionExactBoundary_le_forwardBesselBoundary
    (X : Nat → Omega → Real) {delta : Real} {n : Nat} {omega : Omega}
    (hn : 2 <= n) (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {lam : Real} (hlam_pos : 0 < lam) (hlam : lam <= Real.exp (-1)) :
    singularFractionExactBoundary
        (forwardHybridBesselPenalty (fun k => X k omega) n) delta <=
      singularFractionForwardBesselBoundary X lam delta n omega := by
  rw [singularFractionForwardBesselBoundary_eq_exactNumerator]
  exact singularFractionExactBoundary_le
    (forwardHybridBesselPenalty_nonneg_of_two _ hn) hdelta hdelta_one hlam_pos hlam

end BoundaryComparison

end

end FormalSLT.AnytimeValid
