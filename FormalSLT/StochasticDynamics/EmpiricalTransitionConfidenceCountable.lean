/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayesCountable

/-!
# Countable-tilt empirical transition confidence

This module replaces the finite transition-confidence tilt catalog by the
predeclared natural-number geometric catalog from
`TrajectoryEmpiricalBernsteinPACBayesCountable`.  One countably allocated
outer-mass event is simultaneous over all times, all transition coordinates,
and every natural-number tilt atom.  Consequently a tilt atom, transition
row, and candidate kernel may all be selected after observing the path by
substitution into that common event.

At sample size `n`, the explicit selector
`geometricForwardTiltIndex n` gives coordinate boundaries that tend to zero.
After normalization by a row's visit count, coordinate and row radii tend to
zero under an explicit positive limiting visit-frequency assumption.

The candidate-kernel total-variation budget has two distinct terms: an
empirical candidate discrepancy and a statistical row radius.  Its vanishing
theorem therefore assumes that the empirical candidate discrepancy tends to
zero in every row; vanishing statistical radii alone do not imply that an
arbitrary candidate kernel approaches the true kernel.

As in `EmpiricalTransitionConfidence`, the initial state is deterministic,
the first score is the transition `x 0 -> x 1`, and normalized statements
require a positive row-visit mass.
-/

open Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable

namespace FormalSLT.StochasticDynamics

noncomputable section

attribute [local instance 0] Classical.propDecidable

variable {Z : Type*} [Fintype Z] [Nonempty Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-! ## Countable geometric boundaries and radii -/

/-- Direct or complement Dirac boundary for one transition coordinate, using
the countably allocated geometric tilt catalog. -/
def countableTransitionCoordinateBoundary
    (prior : TransitionCoordinate Z -> Real) (z y : Z)
    (complement : Bool) (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  trajectoryCountableEmpiricalBernsteinPACBayesBoundary
    prior transitionCoordinateTrajectoryScore
    (diracPosterior (⟨z, y, complement⟩ : TransitionCoordinate Z))
    delta j n x

/-- Two-sided normalized coordinate radius from the countable geometric
catalog.  Statistical interpretation requires positive source-visit mass. -/
def countableTransitionCoordinateRadius
    (prior : TransitionCoordinate Z -> Real) (z y : Z)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  (n : Real) / transitionVisitMass z n x *
    max
      (countableTransitionCoordinateBoundary
        prior z y false delta j n x)
      (countableTransitionCoordinateBoundary
        prior z y true delta j n x)

/-- Sum of the simultaneous countable-catalog coordinate radii in
total-variation scale. -/
def countableEmpiricalTransitionRowRadius
    (prior : TransitionCoordinate Z -> Real) (z : Z)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  (1 / 2 : Real) * ∑ y : Z,
    countableTransitionCoordinateRadius prior z y delta j n x

/-- Maximum empirical candidate discrepancy plus countable-catalog
statistical radius over all source rows. -/
def countableEmpiricalCandidateKernelTVBudget
    (Q : Z -> PMF Z) (prior : TransitionCoordinate Z -> Real)
    (delta : Real) (j n : Nat) (x : Nat -> Z) : Real :=
  finiteMaximum fun z =>
    empiricalCandidateRowTotalVariation Q z n x +
      countableEmpiricalTransitionRowRadius prior z delta j n x

/-! ## Selected geometric atom and asymptotic widths -/

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- For either side of a fixed transition coordinate, the exact boundary at
the explicit every-sample-size geometric atom tends to zero along every path.
-/
theorem countableTransitionCoordinateBoundary_selected_tendsto_zero
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (z y : Z) (complement : Bool) (x : Nat -> Z) :
    Tendsto
      (fun n => countableTransitionCoordinateBoundary
        prior z y complement delta (geometricForwardTiltIndex n) n x)
      atTop (nhds 0) := by
  simpa [countableTransitionCoordinateBoundary] using
    (trajectoryCountableEmpiricalBernsteinPACBayesBoundary_selected_tendsto_zero
      hprior
      (fun _n =>
        diracPosterior
          (⟨z, y, complement⟩ : TransitionCoordinate Z))
      (fun _n =>
        diracPosterior_isPMF
          (⟨z, y, complement⟩ : TransitionCoordinate Z))
      transitionCoordinateTrajectoryScore_mem_Icc
      hdelta hdelta_one x)

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- If the source row has positive limiting visit frequency, its normalized
coordinate radius at the selected geometric atom tends to zero. -/
theorem countableTransitionCoordinateRadius_selected_tendsto_zero_of_visitFrequency
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (z y : Z) (x : Nat -> Z) {frequency : Real}
    (hfrequency : Tendsto
      (fun n => transitionVisitMass z n x / (n : Real))
      atTop (nhds frequency))
    (hfrequency_pos : 0 < frequency) :
    Tendsto
      (fun n => countableTransitionCoordinateRadius prior z y delta
        (geometricForwardTiltIndex n) n x)
      atTop (nhds 0) := by
  have hratio : Tendsto
      (fun n : Nat => (n : Real) / transitionVisitMass z n x)
      atTop (nhds frequency⁻¹) := by
    simpa only [inv_div] using hfrequency.inv₀ hfrequency_pos.ne'
  have hdirect :=
    countableTransitionCoordinateBoundary_selected_tendsto_zero
      hprior hdelta hdelta_one z y false x
  have hcomplement :=
    countableTransitionCoordinateBoundary_selected_tendsto_zero
      hprior hdelta hdelta_one z y true x
  have hmax : Tendsto
      (fun n => max
        (countableTransitionCoordinateBoundary
          prior z y false delta (geometricForwardTiltIndex n) n x)
        (countableTransitionCoordinateBoundary
          prior z y true delta (geometricForwardTiltIndex n) n x))
      atTop (nhds 0) := by
    simpa using hdirect.max hcomplement
  simpa [countableTransitionCoordinateRadius] using hratio.mul hmax

omit [Nonempty Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- Under positive limiting visit frequency, the complete row-TV statistical
radius at the selected geometric atom tends to zero. -/
theorem countableEmpiricalTransitionRowRadius_selected_tendsto_zero_of_visitFrequency
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (z : Z) (x : Nat -> Z) {frequency : Real}
    (hfrequency : Tendsto
      (fun n => transitionVisitMass z n x / (n : Real))
      atTop (nhds frequency))
    (hfrequency_pos : 0 < frequency) :
    Tendsto
      (fun n => countableEmpiricalTransitionRowRadius prior z delta
        (geometricForwardTiltIndex n) n x)
      atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n => ∑ y : Z,
        countableTransitionCoordinateRadius prior z y delta
          (geometricForwardTiltIndex n) n x)
      atTop (nhds 0) := by
    simpa using
      (tendsto_finsetSum (Finset.univ : Finset Z) fun y _hy =>
        countableTransitionCoordinateRadius_selected_tendsto_zero_of_visitFrequency
          hprior hdelta hdelta_one z y x hfrequency hfrequency_pos)
  simpa [countableEmpiricalTransitionRowRadius] using
    (tendsto_const_nhds.mul hsum : Tendsto
      (fun n => (1 / 2 : Real) * ∑ y : Z,
        countableTransitionCoordinateRadius prior z y delta
          (geometricForwardTiltIndex n) n x)
      atTop (nhds ((1 / 2 : Real) * 0)))

omit [MeasurableSpace Z] [MeasurableSingletonClass Z] in
/-- The selected kernel-TV budget tends to zero only when every row is visited
at a positive limiting frequency and the selected candidate's empirical row
discrepancy itself tends to zero. -/
theorem countableEmpiricalCandidateKernelTVBudget_selected_tendsto_zero
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (Q : Nat -> Z -> PMF Z) (x : Nat -> Z)
    (hfrequency : ∀ z : Z, ∃ frequency : Real,
      0 < frequency ∧
        Tendsto (fun n => transitionVisitMass z n x / (n : Real))
          atTop (nhds frequency))
    (hcandidate : ∀ z : Z,
      Tendsto
        (fun n => empiricalCandidateRowTotalVariation (Q n) z n x)
        atTop (nhds 0)) :
    Tendsto
      (fun n => countableEmpiricalCandidateKernelTVBudget
        (Q n) prior delta (geometricForwardTiltIndex n) n x)
      atTop (nhds 0) := by
  have hrow : ∀ z : Z, Tendsto
      (fun n => empiricalCandidateRowTotalVariation (Q n) z n x +
        countableEmpiricalTransitionRowRadius prior z delta
          (geometricForwardTiltIndex n) n x)
      atTop (nhds 0) := by
    intro z
    obtain ⟨frequency, hfrequency_pos, hfrequency_limit⟩ := hfrequency z
    simpa using (hcandidate z).add
      (countableEmpiricalTransitionRowRadius_selected_tendsto_zero_of_visitFrequency
        hprior hdelta hdelta_one z x hfrequency_limit hfrequency_pos)
  have hmaximum := Filter.Tendsto.finset_sup'_nhds_apply
    (s := (Finset.univ : Finset Z)) Finset.univ_nonempty
    (g := fun _z : Z => (0 : Real))
    (fun z _hz => hrow z)
  simpa [countableEmpiricalCandidateKernelTVBudget, finiteMaximum] using hmaximum

/-! ## One event, all natural tilt atoms and transition coordinates -/

/-- One countably allocated outer-probability event gives two-sided
time-uniform confidence bands for every transition coordinate and every
natural-number geometric tilt atom. -/
theorem exists_countableEmpiricalTransitionCoordinate_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, ∀ j : Nat, ∀ n : Nat, 2 <= n ->
          ∀ z y : Z,
            |(P z y).toReal * transitionVisitMass z n x / (n : Real) -
                transitionEdgeMass z y n x / (n : Real)| <
              max
                (countableTransitionCoordinateBoundary
                  prior z y false delta j n x)
                (countableTransitionCoordinateBoundary
                  prior z y true delta j n x) := by
  rcases exists_trajectoryCountableEmpiricalBernsteinPACBayes_event
      (ι := TransitionCoordinate Z) (prefixKernel P) x0
      (score := transitionCoordinateTrajectoryScore)
      transitionCoordinateTrajectoryScore_mem_Icc hprior hdelta with
    ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, ?_, ?_⟩
  · simpa [trajectoryMeasure_prefixKernel_eq_markovPathMeasure] using hmass
  · intro x hx j n hn z y
    have hnpos : 0 < n := by omega
    have hdirect := hgood x hx j
      (diracPosterior (⟨z, y, false⟩ : TransitionCoordinate Z))
      (diracPosterior_isPMF (⟨z, y, false⟩ : TransitionCoordinate Z)) n hn
    have hcomplement := hgood x hx j
      (diracPosterior (⟨z, y, true⟩ : TransitionCoordinate Z))
      (diracPosterior_isPMF (⟨z, y, true⟩ : TransitionCoordinate Z)) n hn
    unfold trajectoryPosteriorAverageConditionalRisk
      trajectoryPosteriorEmpiricalPrequentialRisk at hdirect hcomplement
    rw [pacBayesPosteriorAverage_dirac,
      pacBayesPosteriorAverage_dirac] at hdirect hcomplement
    change
      trajectoryAverageConditionalRisk (prefixKernel P)
          (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) n x <
        trajectoryEmpiricalPrequentialRisk
            (transitionCoordinateTrajectoryScore ⟨z, y, false⟩) n x +
          countableTransitionCoordinateBoundary
            prior z y false delta j n x at hdirect
    change
      trajectoryAverageConditionalRisk (prefixKernel P)
          (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) n x <
        trajectoryEmpiricalPrequentialRisk
            (transitionCoordinateTrajectoryScore ⟨z, y, true⟩) n x +
          countableTransitionCoordinateBoundary
            prior z y true delta j n x at hcomplement
    rw [trajectoryAverageConditionalRisk_transitionCoordinate_direct,
      trajectoryEmpiricalPrequentialRisk_transitionCoordinate_direct] at hdirect
    rw [trajectoryAverageConditionalRisk_transitionCoordinate_complement
          P z y hnpos,
      trajectoryEmpiricalPrequentialRisk_transitionCoordinate_complement
          z y hnpos] at hcomplement
    rw [abs_lt]
    constructor
    · calc
        -max
            (countableTransitionCoordinateBoundary
              prior z y false delta j n x)
            (countableTransitionCoordinateBoundary
              prior z y true delta j n x) <=
          -countableTransitionCoordinateBoundary
              prior z y true delta j n x := by
            exact neg_le_neg (le_max_right _ _)
        _ < (P z y).toReal * transitionVisitMass z n x / (n : Real) -
              transitionEdgeMass z y n x / (n : Real) := by
            linarith
    · have hmax := le_max_left
        (countableTransitionCoordinateBoundary
          prior z y false delta j n x)
        (countableTransitionCoordinateBoundary
          prior z y true delta j n x)
      linarith

/-- On the same event, every visited transition row has normalized coordinate
confidence radii for every natural tilt atom. -/
theorem exists_countableEmpiricalTransitionFrequency_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, ∀ j : Nat, ∀ n : Nat, 2 <= n ->
          ∀ z : Z, 0 < transitionVisitMass z n x -> ∀ y : Z,
            |(P z y).toReal - empiricalTransitionFrequency z y n x| <
              countableTransitionCoordinateRadius
                prior z y delta j n x := by
  rcases exists_countableEmpiricalTransitionCoordinate_event
      P x0 hprior hdelta with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j n hn z hvisit y
  have hnpos : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hband := hgood x hx j n hn z y
  let boundary : Real :=
    max
      (countableTransitionCoordinateBoundary
        prior z y false delta j n x)
      (countableTransitionCoordinateBoundary
        prior z y true delta j n x)
  have hfactor : 0 < (n : Real) / transitionVisitMass z n x :=
    div_pos hnpos hvisit
  have hidentity :
      (P z y).toReal - empiricalTransitionFrequency z y n x =
        ((n : Real) / transitionVisitMass z n x) *
          ((P z y).toReal * transitionVisitMass z n x / (n : Real) -
            transitionEdgeMass z y n x / (n : Real)) := by
    unfold empiricalTransitionFrequency
    field_simp [hnpos.ne', hvisit.ne']
  rw [hidentity, abs_mul, abs_of_pos hfactor]
  change (n : Real) / transitionVisitMass z n x *
      |(P z y).toReal * transitionVisitMass z n x / (n : Real) -
        transitionEdgeMass z y n x / (n : Real)| <
    (n : Real) / transitionVisitMass z n x * boundary
  exact mul_lt_mul_of_pos_left hband hfactor

/-- The simultaneous coordinate bands certify a row-total-variation ball
around every candidate kernel.  Candidate quantification occurs inside the
already-fixed event. -/
theorem exists_countableEmpiricalCandidateRowTotalVariation_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, ∀ j : Nat, ∀ n : Nat, 2 <= n ->
          ∀ z : Z, 0 < transitionVisitMass z n x ->
            ∀ Q : Z -> PMF Z,
              finitePMFTotalVariation (P z) (Q z) <=
                empiricalCandidateRowTotalVariation Q z n x +
                  countableEmpiricalTransitionRowRadius
                    prior z delta j n x := by
  rcases exists_countableEmpiricalTransitionFrequency_event
      P x0 hprior hdelta with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j n hn z hvisit Q
  have hcoordinate : ∀ y : Z,
      |(P z y).toReal - (Q z y).toReal| <=
        |(Q z y).toReal - empiricalTransitionFrequency z y n x| +
          countableTransitionCoordinateRadius prior z y delta j n x := by
    intro y
    calc
      |(P z y).toReal - (Q z y).toReal| <=
          |(P z y).toReal - empiricalTransitionFrequency z y n x| +
            |empiricalTransitionFrequency z y n x - (Q z y).toReal| :=
        abs_sub_le _ _ _
      _ <= countableTransitionCoordinateRadius prior z y delta j n x +
            |empiricalTransitionFrequency z y n x - (Q z y).toReal| :=
        add_le_add (le_of_lt (hgood x hx j n hn z hvisit y)) (le_refl _)
      _ = |(Q z y).toReal - empiricalTransitionFrequency z y n x| +
            countableTransitionCoordinateRadius prior z y delta j n x := by
        rw [abs_sub_comm]
        ring
  unfold finitePMFTotalVariation empiricalCandidateRowTotalVariation
    countableEmpiricalTransitionRowRadius
  calc
    (1 / 2 : Real) * ∑ y : Z, |(P z y).toReal - (Q z y).toReal| <=
        (1 / 2 : Real) * ∑ y : Z,
          (|(Q z y).toReal - empiricalTransitionFrequency z y n x| +
            countableTransitionCoordinateRadius prior z y delta j n x) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun y _hy => hcoordinate y) (by norm_num)
    _ = (1 / 2 : Real) * ∑ y : Z,
          |(Q z y).toReal - empiricalTransitionFrequency z y n x| +
        (1 / 2 : Real) * ∑ y : Z,
          countableTransitionCoordinateRadius prior z y delta j n x := by
      rw [Finset.sum_add_distrib]
      ring

/-- Explicit substitution for a path- and time-selected candidate kernel.
No additional selection cost is introduced. -/
theorem exists_selectedCountableEmpiricalCandidateRowTotalVariation_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta)
    (selectQ : (Nat -> Z) -> Nat -> Z -> PMF Z) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, ∀ j : Nat, ∀ n : Nat, 2 <= n ->
          ∀ z : Z, 0 < transitionVisitMass z n x ->
            finitePMFTotalVariation (P z) (selectQ x n z) <=
              empiricalCandidateRowTotalVariation (selectQ x n) z n x +
                countableEmpiricalTransitionRowRadius
                  prior z delta j n x := by
  rcases exists_countableEmpiricalCandidateRowTotalVariation_event
      P x0 hprior hdelta with ⟨goodEvent, hmass, hgood⟩
  exact ⟨goodEvent, hmass, fun x hx j n hn z hvisit =>
    hgood x hx j n hn z hvisit (selectQ x n)⟩

/-- If every source row is visited, the same event gives one kernel-wide TV
budget for every natural tilt atom and every candidate kernel. -/
theorem exists_countableEmpiricalCandidateKernelTV_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, ∀ j : Nat, ∀ n : Nat, 2 <= n ->
          (∀ z : Z, 0 < transitionVisitMass z n x) ->
            ∀ Q : Z -> PMF Z, ∀ z : Z,
              finitePMFTotalVariation (P z) (Q z) <=
                countableEmpiricalCandidateKernelTVBudget
                  Q prior delta j n x := by
  rcases exists_countableEmpiricalCandidateRowTotalVariation_event
      P x0 hprior hdelta with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_⟩
  intro x hx j n hn hall Q z
  exact (hgood x hx j n hn z (hall z) Q).trans
    (le_finiteMaximum
      (fun source =>
        empiricalCandidateRowTotalVariation Q source n x +
          countableEmpiricalTransitionRowRadius
            prior source delta j n x) z)

/-- Path- and time-dependent candidate-kernel selection is valid inside the
same countable coordinate event. -/
theorem exists_selectedCountableEmpiricalCandidateKernelTV_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta)
    (selectQ : (Nat -> Z) -> Nat -> Z -> PMF Z) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        ∀ x ∈ goodEvent, ∀ j : Nat, ∀ n : Nat, 2 <= n ->
          (∀ z : Z, 0 < transitionVisitMass z n x) ->
            ∀ z : Z,
              finitePMFTotalVariation (P z) (selectQ x n z) <=
                countableEmpiricalCandidateKernelTVBudget
                  (selectQ x n) prior delta j n x := by
  rcases exists_countableEmpiricalCandidateKernelTV_event
      P x0 hprior hdelta with ⟨goodEvent, hmass, hgood⟩
  exact ⟨goodEvent, hmass, fun x hx j n hn hall =>
    hgood x hx j n hn hall (selectQ x n)⟩

/-- Selecting `geometricForwardTiltIndex n` inside the common countable event
gives a concrete every-sample-size coordinate band, while both one-sided
coordinate boundaries converge to zero along every path. -/
theorem exists_countableEmpiricalTransitionGeometric_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        (∀ x ∈ goodEvent, ∀ n : Nat, 2 <= n -> ∀ z y : Z,
          |(P z y).toReal * transitionVisitMass z n x / (n : Real) -
              transitionEdgeMass z y n x / (n : Real)| <
            max
              (countableTransitionCoordinateBoundary prior z y false delta
                (geometricForwardTiltIndex n) n x)
              (countableTransitionCoordinateBoundary prior z y true delta
                (geometricForwardTiltIndex n) n x)) ∧
        (∀ x ∈ goodEvent, ∀ z y : Z, ∀ complement : Bool,
          Tendsto
            (fun n => countableTransitionCoordinateBoundary
              prior z y complement delta (geometricForwardTiltIndex n) n x)
            atTop (nhds 0)) := by
  rcases exists_countableEmpiricalTransitionCoordinate_event
      P x0 hprior hdelta with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro x hx n hn z y
    exact hgood x hx (geometricForwardTiltIndex n) n hn z y
  · intro x _hx z y complement
    exact countableTransitionCoordinateBoundary_selected_tendsto_zero
      hprior hdelta hdelta_one z y complement x

/-- Capstone for a path- and time-selected candidate kernel and the explicit
geometric atom.  The common event supplies the all-row TV certificate.  On a
particular path, the displayed kernel budget tends to zero only after both
positive limiting row frequencies and vanishing empirical candidate-row
discrepancies are supplied. -/
theorem exists_selectedCountableEmpiricalCandidateKernelTVGeometric_event
    (P : Z -> PMF Z) (x0 : Z)
    {prior : TransitionCoordinate Z -> Real}
    (hprior : IsFullSupportPMF prior)
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (selectQ : (Nat -> Z) -> Nat -> Z -> PMF Z) :
    ∃ goodEvent : Set (Nat -> Z),
      (markovPathMeasure P x0).real goodEventᶜ <= delta ∧
        (∀ x ∈ goodEvent, ∀ n : Nat, 2 <= n ->
          (∀ z : Z, 0 < transitionVisitMass z n x) -> ∀ z : Z,
            finitePMFTotalVariation (P z) (selectQ x n z) <=
              countableEmpiricalCandidateKernelTVBudget
                (selectQ x n) prior delta
                  (geometricForwardTiltIndex n) n x) ∧
        (∀ x ∈ goodEvent,
          (∀ z : Z, ∃ frequency : Real,
            0 < frequency ∧
              Tendsto (fun n => transitionVisitMass z n x / (n : Real))
                atTop (nhds frequency)) ->
          (∀ z : Z,
            Tendsto
              (fun n => empiricalCandidateRowTotalVariation
                (selectQ x n) z n x)
              atTop (nhds 0)) ->
          Tendsto
            (fun n => countableEmpiricalCandidateKernelTVBudget
              (selectQ x n) prior delta
                (geometricForwardTiltIndex n) n x)
            atTop (nhds 0)) := by
  rcases exists_countableEmpiricalCandidateKernelTV_event
      P x0 hprior hdelta with ⟨goodEvent, hmass, hgood⟩
  refine ⟨goodEvent, hmass, ?_, ?_⟩
  · intro x hx n hn hall z
    exact hgood x hx (geometricForwardTiltIndex n) n hn hall
      (selectQ x n) z
  · intro x _hx hfrequency hcandidate
    exact countableEmpiricalCandidateKernelTVBudget_selected_tendsto_zero
      hprior hdelta hdelta_one (fun n => selectQ x n) x
      hfrequency hcandidate

end

end FormalSLT.StochasticDynamics
