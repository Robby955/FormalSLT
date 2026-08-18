import FormalSLT.StochasticDynamics.StationaryPoissonDepthSelection

/-!
# Confidence-allocated Poisson-depth selection receipt

The concrete one-state chain uses the strictly sharper oscillation envelope
`D = 1/4` (rather than the generic unit-range bound `D = 1`).  Its depth and
tilt selectors depend on the reported sample size, while the theorem remains
one common outer event.
-/

open Finset MeasureTheory ProbabilityTheory
open FormalSLT.AnytimeValid FormalSLT.PACBayesKL
open FormalSLT.PACBayes.ForwardBesselPACBayesCountable
open scoped ENNReal NNReal

namespace FormalSLT.Examples.CheckStationaryPoissonDepthSelection

open FormalSLT.StochasticDynamics

noncomputable section

def unitTransition (_x : Unit) : PMF Unit := PMF.pure ()

def unitStationary : PMF Unit := PMF.pure ()

theorem unitStationary_invariant :
    IsInvariantPMF unitTransition unitStationary := by
  ext z
  cases z
  simp [unitTransition, unitStationary]

def unitScore (i : Bool) : MarkovTransitionScore Unit :=
  fun _x _y ↦ if i then 1 else 0

theorem unitScore_mem_Icc :
    ∀ i x y, unitScore i x y ∈ Set.Icc (0 : ℝ) 1 := by
  intro i x y
  fin_cases i <;> simp [unitScore]

theorem unitTransition_zero_contraction :
    IsOscillationContraction unitTransition 0 := by
  intro f
  have hzero : finiteOscillation (markovPotentialMean unitTransition f) ≤ 0 :=
    finiteOscillation_le _ (fun x y ↦ by cases x; cases y; simp)
  simpa using hzero

theorem unitScore_centeredOscillation_le_quarter :
    ∀ i,
      finiteOscillation
          (centeredMarkovRowRisk unitTransition unitStationary (unitScore i)) ≤
        (1 / 4 : ℝ) := by
  intro i
  exact finiteOscillation_le _ (fun x y ↦ by
    cases x
    cases y
    norm_num)

def uniformBoolPrior (_i : Bool) : ℝ := 1 / 2

theorem uniformBoolPrior_isFullSupportPMF :
    IsFullSupportPMF uniformBoolPrior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]
  · norm_num [uniformBoolPrior, Fintype.sum_bool]
  · intro i
    fin_cases i <;> norm_num [uniformBoolPrior]

def uniformBoolPosterior (_x : ℕ → Unit) (_n : ℕ) : Bool → ℝ :=
  uniformBoolPrior

theorem uniformBoolPosterior_isPMF (x : ℕ → Unit) (n : ℕ) :
    IsPMF (uniformBoolPosterior x n) :=
  uniformBoolPrior_isFullSupportPMF.toIsPMF

def logarithmicDepth (_x : ℕ → Unit) (n : ℕ) : ℕ := Nat.log 2 n

def allTimeTilt (_x : ℕ → Unit) (n : ℕ) : ℕ :=
  geometricForwardTiltIndex n

/-- Concrete post-time depth-selection certificate with `D = 1/4`. -/
theorem unitChain_logarithmicDepth_certificate :
    ∃ goodEvent : Set (ℕ → Unit),
      (markovPathMeasure unitTransition ()).real goodEventᶜ ≤ 1 / 20 ∧
        ∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          stationaryPosteriorMarkovRisk unitTransition unitStationary
              unitScore (uniformBoolPosterior x n) <
            empiricalTransitionPosteriorRisk
                unitScore (uniformBoolPosterior x n) n x +
              stationaryPoissonDepthSelectionBoundary
                unitTransition unitStationary unitScore 0 (1 / 4)
                uniformBoolPrior (uniformBoolPosterior x n) (1 / 20)
                (logarithmicDepth x n) (allTimeTilt x n) n x := by
  exact exists_stationaryPoissonDepthSelection_selected_event
    unitTransition unitStationary unitStationary_invariant ()
    unitScore_mem_Icc (alpha := (0 : ℝ)) (D := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) unitTransition_zero_contraction
    unitScore_centeredOscillation_le_quarter
    uniformBoolPrior_isFullSupportPMF
    (delta := (1 / 20 : ℝ)) (by norm_num)
    logarithmicDepth allTimeTilt
    uniformBoolPosterior uniformBoolPosterior_isPMF

/-- Concrete one-state receipt for the full deterministic all-time result:
the common-event certificate uses the logarithmic depth, and its exact width
converges to zero on every path. -/
theorem unitChain_allTime_vanishing_certificate :
    ∃ goodEvent : Set (ℕ → Unit),
      (markovPathMeasure unitTransition ()).real goodEventᶜ ≤ 1 / 20 ∧
        (∀ x ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
          stationaryPosteriorMarkovRisk unitTransition unitStationary
              unitScore (uniformBoolPosterior x n) <
            empiricalTransitionPosteriorRisk
                unitScore (uniformBoolPosterior x n) n x +
              stationaryPoissonDepthSelectionBoundary
                unitTransition unitStationary unitScore 0 (1 / 4)
                uniformBoolPrior (uniformBoolPosterior x n) (1 / 20)
                (logarithmicPoissonDepth n)
                (geometricForwardTiltIndex n) n x) ∧
        (∀ x ∈ goodEvent,
          Filter.Tendsto
            (fun n ↦ stationaryPoissonDepthSelectionBoundary
              unitTransition unitStationary unitScore 0 (1 / 4)
              uniformBoolPrior (uniformBoolPosterior x n) (1 / 20)
              (logarithmicPoissonDepth n)
              (geometricForwardTiltIndex n) n x)
            Filter.atTop (nhds 0)) := by
  exact exists_stationaryPoissonDepthSelection_allTime_vanishing_event
    unitTransition unitStationary unitStationary_invariant ()
    unitScore_mem_Icc (alpha := (0 : ℝ)) (D := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    unitTransition_zero_contraction
    unitScore_centeredOscillation_le_quarter
    uniformBoolPrior_isFullSupportPMF
    (delta := (1 / 20 : ℝ)) (by norm_num) (by norm_num)
    uniformBoolPosterior uniformBoolPosterior_isPMF

#check finiteDepthPoissonPotentialCatalog
#check finiteDepthPoissonCorrectedTrajectoryScoreCatalog
#check depthTiltPolynomial_log_cost
#check stationaryPoissonDepthSelectionBoundary_eq_explicit
#check stationaryPoissonDepthAtomExceptionalEvent_mass_le
#check stationaryPoissonDepthSelectionExceptionalEvent_mass_le
#check stationaryPoissonDepthSelection_allPosteriors_of_not_mem
#check exists_stationaryPoissonDepthSelection_event
#check exists_stationaryPoissonDepthSelection_selected_event
#check stationaryPoissonFiniteDepthArgmin_lt_succ
#check stationaryPoissonFiniteDepthArgmin_le
#check logarithmicPoissonDepth_tendsto_atTop
#check logarithmicDepthTiltLogRate_tendsto_zero
#check logarithmicPoissonDepthStationaryRate_tendsto_zero
#check stationaryPoissonDepthSelectionBoundary_logarithmic_tendsto_zero
#check exists_stationaryPoissonDepthSelection_allTime_vanishing_event

#print axioms depthTiltPolynomial_log_cost
#print axioms stationaryPoissonDepthSelectionBoundary_eq_explicit
#print axioms stationaryPoissonDepthAtomExceptionalEvent_mass_le
#print axioms stationaryPoissonDepthSelectionExceptionalEvent_mass_le
#print axioms stationaryPoissonDepthSelection_allPosteriors_of_not_mem
#print axioms exists_stationaryPoissonDepthSelection_event
#print axioms exists_stationaryPoissonDepthSelection_selected_event
#print axioms stationaryPoissonFiniteDepthArgmin_le
#print axioms logarithmicDepthTiltLogRate_tendsto_zero
#print axioms stationaryPoissonDepthSelectionBoundary_logarithmic_tendsto_zero
#print axioms exists_stationaryPoissonDepthSelection_allTime_vanishing_event

#check unitChain_logarithmicDepth_certificate
#print axioms unitChain_logarithmicDepth_certificate
#check unitChain_allTime_vanishing_certificate
#print axioms unitChain_allTime_vanishing_certificate

end

end FormalSLT.Examples.CheckStationaryPoissonDepthSelection
