import FormalSLT.Applications.ControlledQueueStructuredOPE

/-!
# Structured controlled-queue unknown-dynamics OPE checker

This checker audits the complete public surface, the frozen depth and tilt
catalogs, and an explicit selector instantiation at a true persistence
parameter outside the three-candidate catalog.  It does not evaluate a path or
claim membership in the theorem-produced good event.
-/

open MeasureTheory ProbabilityTheory

open FormalSLT.PACBayesKL
open FormalSLT.PACBayes.StabilityBridge
open FormalSLT.Applications.ControlledQueue
open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

namespace FormalSLT.Examples.CheckControlledQueueStructuredOPE

noncomputable section

#check QueuePath
#check queueCandidateFiniteDepthSpan
#check queueCandidateFiniteDepthPotential
#check structuredQueueOPEBoundary
#check structuredQueueFiniteDepthResidual
#check queueCandidateFiniteDepthPotential_span
#check exists_structuredControlledQueueFiniteCatalogOPE_event
#check QueueDepthIndex
#check queueDepth
#check QueueCandidateDepthIndex
#check queueCandidateDepthCatalog
#check queueCandidateDepthWeight
#check QueueStructuredTiltIndex
#check queueStructuredTilt
#check queueStructuredTiltWeight
#check queueCandidateDepth_card
#check queueCandidateDepthWeight_apply
#check queueCandidateDepthWeight_isFullSupport
#check queueStructuredTiltWeight_apply
#check queueStructuredTiltWeight_isFullSupport
#check queueStructuredTilt_pos
#check queueStructuredTilt_lt_one
#check queueStructuredOPEBoundary
#check queueStructuredFiniteDepthResidual
#check exists_controlledQueueStructuredAdaptiveOPE_event
#check exists_selectedControlledQueueStructuredAdaptiveOPE_event

#print axioms queueCandidateFiniteDepthPotential_span
#print axioms exists_structuredControlledQueueFiniteCatalogOPE_event
#print axioms queueCandidateDepth_card
#print axioms queueCandidateDepthWeight_apply
#print axioms queueCandidateDepthWeight_isFullSupport
#print axioms queueStructuredTiltWeight_apply
#print axioms queueStructuredTiltWeight_isFullSupport
#print axioms queueStructuredTilt_pos
#print axioms queueStructuredTilt_lt_one
#print axioms exists_controlledQueueStructuredAdaptiveOPE_event
#print axioms exists_selectedControlledQueueStructuredAdaptiveOPE_event

/-- The generated depth and admissible-tilt accessors retain their exact
declared order. -/
theorem frozen_catalog_values :
    (∀ depth : QueueDepthIndex,
      queueDepth depth = [0, 1, 2, 3, 5, 8, 12].get depth) ∧
    (∀ tilt : QueueStructuredTiltIndex,
      queueStructuredTilt tilt =
        ([1 / 16, 1 / 8, 1 / 4, 1 / 2] : List ℝ).get tilt) := by
  constructor
  · intro depth
    fin_cases depth <;>
      norm_num [queueDepth,
        FormalSLT.Applications.ControlledQueueData.depthGrid]
  · intro tilt
    fin_cases tilt <;>
      norm_num [queueStructuredTilt,
        FormalSLT.Applications.ControlledQueueData.tiltGrid]

/-- A true persistence parameter outside the generated three-candidate
catalog. -/
def checkerPersistence : PersistenceParameter :=
  ⟨1 / 2, by constructor <;> norm_num⟩

/-- Checker-selected nominal candidate and depth twelve. -/
def checkerCandidateDepth (_path : QueuePath) (_n : ℕ) :
    QueueCandidateDepthIndex :=
  (1, ⟨6, by norm_num⟩)

/-- Checker-selected first admissible risk tilt. -/
def checkerRiskTilt (_path : QueuePath) (_n : ℕ) :
    QueueStructuredTiltIndex :=
  0

/-- Checker-selected second admissible persistence tilt. -/
def checkerPersistenceTilt (_path : QueuePath) (_n : ℕ) :
    QueueStructuredTiltIndex :=
  1

/-- Checker-selected point posterior on queue-threshold policy and nominal
model predictor. -/
def checkerPosterior (_path : QueuePath) (_n : ℕ) :
    QueueHypothesis → ℝ :=
  diracPosterior ((1 : TargetPolicyIndex), (2 : FixedPredictorIndex))

theorem checkerPosterior_isPMF (path : QueuePath) (n : ℕ) :
    IsPMF (checkerPosterior path n) := by
  exact diracPosterior_isPMF _

/-- Concrete selector instantiation.  The theorem still asserts only an
outer-mass event and does not certify any named path. -/
theorem halfPersistence_selected_event_signature
    (initial : Observation) :
    ∃ goodEvent : Set QueuePath,
      (controlledTrajectoryMeasure
          (refreshEnvironment checkerPersistence)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ 1 / 20 ∧
      ∀ path ∈ goodEvent, ∀ n : ℕ, 2 ≤ n →
        stationaryTargetPolicyPosteriorRisk
            (refreshEnvironment checkerPersistence)
            queueHypothesisTargetPolicy
            (queueHypothesisStationary
              (refreshEnvironment checkerPersistence))
            queueHypothesisScore (checkerPosterior path n) <
          queueStructuredOPEBoundary
              (checkerCandidateDepth path n)
              (checkerRiskTilt path n)
              (checkerPosterior path n) n path +
            queueStructuredFiniteDepthResidual
              (checkerCandidateDepth path n)
              (checkerPersistenceTilt path n) n path := by
  exact exists_selectedControlledQueueStructuredAdaptiveOPE_event
    checkerPersistence initial checkerCandidateDepth
    checkerRiskTilt checkerPersistenceTilt checkerPosterior
    checkerPosterior_isPMF

#print axioms frozen_catalog_values
#print axioms checkerPosterior_isPMF
#print axioms halfPersistence_selected_event_signature

end

end FormalSLT.Examples.CheckControlledQueueStructuredOPE
