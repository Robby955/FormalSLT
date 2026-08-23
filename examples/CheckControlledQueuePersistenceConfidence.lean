import FormalSLT.Applications.ControlledQueuePersistenceConfidence

/-!
# Structured controlled-queue persistence-confidence receipt

The concrete parameter `1/2` belongs to the structured refresh family but is
not one of the three generated candidates.  The first receipt checks candidate
embedding and the exact arbitrary-parameter row-TV identity without expanding
a 24-state sum.  The second instantiates the simultaneous event but does not
claim that a named deterministic path belongs to its good event.
-/

open MeasureTheory ProbabilityTheory

open FormalSLT.PACBayesKL
open FormalSLT.Applications.ControlledQueue
open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

namespace FormalSLT.Examples.CheckControlledQueuePersistenceConfidence

noncomputable section

#check PersistenceParameter
#check refreshEnvironmentMass
#check refreshEnvironment
#check refreshEnvironment_apply_toReal
#check candidatePersistenceParameter
#check persistenceHitProbability
#check candidatePersistenceHitProbability
#check candidateEnvironment_eq_refreshEnvironment
#check persistenceDestinationHitScore
#check orientedPersistenceHitMarkovScore
#check orientedPersistenceHitScore
#check orientedPersistenceHitScore_mem_Icc
#check persistenceDestinationHit_rowRisk
#check empiricalPersistenceHitRate
#check persistenceHitBoundary
#check persistenceHitRadius
#check exists_persistenceHitConfidence_event
#check refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy
#check structuredCandidateTVBudget
#check exists_structuredCandidateTVConfidence_event

#print axioms refreshEnvironment_apply_toReal
#print axioms candidateEnvironment_eq_refreshEnvironment
#print axioms orientedPersistenceHitScore_mem_Icc
#print axioms persistenceDestinationHit_rowRisk
#print axioms exists_persistenceHitConfidence_event
#print axioms refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy
#print axioms exists_structuredCandidateTVConfidence_event

/-- A valid true persistence parameter outside the generated catalog. -/
def halfPersistenceParameter : PersistenceParameter :=
  ⟨1 / 2, by constructor <;> norm_num⟩

/-- Candidate zero embeds exactly, while its row distance from the arbitrary
true parameter `1/2` is `23/192` in every physical row. -/
theorem halfPersistence_structured_row_receipt :
    (∀ candidate : CandidateIndex,
      (halfPersistenceParameter : ℝ) ≠ candidateGamma candidate) ∧
    candidateEnvironment (0 : CandidateIndex) =
      refreshEnvironment
        (candidatePersistenceParameter (0 : CandidateIndex)) ∧
    ∀ state : PhysicalState, ∀ action : Action,
      finitePMFTotalVariation
          (refreshEnvironment halfPersistenceParameter state action)
          (candidateEnvironment (0 : CandidateIndex) state action) =
        (23 / 192 : ℝ) := by
  constructor
  · intro candidate
    fin_cases candidate <;>
      norm_num [halfPersistenceParameter, candidateGamma, candidateGammaRat,
        candidateGammaTable]
  constructor
  · exact candidateEnvironment_eq_refreshEnvironment (0 : CandidateIndex)
  · intro state action
    rw [refreshEnvironment_candidate_rowTV_eq_hitDiscrepancy]
    norm_num [halfPersistenceParameter, persistenceHitProbability,
      candidatePersistenceHitProbability, candidatePersistenceParameter,
      candidateGamma, candidateGammaRat, candidateGammaTable]

/-- Uniform prior over two checker-only persistence tilts. -/
def persistenceReceiptTiltWeight (_j : Bool) : ℝ := 1 / 2

theorem persistenceReceiptTiltWeight_isFullSupport :
    IsFullSupportPMF persistenceReceiptTiltWeight := by
  constructor
  · constructor <;> simp [persistenceReceiptTiltWeight]
  · intro j
    simp [persistenceReceiptTiltWeight]

def persistenceReceiptTilt (j : Bool) : ℝ :=
  if j then 1 / 4 else 1 / 8

theorem persistenceReceiptTilt_pos (j : Bool) :
    0 < persistenceReceiptTilt j := by
  cases j <;> norm_num [persistenceReceiptTilt]

theorem persistenceReceiptTilt_lt_one (j : Bool) :
    persistenceReceiptTilt j < 1 := by
  cases j <;> norm_num [persistenceReceiptTilt]

/-- Concrete simultaneous event at a true parameter that is not itself a
generated candidate. -/
theorem halfPersistence_structured_event_signature
    (initial : Observation) :
    ∃ goodEvent : Set (ℕ → Observation),
      (controlledTrajectoryMeasure
          (refreshEnvironment halfPersistenceParameter)
          (markovBehaviorPolicyAsHistory behaviorPolicy) initial).real
          goodEventᶜ ≤ (1 / 40 : ℝ) ∧
      ∀ path ∈ goodEvent, ∀ j : Bool, ∀ n : ℕ, 2 ≤ n →
        ∀ candidate : CandidateIndex,
          ∀ state : PhysicalState, ∀ action : Action,
            finitePMFTotalVariation
                (refreshEnvironment halfPersistenceParameter state action)
                (candidateEnvironment candidate state action) <
              structuredCandidateTVBudget candidate
                persistenceReceiptTiltWeight persistenceReceiptTilt
                (1 / 40 : ℝ) j n path := by
  exact exists_structuredCandidateTVConfidence_event
    (τ := Bool)
    halfPersistenceParameter initial
    (weight := persistenceReceiptTiltWeight)
    (lam := persistenceReceiptTilt)
    (delta := (1 / 40 : ℝ))
    persistenceReceiptTiltWeight_isFullSupport
    (by norm_num)
    persistenceReceiptTilt_pos
    persistenceReceiptTilt_lt_one

#print axioms halfPersistence_structured_row_receipt
#print axioms persistenceReceiptTiltWeight_isFullSupport
#print axioms persistenceReceiptTilt_pos
#print axioms persistenceReceiptTilt_lt_one
#print axioms halfPersistence_structured_event_signature

end

end FormalSLT.Examples.CheckControlledQueuePersistenceConfidence
