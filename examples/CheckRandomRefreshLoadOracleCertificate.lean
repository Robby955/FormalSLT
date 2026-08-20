import FormalSLT.Applications.RandomRefreshLoadOracleCertificate

open FormalSLT.StochasticDynamics
open FormalSLT.StochasticDynamics.RandomRefreshLoadModel
open FormalSLT.StochasticDynamics.RandomRefreshLoadOracleCertificate

#check OrientedPredictor
#check orientedBrierScore
#check orientedPredictorPrior
#check oracleRiskFailureBudget
#check orientedPosterior
#check orientedPredictorPrior_isFullSupport
#check oracleRiskFailureBudget_pos
#check orientedPosterior_isPMF
#check orientedBrierScore_mem_Icc
#check markovRowRisk_one_sub
#check stationaryMarkovRisk_one_sub
#check empiricalTransitionRisk_one_sub
#check centeredMarkovRowRisk_one_sub
#check orientedBrierScore_centeredOscillation_le
#check empiricalPredictorRisk
#check oracleSelectedPredictor
#check oracleSelectedPredictor_empiricalRisk_minimal
#check orientedNormal_stationaryPosteriorRisk
#check orientedFlipped_stationaryPosteriorRisk
#check orientedNormal_empiricalPosteriorRisk
#check orientedFlipped_empiricalPosteriorRisk
#check selectedUpperBoundary
#check predictorLowerBoundary
#check predictorLowerConfidenceEndpoint
#check selectedOraclePenalty
#check catalogMinimumStationaryRisk
#check oracle_stationaryRisk_eq_catalogMinimum
#check catalogMinimumStationaryRisk_le
#check twoSidedOracleExceptionalEvent
#check twoSidedOracleExceptionalEvent_mass_le
#check IsTwoSidedOracleEvent
#check exists_randomRefreshLoad_twoSidedOracle_event
#check exists_randomRefreshLoad_twoSidedOracle_le_event

#print axioms orientedPredictorPrior_isFullSupport
#print axioms oracleRiskFailureBudget_pos
#print axioms orientedPosterior_isPMF
#print axioms orientedBrierScore_mem_Icc
#print axioms markovRowRisk_one_sub
#print axioms stationaryMarkovRisk_one_sub
#print axioms empiricalTransitionRisk_one_sub
#print axioms centeredMarkovRowRisk_one_sub
#print axioms orientedBrierScore_centeredOscillation_le
#print axioms oracleSelectedPredictor_empiricalRisk_minimal
#print axioms orientedNormal_stationaryPosteriorRisk
#print axioms orientedFlipped_stationaryPosteriorRisk
#print axioms orientedNormal_empiricalPosteriorRisk
#print axioms orientedFlipped_empiricalPosteriorRisk
#print axioms oracle_stationaryRisk_eq_catalogMinimum
#print axioms catalogMinimumStationaryRisk_le
#print axioms twoSidedOracleExceptionalEvent_mass_le
#print axioms exists_randomRefreshLoad_twoSidedOracle_event
#print axioms exists_randomRefreshLoad_twoSidedOracle_le_event

/-! A real checker witness: this instantiates the nominal catalog minimum and
the complete theorem-produced two-sided event. -/
example :
    catalogMinimumStationaryRisk = 3 / 20 ∧
      (∀ i : Predictor,
        catalogMinimumStationaryRisk ≤
          stationaryMarkovRisk (refreshKernel Candidate.nominal) uniformLaw
            (brierScore i)) := by
  exact ⟨rfl, catalogMinimumStationaryRisk_le⟩

example :
    ∃ goodEvent : Set (ℕ → State),
      (markovPathMeasure (refreshKernel Candidate.nominal) 0).real
          goodEventᶜ ≤ 1 / 20 ∧
        IsTwoSidedOracleEvent goodEvent :=
  exists_randomRefreshLoad_twoSidedOracle_event
