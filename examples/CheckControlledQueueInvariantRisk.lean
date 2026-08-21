import FormalSLT.Applications.ControlledQueueInvariantRisk

open FormalSLT.Applications.ControlledQueue

#check queueThresholdTargetIndex
#check nominalModelOverloadPredictorIndex
#check queueThresholdNominalModelHypothesis
#check queueThresholdStationaryMassRat
#check queueThresholdStationaryMass_isPMF
#check queueThresholdStationaryLaw
#check queueThresholdStationaryLaw_apply_toReal
#check queueThresholdNominalKernelMassRat
#check queueThresholdNominalTargetKernel_apply_toReal
#check queueThresholdStationaryLaw_isInvariant
#check queueThresholdStationaryLaw_eq_catalogStationary
#check queueThresholdNominalModelRowRisk
#check queueThreshold_nominalModelOverload_rowRisk
#check queueThreshold_nominalModelOverload_stationaryRisk
#check queueThreshold_nominalModelOverload_catalogStationaryRisk

#print axioms queueThresholdStationaryMass_isPMF
#print axioms queueThresholdStationaryLaw_apply_toReal
#print axioms queueThresholdNominalTargetKernel_apply_toReal
#print axioms queueThresholdStationaryLaw_isInvariant
#print axioms queueThresholdStationaryLaw_eq_catalogStationary
#print axioms queueThreshold_nominalModelOverload_rowRisk
#print axioms queueThreshold_nominalModelOverload_stationaryRisk
#print axioms queueThreshold_nominalModelOverload_catalogStationaryRisk

example :
    FormalSLT.StochasticDynamics.stationaryTargetPolicyRisk
        nominalCandidateEnvironment
        (targetPolicy queueThresholdTargetIndex)
        queueThresholdStationaryLaw
        (fixedBrierScore nominalModelOverloadPredictorIndex) < 13 / 200 := by
  rw [queueThreshold_nominalModelOverload_stationaryRisk]
  norm_num

example :
    FormalSLT.StochasticDynamics.stationaryTargetPolicyRisk
        nominalCandidateEnvironment
        (queueHypothesisTargetPolicy queueThresholdNominalModelHypothesis)
        (queueHypothesisStationary nominalCandidateEnvironment
          queueThresholdNominalModelHypothesis)
        (queueHypothesisScore queueThresholdNominalModelHypothesis) < 13 / 200 := by
  rw [queueThreshold_nominalModelOverload_catalogStationaryRisk]
  norm_num
