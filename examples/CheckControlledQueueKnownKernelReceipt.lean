import FormalSLT.Applications.ControlledQueueKnownKernelReceipt

open FormalSLT.Applications.ControlledQueue

#check queueThresholdTargetIndex
#check nominalModelOverloadPredictorIndex
#check queueThresholdNominalModelHypothesis
#check KnownKernelReceiptInternal.RowCertificate
#check certificates00To02
#check certificates03To05
#check certificates06To08
#check certificates09To11
#check certificates12To14
#check certificates15To17
#check certificates18To20
#check certificates21To23
#check knownKernelReceiptDepth
#check knownKernelRiskTilt
#check knownKernelPotentialSpan
#check knownKernelNormalizedScale
#check knownKernelNormalizedScale_eq
#check knownKernelSelectedResidualEnvelope
#check knownKernelSelectedResidual
#check knownKernelSelectedPotential
#check knownKernelPotential
#check knownKernelResidualEnvelope
#check knownKernelSelectedPosterior
#check knownKernelOPEBoundary
#check knownKernelSelectedPotential_mem_Icc
#check knownKernelPotential_span
#check knownKernelCatalogStationaryRisk_mem_Icc
#check nominalTargetPolicyPotentialMean_eq_refreshMixture
#check knownKernelSelectedPotential_residual_eq
#check knownKernelSelectedPotential_residual_le
#check knownKernelPotential_residual_le
#check knownKernelSelectedPosterior_isPMF
#check knownKernelSelectedPosteriorRisk_eq
#check knownKernelRiskTilt_pos
#check knownKernelRiskTilt_lt_one
#check knownKernelReceiptInitial
#check knownKernelReceiptInitial_eq
#check exists_controlledQueueKnownKernelOPE_event
#check exists_controlledQueueKnownKernelReceiptOPE_event
#check knownKernelReceiptHorizon
#check knownKernelReceiptScoreSum
#check knownKernelReceiptSquaredScoreSum
#check knownKernelReceiptBesselQ
#check knownKernelReceiptAffinePenalty
#check knownKernelReceiptD9Bound
#check knownKernelSelectedObservedScore
#check knownKernelSelectedTransitionScore
#check knownKernelSelectedObservedScore_eq_transitionScore
#check knownKernelReceiptSuffixEdgeCount
#check HasReceiptSuffixEdgeHistogram
#check KnownKernelReceiptPathSummary
#check knownKernelReceiptPathSummary_of_suffixEdgeHistogram
#check knownKernelReceipt_besselQ_eq
#check knownKernelReceipt_selectedEmpiricalScore_eq
#check knownKernelReceipt_selectedPenalty_le
#check knownKernelReceipt_selectedLogCost_le_nine
#check knownKernelReceipt_psi_one_sixteen_le_one_twoForty
#check knownKernelReceipt_selectedBoundary_add_residual_le_d9
#check knownKernelReceipt_selectedBoundary_add_residual_le_d9_of_suffixEdgeHistogram
#check knownKernelReceipt_d9_lt_seven_hundredths
#check knownKernelReceipt_selectedRisk_lt_seven_hundredths

#print axioms knownKernelSelectedPotential_mem_Icc
#print axioms certificates00To02
#print axioms certificates03To05
#print axioms certificates06To08
#print axioms certificates09To11
#print axioms certificates12To14
#print axioms certificates15To17
#print axioms certificates18To20
#print axioms certificates21To23
#print axioms knownKernelNormalizedScale_eq
#print axioms knownKernelPotential_span
#print axioms knownKernelCatalogStationaryRisk_mem_Icc
#print axioms nominalTargetPolicyPotentialMean_eq_refreshMixture
#print axioms knownKernelSelectedPotential_residual_eq
#print axioms knownKernelSelectedPotential_residual_le
#print axioms knownKernelPotential_residual_le
#print axioms knownKernelSelectedPosterior_isPMF
#print axioms knownKernelSelectedPosteriorRisk_eq
#print axioms knownKernelRiskTilt_pos
#print axioms knownKernelRiskTilt_lt_one
#print axioms knownKernelReceiptInitial_eq
#print axioms exists_controlledQueueKnownKernelOPE_event
#print axioms exists_controlledQueueKnownKernelReceiptOPE_event
#print axioms knownKernelSelectedObservedScore_eq_transitionScore
#print axioms knownKernelReceiptPathSummary_of_suffixEdgeHistogram
#print axioms knownKernelReceipt_besselQ_eq
#print axioms knownKernelReceipt_selectedEmpiricalScore_eq
#print axioms knownKernelReceipt_selectedPenalty_le
#print axioms knownKernelReceipt_selectedLogCost_le_nine
#print axioms knownKernelReceipt_psi_one_sixteen_le_one_twoForty
#print axioms knownKernelReceipt_selectedBoundary_add_residual_le_d9
#print axioms knownKernelReceipt_selectedBoundary_add_residual_le_d9_of_suffixEdgeHistogram
#print axioms knownKernelReceipt_d9_lt_seven_hundredths
#print axioms knownKernelReceipt_selectedRisk_lt_seven_hundredths

example : knownKernelRiskTilt () = (1 / 16 : ℝ) := by
  rfl

example : knownKernelReceiptHorizon = 199999 := by
  rfl

example : knownKernelReceiptD9Bound < 7 / 100 := by
  exact knownKernelReceipt_d9_lt_seven_hundredths

example (initial : Observation) :
    ∃ goodEvent : Set (ℕ → Observation),
      (FormalSLT.StochasticDynamics.controlledTrajectoryMeasure
          nominalCandidateEnvironment
          (FormalSLT.StochasticDynamics.markovBehaviorPolicyAsHistory
            behaviorPolicy)
          initial).real goodEventᶜ ≤ 1 / 40 := by
  rcases exists_controlledQueueKnownKernelOPE_event initial with
    ⟨goodEvent, hmass, _hgood⟩
  exact ⟨goodEvent, hmass⟩
