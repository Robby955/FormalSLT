import FormalSLT.Applications.ControlledQueueReindex

open FormalSLT.Applications.ControlledQueue

#check Observation
#check stateActionRowEquiv
#check observationRowEquiv
#check transitionRow
#check stateActionRowEquiv_apply_val
#check observationRowEquiv_apply_val
#check observationRowEquiv_symm_action_val
#check observationRowEquiv_symm_state_val
#check augmentedBehaviorStateTable_length
#check augmentedBehaviorStateTable_getElem?_stateAction
#check augmentedBehaviorStateTable_getElem?_observation
#check transitionRow_val
#check transitionRow_pair

#print axioms stateActionRowEquiv_apply_val
#print axioms observationRowEquiv_apply_val
#print axioms observationRowEquiv_symm_action_val
#print axioms observationRowEquiv_symm_state_val
#print axioms augmentedBehaviorStateTable_length
#print axioms augmentedBehaviorStateTable_getElem?_stateAction
#print axioms augmentedBehaviorStateTable_getElem?_observation
#print axioms transitionRow_val
#print axioms transitionRow_pair

/-- A concrete edge uses the current state and next action, not the next
state, to select its generated table row. -/
example :
    (transitionRow
      ((0 : FormalSLT.Applications.ControlledQueueData.Action),
        (7 : FormalSLT.Applications.ControlledQueueData.PhysicalState))
      ((1 : FormalSLT.Applications.ControlledQueueData.Action),
        (12 : FormalSLT.Applications.ControlledQueueData.PhysicalState))).val = 15 := by
  norm_num
