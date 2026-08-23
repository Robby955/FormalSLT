/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.Applications.ControlledQueueData
import FormalSLT.StochasticDynamics.ControlledMarkovization

/-!
# Controlled-queue row indexing

The generated queue tables enumerate rows in state-major/action-minor order,
whereas controlled trajectories store observations as action--state pairs.
This module gives the exact finite equivalence between those conventions and
identifies the table row used by a controlled transition.

For an edge `(A_{t-1}, S_t) -> (A_t, S_{t+1})`, the transition row is
`(S_t, A_t)`.  It is therefore determined by the current state and the next
action, not by the next state.

This is a representation bridge only.  It does not turn the rational tables
into PMFs, import the frozen trace into Lean, or prove a statistical
certificate or good-event membership claim.
-/

namespace FormalSLT.Applications.ControlledQueue

open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

/-- The controlled action--state observation type for the queue model. -/
abbrev Observation := ControlledObservation PhysicalState Action

/-- State-major/action-minor table rows: `row = 2 * state + action`. -/
def stateActionRowEquiv : PhysicalState × Action ≃ Fin 48 :=
  finProdFinEquiv

/-- Explicitly swap action--state observations into state-major table rows. -/
def observationRowEquiv : Observation ≃ Fin 48 :=
  (Equiv.prodComm Action PhysicalState).trans stateActionRowEquiv

/-- The generated table row used by a controlled transition. -/
def transitionRow (current next : Observation) : Fin 48 :=
  stateActionRowEquiv (current.2, next.1)

@[simp]
theorem stateActionRowEquiv_apply_val
    (z : PhysicalState) (a : Action) :
    (stateActionRowEquiv (z, a)).val = 2 * z.val + a.val := by
  change a.val + 2 * z.val = 2 * z.val + a.val
  omega

@[simp]
theorem observationRowEquiv_apply_val (o : Observation) :
    (observationRowEquiv o).val = 2 * o.2.val + o.1.val := by
  rcases o with ⟨a, z⟩
  exact stateActionRowEquiv_apply_val z a

@[simp]
theorem observationRowEquiv_symm_action_val (r : Fin 48) :
    (observationRowEquiv.symm r).1.val = r.val % 2 := by
  rfl

@[simp]
theorem observationRowEquiv_symm_state_val (r : Fin 48) :
    (observationRowEquiv.symm r).2.val = r.val / 2 := by
  rfl

@[simp]
theorem augmentedBehaviorStateTable_length :
    augmentedBehaviorStateTable.length = 48 := by
  rfl

@[simp]
theorem augmentedBehaviorStateTable_getElem?_stateAction
    (z : PhysicalState) (a : Action) :
    augmentedBehaviorStateTable[(stateActionRowEquiv (z, a)).val]? =
      some (z.val, a.val) := by
  fin_cases z <;> fin_cases a <;> decide

@[simp]
theorem augmentedBehaviorStateTable_getElem?_observation (o : Observation) :
    augmentedBehaviorStateTable[(observationRowEquiv o).val]? =
      some (o.2.val, o.1.val) := by
  rcases o with ⟨a, z⟩
  exact augmentedBehaviorStateTable_getElem?_stateAction z a

@[simp]
theorem transitionRow_val (current next : Observation) :
    (transitionRow current next).val =
      2 * current.2.val + next.1.val := by
  exact stateActionRowEquiv_apply_val current.2 next.1

@[simp]
theorem transitionRow_pair
    (previousAction action : Action) (state nextState : PhysicalState) :
    transitionRow (previousAction, state) (action, nextState) =
      stateActionRowEquiv (state, action) := rfl

end FormalSLT.Applications.ControlledQueue
