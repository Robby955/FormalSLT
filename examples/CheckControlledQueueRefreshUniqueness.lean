import FormalSLT.Applications.ControlledQueueRefreshUniqueness

open ProbabilityTheory

open FormalSLT.Applications.ControlledQueue
open FormalSLT.Applications.ControlledQueueData
open FormalSLT.StochasticDynamics

#check refreshTargetPolicyKernel_dobrushin_le_gamma
#check refreshTargetPolicyKernel_existsUnique_invariantPMF

#print axioms refreshTargetPolicyKernel_dobrushin_le_gamma
#print axioms refreshTargetPolicyKernel_existsUnique_invariantPMF

/-- A valid refresh persistence parameter outside the three generated
candidate values. -/
noncomputable def halfPersistenceParameter : PersistenceParameter :=
  ⟨1 / 2, by constructor <;> norm_num⟩

example (pi : MarkovTargetPolicy PhysicalState Action) :
    finiteDobrushinCoefficient
        (targetPolicyKernel (refreshEnvironment halfPersistenceParameter) pi) ≤
      (1 / 2 : ℝ) := by
  simpa [halfPersistenceParameter] using
    refreshTargetPolicyKernel_dobrushin_le_gamma
      halfPersistenceParameter pi
