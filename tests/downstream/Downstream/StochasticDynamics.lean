import FormalSLT.StochasticDynamics

open FormalSLT.StochasticDynamics

#check FormalSLT.StochasticDynamics.exists_stationaryPoissonDepthSelection_allTime_vanishing_event

example :
    transitionSquaredLoss (fun _ : Bool => 1) (fun _ : Bool => 0) false true
      ∈ Set.Icc (0 : ℝ) 1 :=
  transitionSquaredLoss_mem_Icc
    (by intro z; simp) (by intro z; simp) false true
