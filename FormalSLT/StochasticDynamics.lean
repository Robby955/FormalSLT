/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.MarkovRisk
import FormalSLT.StochasticDynamics.TrajectoryRisk
import FormalSLT.StochasticDynamics.ControlledTrajectory
import FormalSLT.StochasticDynamics.MarkovPACBayes
import FormalSLT.StochasticDynamics.TrajectoryPACBayes
import FormalSLT.StochasticDynamics.MarkovPACBayesTiltMixture
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.StationaryPoissonPACBayes
import FormalSLT.StochasticDynamics.StationaryTargetPolicyOPE
import FormalSLT.StochasticDynamics.DynamicTargetPolicyComparator
import FormalSLT.StochasticDynamics.PrefixDynamicTargetPolicyComparator

/-!
# Stable stochastic-dynamics imports

This declaration-free umbrella re-exports finite-state trajectory semantics,
including arbitrary prefix-dependent probability kernels and bounded
prefix/next-state scores with deterministic start.  It also re-exports the
separate Markov anytime-valid and posterior-uniform PAC-Bayes certificates for
finite predictor catalogs, including the empirical-Bernstein trajectory
endpoint and its supplied-Poisson stationary-risk specialization.
It additionally exports finite state--action behavior-law semantics and
normalized one-step importance-weighting interfaces.  For finite state-based
Markov target policies, it exports a stationary target-policy OPE endpoint
under a known environment and behavior policy, supplied invariant target
laws and exact Poisson potentials, and declared overlap and span bounds.  It
also exports encountered-prefix dynamic comparators for finite catalogs of
history-dependent target policies, including a known prefix/time-dependent
environment kernel.  These do not estimate an unknown kernel or invariant
law, identify target-law occupancy value, or provide a full-trajectory
importance-sampling theorem.
-/
