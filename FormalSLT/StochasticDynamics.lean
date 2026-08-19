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
import FormalSLT.StochasticDynamics.StationaryPoissonContraction
import FormalSLT.StochasticDynamics.StationaryPoissonDobrushin
import FormalSLT.StochasticDynamics.StationaryPoissonRobustCandidate
import FormalSLT.StochasticDynamics.StationaryPoissonRobustInvariant
import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence
import FormalSLT.StochasticDynamics.StationaryPoissonDepthSelection
import FormalSLT.StochasticDynamics.EmpiricalStationaryCatalog
import FormalSLT.StochasticDynamics.FiniteInvariantUniqueness
import FormalSLT.StochasticDynamics.StationaryTargetPolicyOPE
import FormalSLT.StochasticDynamics.DynamicTargetPolicyComparator
import FormalSLT.StochasticDynamics.PrefixDynamicTargetPolicyComparator
import FormalSLT.StochasticDynamics.TargetPathChangeOfMeasure

/-!
# Stable stochastic-dynamics imports

This declaration-free umbrella re-exports finite-state trajectory semantics,
including arbitrary prefix-dependent probability kernels and bounded
prefix/next-state scores with deterministic start.  It also re-exports the
separate Markov anytime-valid and posterior-uniform PAC-Bayes certificates for
finite predictor catalogs, including the empirical-Bernstein trajectory
endpoint, its supplied-Poisson stationary-risk specialization, and the
finite-depth automatic Poisson construction under oscillation contraction.
It also exposes the robust fixed-candidate Poisson bridge under an explicit
row-wise total-variation misspecification budget, together with the induced
Dobrushin perturbation certificate and uniqueness of supplied invariant laws.
It additionally exposes time-uniform empirical transition-coordinate and
row-total-variation confidence certificates for unknown finite kernels.
Finite-simplex Cesaro compactness constructs an invariant PMF for every
nonempty finite kernel; strict Dobrushin or candidate row-TV certificates
upgrade existence to uniqueness.

It additionally exports finite state--action behavior-law semantics and
normalized one-step importance-weighting interfaces.  For finite state-based
Markov target policies, it exports a stationary target-policy OPE endpoint
under a known environment and behavior policy, supplied invariant target
laws and exact Poisson potentials, and declared overlap and span bounds.  It
also exports encountered-prefix dynamic comparators for finite catalogs of
history-dependent target policies, including a known prefix/time-dependent
environment kernel.  For a supplied target policy, it also exports an exact
finite-horizon target-path change-of-measure identity, target state occupancy
identity, and the explicit `C ^ n` likelihood-weight range inflation.  These
do not estimate an unknown kernel or invariant law or provide an anytime
full-trajectory importance-sampling guarantee.
-/
