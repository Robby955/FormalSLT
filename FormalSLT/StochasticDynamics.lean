/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.MarkovRisk
import FormalSLT.StochasticDynamics.TrajectoryRisk
import FormalSLT.StochasticDynamics.MeasurableTrajectoryRisk
import FormalSLT.StochasticDynamics.ControlledTrajectory
import FormalSLT.StochasticDynamics.ControlledMarkovization
import FormalSLT.StochasticDynamics.ControlledKernelTV
import FormalSLT.StochasticDynamics.MarkovPACBayes
import FormalSLT.StochasticDynamics.TrajectoryPACBayes
import FormalSLT.StochasticDynamics.MarkovPACBayesTiltMixture
import FormalSLT.StochasticDynamics.MarkovPACBayesTiltMixtureInitialLaw
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.TrajectoryEmpiricalBernsteinPACBayesCountable
import FormalSLT.StochasticDynamics.ContinuousTrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.ContinuousMeasurableTrajectoryEmpiricalBernsteinPACBayes
import FormalSLT.StochasticDynamics.StationaryPoissonPACBayes
import FormalSLT.StochasticDynamics.StationaryPoissonContraction
import FormalSLT.StochasticDynamics.StationaryPoissonDobrushin
import FormalSLT.StochasticDynamics.StationaryPoissonRobustCandidate
import FormalSLT.StochasticDynamics.StationaryPoissonRobustInvariant
import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidence
import FormalSLT.StochasticDynamics.EmpiricalTransitionConfidenceCountable
import FormalSLT.StochasticDynamics.StationaryPoissonDepthSelection
import FormalSLT.StochasticDynamics.EmpiricalStationaryCatalog
import FormalSLT.StochasticDynamics.FiniteInvariantUniqueness
import FormalSLT.StochasticDynamics.StationaryTargetPolicyOPE
import FormalSLT.StochasticDynamics.DynamicTargetPolicyComparator
import FormalSLT.StochasticDynamics.PrefixDynamicTargetPolicyComparator
import FormalSLT.StochasticDynamics.TargetPathChangeOfMeasure

/-!
# Stable stochastic-dynamics imports

This declaration-free umbrella re-exports deterministic-start trajectory
semantics for both finite and arbitrary measurable state spaces. The finite
layer supports arbitrary prefix-dependent probability kernels and bounded
prefix/next-state scores; the measurable-state layer uses a jointly measurable
bounded score contract. It also re-exports Markov anytime-valid and
posterior-uniform PAC-Bayes certificates, including finite-catalog and
countable-tilt finite-state trajectory endpoints and arbitrary-measurable-
hypothesis empirical-Bernstein trajectory endpoints.
For the finite homogeneous Markov tilt-catalog endpoint, it also re-exports
the extension from a deterministic start to an arbitrary supplied finite-state
initial PMF.

The stationary finite-state layer includes the supplied-Poisson
endpoint, its supplied-Poisson stationary-risk specialization, and the
finite-depth automatic Poisson construction under oscillation contraction.
It also exposes the robust fixed-candidate Poisson bridge under an explicit
row-wise total-variation misspecification budget, together with the induced
Dobrushin perturbation certificate and uniqueness of supplied invariant laws.
It additionally exposes time-uniform empirical transition-coordinate and
row-total-variation confidence certificates for unknown finite kernels,
including countably allocated geometric tilt selection with vanishing
statistical radii under positive limiting row-visit frequencies.
Finite-simplex Cesaro compactness constructs an invariant PMF for every
nonempty finite kernel; strict Dobrushin or candidate row-TV certificates
upgrade existence to uniqueness.

It additionally exports finite state--action behavior-law semantics and
normalized one-step importance-weighting interfaces.  For finite state-based
behavior policies, the controlled prefix kernel and path law are identified
exactly with the ordinary Markov law on action--state pairs.  Under a positive
behavior-probability floor, augmented-kernel row-TV control also yields
action-conditioned environment-row control with the explicit inverse-floor
factor.  For finite state-based Markov target policies, it exports a stationary
target-policy OPE endpoint under a known environment and behavior policy,
supplied invariant target laws and exact Poisson potentials, and declared
overlap and span bounds.  It
also exports encountered-prefix dynamic comparators for finite catalogs of
history-dependent target policies, including a known prefix/time-dependent
environment kernel.  For a supplied target policy, it also exports an exact
finite-horizon target-path change-of-measure identity, target state occupancy
identity, and the explicit `C ^ n` likelihood-weight range inflation.  These
controlled endpoints do not themselves estimate the environment, invariant
law, or nuisance functions, and no endpoint gives an anytime cumulative-weight
importance-sampling guarantee.
-/
