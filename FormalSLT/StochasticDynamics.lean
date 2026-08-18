/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import FormalSLT.StochasticDynamics.MarkovRisk
import FormalSLT.StochasticDynamics.TrajectoryRisk
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
-/
