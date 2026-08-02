/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.TimeUniformIIDGrid

/-!
Public audit for the finite-grid, time-uniform i.i.d. PAC-Bayes theorem.
-/

open FormalSLT.PACBayes.TimeUniformIIDGrid

#check @timeUniformIIDPACBayesGridAnyPosteriorUpperFailure
#check @timeUniformIIDPACBayesGridAnyPosteriorUpperFailure_subset_iUnion
#check @timeUniformIIDPACBayes_grid_allPosteriors_bound

#print axioms timeUniformIIDPACBayesGridAnyPosteriorUpperFailure_subset_iUnion
#print axioms timeUniformIIDPACBayes_grid_allPosteriors_bound
