/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.MaurerKL

/-!
# Axiom audit for the Maurer kl-form PAC-Bayes bound

Type-checks the three Maurer headline results and the discharged Jensen lemma,
and prints their axiom dependencies. Each must depend only on the standard
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axiom.
-/

open FormalSLT.PACBayes.MaurerKL

#check @logSum_ineq
#check @binKL_posteriorMixture_jensen
#check @maurer_pacbayes_kl_bound
#check @maurer_pacbayes_kl_pinsker_corollary
#check @maurer_pacbayes_kl_complexity_nonneg

#print axioms logSum_ineq
#print axioms binKL_posteriorMixture_jensen
#print axioms maurer_pacbayes_kl_bound
#print axioms maurer_pacbayes_kl_pinsker_corollary
#print axioms maurer_pacbayes_kl_complexity_nonneg
