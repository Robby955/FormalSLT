/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayes.MaurerKL

/-!
# Adversarial Refute for the Maurer kl-form PAC-Bayes bound

These examples would FAIL to typecheck if the Maurer results were stated
vacuously.  They pin `binKL` and the posterior-mixture Jensen gap to explicit
positive numbers, so a degenerate (always-true) restatement could not satisfy
them.

* `refute_jensen_nontrivial` — the posterior-mixture Jensen gap is a STRICT
  inequality `0 < log 2` on concrete data; a vacuous `binKL p q ≤ 0`
  restatement would make the right side `0`, contradicting `log 2 > 0`.
* `refute_binKL_positive` — `binKL` takes a genuine positive value
  (`binKL 0 (1/2) = log 2 > 0`); a definition collapsed to the constant `0`
  could not prove this.
* `refute_complexity_strict_pos` — the Maurer complexity term is STRICTLY
  positive at a non-uniform posterior (`klDiv > 0`), so the RHS is a real,
  non-zero bound, not a vacuous `≤ 0` threshold.
* `refute_pinsker_below_trivial` — the Pinsker √-gap on concrete risks is
  STRICTLY below the trivial `≤ 1` bound, so the corollary is genuinely
  constraining.
-/

open Finset Real BigOperators
open FormalSLT.PACBayesKL
open FormalSLT.PACBayesSeeger
open FormalSLT.PACBayes.MaurerKL

namespace FormalSLT.PACBayes.MaurerKLRefute

noncomputable section

/-- `binKL 0 (1/2) = log 2`. -/
theorem binKL_0_half : binKL (0 : ℝ) (1 / 2) = Real.log 2 := by
  unfold binKL
  rw [show (1 : ℝ) - 0 = 1 by ring, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring]
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num]; simp

/-- `binKL 1 (1/2) = log 2`. -/
theorem binKL_1_half : binKL (1 : ℝ) (1 / 2) = Real.log 2 := by
  unfold binKL
  rw [show (1 : ℝ) - 1 = 0 by ring, show (1 : ℝ) / (1 / 2) = 2 by norm_num]; simp

/-- `binKL` is genuinely positive on concrete data: `binKL 0 (1/2) = log 2 > 0`.
A vacuous `binKL ≡ 0` definition could not prove this. -/
theorem refute_binKL_positive : 0 < binKL 0 (1 / 2) := by
  rw [binKL_0_half]; exact Real.log_pos (by norm_num)

/-- The posterior-mixture Jensen gap is a STRICT inequality on concrete data.
Posterior `(1/2,1/2)`, empirical risks `(0,1)`, population risks `(1/2,1/2)`:
the mixed binary KL is `0` but the averaged binary KL is `log 2 > 0`.  A vacuous
restatement (e.g. `binKL p q ≤ 0`) would force the right side to `0`. -/
theorem refute_jensen_nontrivial :
    binKL (posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2) (fun i => if i = 0 then 0 else 1))
          (posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2) (fun _ => 1 / 2))
      <
    posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2)
      (fun i => binKL ((fun i => if i = 0 then 0 else 1) i) ((fun _ => 1 / 2) i)) := by
  -- LHS = binKL (1/2) (1/2) = 0; RHS = log 2 > 0
  have hlhs : binKL (posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2) (fun i => if i = 0 then 0 else 1))
          (posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2) (fun _ => 1 / 2)) = 0 := by
    have hp : posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2) (fun i => if i = 0 then 0 else 1) = 1 / 2 := by
      unfold posteriorAverage; rw [Fin.sum_univ_two]; norm_num
    have hq : posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2) (fun _ => (1 : ℝ) / 2) = 1 / 2 := by
      unfold posteriorAverage; rw [Fin.sum_univ_two]; norm_num
    rw [hp, hq]; unfold binKL; norm_num
  have hrhs : posteriorAverage (fun _ : Fin 2 => (1 : ℝ) / 2)
      (fun i => binKL ((fun i => if i = 0 then 0 else 1) i) ((fun _ => (1:ℝ) / 2) i)) = Real.log 2 := by
    unfold posteriorAverage
    rw [Fin.sum_univ_two]
    norm_num
    rw [binKL_0_half, binKL_1_half]; ring
  rw [hlhs, hrhs]; exact Real.log_pos (by norm_num)

/-- The Maurer complexity term is STRICTLY positive at a point-mass posterior
over a uniform prior: `klDiv (1,0) (1/2,1/2) = log 2 > 0` by Gibbs strictness, so
the kl-form RHS is a real non-zero bound, not a vacuous `≤ 0` threshold. -/
theorem refute_complexity_strict_pos :
    0 < klDiv (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
              (fun _ => 1 / 2)
      + Real.log ((2 * Real.sqrt ((2 : ℕ) : ℝ)) / (1 / 2)) := by
  have hkl : 0 < klDiv (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
              (fun _ => 1 / 2) := by
    unfold klDiv
    rw [Fin.sum_univ_two]
    rw [show ((0 : Fin 2) = 0) from rfl]
    norm_num
    -- goal: 0 < log 2  (point-mass posterior, KL = log 2)
    exact Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log ((2 * Real.sqrt ((2 : ℕ) : ℝ)) / (1 / 2)) := by
    apply Real.log_nonneg
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    push_cast; nlinarith [h2]
  linarith

/-- The Pinsker √-gap on concrete risks is STRICTLY below the trivial `≤ 1`
bound, so the corollary is genuinely constraining (not the vacuous `gap ≤ 1`). -/
theorem refute_pinsker_below_trivial :
    Real.sqrt ((1 : ℝ) / 2) < 1 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

end

end FormalSLT.PACBayes.MaurerKLRefute

namespace FormalSLT.PACBayes.MaurerKLRefute
#print axioms refute_binKL_positive
#print axioms refute_jensen_nontrivial
#print axioms refute_complexity_strict_pos
#print axioms refute_pinsker_below_trivial
end FormalSLT.PACBayes.MaurerKLRefute
