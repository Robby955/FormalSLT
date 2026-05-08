# Upstream candidates

Lemmas and definitions in this library that may be suitable for contribution to [Mathlib4](https://github.com/leanprover-community/mathlib4).

## Likely upstream candidates

| Lemma / definition | Module | Why |
|---|---|---|
| `abs_sup'_sub_sup'_le_sup'_abs_sub` | `BoundedDifferences` | Pure order/lattice fact: `Finset.sup'` is 1-Lipschitz in the function argument. General enough for `Mathlib.Order.Lattice` or `Mathlib.Algebra.Order`. |
| `cosh_le_exp_sq_half` | `Massart` | Hoeffding's cosh lemma: `cosh(x) ≤ exp(x²/2)`. Standard sub-Gaussian tool. Already partially in Mathlib as `Real.cosh_le_exp_half_sq` but the `t*a` decomposition is useful. |
| `sup_le_log_sum_exp` | `Massart` | Log-sum-exp bound for finite supremum: `sup_i x_i ≤ (1/t) log(Σ exp(t x_i))`. |
| `sum_signOfBool_eq_zero` | `FiniteSample` | Discrete mean-zero property of uniform ±1 signs over `Fin n → Bool`. |
| `card_signVectors` | `FiniteSample` | `Fintype.card (Fin n → Bool) = 2^n`. Trivial but convenient. |
| Sauer-Shelah polynomial bound | `SauerShelah` | `shatterCoeff(n,d) ≤ (en/d)^d`. Pure combinatorics / real analysis. |
| `flipAtEquiv` | `FiniteSample` | Involutive coordinate flip on `Fin n → Bool`, packaged as `Equiv.Perm`. |

## Probably repo-specific

These are useful within our library but too specialized or too coupled to our definitions for Mathlib:

- `empiricalRademacherComplexity` — our specific finite-sample definition (discrete uniform over sign vectors, `sup'` over finite class)
- `genGap` — learning-theory-specific definition
- VC-style ERM excess-risk corollaries — composition of multiple bounds
- `piMeasure` — product measure for iid sampling
- `effectiveClass` — loss-pattern finset indexed by sample
- Binary VC bridge theorems — too domain-specific

## Contribution guidelines

Before upstreaming:

1. Check Mathlib does not already have an equivalent lemma (search Loogle, Moogle).
2. Generalize type assumptions where possible (e.g., `LinearOrder` instead of `ℝ`).
3. Follow Mathlib naming conventions and style.
4. Add docstrings in the Mathlib format.
5. Open a Mathlib PR with a link back to this repo for context.
