# Related work

Existing Lean 4 formalizations of statistical learning theory and probability.

## YuanheZ/lean-stat-learning-theory

A comprehensive Lean 4 formalization of statistical learning theory grounded in empirical processes. Includes:

- Gaussian Lipschitz concentration
- Dudley's entropy integral for sub-Gaussian processes
- Sparse least-squares regression with sharp rates
- Lean proof trace datasets for ML-assisted formalization

**Scope:** Broad empirical-process infrastructure aiming at infinite-class results. Around 30,000 lines of Lean.

**Reference:** [Statistical Learning Theory in Lean 4: Empirical Processes from Scratch](https://huggingface.co/papers/2602.02285) (2025).

## MohanadAhmed/lean-rademacher-generalization

Lean 4 formalization of generalization error bounds via Rademacher complexity. Includes:

- Empirical and population Rademacher complexity definitions
- Symmetrization inequality
- McDiarmid's inequality
- Hoeffding's inequality

**Scope:** Rademacher-route generalization bounds through high-probability results.

**Reference:** [Lean Formalization of Generalization Error Bound by Rademacher Complexity](https://www.emergentmind.com/papers/2503.19605) (2025).

## How this repo differs

This repo (`lean-statistical-learning` / FormalSLT) occupies a different lane:

| Dimension | YuanheZ | MohanadAhmed | This repo |
|---|---|---|---|
| **Scope** | Broad empirical-process theory | Rademacher route | Compact finite-class VC/Rademacher spine |
| **Target audience** | Research formalization | Formalization | ML people learning SLT formally |
| **Infinite classes** | Yes | Partial | No (finite index types) |
| **Dudley/chaining** | Yes | No | Finite chaining and finite entropy-budget wrappers |
| **VC dimension** | Not in scope | No | Yes (Sauer-Shelah + binary bridge) |
| **ERM bounds** | Via sparse regression | No | Yes (full VC-style ERM tail) |
| **Diagrams/docs** | Minimal | Minimal | Extensive |
| **Examples** | No | No | Yes |
| **Assumption tables** | No | No | Yes |
| **Scope tables** | No | No | Yes |

### Our positioning

We do not claim to be the first formalization of statistical learning theory. We aim to be the **cleanest, most readable, contributor-friendly** Lean 4 finite-class SLT library:

1. A stranger can understand the theorem spine in 60 seconds (README diagram).
2. The repo builds with one command (`lake build FormalSLT`).
3. Every theorem family has an informal statement, Lean declaration, and scoped assumptions.
4. There are examples showing how to import and use the theorems.
5. The roadmap separates closed theorems from current boundaries and future work.
6. Open formalization problems invite contribution.

### Complementary, not competitive

These projects are complementary. YuanheZ builds deep empirical-process infrastructure for research-level results. We build a readable theorem spine for the finite-class route that ML practitioners encounter first. Both contribute to the broader goal of machine-checked statistical learning theory.
