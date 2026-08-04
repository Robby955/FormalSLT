# Comparison with adjacent formalizations

This table records differences in checked scope. It is not a ranking, and a
repository creation date is not a priority claim for the mathematics or its
predecessor artifacts. See [related-work.md](./related-work.md) for citations
and provenance notes.

| Property | FormalSLT | StatsMLlib | lean-rademacher (Sonoda et al., 2025) | Karayel--Tan AFP (2023) |
|---|---|---|---|---|
| Proof assistant | Lean 4 + Mathlib4 | Lean 4 + Mathlib4 | Lean 4 + Mathlib4 | Isabelle/HOL |
| Primary scope | Audited finite-sample SLT: ERM, Rademacher, VC, PAC-Bayes, stability, finite chaining, and sequential inference | Probability, empirical processes, Gaussian concentration, continuous Dudley machinery, localized least squares, and random matrices | Rademacher-complexity generalization and Dudley infrastructure | Concentration inequalities including Bennett, Bernstein, McDiarmid, Efron--Stein, and Paley--Zygmund |
| Sharp McDiarmid | Upper, lower, and two-sided; homogeneous and heterogeneous independent products | Concentration infrastructure includes bounded-difference results | One-sided plus negated form over independent coordinate maps | McDiarmid 1989 Lemma 1.2 form |
| PAC-Bayes | Finite bounded-loss, change-of-measure, Gaussian KL, and time-uniform finite/process-level routes | No PAC-Bayes layer in the current public tree | No PAC-Bayes layer | No PAC-Bayes layer |
| VC / Sauer--Shelah | Finite VC and binary-trace bridges | No VC-dimension layer in the current public tree | Not its primary scope | No learning-theory spine |
| Sequential inference | Ville bounds, e-processes, betting processes, mixtures, and confidence sequences | No corresponding layer in the current public tree | No corresponding layer | No corresponding layer |
| Continuous empirical processes | Finite-net and explicitly scoped continuous-boundary adapters; no general measurable-supremum theorem | Sub-Gaussian processes, entropy integrals, Gaussian machinery, and localized critical-radius results | Dudley/Rademacher infrastructure | Not its primary scope |
| Public verification surface | Dedicated checker/example files, published `#print axioms` transcripts, concrete witnesses, and CI statement-fidelity gates | Full-library build and source hygiene; fewer separate public checker artifacts | Lean build and source-level proof hygiene | Isabelle session build |
| Organization | Topic directories plus legacy flat modules under incremental migration | Strict subject-first hierarchy and documented import direction | Focused theorem-family tree | AFP entry structure |

## What FormalSLT should own

FormalSLT should not duplicate StatsMLlib's Gaussian-analysis or random-matrix
breadth. Its clearest complementary role is the definitive audited layer for:

- finite-sample learning bounds with explicit constants and assumptions;
- PAC-Bayes change-of-measure and posterior-uniform statements;
- VC, stability, and online-to-PAC compositions;
- anytime-valid inference, e-processes, and time-uniform PAC-Bayes; and
- proof receipts combining `#print axioms`, concrete witnesses, statement
  fidelity, and non-vacuity checks.

StatsMLlib's subject ownership and import-direction discipline are useful
engineering models. FormalSLT adopts those principles incrementally through
[ARCHITECTURE.md](../ARCHITECTURE.md), without a breaking whole-tree rename.

## Current boundaries

- FormalSLT's heterogeneous McDiarmid theorem allows a family of coordinate
  laws `μ : Fin n → Measure Z`, but retains a common coordinate state space
  `Z`.
- FormalSLT's arbitrary-hypothesis time-uniform PAC-Bayes theorem is
  process-level. The checked i.i.d. bounded-loss specialization is currently
  finite-class.
- FormalSLT's Dudley development does not yet provide the general continuous
  measurable-supremum theorem available in the broader empirical-process line.
- Source-tree feature comparisons can change. The linked theorem statements,
  checker files, and upstream repositories are the authoritative evidence.

## Sources

- StatsMLlib: <https://github.com/Lean-MoDS/StatsMLlib>
- Zhang--Lee--Liu artifact: <https://github.com/YuanheZ/lean-stat-learning-theory>
- lean-rademacher: <https://github.com/auto-res/lean-rademacher>
- Karayel--Tan AFP: <https://isa-afp.org/entries/Concentration_Inequalities.html>
- FormalSLT heterogeneous McDiarmid:
  [`FormalSLT/Concentration/HeterogeneousMcDiarmid.lean`](../FormalSLT/Concentration/HeterogeneousMcDiarmid.lean)
- FormalSLT time-uniform PAC-Bayes:
  [`FormalSLT/PACBayes/TimeUniformIID.lean`](../FormalSLT/PACBayes/TimeUniformIID.lean)
