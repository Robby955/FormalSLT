# Related Work

Existing Lean 4 formalizations of statistical learning theory and probability.
FormalSLT is intended to be complementary to these projects, not a replacement
for them.

## Adjacent Lean Projects

| Project | Scope | Relation to FormalSLT |
|---|---|---|
| [Lean-MoDS/StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib) | Subject-organized probability, statistics, and machine-learning library consolidating Gaussian concentration, empirical-process, Rademacher/Dudley, localized least-squares, and random-matrix developments associated with the Zhang--Lee--Liu and Sonoda lines of work. | Broader foundational and continuous empirical-process coverage. FormalSLT provides a complementary audited layer for finite-sample PAC-Bayes, VC, stability, and anytime-valid inference. |
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) / [arXiv:2602.02285](https://arxiv.org/abs/2602.02285) | Empirical-process formalization: Gaussian Lipschitz concentration, Dudley's entropy integral for sub-Gaussian processes, localized Gaussian complexity, critical radii, and least-squares rates. | Strong adjacent prior art for localized SLT formalization. FormalSLT's finite Bernstein/localization route is a different bounded-excess-loss path. |
| [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher) / [arXiv:2503.19605](https://arxiv.org/abs/2503.19605) | Rademacher-complexity generalization bounds, symmetrization, McDiarmid/Hoeffding-style concentration, and Dudley/Rademacher infrastructure. | Prior Lean infrastructure for Rademacher and Dudley-style generalization. FormalSLT overlaps in theme but keeps a finite-class theorem spine. |
| [formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) | PAC/VC characterization, compression, PAC-Bayes, learning paradigms, measurability, and finite-support machinery. | Adjacent finite learning-theory formalization. FormalSLT shares VC/PAC/PAC-Bayes themes but organizes them around a checked finite-sample route. |

## Scope

FormalSLT makes no broad priority claim. The public repository was released on
May 8, 2026, after the first public release of
`YuanheZ/lean-stat-learning-theory` and before the consolidated StatsMLlib
repository. Repository dates do not supersede the dates of the underlying
papers or predecessor artifacts.

The current library is scoped more narrowly:

```text
audited finite-sample empirical-risk, Rademacher/VC/PAC-Bayes, stability,
and sequential-inference infrastructure, including finite-class i.i.d.
time-uniform PAC-Bayes bounds and explicitly scoped finite chaining.
```

The localized Bernstein theorem should be cited alongside the projects above:
Sonoda et al. for Rademacher/Dudley infrastructure, Zhang et al. for localized
empirical-process and Gaussian/Dudley machinery, and
`formal-learning-theory-kernel` for PAC/VC/PAC-Bayes and measurability
infrastructure.

## Complementary, Not Competitive

The checked sources do not show an exact duplicate of FormalSLT's finite
localized Bernstein route, but this is not a broad novelty claim. The useful
comparison is by scope:

- Zhang et al. develop deeper Gaussian/Dudley and critical-radius machinery.
- `lean-rademacher` develops a Rademacher-generalization route.
- StatsMLlib organizes those broader probability, empirical-process, and
  high-dimensional-statistics foundations into a subject-first library.
- `formal-learning-theory-kernel` develops PAC/VC/PAC-Bayes and measurability
  infrastructure.
- FormalSLT emphasizes finite-sample PAC-Bayes, VC, stability, and
  anytime-valid theorem spines with explicit assumptions, concrete witnesses,
  theorem maps, and published axiom audits.

FormalSLT does not import any of these repositories. Mathematical influence and
overlap are recorded here as prior work; the implementations remain separate
codebases with different theorem endpoints and dependency graphs.

