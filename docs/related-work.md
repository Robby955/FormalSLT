# Related Work

Existing Lean 4 formalizations of statistical learning theory and probability.
FormalSLT is intended to be complementary to these projects, not a replacement
for them.

## Adjacent Lean Projects

| Project | Scope | Relation to FormalSLT |
|---|---|---|
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) / [arXiv:2602.02285](https://arxiv.org/abs/2602.02285) | Empirical-process formalization: Gaussian Lipschitz concentration, Dudley's entropy integral for sub-Gaussian processes, localized Gaussian complexity, critical radii, and least-squares rates. | Strong adjacent prior art for localized SLT formalization. FormalSLT's finite Bernstein/localization route is a different bounded-excess-loss path. |
| [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher) / [arXiv:2503.19605](https://arxiv.org/abs/2503.19605) | Rademacher-complexity generalization bounds, symmetrization, McDiarmid/Hoeffding-style concentration, and Dudley/Rademacher infrastructure. | Prior Lean infrastructure for Rademacher and Dudley-style generalization. FormalSLT overlaps in theme but keeps a finite-class theorem spine. |
| [formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) | PAC/VC characterization, compression, PAC-Bayes, learning paradigms, measurability, and finite-support machinery. | Adjacent finite learning-theory formalization. FormalSLT shares VC/PAC/PAC-Bayes themes but organizes them around a checked finite-sample route. |

## Scope

FormalSLT makes no priority claim. The current release candidate is scoped
more narrowly:

```text
finite-class empirical-risk and Rademacher/VC/PAC-Bayes infrastructure,
plus a finite localized Bernstein high-confidence theorem under explicit
boundedness and Bernstein-type assumptions.
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
- `formal-learning-theory-kernel` develops PAC/VC/PAC-Bayes and measurability
  infrastructure.
- FormalSLT emphasizes a finite-class theorem spine, explicit
  assumptions, examples, theorem maps, and auditable finite-sample bounds.

Public wording should avoid priority claims, broad novelty claims, or claims
that the project solves localized Rademacher theory.
