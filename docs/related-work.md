# Related Work

Existing formalizations of statistical learning theory, probability, Markov
chains, and reinforcement learning. FormalSLT is intended to be complementary
to these projects, not a replacement for them.

This page records formalization prior art. Textbooks and primary mathematical
papers are mapped to FormalSLT's theorem families in
[Mathematical sources](./references.md).

## Adjacent Lean Projects

| Project | Scope | Relation to FormalSLT |
|---|---|---|
| [Lean-MoDS/StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib) | Subject-organized probability, statistics, and machine-learning library consolidating Gaussian concentration, empirical-process, Rademacher/Dudley, localized least-squares, and random-matrix developments associated with the Zhang--Lee--Liu and Sonoda lines of work. | Broader foundational and continuous empirical-process coverage. FormalSLT provides a complementary audited layer for finite-sample PAC-Bayes, VC, stability, and anytime-valid inference. |
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) / [arXiv:2602.02285](https://arxiv.org/abs/2602.02285) | Empirical-process formalization: Gaussian Lipschitz concentration, Dudley's entropy integral for sub-Gaussian processes, localized Gaussian complexity, critical radii, and least-squares rates. | Strong adjacent prior art for localized SLT formalization. FormalSLT's finite Bernstein/localization route is a different bounded-excess-loss path. |
| [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher) / [arXiv:2503.19605](https://arxiv.org/abs/2503.19605) | Rademacher-complexity generalization bounds, symmetrization, McDiarmid/Hoeffding-style concentration, and Dudley/Rademacher infrastructure. | Prior Lean infrastructure for Rademacher and Dudley-style generalization. FormalSLT overlaps in theme but keeps a finite-class theorem spine. |
| [formal-learning-theory-kernel at `7511199`](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/tree/7511199db276505a464fb8548e9369fc6cbc2209) | PAC/VC characterization, compression, learning paradigms, and finite-support machinery. [`pac_bayes_finite`](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/blob/7511199db276505a464fb8548e9369fc6cbc2209/FLT_Proofs/Theorem/PACBayes.lean#L450-L490) is a proved finite-class McAllester-style union-bound theorem whose complexity is `crossEntropyFinitePMF Q P`. The source identifies the tighter `klDivFinitePMF` change-of-measure form as future work. | Direct finite-class PAC-Bayes prior art, but not the KL change-of-measure, empirical-variance, all-time, or trajectory theorem used in FormalSLT's flagship lanes. `crossEntropyFinitePMF Q P = KL(Q, P) + H(Q)` is materially different from a single KL penalty. |
| [StatLean at `e1ef06b`](https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254) | [`StatLean.StatisticalLearning.pac_bayes`](https://github.com/StatLean/Stat-Lean/blob/e1ef06bf52d2a8896439c5b59d982d9aad28a254/StatLean/StatisticalLearning/PACBayes/Generalization.lean#L191-L215) is a proved fixed-sample PAC-Bayes theorem for arbitrary measurable observations and a countable discrete hypothesis space. One event covers every probability posterior `Q << P` with finite KL and gives `risk(Q) <= empiricalRisk(Q) + sqrt((KL.toReal + log(2*n/delta)) / (2*(n-1)))`. | Direct Lean PAC-Bayes prior art and the closest formal comparator in this table. It is Hoeffding-style and fixed-`n`; it does not use empirical variance, an all-time event, adaptive trajectories, or stationary risk. |
| [Pythia at `6540433`](https://github.com/athanor-ai/pythia/tree/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3) | Proved sequential infrastructure includes [`ville_finite_horizon` and `ville_supermartingale`](https://github.com/athanor-ai/pythia/blob/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3/Pythia/VilleSupermartingale.lean#L76-L138), plus an [`EProcess`](https://github.com/athanor-ai/pythia/blob/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3/Pythia/EDetector.lean#L100-L154) structure, Type-I-error control, exponential e-process construction, and averaging closure. | Direct prior art for Ville/e-process and confidence-sequence infrastructure. The two advertised PAC-Bayes capstones in [`PACBayesCS.lean`](https://github.com/athanor-ai/pythia/blob/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3/Pythia/PACBayesCS.lean#L67-L95), `pacbayes_cs_ville` and `pacbayes_mixture_eprocess`, currently conclude literally `True := by trivial`; they are placeholders, not competing checked PAC-Bayes theorems. |
| [Mathlib at FormalSLT's pinned revision `905b958`](https://github.com/leanprover-community/mathlib4/blob/905b95818eb32af7874a58b427f50c1711a5e96c/Mathlib/Probability/Kernel/Invariance.lean#L39-L40) | `ProbabilityTheory.Kernel.Invariant kappa mu` is exactly `mu.bind kappa = mu`; [`Kernel.IsReversible.invariant`](https://github.com/leanprover-community/mathlib4/blob/905b95818eb32af7874a58b427f50c1711a5e96c/Mathlib/Probability/Kernel/Invariance.lean#L65-L75) proves invariance from reversibility. The same revision supplies stochastic-matrix and finite-simplex infrastructure. | FormalSLT's PMF-level `StochasticDynamics.IsInvariantPMF P stationary` is the algebraic identity `stationary.bind P = stationary`. The checked finite-simplex construction then proves `exists_invariantPMF`. An explicit bridge between this PMF identity and Mathlib's measure-kernel `Kernel.Invariant`, and a wider pinned-Mathlib search beyond the inspected invariance/stochastic-matrix files, remain **UNSWEPT**. No general finite invariant-law existence theorem was found in the inspected pinned files; this is not a repository-wide absence claim. |
| [Econlib at release commit `003655c` (July 9, 2026)](https://github.com/danlyng/Econlib/tree/003655ccf010cdf44c4f67d6675167b54ce0e9df) | [`FiniteMarkovChain.exists_stationary`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Probability/Markov/Ergodic.lean#L68-L69) proves finite-state stationary-distribution existence by Brouwer; [`FiniteMarkovChain.unique_stationary`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Probability/Markov/Ergodic.lean#L129-L132) assumes strictly positive transitions. [`exists_invariant_probDist`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Probability/ProbDist/Stationary.lean#L241-L247) proves invariant-law existence for Feller kernels on nonempty compact metrizable spaces by a fixed-point route. | This is direct Lean prior art for invariant-law existence. FormalSLT's `exists_invariantPMF` uses finite Cesaro averages, compact subsequence extraction, and a telescoping defect; its uniqueness theorem assumes Dobrushin coefficient below one rather than entrywise-positive transitions. Econlib's exact dependency build, proof-debt scan, and axiom surface at the pinned commit remain **UNSWEPT**. No priority inference is made from repository dates. |

## Isabelle/HOL and Rocq/Coq formalizations

| Project | Checked declarations | Relation to FormalSLT |
|---|---|---|
| [AFP: Concentration Inequalities](https://www.isa-afp.org/browser_info/current/AFP/Concentration_Inequalities/document.pdf) | Isabelle/HOL formalization of probability and concentration infrastructure, including Chernoff-, Hoeffding-, and McDiarmid-style inequalities. | Foundational concentration prior art. The bounded review did not identify in this entry the exact empirical-Bernstein PAC-Bayes, adaptive trajectory, or continuous-posterior capstones listed in this ledger; that is not an exhaustive absence claim. |
| [AFP: Stochastic Matrices and the Perron--Frobenius Theorem](https://www.isa-afp.org/entries/Stochastic_Matrices.html) | [`stationary_distribution_exists`](https://www.isa-afp.org/browser_info/current/AFP/Stochastic_Matrices/Stochastic_Matrix_Perron_Frobenius.html#Stochastic_Matrix_Perron_Frobenius.stationary_distribution_exists%7Cfact) proves existence for a finite stochastic matrix; `transition_matrix.stationary_distribution_exists` transports it to the AFP Markov-chain representation. [`stationary_distribution_unique`](https://www.isa-afp.org/browser_info/current/AFP/Stochastic_Matrices/Stochastic_Matrix_Perron_Frobenius.html#Stochastic_Matrix_Perron_Frobenius.stationary_distribution_unique%7Cfact) proves uniqueness under irreducibility. The companion [`Stochastic_Matrix_Markov_Models`](https://www.isa-afp.org/browser_info/current/AFP/Stochastic_Matrices/Stochastic_Matrix_Markov_Models.html) theory connects PMF bind with matrix-vector multiplication. | Direct prior formalization of finite invariant-law existence and irreducible uniqueness, using Perron--Frobenius. FormalSLT instead uses a finite Krylov--Bogolyubov/Cesaro compactness proof and Dobrushin contraction for uniqueness. The theorem statements and proof routes are related but not reproductions. |
| [AFP: Markov Models](https://www.isa-afp.org/entries/Markov_Models.html) / [proof document](https://isa-afp.org/browser_info/current/AFP/Markov_Models/document.pdf) | Defines `stationary_distribution N` by the PMF identity `N = bind_pmf N K` and develops countable-state Markov-chain, stopping-time, and recurrence infrastructure. | Exact definitional comparator for FormalSLT's `IsInvariantPMF P stationary := stationary.bind P = stationary`, up to equality orientation and notation. A full Isabelle audit for Poisson correction, Dobrushin perturbation, and time-uniform transition confidence remains **UNSWEPT**. |
| [CertRL](https://arxiv.org/abs/2009.11403) / [IBM publication record](https://research.ibm.com/publications/certrl-formalizing-convergence-proofs-for-value-and-policy-iteration-in-coq) | Coq formalization of value and policy iteration for finite-state MDPs, including Bellman optimality and contraction-based infinite-horizon convergence. | Adjacent mechanized Markov/MDP and contraction work, not an exact stationary-Poisson, invariant-law, Dobrushin-row-TV, PAC-Bayes, or transition-confidence formalization. A broader Coq/Rocq search for those exact theorem families remains **UNSWEPT**. |
| Rocq probability and information foundations: [MathComp Analysis](https://github.com/math-comp/analysis), [Infotheo 0.3](https://rocq-prover.org/p/coq-infotheo/0.3), and [coq-proba](https://github.com/jtassarotti/coq-proba) | Measure/integration, probability, information-theoretic, and probabilistic-program reasoning infrastructure in the Rocq ecosystem. | Relevant foundations rather than verified matches for the three empirical-Bernstein/trajectory endpoints. This bounded review is not an exhaustive Rocq search and supports no absence or priority claim. |

## Sweep status

This is a source-level audit, not an exhaustive prior-art search. In particular:

- the pinned StatLean theorem is direct fixed-sample PAC-Bayes prior art, while
  Pythia's sequential Ville/e-process layer is proved but its two named
  `PACBayesCS` capstones are `True` placeholders;
- the bounded Isabelle/HOL and Rocq/Coq review of the named concentration,
  Markov, probability, and information-theory sources did not reveal an exact
  analogue of the IID all-`n`, finite-state countable-trajectory, or arbitrary
  measurable-state/hypothesis trajectory endpoints. This is not evidence of
  exhaustive absence or priority;
- exact Isabelle/HOL formalizations of finite-depth Poisson correction,
  Dobrushin row-TV perturbation, and time-uniform transition confidence are
  **UNSWEPT**;
- exact Coq/Rocq formalizations of stationary Poisson equations, finite
  invariant-law existence, Dobrushin perturbation, and transition confidence
  are **UNSWEPT**;
- Econlib's build, proof-debt, transitive dependency, and axiom audit at
  `003655ccf010cdf44c4f67d6675167b54ce0e9df` is **UNSWEPT**;
- the direct PMF-to-`Kernel.Invariant` interoperability bridge against pinned
  Mathlib is **UNSWEPT**; and
- the June-2026 MDP confidence-sequence paper has been checked at its sampling
  model and Theorem 3; a symbol-by-symbol comparison of all four confidence
  sequences with FormalSLT remains **UNSWEPT**.

`UNSWEPT` means that this audit has not established the relation. It is not an
absence, novelty, or priority claim.

## Potential Mathlib upstreams

The following are candidates for separate, review-sized Mathlib contributions.
They are not claimed to be upstream-ready merely because they compile in
FormalSLT.

| Candidate surface | Why it may be reusable | Work required before proposing it |
|---|---|---|
| PMF invariance bridge from `StochasticDynamics.IsInvariantPMF` to Mathlib's measure-level `ProbabilityTheory.Kernel.Invariant` | Connects finite algebraic Markov-chain calculations to the standard kernel API | Remove FormalSLT naming, state the coercion assumptions explicitly, and check for an existing bridge outside the pinned files already inspected |
| `finitePMFTotalVariation`, `finiteDobrushinCoefficient`, and the oscillation-contraction lemma | Provides a finite-kernel contraction interface useful beyond PAC-Bayes | Reconcile with stochastic-matrix norms and existing total-variation conventions; split definitions from the application theorem |
| `continuous_donsker_varadhan` | A measure-theoretic KL change-of-measure inequality is broadly useful for probability formalization | Audit Mathlib's current KL and log-likelihood-ratio namespace, minimize typeclass assumptions, and obtain a measure-theory review |
| `integral_observedTrajectoryScore_traj_of_joint` and `observedTrajectoryScore_condExp_of_joint` | Packages a recurring conditional-expectation step for `Kernel.traj` and jointly measurable prefix scores | Generalize away FormalSLT's score wrapper and align the statement with `Kernel.IonescuTulcea.Traj` conventions |
| Finite-prefix expectation / `partialTraj` / `traj` cylinder-integral bridge | Avoids re-proving projective finite-prefix identities in controlled-process developments | Isolate the kernel theorem from policy and PAC-Bayes definitions and benchmark elaboration cost |
| Finite and countable nonnegative e-process mixture closure | Useful once multiple sequential-testing libraries share a common process interface | First establish or adopt a stable Mathlib e-process abstraction; the current FormalSLT result alone is not sufficient API evidence |

These candidates should be submitted independently of the v0.2 release. A
Mathlib proposal needs its own source audit, minimized imports, naming review,
and downstream use case.

## Scope

FormalSLT makes no broad priority claim. The public repository was released on
May 8, 2026, after the first public release of
`YuanheZ/lean-stat-learning-theory` and before the consolidated StatsMLlib
repository. Repository dates do not supersede the dates of the underlying
papers or predecessor artifacts.

The current library is scoped more narrowly:

```text
audited finite-sample empirical-risk, Rademacher/VC/PAC-Bayes, stability,
sequential-inference, and finite stochastic-dynamics infrastructure, including
time-uniform PAC-Bayes bounds, stationary Poisson correction, finite invariant
laws, and one-trajectory empirical transition confidence under explicit gates.
```

The localized Bernstein theorem should be cited alongside the projects above:
Sonoda et al. for Rademacher/Dudley infrastructure, Zhang et al. for localized
empirical-process and Gaussian/Dudley machinery, and
`formal-learning-theory-kernel` for PAC/VC/PAC-Bayes and measurability
infrastructure.

## Complementary, Not Competitive

No novelty or priority conclusion follows from the current audit. The useful
comparison is by scope:

- Zhang et al. develop deeper Gaussian/Dudley and critical-radius machinery.
- `lean-rademacher` develops a Rademacher-generalization route.
- StatsMLlib organizes those broader probability, empirical-process, and
  high-dimensional-statistics foundations into a subject-first library.
- `formal-learning-theory-kernel` develops PAC/VC/PAC-Bayes and measurability
  infrastructure, including a finite-class cross-entropy PAC-Bayes theorem.
- StatLean provides a direct fixed-sample KL PAC-Bayes theorem over countable
  discrete hypotheses, and Pythia provides Ville/e-process infrastructure.
- Mathlib supplies the invariant-measure definition and foundational kernel,
  simplex, and stochastic-matrix APIs used or paralleled by this work.
- AFP Stochastic Matrices and Econlib directly formalize finite stationary-law
  existence by different fixed-point or Perron--Frobenius routes.
- CertRL develops contraction-based finite-MDP convergence in Coq.
- FormalSLT emphasizes finite-sample PAC-Bayes, VC, stability, and
  anytime-valid theorem spines plus finite stationary/transition layers with
  explicit assumptions, concrete witnesses, theorem maps, and published axiom
  audits.

FormalSLT does not import any of these repositories. Mathematical influence and
overlap are recorded here as prior work; the implementations remain separate
codebases with different theorem endpoints and dependency graphs.
