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
| [Lean-MoDS/StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib) | Subject-organized probability, statistics, and machine-learning library consolidating Gaussian concentration, empirical-process, Rademacher/Dudley, localized least-squares, and random-matrix developments associated with the Zhang--Lee--Liu and Sonoda lines of work. | Broader foundational and continuous empirical-process coverage. FormalSLT provides a complementary audited layer for PAC-Bayes, sequential inference, finite-class learning, and explicitly scoped dependent trajectories. |
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) / [arXiv:2602.02285](https://arxiv.org/abs/2602.02285) | Empirical-process formalization: Gaussian Lipschitz concentration, Dudley's entropy integral for sub-Gaussian processes, localized Gaussian complexity, critical radii, and least-squares rates. | Strong adjacent prior art for localized SLT formalization. FormalSLT's finite Bernstein/localization route is a different bounded-excess-loss path. |
| [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher) / [arXiv:2503.19605](https://arxiv.org/abs/2503.19605) | Rademacher-complexity generalization bounds, symmetrization, McDiarmid/Hoeffding-style concentration, and Dudley/Rademacher infrastructure. | Prior Lean infrastructure for Rademacher and Dudley-style generalization. FormalSLT overlaps in theme but keeps a finite-class theorem spine. |
| [formal-learning-theory-kernel at `7511199`](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/tree/7511199db276505a464fb8548e9369fc6cbc2209) | PAC/VC characterization, compression, learning paradigms, and finite-support machinery. [`pac_bayes_finite`](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/blob/7511199db276505a464fb8548e9369fc6cbc2209/FLT_Proofs/Theorem/PACBayes.lean#L450-L490) is a proved finite-class McAllester-style union-bound theorem whose complexity is `crossEntropyFinitePMF Q P`. The source identifies the tighter `klDivFinitePMF` change-of-measure form as future work. | Direct finite-class PAC-Bayes prior art, but not the KL change-of-measure, empirical-variance, all-time, or trajectory theorem used in FormalSLT's flagship lanes. `crossEntropyFinitePMF Q P = KL(Q, P) + H(Q)` is materially different from a single KL penalty. |
| [StatLean at `e1ef06b`](https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254) | [`StatLean.StatisticalLearning.pac_bayes`](https://github.com/StatLean/Stat-Lean/blob/e1ef06bf52d2a8896439c5b59d982d9aad28a254/StatLean/StatisticalLearning/PACBayes/Generalization.lean#L191-L215) is a proved fixed-sample PAC-Bayes theorem for arbitrary measurable observations and a countable discrete hypothesis space. One event covers every probability posterior `Q << P` with finite KL and gives `risk(Q) <= empiricalRisk(Q) + sqrt((KL.toReal + log(2*n/delta)) / (2*(n-1)))`. | Direct Lean PAC-Bayes prior art and the closest formal comparator in this table. It is Hoeffding-style and fixed-`n`; it does not use empirical variance, an all-time event, adaptive trajectories, or stationary risk. |
| [StatLean Markov ergodicity at `e1ef06b`](https://github.com/StatLean/Stat-Lean/blob/e1ef06bf52d2a8896439c5b59d982d9aad28a254/StatLean/TimeSeries/ForMathlib/Markov/GeometricErgodicity.lean#L67-L203) | `IsErgodicKernel.invariant` and `eq_of_invariant_of_isErgodicKernel` give invariant-law existence and uniqueness from geometric total-variation ergodicity. [`harris_theorem_envelope`](https://github.com/StatLean/Stat-Lean/blob/e1ef06bf52d2a8896439c5b59d982d9aad28a254/StatLean/TimeSeries/ForMathlib/Markov/HarrisTheorem.lean#L1126-L1133) and the companion `harris_theorem` establish general-state invariant-law existence and geometric total-variation convergence under Harris drift and minorization. | Direct adjacent invariant-law prior art. FormalSLT uses a different finite-PMF route: unconditional finite existence by Cesaro compactness and uniqueness under a computable maximum-row Dobrushin certificate. The relevant StatLean sources had no declaration-form `sorry`, `admit`, `axiom`, or `constant` matches in this audit, but no clean build or `#print axioms` receipt was produced. |
| [Pythia at `6540433`](https://github.com/athanor-ai/pythia/tree/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3) | Proved sequential infrastructure includes [`ville_finite_horizon` and `ville_supermartingale`](https://github.com/athanor-ai/pythia/blob/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3/Pythia/VilleSupermartingale.lean#L76-L138), plus an [`EProcess`](https://github.com/athanor-ai/pythia/blob/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3/Pythia/EDetector.lean#L100-L154) structure, Type-I-error control, exponential e-process construction, and averaging closure. | Direct prior art for Ville/e-process and confidence-sequence infrastructure. The two advertised PAC-Bayes capstones in [`PACBayesCS.lean`](https://github.com/athanor-ai/pythia/blob/65404339b5c6fe8004d91fdd9c0c14ceb0bf7cd3/Pythia/PACBayesCS.lean#L67-L95), `pacbayes_cs_ville` and `pacbayes_mixture_eprocess`, currently conclude literally `True := by trivial`; they are placeholders, not competing checked PAC-Bayes theorems. |
| [Mathlib at FormalSLT's pinned revision `905b958`](https://github.com/leanprover-community/mathlib4/blob/905b95818eb32af7874a58b427f50c1711a5e96c/Mathlib/Probability/Kernel/Invariance.lean#L37-L72) | `ProbabilityTheory.Kernel.Invariant kappa mu` is exactly `mu.bind kappa = mu`; `Kernel.IsReversible.invariant` proves invariance from reversibility. [`PMF.toMeasure_bind_apply`](https://github.com/leanprover-community/mathlib4/blob/905b95818eb32af7874a58b427f50c1711a5e96c/Mathlib/Probability/ProbabilityMassFunction/Monad.lean#L169-L177) gives the corresponding setwise PMF-bind identity. A full-source exact-identifier and text scan at `905b958` and current-audit revision [`c947440`](https://github.com/leanprover-community/mathlib4/tree/c9474400f5dea53081566459496b32c896dbe9ab) found no direct PMF-bind-to-kernel-invariance theorem under the audited identifiers. | FormalSLT's PMF identity and Mathlib's measure-kernel identity are related by a coercion bridge. Separate local commit `70e2847` proves a generic countable bridge and was locally verified against `905b958`; it is not in this public release or upstream Mathlib. Econlib `003655c` already contains a direct finite bundled analogue, so the supported claim is that the candidate fills a Mathlib API gap, not that it is the first formal bridge. The source scan is bounded by its identifiers and revisions and makes no absence claim beyond them. |
| [Econlib at release commit `003655c` (July 9, 2026)](https://github.com/danlyng/Econlib/tree/003655ccf010cdf44c4f67d6675167b54ce0e9df) | [`FiniteMarkovChain.exists_stationary`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Probability/Markov/Ergodic.lean#L66-L102) proves finite-state stationary-distribution existence by Brouwer; `FiniteMarkovChain.unique_stationary` assumes strictly positive transitions. [`step_toProbDist` and `FiniteMarkovChain.isStationary_iff_invariant`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Probability/Markov/FiniteToKernel.lean#L81-L160) give a direct finite bundled PMF-to-measure-kernel invariance bridge. [`tvDist_step_le` and `tvDist_nStep_le`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/Probability/Doeblin.lean#L49-L180) prove Doeblin contraction under a common entrywise lower bound. Econlib also has FOSD-lattice stationary-law existence and compact-Feller invariant-law existence. | Direct Lean prior art for invariant-law existence, interoperability, and finite total-variation contraction. The Doeblin factor is `1 - card(alpha) * epsilon`; it is not FormalSLT's maximum-row-pair Dobrushin coefficient, stationary Poisson correction, or visit-gated transition confidence. FormalSLT's finite existence proof uses Cesaro compactness, and its uniqueness theorem assumes a computable Dobrushin coefficient below one. The pinned manifest and static declaration-form proof-debt/custom-declaration scans are complete. No hosted check was present for this commit during the audit; a clean build and exact `#print axioms` surface remain **UNSWEPT**. No priority inference is made from repository dates. |

## Isabelle/HOL and Rocq/Coq formalizations

| Project | Checked declarations | Relation to FormalSLT |
|---|---|---|
| [AFP: Concentration Inequalities](https://www.isa-afp.org/browser_info/current/AFP/Concentration_Inequalities/document.pdf) | Isabelle/HOL formalization of probability and concentration infrastructure, including Chernoff-, Hoeffding-, and McDiarmid-style inequalities. | Foundational concentration prior art. The bounded review did not identify in this entry the exact empirical-Bernstein PAC-Bayes, adaptive trajectory, or continuous-posterior capstones listed in this ledger; that is not an exhaustive absence claim. |
| [AFP: Stochastic Matrices and the Perron--Frobenius Theorem](https://www.isa-afp.org/entries/Stochastic_Matrices.html) | [`stationary_distribution_exists`](https://www.isa-afp.org/browser_info/current/AFP/Stochastic_Matrices/Stochastic_Matrix_Perron_Frobenius.html#Stochastic_Matrix_Perron_Frobenius.stationary_distribution_exists%7Cfact) proves existence for a finite stochastic matrix; `transition_matrix.stationary_distribution_exists` transports it to the AFP Markov-chain representation. [`stationary_distribution_unique`](https://www.isa-afp.org/browser_info/current/AFP/Stochastic_Matrices/Stochastic_Matrix_Perron_Frobenius.html#Stochastic_Matrix_Perron_Frobenius.stationary_distribution_unique%7Cfact) proves uniqueness under irreducibility. The companion [`Stochastic_Matrix_Markov_Models`](https://www.isa-afp.org/browser_info/current/AFP/Stochastic_Matrices/Stochastic_Matrix_Markov_Models.html) theory connects PMF bind with matrix-vector multiplication. | Direct prior formalization of finite invariant-law existence and irreducible uniqueness, using Perron--Frobenius. FormalSLT instead uses a finite Krylov--Bogolyubov/Cesaro compactness proof and Dobrushin contraction for uniqueness. The theorem statements and proof routes are related but not reproductions. |
| [AFP: Markov Models](https://www.isa-afp.org/entries/Markov_Models.html) / [proof document](https://isa-afp.org/browser_info/current/AFP/Markov_Models/document.pdf) | Defines `stationary_distribution N` by the PMF identity `N = bind_pmf N K` and develops countable-state Markov-chain, stopping-time, and recurrence infrastructure. The source sweep used the exact official [`afp-2026-08-12` artifact](https://isa-afp.org/release/afp-2026-08-12.tar.gz), SHA-256 `d6e2dfab798fca4cb66680532fc5c24f5528864e897ca95a1fd19070c8992574`. | Exact definitional comparator for FormalSLT's `IsInvariantPMF P stationary := stationary.bind P = stationary`, up to equality orientation and notation. A full `.thy` lexical scan of that artifact for the named stationary-Poisson/coboundary, Dobrushin/coefficient-of-ergodicity, time-uniform-confidence, and empirical-transition-confidence families found no exact target terminology beyond the invariant-law sources already recorded. This closes only the named artifact/source scan; it is not a semantic absence claim about other Isabelle sources or a priority claim. |
| [CertRL](https://arxiv.org/abs/2009.11403) / [IBM publication record](https://research.ibm.com/publications/certrl-formalizing-convergence-proofs-for-value-and-policy-iteration-in-coq) | Coq formalization of value and policy iteration for finite-state MDPs, including [`is_contraction_bellman_op`](https://github.com/IBM/FormalML/blob/8495ce1406436aba0d467f0a84a2569f9a9a7af5/rocq/CertRL/mdp.v#L1231), a discounted Bellman contraction used for infinite-horizon convergence. | Adjacent mechanized Markov/MDP work. Its contraction is a discounted value-iteration result, not an invariant-law or Dobrushin row-TV theorem. |
| Named Rocq probability and information sources: [MathComp Analysis at `fcd4ec5`](https://github.com/math-comp/analysis/tree/fcd4ec53d253f3298964988ff9f6c78fabe111a0), [Infotheo 0.3](https://rocq-prover.org/p/coq-infotheo/0.3), [coq-proba at `c5a74b5`](https://github.com/jtassarotti/coq-proba/tree/c5a74b57446a6440f34c4afa7a23dc0af8c31c72), and [FormalML at `8495ce1`](https://github.com/IBM/FormalML/tree/8495ce1406436aba0d467f0a84a2569f9a9a7af5) | Measure/integration, probability, information-theoretic, probabilistic-program, and formal reinforcement-learning infrastructure. The pinned `.v` source scan also inspected Infotheo source revision `98573b5283df152cbe0b4b0b69ab850bd6d6c96f`. | A full lexical scan of these pinned sources found no exact declaration matching the named stationary Poisson, finite invariant-law, Dobrushin row-TV perturbation, or visit-gated transition-confidence families. This closes only the named-source scan and supports no broader Rocq absence or priority claim. |

## Sweep status

This is a source-level audit, not an exhaustive prior-art search. In particular:

- the pinned StatLean theorem is direct fixed-sample PAC-Bayes prior art, while
  Pythia's sequential Ville/e-process layer is proved but its two named
  `PACBayesCS` capstones are `True` placeholders;
- the exact AFP `afp-2026-08-12` artifact and the named pinned Rocq sources were
  scanned for the stated theorem families. Those bounded source scans are
  complete, but they do not establish semantic absence across other sources or
  priority;
- Mathlib source revisions `905b958` and `c947440` were scanned for the named
  PMF-to-kernel bridge. Local commit `70e2847` is **LOCAL-VERIFIED** against the
  pinned dependency, but inclusion in a public FormalSLT release and any
  upstream Mathlib proposal remain **OPEN**;
- Econlib's exact manifest and static declaration-form proof-debt and custom
  declaration scans at `003655ccf010cdf44c4f67d6675167b54ce0e9df` are
  complete. Its clean build and exact `#print axioms` surface remain
  **UNSWEPT**; and
- Kueffner et al.'s Theorem 3 has been compared formula by formula across its
  four displayed confidence sequences. Betting Bernstein is the closest
  process comparator, but the clock, tilt, weighting, and allocation structures
  differ from FormalSLT's coordinate boundary.

`UNSWEPT` means that this audit has not established the relation. It is not an
absence, novelty, or priority claim.

## Potential Mathlib upstreams

The following are candidates for separate, review-sized Mathlib contributions.
They are not claimed to be upstream-ready merely because they compile in
FormalSLT.

| Candidate surface | Why it may be reusable | Work required before proposing it |
|---|---|---|
| PMF invariance bridge from `StochasticDynamics.IsInvariantPMF` to Mathlib's measure-level `ProbabilityTheory.Kernel.Invariant` | Connects finite algebraic Markov-chain calculations to the standard kernel API | Generalize the locally verified `70e2847` candidate, minimize imports and assumptions, cite Econlib's finite bundled analogue, and obtain Mathlib probability review |
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

The current library is scoped theorem by theorem. Its three headline families
are:

- an offline all-sample-size empirical-Bernstein PAC-Bayes bound for
  finite-valued IID observations and arbitrary measurable hypothesis spaces;
- forward PAC-Bayes inference for prefix-dependent trajectories, with separate
  finite-state countable-allocation and arbitrary-measurable-state endpoints;
- finite-state stationary-risk certificates built from Poisson corrections,
  including finite-depth contraction and same-trajectory confidence for a
  predeclared candidate-kernel catalog.

The library also retains its finite-sample Rademacher, VC, stability,
localization, chaining, and classical PAC-Bayes foundations. These statements
do not imply unrestricted measurable-supremum theory, continuous-observation
empirical-Bernstein bounds, continuous-state stationary risk, or validity for
models invented after observing the outcomes on which they are scored.

The classical localized Bernstein lane should be cited alongside the projects
above: Sonoda et al. for Rademacher/Dudley infrastructure, Zhang et al. for
localized empirical-process and Gaussian/Dudley machinery, and
`formal-learning-theory-kernel` for PAC/VC/PAC-Bayes and measurability
infrastructure. This page records adjacent Lean projects already reviewed; it
does not establish novelty or priority for the trajectory or stationary
Poisson endpoints.

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
  discrete hypotheses and general-state Harris invariant-law results; Pythia
  provides Ville/e-process infrastructure.
- Mathlib supplies the invariant-measure definition and foundational kernel,
  simplex, and stochastic-matrix APIs used or paralleled by this work.
- AFP Stochastic Matrices and Econlib directly formalize finite stationary-law
  existence by different fixed-point or Perron--Frobenius routes; Econlib also
  has a finite PMF/kernel bridge and entrywise-minorization TV contraction.
- CertRL develops contraction-based finite-MDP convergence in Coq.
- FormalSLT emphasizes finite-sample PAC-Bayes, VC, stability, and
  anytime-valid theorem spines, adaptive trajectories, and finite
  stationary/transition layers with explicit assumptions, concrete receipts,
  theorem maps, and published axiom audits.

FormalSLT does not import any of these repositories. Mathematical influence and
overlap are recorded here as prior work; the implementations remain separate
codebases with different theorem endpoints and dependency graphs.
