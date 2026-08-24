# FormalSLT overview transcript

The film uses an original instrumental score. Its explanation is written on
screen; this transcript provides an accessible, searchable version.

## 00:00.000 · FormalSLT

FormalSLT is a Lean foundation for statistical learning and modern
finite-sample inference. It spans classical generalization theory and results
for data gathered or analyzed adaptively.

## 00:05.000 · One library across the field

The program covers VC theory, Rademacher complexity, metric entropy and
chaining, PAC-Bayes, sequential inference, and dependent data. These are parts
of one mathematical stack: capacity, complexity, selection, time, and
dependence.

## 00:14.000 · From capacity to generalization

VC growth bounds and metric entropy feed complexity estimates. Those estimates
lead to finite-sample learning guarantees. Two checked bound shapes appear on
screen. The VC route: the probability that the excess risk of empirical risk
minimization exceeds `4·sqrt(2d·log(en/d)/n) + 2ε` is at most
`2·exp(−ε²n/8)`. The entropy route: the expected generalization gap is at
most `8·sqrt(2/n)` times the integral of `sqrt(log N(ε))` over the chaining
radii. The diagram is a map of reusable results, not a claim that every arrow
is one theorem.

## 00:23.000 · Choose after seeing the data

PAC-Bayes starts from a prior and prices posterior selection by relative
entropy. The checked event covers every posterior allowed by the theorem, so a
posterior may be chosen after seeing the data. The bound fails for some
allowed posterior with probability at most `δ`.

## 00:32.000 · Keep looking. Keep the guarantee.

Confidence sequences and e-processes are built for repeated looks. Each look
lands inside the band. One event covers every time and every declared choice
in the theorem. For an e-process, the running maximum reaches `1/α` with
probability at most `α`.

## 00:41.000 · Learning along a path

For dependent observations, the posterior and tilt may use the observed
prefix, while the next score is fixed before the next state arrives. In the
finite-state setting shown here, a Poisson correction connects pathwise
evidence to stationary risk.

## 00:50.000 · One worked case study

The controlled queue is one application. A generic transition comparison has
4,608 coordinates. Inside a declared one-parameter refresh family, it reduces
to one hit rate, `p_hit(γ) = (1 + 23γ) / 24`. Lean proves the exact transfer
identity `TV(row γ, row γ′) = |p_γ − p_γ′|` for every physical row. The result
assumes that family; it is not a test of family membership.

## 00:59.000 · Reusable results across the field

The film lists four checked declarations by name: VC empirical-risk
minimization (`vc_erm_excessRisk_tail_binary_zeroOneLoss`), metric-entropy
generalization (`metricEntropy_generalization_mean`), anytime PAC-Bayes
(`timeUniformPACBayes_tiltMixture_allPosteriors_bound`), and the adaptive
trajectory guarantee
(`exists_trajectoryCountableEmpiricalBernsteinPACBayes_allTime_vanishing_event`).
The declarations and files are recorded in `facts.json` at the pinned source
revision. The queue is one application of this wider library.

## 01:06.000 · FormalSLT

A Lean foundation for statistical learning and modern finite-sample inference.
