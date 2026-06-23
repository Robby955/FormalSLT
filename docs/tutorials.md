# Getting-started tutorials

These are worked, end-to-end walkthroughs that USE the library's results on a
concrete problem and compute a real number. They differ from the `examples/`
checkers (`#check` / `#print axioms` verifiers): a tutorial reads like a recipe
you copy and edit for your own setting.

Each file compiles `[propext, Classical.choice, Quot.sound]`-clean and is
type-checked in CI. Run them locally with:

```
make tutorials
# or, per file:
lake env lean examples/tutorials/Tutorial1_TailBound.lean
```

## The three tracks

1. **A tail bound** — [`examples/tutorials/Tutorial1_TailBound.lean`](../examples/tutorials/Tutorial1_TailBound.lean).
   "How far can the centered indicator of a biased coin deviate?" Applies the
   Bernoulli specialization of the two-sided Bernstein tail
   (`FormalSLT.Statistics.Bernoulli.bernoulli_bernstein_tail`), reads off the
   explicit bound, and shows where the bound is vacuous vs. genuinely useful
   (proving the right-hand side drops below `1`). Adapt by changing the success
   probability `p` and the margin `ε`.

2. **A PAC-Bayes bound** — [`examples/tutorials/Tutorial2_PACBayes.lean`](../examples/tutorials/Tutorial2_PACBayes.lean).
   Instantiates McAllester's sqrt-form bound
   (`FormalSLT.PACBayesMcAllester.pacbayes_mcallester_sqrt`) on a two-hypothesis
   class: supply the prior, posterior, score, and the sub-Gaussian MGF
   certificate, and read off `∑ ρ_i f_i ≤ √(2(KL(ρ‖π) + α)c)`. Adapt by enlarging
   the class or moving the posterior away from the prior (which makes the KL
   penalty bite).

3. **An anytime-valid confidence sequence** —
   [`examples/tutorials/Tutorial3_AnytimeValidCS.lean`](../examples/tutorials/Tutorial3_AnytimeValidCS.lean).
   Computes the sub-Gamma CS half-width (`FormalSLT.AnytimeValid.subGammaWidth`)
   on concrete parameters, proves it shrinks as the sample size grows (the reason
   you may peek at every `n`), and points at the coverage guarantee
   `anytime_valid_confidence_sequence_subGamma`. Adapt by changing the scale
   `σ²`, range `b`, and confidence `δ`.

## Finding the right result

To search for a theorem by mathematical concept rather than by name, use the
[searchable theorem index](./INDEX.html) (live filter) or the grep-friendly
[INDEX.md](./INDEX.md). Every entry links to its exact `file:line`.
