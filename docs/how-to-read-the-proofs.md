# How to Read the Proofs

This guide is for ML theory people who know the theorems but not Lean 4.

## Lean 4 in 60 seconds

Lean 4 is a dependently typed programming language and interactive theorem prover. A "proof" in Lean is a program whose type is a proposition. If the program compiles, the proposition is true (relative to the axioms).

```lean
-- This declares a theorem named `my_theorem`.
-- The type signature IS the statement.
-- Everything after `:= by` is the proof.
theorem my_theorem (n : ℕ) (h : 0 < n) : n ≠ 0 := by
  omega
```

## Reading a theorem statement

Look at the type signature. Everything before the colon (`:`) is a hypothesis; everything after is the conclusion.

```lean
theorem genGap_highProb_rademacher
    {ι : Type*} [Fintype ι] [Nonempty ι]     -- finite nonempty hypothesis class
    [MeasurableSpace Z] {μ : Measure Z}       -- probability space
    [IsProbabilityMeasure μ]
    {ℓ : ι → Z → ℝ}                          -- loss function
    {B : ℝ} (hB : 0 < B)                     -- bound B > 0
    (hℓ_bdd : ∀ i z, |ℓ i z| ≤ B)           -- loss bounded by B
    {n : ℕ} (hn : 0 < n)                     -- sample size n > 0
    {ε : ℝ} (hε : 0 ≤ ε) :                  -- tolerance ε ≥ 0
    -- CONCLUSION:
    (piMeasure μ n).real {S | genGap μ ℓ S ≥ 2 * E[Rad] + ε}
      ≤ Real.exp (-(ε ^ 2 * n) / (8 * B ^ 2)) := by
  ...
```

Read this as: "For any finite nonempty hypothesis class, probability measure, B-bounded loss, sample size n > 0, and ε ≥ 0, the probability that the generalization gap exceeds 2·E[Rad] + ε is at most exp(-ε²n/(8B²))."

## Typeclass brackets

| Syntax | Meaning |
|--------|---------|
| `(n : ℕ)` | Explicit argument |
| `{n : ℕ}` | Implicit argument (Lean infers it) |
| `[Fintype ι]` | Typeclass instance (ι has finitely many elements) |
| `[Nonempty ι]` | Typeclass instance (ι has at least one element) |
| `[IsProbabilityMeasure μ]` | μ is a probability measure |
| `[MeasurableSpace Z]` | Z has a sigma-algebra |

## Common proof tactics

| Tactic | What it does |
|--------|-------------|
| `exact h` | Close the goal using hypothesis `h` |
| `apply f` | Reduce the goal by applying `f` |
| `rw [lemma]` | Rewrite using `lemma` |
| `simp` | Simplify using built-in rules |
| `linarith` | Solve linear arithmetic |
| `ring` | Solve ring equalities |
| `omega` | Solve natural number arithmetic |
| `intro x` | Introduce a universally quantified variable |
| `cases h` | Case split on hypothesis `h` |
| `calc` | Chain of equalities/inequalities |
| `have h : P := ...` | Prove an intermediate fact |
| `ext k` | Prove function equality pointwise |
| `funext` | Function extensionality |

## Where to look in this repo

**Start with definitions.** Read `FormalSLT/Risk.lean` and `FormalSLT/GhostSample.lean` first. These define `populationRisk`, `empiricalRisk`, and `genGap`. The theorem statements in later files reference these.

**Then read the main results.** Each module's `/-! ... -/` docstring explains the theorem, the proof strategy, and the scope. The docstring is the best entry point for each file.

**Skip the Azuma internals.** The `FormalSLT/Azuma/` directory has 9 files building up the exposure martingale and bounded-differences machinery. This is infrastructure. Read `GenGapTail.lean` for the final result and skip the intermediate files unless you want the measure-theory details.

## Mathlib

This repo depends on [Mathlib](https://github.com/leanprover-community/mathlib4), the standard mathematics library for Lean 4. Mathlib provides:

- `MeasureTheory.Measure`, `MeasureTheory.integral` — measure spaces and integration
- `Finset.sup'`, `Finset.sum` — finite suprema and sums
- `Finset.vcDim`, `Finset.card_shatterer_le_sum_vcDim` — VC dimension and Sauer-Shelah
- `Real.exp`, `Real.log`, `Real.sqrt` — standard functions

When you see a lemma name like `MeasureTheory.integral_mono` or `Finset.card_image_of_injOn`, it comes from Mathlib. You can search for it at [leanprover-community.github.io/mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/).
