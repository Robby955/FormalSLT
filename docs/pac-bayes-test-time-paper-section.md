# PAC-Bayes Test-Time Meta-Theorem Paper Section

This is a paste-ready theorem section for a paper or reviewer packet. It is
written to track the current q061/q059/q062/q084 -> q063/q064/q066 Lean
surface without adding priority claims or hiding certificate-supplied parts.

## Section Draft

### Verified PAC-Bayes Test-Time Certificate

We use a certificate interface to state the verified test-time bound. A
certificate separates user-supplied problem quantities from contributions
derived by checked component theorems. The user-supplied fields are the sample
size, confidence level, confidence parameter, loss width, empirical risk, and
population risk. The derived fields are five nonnegative contributions:

```text
mcAllesterGeneralWidthContribution
onlineIidContribution
bernsteinOrGaussianContribution
anytimeVilleContribution
prefixKernelContribution
```

For a certificate `C`, the bound side is

```text
flagshipBound C =
  empiricalRisk
  + lossWidth * mcAllesterGeneralWidthContribution
  + onlineIidContribution
  + bernsteinOrGaussianContribution
  + anytimeVilleContribution
  + prefixKernelContribution.
```

The public Lean theorem is:

```lean
FormalSLT.TestTimeMeta.pacBayesTestTimeFlagship_theorem :
  ∀ (certificate : FormalSLT.TestTimeMeta.FlagshipCertificate),
    FormalSLT.TestTimeMeta.flagshipConclusion certificate
```

Equivalently, after unfolding `flagshipConclusion`, Lean proves

```lean
certificate.user.populationRisk ≤
  FormalSLT.TestTimeMeta.flagshipBound
    certificate.user certificate.derived
```

for every `FlagshipCertificate`.

### Paper Theorem

**Theorem (verified finite-sample PAC-Bayes test-time certificate).** Consider
the finite-sample test-time setting represented by a Lean certificate
`C : FormalSLT.TestTimeMeta.FlagshipCertificate`. Let `n` be the certified
sample size, `delta` the certified confidence parameter, `b` the certified loss
width, and `Rhat` and `R` the certified empirical and population risks. Let
`M`, `O`, `G`, `V`, and `P` be the certified nonnegative contributions from the
general-width PAC-Bayes compiler, the iid online-to-PAC conversion, the
Gaussian/Bernstein PAC-Bayes route, the anytime Ville route, and the prefix
kernel route. Then Lean proves

```text
R ≤ Rhat + b * M + O + G + V + P.
```

The proof is the theorem
`FormalSLT.TestTimeMeta.pacBayesTestTimeFlagship_theorem`. The q064/q066 bridge
`FormalSLT.TestTimeMeta.flagshipCertificate_from_components` constructs the
same q063 certificate shape from component-derived contributions and
component-level scalar gap inequalities. It no longer takes a single opaque
final scalar assembly proof; q066 derives the final comparison from
`FormalSLT.TestTimeMeta.FlagshipScalarComponentBounds`.

### Component Routes

The q064/q066 composition bridge exposes three theorem-derived contribution
routes plus the scalar assembly route:

| Contribution slot | Lean route | What is checked |
| --- | --- | --- |
| `M` | `flagshipMcAllesterContribution_from_compileGeneralWidth` | q061 derives the general-width McAllester contribution from the finite PAC-Bayes compiler. |
| `O` | `flagshipOnlineIidContribution_from_iidRegretConversion` | q059 converts an iid regret/deviation certificate into the online-to-PAC contribution outside the iid bad event. |
| `G` | `flagshipGaussianBernsteinContribution_from_sphericalGaussian` | q062 supplies the finite-dimensional spherical Gaussian KL expression and q060 supplies the Bernstein/Vitale path. |
| `V` | q084 conditional sub-Gamma extractor surface | q064 keeps the final anytime contribution explicit; q084 checks the conditional MGF extractor used by that route. |
| `P` | prefix-kernel contribution slot | The prefix-kernel contribution remains named in the certificate instead of being folded into an anonymous residual term. |
| Assembly | `flagshipScalarAssembly_from_componentInequalities` | q066 derives the final `flagshipBound` comparison from five component gap inequalities packaged in `FlagshipScalarComponentBounds`. |

The main proof route is:

```text
q061 + q059 + q062/q060 + q084
  -> q057 named-assumption meta-theorem
  -> q063 reviewer-facing FlagshipCertificate API
  -> q064 component-to-certificate bridge
  -> q066 scalar assembly from component inequalities
```

The q063 theorem rewrites the paper-facing `flagshipBound` into q057's
`testTimeMetaBound` and then invokes
`FormalSLT.TestTimeMeta.pacBayesTestTimeMeta_theorem`. The q064/q066 bridge
derives the named contribution bundle, derives the scalar comparison through
`flagshipScalarAssembly_from_componentInequalities`, and invokes the q063
theorem on the constructed certificate.

## Lean Citations

Use these names in the paper, supplementary material, or reviewer response.

| Claim in prose | Lean declaration |
| --- | --- |
| Public flagship certificate theorem | `FormalSLT.TestTimeMeta.pacBayesTestTimeFlagship_theorem` |
| q057 named-assumption theorem | `FormalSLT.TestTimeMeta.pacBayesTestTimeMeta_theorem` |
| q064 component certificate bridge | `FormalSLT.TestTimeMeta.flagshipCertificate_from_components` |
| q064 derived contribution bundle | `FormalSLT.TestTimeMeta.flagshipDerivedContributions_from_components` |
| q066 scalar component bounds | `FormalSLT.TestTimeMeta.FlagshipScalarComponentBounds` |
| q066 scalar assembly theorem | `FormalSLT.TestTimeMeta.flagshipScalarAssembly_from_componentInequalities` |
| q061 general-width compiler soundness | `FormalSLT.PACBayes.PACBayesCertificateCompiler.compileGeneralWidth_sound` |
| q059 iid online-to-PAC theorem | `FormalSLT.OnlineToPAC.cesaBianchi_iid` |
| q062 spherical Gaussian KL formula | `FormalSLT.PACBayes.sphericalGaussianKL_eq_closedForm` |
| q062 diagonal Gaussian KL formula | `FormalSLT.PACBayes.diagonalGaussianKL_eq_sum_closedForm` |
| q084 conditional sub-Gamma extractor | `FormalSLT.Concentration.SubGamma.condSubGammaMGF_of_bounded_centered_condVariance` |

The public statement copied from Lean for the component bridge is:

```lean
@FormalSLT.TestTimeMeta.flagshipCertificate_from_components :
  ∀ {ι : Type u_1} {Z : Type u_2} {T d : ℕ}
    (user : FormalSLT.TestTimeMeta.FlagshipUserSupplied)
    (mcAllesterSpec : FormalSLT.PACBayes.PACBayesCertificateSpec ι Z)
    (onlineInput : FormalSLT.OnlineToPAC.BoundedLossRegretConversionInput T)
    (onlineRegretRate : ℝ)
    (gaussianBernsteinSpec :
      FormalSLT.PACBayes.ContinuousPriorPosteriorSpec
        (FormalSLT.PACBayes.GaussianParameterSpace d))
    (anytimeContribution prefixKernelContribution : ℝ)
    (hmcAllester :
      0 ≤ FormalSLT.TestTimeMeta.flagshipMcAllesterContribution mcAllesterSpec)
    (honline :
      0 ≤ FormalSLT.TestTimeMeta.flagshipOnlineIidContribution
        onlineInput onlineRegretRate)
    (hgaussianBernstein :
      0 ≤ FormalSLT.TestTimeMeta.flagshipGaussianBernsteinContribution
        gaussianBernsteinSpec)
    (hanytime : 0 ≤ anytimeContribution)
    (hprefix : 0 ≤ prefixKernelContribution)
    (mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ)
    (scalarBounds :
      FormalSLT.TestTimeMeta.FlagshipScalarComponentBounds user
        (FormalSLT.TestTimeMeta.flagshipDerivedContributionsOfComponents
          mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
          anytimeContribution prefixKernelContribution hmcAllester honline
          hgaussianBernstein hanytime hprefix)
        mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap),
    FormalSLT.TestTimeMeta.flagshipConclusion
      (FormalSLT.TestTimeMeta.flagshipCertificateOfComponents
        user mcAllesterSpec onlineInput onlineRegretRate gaussianBernsteinSpec
        anytimeContribution prefixKernelContribution hmcAllester honline
        hgaussianBernstein hanytime hprefix mcAllesterGap onlineGap
        gaussianBernsteinGap anytimeGap prefixGap scalarBounds)
```

The scalar assembly theorem used inside the bridge is:

```lean
FormalSLT.TestTimeMeta.flagshipScalarAssembly_from_componentInequalities :
  ∀ (user : FormalSLT.TestTimeMeta.FlagshipUserSupplied)
    (derived : FormalSLT.TestTimeMeta.FlagshipDerivedContributions)
    {mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap : ℝ},
    FormalSLT.TestTimeMeta.FlagshipScalarComponentBounds
      user derived mcAllesterGap onlineGap gaussianBernsteinGap anytimeGap prefixGap →
      user.populationRisk ≤
        FormalSLT.TestTimeMeta.flagshipBound user derived
```

## Verification Paragraph

The public theorem and q064/q066 bridge are checked in Lean 4 against the
standard Lean/mathlib axiom surface. The focused audit command is:

```bash
scripts/audit_flagship_stack.sh
```

The q068 run of this command passed in `28.34s` wallclock. It built the
flagship, Gaussian KL, iid online-to-PAC, and conditional sub-Gamma modules;
ran the public axiom audit examples; checked the proof-frontier manifest; and
scanned for `sorry`, `admit`, custom `axiom`, and custom `constant`
declarations. The q068 branch also passed:

```bash
~/.elan/bin/lake exe cache get
```

in `4.361s` wallclock, generated certificate builds for `Cert_A` through
`Cert_E` in `5.53s` wallclock, and all `examples/*.lean` in `107.63s`
wallclock. The warmed full repository build

```bash
~/.elan/bin/lake build FormalSLT
```

passed in `1.496s` wallclock.

The claimability, faithfulness, and non-vacuousness source-of-truth report is
outside this repository at
`/Users/robsneiderman/Projects/theorempath/HQ/FORMALSLT_CLAIMABILITY_2026-06-08.md`.
This paper-section draft does not duplicate that verdict.

## What Not To Claim

Do not state that the current theorem removes all certificates. The q064/q066
bridge removes the single opaque final scalar assembly proof, but a concrete
application still supplies the component gap decomposition packaged as
`FlagshipScalarComponentBounds`.

Do not state a general continuous-prior KL theorem. The q062 Gaussian backend
proves finite-dimensional diagonal and spherical Gaussian parameter formulas,
not arbitrary Radon-Nikodym KL for all continuous measures.

Do not state that q084 is a complete sequential concentration theorem. It
checks a conditional sub-Gamma MGF extractor for a bounded centered increment;
the final anytime contribution remains explicit in q064.

Do not make a priority claim. The section should cite exact Lean declarations
and state the verified scope.

## Paste-Ready LaTeX Block

```tex
\paragraph{Verified PAC-Bayes test-time certificate.}
We state the final test-time result through a Lean certificate object. A
certificate separates user-supplied quantities, including sample size,
confidence parameter, loss width, empirical risk, and population risk, from
five nonnegative theorem contributions: the general-width PAC-Bayes compiler
term, the iid online-to-PAC term, the Gaussian/Bernstein PAC-Bayes term, the
anytime Ville term, and the prefix-kernel term. In Lean this is the theorem
\texttt{FormalSLT.TestTimeMeta.pacBayesTestTimeFlagship\_theorem}:
for every \texttt{FlagshipCertificate} \(C\),
\[
  R(C) \leq
  \widehat R(C)
  + b(C)M(C)
  + O(C)
  + G(C)
  + V(C)
  + P(C).
\]
The component bridge
\texttt{FormalSLT.TestTimeMeta.flagshipCertificate\_from\_components}
constructs this certificate from checked component routes: q061's
general-width McAllester compiler, q059's iid online-to-PAC conversion,
q062's finite-dimensional Gaussian KL backend together with q060's
Bernstein/Vitale route, and q084's conditional sub-Gamma extractor surface.
The scalar assembly is derived from explicit component gap inequalities via
\texttt{FormalSLT.TestTimeMeta.flagshipScalarAssembly\_from\_componentInequalities};
the remaining application-specific obligation is the gap decomposition, not a
single opaque final bound. The audited public theorem surface depends only on
\texttt{[propext, Classical.choice, Quot.sound]}.
```
