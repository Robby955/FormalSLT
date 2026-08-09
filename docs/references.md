# Mathematical Sources

FormalSLT is not a line-by-line translation of a single textbook. It assembles
machine-checked theorem families whose mathematical provenance comes from
standard learning-theory texts and primary research papers. This page records
that provenance and the scope in which each source is used.

The Lean declaration and its hypotheses remain the authority for what the
library proves. A source listed here explains the mathematical route; it does
not imply that FormalSLT reproduces every theorem or the full generality of the
source.

## Source map

| FormalSLT area | Main mathematical sources | Role in FormalSLT | Current checked scope |
|---|---|---|---|
| ERM, learnability, uniform convergence, and finite classes | Shalev-Shwartz and Ben-David (2014); Mohri, Rostamizadeh, and Talwalkar (2018) | Definitions, proof organization, and finite-sample learning bounds | Primarily finite hypothesis classes and finite samples |
| Rademacher complexity and VC theory | Mohri, Rostamizadeh, and Talwalkar (2018); Shalev-Shwartz and Ben-David (2014) | Symmetrization, contraction, finite-class bounds, Sauer--Shelah, and VC-to-generalization routes | Finite classes or finite trace/effective-class reductions |
| Concentration and bounded differences | Boucheron, Lugosi, and Massart (2013); McDiarmid (1989) | Hoeffding-, Bernstein-, Bennett-, and McDiarmid-style inequalities | Explicit boundedness, moment, independence, or product-measure assumptions in each theorem |
| Metric entropy and Dudley chaining | Dudley (1967); Boucheron, Lugosi, and Massart (2013, Section 13); Massart (2007); Talagrand (2014) | Finite chaining, covering-number entropy budgets, and continuous-integral boundary interfaces | Finite-net constructions plus explicitly stated separability, measurability, and boundary certificates where required |
| Algorithmic stability | Bousquet and Elisseeff (2002); McDiarmid (1989) | Expected-gap and bounded-differences route from uniform stability to generalization | Stability is supplied as a hypothesis; the library does not infer it for every learning algorithm |
| PAC-Bayes change of measure and finite confidence bounds | Donsker and Varadhan (1975); McAllester (1999, 2003); Seeger (2002); Catoni (2007) | KL change of measure, fixed-tilt bounds, square-root consequences, finite confidence shells, and Bernoulli-KL infrastructure | Finite priors/posteriors for the main finite-sample layer; continuous results have their own explicit measure-theoretic assumptions |
| PAC-Bayes Bernstein and Gaussian/variational interfaces | Tolstikhin and Seldin (2013); Alquier, Ridgway, and Chopin (2016) | Variance-sensitive penalties and continuous-posterior analytic interfaces | Supplied variance/moment certificates except where a concrete finite or spherical-Gaussian specialization discharges them |
| Anytime-valid inference and e-processes | Ville (1939); Howard et al. (2020, 2021); Chugg, Wang, and Ramdas (2023); Ramdas et al. (2023); Grünwald, de Heide, and Koolen (2024) | Ville inequalities, confidence sequences, time-uniform PAC-Bayes mixtures, line-crossing bounds, and safe-testing interfaces | Discrete-time processes with the adaptedness, integrability, conditional-MGF, or supermartingale assumptions shown in the signatures |
| Probability and statistics interfaces | Durrett (2019); van der Vaart (1998); the corresponding Mathlib declarations | Background for convergence, moments, estimation, Fisher information, and asymptotic-statistics wrappers | The wrappers preserve the hypotheses and generality of the Mathlib results they expose |

## Repository routes

The table maps to these public module families:

- ERM and uniform convergence: `FormalSLT.Risk`, `FormalSLT.ERM`, and
  `FormalSLT.UniformConvergence`.
- Rademacher and VC theory: `FormalSLT.Rademacher.*` and `FormalSLT.VC.*`.
- Concentration and stability: `FormalSLT.Concentration.*`,
  `FormalSLT.Azuma.*`, and `FormalSLT.Stability.*`.
- Covering and chaining: `FormalSLT.Covering.*`.
- PAC-Bayes: `FormalSLT.PACBayes`, including the older compatibility modules
  re-exported by that topic import.
- Sequential inference: `FormalSLT.Sequential` and `FormalSLT.AnytimeValid.*`.
- Probability and statistics: `FormalSLT.Probability.*` and
  `FormalSLT.Statistics.*`.

Use the [theorem index](./INDEX.md) to locate declarations and the
[proof-frontier manifest](./proof-frontier.md) to distinguish proved endpoints
from supplied interfaces and open boundaries.

## Textbooks and monographs

- Shalev-Shwartz, S., and Ben-David, S. (2014). *Understanding Machine
  Learning: From Theory to Algorithms*. Cambridge University Press.
  [Publisher record](https://doi.org/10.1017/CBO9781107298019).
- Mohri, M., Rostamizadeh, A., and Talwalkar, A. (2018). *Foundations of
  Machine Learning*, second edition. MIT Press.
  [Publisher record](https://mitpress.mit.edu/9780262039406/foundations-of-machine-learning/).
- Boucheron, S., Lugosi, G., and Massart, P. (2013). *Concentration
  Inequalities: A Nonasymptotic Theory of Independence*. Oxford University
  Press. [Publisher record](https://doi.org/10.1093/acprof:oso/9780199535255.001.0001).
- Massart, P. (2007). *Concentration Inequalities and Model Selection*.
  Lecture Notes in Mathematics 1896, Springer.
  [Publisher record](https://doi.org/10.1007/978-3-540-48503-2).
- Talagrand, M. (2014). *Upper and Lower Bounds for Stochastic Processes*.
  Springer. [Publisher record](https://doi.org/10.1007/978-3-642-54075-2).
- Catoni, O. (2007). *PAC-Bayesian Supervised Classification: The
  Thermodynamics of Statistical Learning*. IMS Lecture Notes--Monograph Series
  56. [Chapter 1](https://doi.org/10.1214/lnms/1199996415).
- Durrett, R. (2019). *Probability: Theory and Examples*, fifth edition.
  Cambridge University Press.
- van der Vaart, A. W. (1998). *Asymptotic Statistics*. Cambridge University
  Press.

## Primary papers

### Concentration, chaining, and stability

- McDiarmid, C. (1989). "On the method of bounded differences." In *Surveys in
  Combinatorics, 1989*, London Mathematical Society Lecture Note Series 141,
  148--188. [Publisher record](https://doi.org/10.1017/CBO9781107359949.008).
- Dudley, R. M. (1967). "The sizes of compact subsets of Hilbert space and
  continuity of Gaussian processes." *Journal of Functional Analysis* 1(3),
  290--330.
  [Publisher record](https://doi.org/10.1016/0022-1236%2867%2990017-1).
- Bousquet, O., and Elisseeff, A. (2002). "Stability and generalization."
  *Journal of Machine Learning Research* 2, 499--526.
  [Open article](https://www.jmlr.org/papers/v2/bousquet02a.html).

### PAC-Bayes

- Donsker, M. D., and Varadhan, S. R. S. (1975). "Asymptotic evaluation of
  certain Markov process expectations for large time, I." *Communications on
  Pure and Applied Mathematics* 28(1), 1--47.
  [Publisher record](https://doi.org/10.1002/cpa.3160280102).
- McAllester, D. A. (1999). "PAC-Bayesian model averaging." In *Proceedings of
  the Twelfth Annual Conference on Computational Learning Theory*, 164--170.
  [Publisher record](https://doi.org/10.1145/307400.307435).
- McAllester, D. A. (2003). "PAC-Bayesian stochastic model selection."
  *Machine Learning* 51, 5--21.
  [Publisher record](https://doi.org/10.1023/A:1021840411064).
- Seeger, M. (2002). "PAC-Bayesian generalisation error bounds for Gaussian
  process classification." *Journal of Machine Learning Research* 3,
  233--269. [Open article](https://www.jmlr.org/papers/v3/seeger02a.html).
- Tolstikhin, I. O., and Seldin, Y. (2013). "PAC-Bayes-Empirical-Bernstein
  inequality." In *Advances in Neural Information Processing Systems 26*.
  [Proceedings record](https://proceedings.neurips.cc/paper_files/paper/2013/hash/a97da629b098b75c294dffdc3e463904-Abstract.html).
- Alquier, P., Ridgway, J., and Chopin, N. (2016). "On the properties of
  variational approximations of Gibbs posteriors." *Journal of Machine
  Learning Research* 17(239), 1--41.
  [Open article](https://www.jmlr.org/papers/v17/15-290.html).

### Anytime-valid inference

- Ville, J. (1939). *Étude critique de la notion de collectif*. Gauthier-Villars.
- Howard, S. R., Ramdas, A., McAuliffe, J., and Sekhon, J. (2020).
  "Time-uniform Chernoff bounds via nonnegative supermartingales."
  *Probability Surveys* 17, 257--317.
  [Publisher record](https://doi.org/10.1214/18-PS321).
- Howard, S. R., Ramdas, A., McAuliffe, J., and Sekhon, J. (2021).
  "Time-uniform, nonparametric, nonasymptotic confidence sequences."
  *The Annals of Statistics* 49(2), 1055--1080.
  [Publisher record](https://doi.org/10.1214/20-AOS1991).
- Chugg, B., Wang, H., and Ramdas, A. (2023). "A unified recipe for
  deriving (time-uniform) PAC-Bayes bounds." *Journal of Machine Learning
  Research* 24(372), 1--60.
  [Open article](https://jmlr.org/papers/v24/23-0401.html).
- Ramdas, A., Grünwald, P., Vovk, V., and Shafer, G. (2023).
  "Game-theoretic statistics and safe anytime-valid inference."
  *Statistical Science* 38(4), 576--601.
  [Publisher record](https://doi.org/10.1214/23-STS894).
- Grünwald, P., de Heide, R., and Koolen, W. (2024). "Safe testing."
  *Journal of the Royal Statistical Society Series B* 86(5), 1091--1128.
  [Publisher record](https://doi.org/10.1093/jrsssb/qkae011).

## How this relates to TheoremPath

[TheoremPath's reference map](https://theorempath.com/references) is the broader
curriculum bibliography. It includes optimization, deep learning, language
modeling, reinforcement learning, causal inference, and systems sources that
are outside FormalSLT's present theorem surface.

The division of responsibility is:

- TheoremPath supplies learning routes, chapter-level context, exercises, and
  links across the wider machine-learning curriculum.
- FormalSLT supplies checked Lean declarations, explicit assumptions, concrete
  examples, and axiom audits for the theorem families implemented here.
- Both should cite the underlying textbook or primary paper. TheoremPath is not
  a substitute for mathematical provenance in FormalSLT.

For independent formalization projects and code-level overlap, see
[Related work](./related-work.md). For the exact limits of the current library,
see [Assumptions and nonclaims](./assumptions-and-nonclaims.md).

## Citation practice

When a result depends materially on one of these theorem families, cite both
the original mathematical source and FormalSLT. Use [`CITATION.cff`](../CITATION.cff)
or the README citation block for the software citation. Repository publication
dates do not supersede the dates of the mathematical results or predecessor
formalizations.
