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
| PAC-Bayes Bernstein and Gaussian/variational interfaces | Tolstikhin and Seldin (2013); Alquier, Ridgway, and Chopin (2016); Chugg, Wang, and Ramdas (2023); Jang, Jun, Kuzborskij, and Orabona (2023) | Variance-sensitive penalties, the source-normalized finite empirical-variance MGF, fixed-parameter and finite-catalog observable empirical-Bernstein risk, the retained-Bennett joint mean/variance score, its one-event finite posterior catalog, a closed-form logarithmic-grid endpoint, a reverse-epoch all-sample-size finite-IID endpoint, and continuous-posterior analytic interfaces | The empirical-variance moment, posterior-uniform variance lift, general bounded-loss Bernstein event, two-event rational risk endpoint, separately weighted finite `eta`/`lambda` catalogs, one-event finite joint-pair catalog, zero-residual specialization, exact attained residual penalty, direct fixed-sample square-root bound, and offline all-sample-size reverse-epoch stitch are checked for finite-valued IID observations with `[0,1]` losses. The all-sample-size endpoint is uniform over admissible posterior measures on an arbitrary measurable hypothesis space while retaining finite observations. All-real optimization and a forward exact-Bessel e-process with optional-stopping semantics remain outside the checked scope. |
| Anytime-valid inference and e-processes | Ville (1939); Seldin et al. (2012); Howard et al. (2020, 2021); Chugg, Wang, and Ramdas (2023); Jang et al. (2023); Ramdas et al. (2023); Grünwald, de Heide, and Koolen (2024) | Ville inequalities, confidence sequences, time-uniform PAC-Bayes mixtures, line-crossing bounds, and safe-testing interfaces | Discrete-time processes with the adaptedness, integrability, conditional-MGF, or supermartingale assumptions shown in the signatures |
| Finite stationary laws and Dobrushin contraction | Gaubert and Qu (2015; online 2014); Wolfer (2020); Mitrophanov (2005); the classical finite Krylov--Bogolyubov/Cesaro route | Probabilists' row total variation, maximum row-pair Dobrushin coefficient, oscillation contraction, row-perturbation certificates, finite invariant-law existence, and contraction-based uniqueness | Finite nonempty state spaces. FormalSLT uses `TV = L1 / 2`; its oscillation contraction has no extra factor two, while a uniform row-TV error `eta` yields the candidate perturbation term `2 * eta` after conversion to maximum row `L1` |
| Poisson-corrected stationary risk | Glynn and Meyn (1996); Gaubert and Qu (2015; online 2014); Howard et al. (2021); Chugg, Wang, and Ramdas (2023) | Poisson coboundary/telescoping structure, finite-depth potential and explicit residual, contraction-controlled span, and a forward empirical-Bernstein PAC-Bayes event | Known finite kernel, supplied invariant PMF, deterministic start, finite predictor catalog, bounded transition scores, supplied contraction and centered-risk oscillation envelope, and confidence-allocated finite depths. The library does not assume or construct an exact infinite-series Poisson solution in this capstone |
| Unknown-transition confidence and stationary catalogs | Wolfer (2020); Kueffner, Meggendorfer, Weininger, and Wienhöft (2026); Mitrophanov (2005); Howard et al. (2021); Chugg, Wang, and Ramdas (2023) | One-trajectory visit/edge counts, visit-gated time-uniform coordinate confidence, normalized empirical transition rows, row-TV candidate certificates, Dobrushin perturbation, and stationary-risk composition | One deterministic-start, non-reset finite-state trajectory; predeclared candidate and tilt catalogs; every row visited at the reported time; separate risk and transition failure budgets. This is not the reset/simulation-access MDP sampling model or Wolfer's stationary-ergodic mixing-time interval |
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
- Stochastic dynamics, stationary laws, Poisson correction, and transition
  confidence: `FormalSLT.StochasticDynamics.*`.
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
  [Paper](https://proceedings.neurips.cc/paper/2013/file/a97da629b098b75c294dffdc3e463904-Paper.pdf),
  especially Eq. (9) and Theorems 3--4.
- Maurer, A., and Pontil, M. (2009). "Empirical Bernstein bounds and sample
  variance penalization." In *Proceedings of the 22nd Annual Conference on
  Learning Theory*.
  [Open preprint](https://arxiv.org/abs/0907.3740).
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
  [Preprint](https://arxiv.org/pdf/1810.08240), especially Theorem 4 and
  Appendix A.8.
- Chugg, B., Wang, H., and Ramdas, A. (2023). "A unified recipe for
  deriving (time-uniform) PAC-Bayes bounds." *Journal of Machine Learning
  Research* 24(372), 1--61.
  [Open article](https://jmlr.org/papers/v24/23-0401.html), especially
  Corollary 27 and Appendix A.11.
- Jang, K., Jun, K.-S., Kuzborskij, I., and Orabona, F. (2023). "Tighter
  PAC-Bayes bounds through coin-betting." In *Proceedings of COLT 2023*.
  [Open article](https://proceedings.mlr.press/v195/jang23a.html), especially
  Theorem 1 and Corollary 4.
- Seldin, Y., Cesa-Bianchi, N., Auer, P., Laviolette, F., and Shawe-Taylor,
  J. (2012). "PAC-Bayes-Bernstein inequality for martingales and its
  application to multiarmed bandits." In *Proceedings of the Workshop on
  On-line Trading of Exploration and Exploitation 2*, PMLR 26, 98--111.
  [Open article](https://proceedings.mlr.press/v26/seldin12a.html).
- Ramdas, A., Grünwald, P., Vovk, V., and Shafer, G. (2023).
  "Game-theoretic statistics and safe anytime-valid inference."
  *Statistical Science* 38(4), 576--601.
  [Publisher record](https://doi.org/10.1214/23-STS894).
- Grünwald, P., de Heide, R., and Koolen, W. (2024). "Safe testing."
  *Journal of the Royal Statistical Society Series B* 86(5), 1091--1128.
  [Publisher record](https://doi.org/10.1093/jrsssb/qkae011).
- Karagulyan, V., and Alquier, P. (2026). "Empirical PAC-Bayes bounds for
  Markov chains." In *Proceedings of the 29th International Conference on
  Artificial Intelligence and Statistics*, PMLR 300.
  [OpenReview record](https://openreview.net/forum?id=GlAeeN1Lhp).

### Markov chains, Poisson equations, and transition confidence

- Glynn, P. W., and Meyn, S. P. (1996). "A Liapounov bound for solutions of
  the Poisson equation." *The Annals of Probability* 24(2), 916--931.
  [Author-hosted paper](https://web.stanford.edu/~glynn/papers/1996/GM96.pdf).
  FormalSLT's source dictionary uses the discrete Poisson equation (1),
  additive functional (3), and martingale decomposition (4); its finite-depth
  potential and explicit residual are derived variants.
- Gaubert, S., and Qu, Z. (2015; published online 2014). "Dobrushin's
  ergodicity coefficient for Markov operators on cones." *Integral Equations
  and Operator Theory* 81(1), 127--150.
  [Author-hosted paper](https://www.cmap.polytechnique.fr/~gaubert/PAPERS/GaubertQuIEOTD14QuFinal.pdf) ·
  [publisher record](https://doi.org/10.1007/s00020-014-2193-2).
  Equations (1) and (4) are the finite row-TV and Hopf-oscillation comparators.
- Mitrophanov, A. Yu. (2005). "Sensitivity and convergence of uniformly
  ergodic Markov chains." *Journal of Applied Probability* 42(4), 1003--1014.
  [Publisher record](https://doi.org/10.1239/jap/1134587812). This is nearby
  finite-time and invariant-law perturbation theory, not the exact source of
  FormalSLT's row-triangle `+ 2 * eta` inequality.
- Wolfer, G. (2020). "Mixing time estimation in ergodic Markov chains from a
  single trajectory with contraction methods." In *Proceedings of ALT 2020*,
  PMLR 117, 890--905.
  [Open article](https://proceedings.mlr.press/v117/wolfer20a.html).
  The exact comparators are the `TV = L1 / 2` convention (1), Dobrushin
  coefficient and contraction (6)--(7), visit/edge counts (11), empirical
  transition matrix (12), and coefficient perturbation Fact 5.1.
- Kueffner, K., Meggendorfer, T., Weininger, M., and Wienhöft, P. (2026).
  "Confidence sequences for online statistical model checking of Markov
  decision processes." arXiv:2606.25797v1.
  [Preprint](https://arxiv.org/abs/2606.25797v1). Theorem 3 is the required
  time-uniform transition-coordinate comparator. It works with an IID
  successor stream localized to each state-action pair and an MDP simulator
  that permits resets and adaptive actions; FormalSLT's observed-row process
  instead comes from one non-reset Markov trajectory.

The exact source-to-declaration classifications and total-variation conversion
are in the [literature and theorem-fidelity ledger](./LITERATURE.md). Formal
proof-assistant comparators are recorded in [Related work](./related-work.md).
Neither page makes a priority claim, and entries marked **UNSWEPT** remain open
audit obligations rather than evidence of absence.

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
