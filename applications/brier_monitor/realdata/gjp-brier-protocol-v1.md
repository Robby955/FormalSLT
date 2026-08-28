# Prospective real-data Brier monitor protocol v1.1

Status: **PROSPECTIVE PROTOCOL ONLY. NO STREAM, RECEIPT, OR RESULT.**

Human-readable companion to
[`gjp-brier-protocol-v1.json`](gjp-brier-protocol-v1.json). The JSON is the
fail-closed analytic contract. Where prose and JSON differ, the JSON wins.

## Why this protocol exists

`applications/brier_monitor/` currently holds a synthetic proof-of-life
arithmetic artifact. Its 512-observation stream reduces to 512 identical
losses of `1/16` for the only model carrying posterior mass, and its whole
observable quadratic variation `49/256` is the single residual produced by
initializing the forward predictor at `1/2`. That artifact demonstrates
replayable exact arithmetic. It demonstrates nothing statistical, and it is
not attached to a Lean theorem.

This protocol freezes the analysis of a real, externally timestamped
forecasting stream before that stream is joined to its outcomes.

## Authoritative dataset

Good Judgment Project data released from IARPA's Aggregative Contingent
Estimation program.

- Persistent identifier: `doi:10.7910/DVN/BPCDH5`
- Version: `1.0`, `versionState` `RELEASED`, released `2016-11-11T18:47:06Z`
- Terms: CC0 1.0 (`rightsIdentifier` `CC0-1.0` in the Dataverse record)
- Six files are used, pinned by the repository's own published MD5:

  | file | Dataverse id | MD5 |
  | --- | --- | --- |
  | `ifps.csv` | 2917330 | `5c703d02284f8b563399967c554f1417` |
  | `readme.txt` | 2917350 | `304832fa3e6b06861897f31eda69ba1f` |
  | `survey_fcasts.yr1.tab` | 2917351 | `091ae92c90ec426772ea784a906d7ddb` |
  | `survey_fcasts.yr2.tab` | 2917352 | `528d1bfbff2ab8da6ba2b599b3b80e26` |
  | `survey_fcasts.yr3.tab` | 2917353 | `e5837d12b2a17d3ffd0f0bf1f46e61b0` |
  | `survey_fcasts.yr4.tab` | 2917354 | `47041be832baed547963c0ffd0d71a9d` |

Download hazard, checked and recorded here because it silently breaks replay:
the tabular files are ingested by Dataverse, and the plain
`/api/access/datafile/{id}` route returns a regenerated TSV whose bytes do not
match the published MD5. The `filesize` reported by the metadata API is the
regenerated size, not the original. Only `?format=original` reproduces the
pinned digest. `ifps.csv` downloaded via `?format=original` was confirmed at
1072153 bytes with the published MD5; `survey_fcasts.yr1.tab` was confirmed at
30495631 original bytes with the published MD5, against a metadata `filesize`
of 29454945.

Candidates rejected, with the reason:

- **Metaculus public API.** Questions, resolutions, and community forecasts are
  served from a live endpoint with no versioned release and no DOI. A replay
  cannot be pinned.
- **FiveThirtyEight `fivethirtyeight/data`.** CC-BY-4.0 and a commit SHA gives
  an immutable pin, but at `4c1ff5e3aef1816ae04af63218015066e186c147`
  (pushed 2025-02-25) `nfl-elo/` contains only `README.md`; the forecast CSVs
  were served from a project endpoint, not the repository. Pinning the repo
  pins a pointer, not data. Separately, the historical `nfl_elo.csv` Elo path
  is a retrospective backfill whose hyperparameters were fit over the whole
  history, which is model-selection leakage that no timestamp can rule out.
- **NOAA/NWS probability-of-precipitation verification archives.** Genuine
  forecast-before-outcome structure, but distributed as rolling operational
  archives without a release tag or DOI.
- **Rain in Australia.** Contains covariates and outcomes, not emitted
  probabilistic forecasts. There is nothing to monitor that a modeler did not
  themselves produce after seeing the data.

## Pre-registration disclosure

During design the following aggregates of `ifps.csv` were inspected: the count
of binary questions with a resolved `a`/`b` outcome (382), the marginal outcome
counts (`a` 96, `b` 286), the `date_start` and `date_closed` ranges, and the
`date_closed` counts by calendar year (2011: 22, 2012: 100, 2013: 83,
2014: 110, 2015: 67). The column header line and the first three data rows of
`survey_fcasts.yr1.tab` were inspected. No individual forecast value was
joined to any outcome, and no per-question outcome was read.

The global marginal is therefore not blind. The constant baseline below is
consequently defined to read its probability from the train split at run time
rather than from any number appearing in this document.

## Prospective safety amendments

No score, posterior, boundary, or monitor result existed when these amendments
were made. A structural pass over the pinned timestamps found that the original
date-suspension rule was insufficient:

- 200 of the 382 candidate questions have `date_closed < date_suspend`;
- 3,987 option-`a` rows occur at or after closure but before suspension;
- 5,442 option-`a` rows predate the recorded question start;
- `5008-0` and `5009-0` have no forecast inside the corrected window.

The admissible window is therefore fixed to

```text
date_start <= timestamp < min(date_suspend, start-of-date_closed).
```

`date_closed` is day-only in these rows, so `start-of-date_closed` means
midnight at the start of that recorded date in the same naive source clock.
This deliberately excludes all forecasts from the closure date when no closure
time is available. The two questions with no admissible forecast are excluded
by identifier, leaving 380 complete cases. This is a safety correction based
only on timestamp structure, not model performance.

The original Gibbs-posterior formula was also incomplete as an exact replay
contract: exponential weights are transcendental, but the Lean input must be a
rational probability mass function. The certified posterior is now the
deterministic `10^15`-simplex quantization of the ideal Gibbs weights. The ideal
weights are evaluated with decimal precision 80 and `ROUND_HALF_EVEN`; scaled
weights are floored and the remaining integer units go to descending
fractional remainders, with model identifiers breaking ties. The resulting
rational posterior, not the ideal decimal diagnostic, is the theorem input.

## Monitored unit and chronological split

One observation per binary question with a resolved outcome, ordered by
`date_closed` ascending, ties broken by `ifp_id` ascending. The outcome is
`y = 1` when `outcome == "a"` and `y = 0` when `outcome == "b"`.

Question level is the correct unit because an outcome is revealed once per
question. Expanding to question-day pairs would reuse one outcome across many
predictions and destroy the one-step-ahead structure the monitor assumes.

| split | `date_closed` window | expected count |
| --- | --- | --- |
| train | through 2012-12-31 | 122 |
| calibration | 2013-01-01 through 2013-12-31 | 83 |
| monitor | 2014-01-01 onward | 175 |

Boundaries are calendar-year cuts on the resolution date, chosen before any
forecast file was joined. The two timestamp-ineligible monitor questions are
excluded by the prospective amendment above; train and calibration remain 122
and 83. The monitor split is the tournament's final stretch, where the
forecaster pool is largest and most experienced, so a failure there is a
failure of the method rather than of a thin early panel.

## Prediction before outcome

Every model reads only rows of `survey_fcasts.*` satisfying
`date_start <= timestamp < effective_cutoff`, where `effective_cutoff` is the
earlier of `date_suspend` and conservative closure midnight. Two enforcements:

1. The stream builder records, per observation, the minimum and maximum
   forecast `timestamp` it consumed together with `date_start`, `date_suspend`,
   and `date_closed`. Any observation with a consumed row outside the amended
   interval aborts the run.
2. The builder is given the outcome column only after the forecast table has
   been reduced to one probability per model per question. The reduction
   function's signature admits no outcome argument.

Both are auditable after the fact from the receipt alone. Forecast event types
`0` (new), `1` (update), `2` (affirm), and `4` (withdraw) are all retained as
emitted values, following the pinned survey `readme.txt`; any unknown type
aborts the replay. Same-user events are ordered by timestamp, numeric
`forecast_id`, source year, and source line.

## Predeclared model catalog and posterior

Four models, all reading only amended-window forecasts of option `a`:

| id | definition |
| --- | --- |
| `constant-train-baserate` | the train-split outcome frequency, quantized |
| `first-week-mean` | row-level mean of recognized events in `[date_start, min(date_start + 7 days, effective_cutoff))` |
| `final-consensus-median` | median over users of each user's last emitted value before `effective_cutoff`; withdrawals retain their emitted last-standing probability |
| `extremized-final-consensus` | logit extremization of the previous with exponent 2, clipped to `[1/100, 99/100]` |

The extremization exponent is fixed at 2 and is not tuned. Prior `pi` is
uniform, `1/4` on each model.

An ideal posterior is computed on the calibration split only, by exponential
weights with learning rate `eta = 1`:

```text
rho_ideal(m)  proportional to  pi(m) * exp( - n_cal * empiricalBrier_cal(m) )
```

The largest-remainder rule above converts `rho_ideal` to the exact rational
posterior `rho`. `rho` is then frozen and used unchanged across the entire
monitor split, so `klDiv rho pi` is a constant fixed before any monitored
observation.

## Rational quantization

Denominator `D = 10^6`, fixed here.

Every model emits `p` already rounded to the nearest multiple of `1/D`, ties
to even. The monitored forecaster **is** the quantized forecaster. There is no
downstream approximation to bound, because nothing unquantized is ever the
object of a claim. Losses `(p - y)^2` are then exact rationals with
denominator `D^2`, and both

- `finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk` and
- `finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation`

are exact rationals, since the forward predictor is `1/2` at index 0 and a
prefix mean thereafter.

Only `klDiv`, the confidence log, and `forwardEmpiricalBernsteinPsi` are
transcendental. Each is replaced by a rational enclosure and reported at its
**upper** endpoint on a `10^-15` grid:

| quantity | sign in the boundary | rounding |
| --- | --- | --- |
| `empiricalSuffixRisk` | `+`, exact | none |
| `suffixQuadraticVariation` | `+`, exact, `>= 0` | none |
| `klDiv rho pi` | `+` | up |
| `log((a+1)(a+2)/deltaEff)` | `+` | up |
| `forwardEmpiricalBernsteinPsi lambda` | `+`, multiplied by a nonnegative | up |
| `(n - w) * lambda` | denominator, exact, `> 0` | none |

Validity: write the reported endpoint as
`Rhat + (KLup + LOGup + PSIup * V) / ((n - w) * lambda)`. Each numerator
summand is at least its real counterpart, using `V >= 0` from
`finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation_mem_Icc` for the
`PSIup * V` term. The denominator is exact and strictly positive, and `Rhat`
is exact, so the reported endpoint is at least
`finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary` at that atom.
Every rounding therefore makes the certificate harder to satisfy, never
easier.

## Confidence allocation, wakes, atoms

`delta = 1/160`, matching the synthetic artifact so the two are comparable.

Wake grid `W = {0, 8, 32, 128}`, declared here. Wake `w` spends
`delta * polynomialEpochWeight w = delta / ((w+1)(w+2))`.

Atoms at wake `w` range over
`Finset.range (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1)`, that
is `(Nat.log 4 (n - w)).pred + 2 + 1` atoms, with
`lambda_a = geometricForwardTilt a = 1 / 2^(a+1)`.

Shopping outside the declared wake grid, or over a different atom range, voids
the allocation. The grid is in the JSON and the checker enforces it.

## Baselines and the comparison

- **B1 fixed-time.** The same PAC-Bayes empirical-Bernstein endpoint evaluated
  once, at a single predeclared `n`, with no wake weight.
- **B2 naive repeated look.** B1's fixed-time endpoint recomputed at every `t`
  and reported at the first `t` that clears the operating threshold. This
  procedure is invalid and is included to be shown failing.
- **B3 anytime-valid monitor.** The wake-and-atom construction above.

Primary metric, type-I control: over `R = 2000` null replicates in which each
`y_t` is redrawn independently from the train-split base rate while `p_t` is
held fixed, the fraction of replicates in which the procedure ever declares.
Target for B1 and B3 is at most `delta = 1/160`. B2 is expected to exceed it.

Secondary metric, on the real monitor stream: the first index `t` at which the
reported endpoint falls below the train-split base-rate Brier score, and the
endpoint width at the final `n` for each of B1 and B3.

A win is: B3's null exceedance is at most `delta` while B2's is materially
above it, **and** B3's endpoint at final `n` is within a factor stated in the
receipt of B1's single-look endpoint. Anything else is published unchanged.

## Receipt fields and their Lean bindings

| receipt field | Lean object it must instantiate |
| --- | --- |
| `horizon` | `n` |
| `wake` | `w`, with `w <= n` and `4 <= n - w` |
| `prior`, `posterior` | `prior posterior : iota -> Real`, satisfying `IsFullSupportPMF` and `IsPMF` |
| `posterior_empirical_brier_risk` | `finiteTrajectoryPosteriorEmpiricalPrequentialSuffixRisk score posterior w n x` |
| `suffix_predictor_quadratic_variation` | `finiteTrajectoryPosteriorSuffixPredictorQuadraticVariation score posterior w n x` |
| `confidence_delta` | `delta` |
| `effective_delta` | `continuousTrajectorySleepingSuffixEffectiveConfidence delta w` |
| `tilt_atom` | `a`, together with the hypothesis `a ∈ Finset.range (finiteTrajectorySleepingSuffixVarianceMaxIndex w n + 1)` |
| `tilt` | `geometricForwardTilt a` |
| `kl_interval.upper` | an upper bound on `klDiv posterior prior` |
| `boundary_interval.upper` | an upper bound on `finiteTrajectorySleepingSuffixVarianceGeometricTiltBoundary prior posterior score delta a w n x`, hence via `finiteTrajectorySleepingSuffixVarianceSelectedBoundary_le` on `...SelectedBoundary ...` |
| `stream.max_consumed_timestamp[t]` | no Lean binding; audit field |

The binding that does **not** exist yet, and without which every row above is
decoration:

> a Lean `score : iota -> TrajectoryScore Z` and path `x : Nat -> Z` realizing
> the monitored stream, plus lemmas proving that the two exact rationals equal
> the corresponding Lean expressions at that `score` and `x`.

Until an `examples/CheckGJPBrierMonitorReceipt.lean` builds that instantiation
and discharges those two equalities, the receipt is arithmetic that mirrors
the Lean definitions rather than a certificate the Lean theorem produced. The
JSON records this as an open obligation and the checker refuses to call the
artifact certified while it is open.

## Replay contract

A third party runs, in a clean checkout at the protocol commit:

```bash
python3 scripts/check_gjp_brier_protocol.py
python3 scripts/fetch_gjp_brier_inputs.py --out <dir>
```

What must match bit for bit:

- the six downloaded files, by the MD5 values tabled above, fetched with
  `?format=original`;
- the canonical JSON bytes of the built stream file, and its SHA-256;
- the canonical JSON bytes of the receipt, and its SHA-256;
- the generated Lean data module bytes.

What must match by value rather than bytes: nothing. Floating point never
enters a tracked artifact; every tracked number is a canonical reduced
rational string.

## Leakage tests

Each test states the condition under which it fails, and the pipeline is
considered broken unless every one of them behaves as written.

1. **Timestamp assertion.** For every observation, every consumed forecast
   satisfies `date_start <= timestamp < effective_cutoff`. Fails closed on the
   first violation.
2. **Deliberately leaked tripwire.** A model `oracle-leak` defined as `99/100`
   when the outcome is `a` and `1/100` otherwise is submitted to the same
   ingestion path. The ingestion must **refuse** it, because building it
   requires reading the outcome column that the reduction function does not
   accept. The test asserts the refusal fires. If the tripwire is instead
   scored and merely reports a small risk, the ingestion boundary is not real.
3. **Future-feature ablation.** Rebuild `first-week-mean` with windows of 1, 3,
   7, and 14 days. Every ablation remains clamped by the same start,
   suspension, and closure window; consuming a row outside it is a hard
   failure.
4. **Shuffled-time control.** Permute the monitor stream order, holding
   `(p_t, y_t)` pairs together, over 200 permutations. The empirical suffix
   risk is permutation invariant and must be identical to the last rational
   digit; the quadratic variation is not, and its permutation distribution is
   reported. A shifted empirical risk means the pipeline is order sensitive
   somewhere it should not be.
5. **Outcome-shuffle null.** The `R = 2000` replicate null above. A B3
   exceedance rate above `delta` means the construction, the allocation, or
   the implementation is wrong, and the result is reported as such.

## When this protocol produces a misleading result

- **Vacuity.** At `n = 175` the confidence log term dominates. A back of the
  envelope with `n = 175`, `w = 0`, `KL <= log 4`, `a = 0` puts the excess near
  `0.1`, against a base-rate Brier score near `0.19`. The endpoint may well
  land above the base rate. That is a real negative result about sample size,
  it is predeclared here, and no re-tuning of `delta`, the wake grid, the
  catalog, or the split is permitted in response to it.
- **Encountered risk is not future risk.** Everything bounded here is the
  posterior-averaged empirical Brier risk on the encountered suffix of *these*
  questions. It is not the risk on future questions, not a stationary
  population risk, and not deployment risk. GJP question difficulty drifts
  across the tournament, so the gap is not a formality.
- **Question selection.** GJP voided and retired questions. The 382 resolved
  binaries are already a selected subset, and the temporal amendment excludes
  two more questions with no legal forecast. The 380-question result does not
  generalize to every question the tournament posed. The receipt records both
  selection stages.
- **Catalog contamination.** `final-consensus-median` and its extremization
  use the same crowd whose behavior the tournament's own feedback shaped. The
  bound stays valid for the encountered suffix regardless, but a favorable
  reading of the catalog's skill is not licensed by it.
- **Wake shopping.** The polynomial wake weight pays for the declared grid
  only. Reporting a wake outside `W` after seeing the stream silently spends
  confidence that was never allocated.
