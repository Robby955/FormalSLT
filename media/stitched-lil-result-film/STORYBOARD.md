# Storyboard: one checked event, every sample size from four onward

Two caption-led films explain the checked endpoint at FormalSLT v0.2.0 commit
`e01f857d1604788be35fdc2f3dc7108851471a88`. There is no voiceover. The score
supports transitions but carries no mathematical information.

## Main composition: 86 seconds, 16:9

### 00:00-00:08 — The fixed look

A discrete running-mean path continues past one fixed confidence interval.

On screen: “A fixed-time guarantee assumes one fixed look.” Then a single event
and the sample-size condition `n >= 4` replace the isolated slice.

The contrast is fixed-sample versus simultaneous-over-sample-size validity. It
does not assert that fixed-sample bounds are invalid.

### 00:08-00:20 — Exact process assumptions

The process spine and four cards state:

- `X_k` is strongly measurable with respect to `F_(k+1)`;
- `|X_k| <= b` almost everywhere;
- `E[X_k | F_k] = 0` almost everywhere;
- `E[X_k^2 | F_k] <= sigma^2` almost everywhere.

Measurability, integrability, `0 < delta <= 1`, `b > 0`, and `sigma^2 > 0`
remain visible. The scene makes no IID or empirical-variance claim.

### 00:20-00:33 — Checked geometric selector

The factor-four epochs `[4,16)`, `[16,64)`, `[64,256)`, and `[256,1024)`
appear on a log-scaled sample-size axis. The selected epoch satisfies
`4^(j+1) <= n < 4^(j+2)`.

### 00:33-00:46 — Polynomial allocation

The first weights `1/2`, `1/6`, `1/12`, and `1/20` telescope through

`w_j = 1/(j+1) - 1/(j+2)`

to the checked identity `sum_j w_j = 1`.

### 00:46-01:00 — Fixed-tilt boundaries

For declared illustrative parameters `sigma^2 = 0.08`, `b = 0.25`, and
`delta = 0.05`, the film evaluates each checked epoch tilt and plots the actual
fixed-tilt mean-boundary shape

`subGammaCgf(sigma^2,b,lambda_j)/lambda_j + B_j/(n lambda_j)`

on a log-scaled `n` axis. Each curve's matching epoch is bright; its later
all-sample-size tail remains faint. These are computed `a + c/n` curves, not
arbitrary screen-space lines.

### 01:00-01:14 — The stitch

The upper and lower segments evaluate the displayed `W_n` at every integer
sample size in the four plotted epochs under the same declared parameters.
They split at each epoch jump. The path between them is explicitly labeled
illustrative. Epoch cuts remain visible while the allocation ledger resolves
to `sum_j delta w_j = delta` and `mu.real(G^c) <= delta`.

The proof uses countable subadditivity. It does not construct a countable
e-process.

### 01:14-01:26 — Checked endpoint

The final card binds the selected epoch, budget, width, event complement mass,
and all-sample-size conclusion. It identifies

`FormalSLT.AnytimeValid.PolynomialStitchedLIL.exists_polynomialStitchedLIL_explicit_event`

at source `e01f857`. The boundary line says: allocated fixed-tilt stitch; no
sharp-constant claim; not itself an e-process. `G` is a set; its measurability
is not asserted by this theorem.

## Mobile composition: 44 seconds, 4:5

This is a native `1080 x 1350` composition, not a center crop.

- **00:00-00:07:** fixed look versus one event for every sample size `n >= 4`.
- **00:07-00:15:** the four exact process conditions, with a.e. scope visible.
- **00:15-00:26:** factor-four epochs, telescoping weights, selected-epoch
  bucket, and exact budget.
- **00:26-00:35:** the exact numerical `W_n` envelope with the path labeled
  illustrative, followed by complement mass at most `delta`.
- **00:35-00:44:** the checked formula, source identifier, and scope boundary.

## Render discipline

- Prose uses Avenir Next; mathematical content uses TeX through `MathTex`.
- The 16:9 and 4:5 scenes have separate safe-frame assertions.
- No essential text is placed near platform crop or overlay regions.
- Runtime assertions reject overflow and selected group overlaps.
- All scene starts are locked to `film_config.json` and caption sidecars.
- Render caches and temporary TeX products remain ignored.

## Evidence anchors

The extractor checks at the exact release commit:

- `FormalSLT/AnytimeValid/PolynomialStitchedLIL.lean` for assumptions,
  selector, failure-mass result, and explicit endpoint;
- `FormalSLT/AnytimeValid/AllocationLogLog.lean` for polynomial weights;
- `FormalSLT/AnytimeValid/SubGaussianCS.lean` for the running mean;
- `FormalSLT/AnytimeValid/MixtureCS.lean` for increment adaptedness;
- `examples/CheckPolynomialStitchedLIL.lean` for the public theorem and axiom
  query;
- public frontier/nonclaim documents for scope and priority boundaries.
