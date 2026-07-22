# Walking to infinity on visible points with a composite coordinate: chain scales, an unconditional ubiquity theorem, and a power-scale reduction

**Status: working note, July 2026.** Nothing here solves the problem. The
problem remains open. This note records, with complete proofs, several new
partial results that extend the "composite-anchor" reduction, and it maps the
remaining obstruction precisely.

## 0. The problem

Call a lattice point $(x,y) \in \mathbb{Z}^2$ **admissible** if

* $x > 1$ and $y > 1$,
* $\gcd(x,y) = 1$ (the point is *visible* from the origin), and
* at least one of $x, y$ is composite (the point is not prime–prime).

**Question (Erdős; open).** Does the graph on admissible points, with edges
between lattice points at distance $1$, contain an infinite path?

A path is **monotone** if every step increases $x$ or increases $y$. Every
result below produces monotone paths, which is stronger than required.

Throughout, $P^-(n)$ denotes the least prime factor of $n \ge 2$.

### Provenance

Sections 1–2 restate, with proofs, prior partial results from the working
notes accompanying this repository lane (parity lemma, barrier lemma, the
gap-condition reduction, and a CRT construction of arbitrarily long finite
paths). Sections 3–7 are new in this note:

* **Theorem C** (§4): unconditionally, *every* dyadic window $[X, 2X]$ with
  $X \ge \exp(C\, m\log m)$ contains an $m$-stage monotone admissible path.
  The prior CRT construction gave one such path *somewhere*, at doubly
  exponential height $\exp(m e^{m(1+o(1))})$; Theorem C brings the height to
  singly exponential and, more importantly, shows the finite paths are
  *ubiquitous at every scale*.
* **Theorem A** (§5): a conditional solution from a hypothesis at *any single
  fixed power scale* $x^\theta$, $0 < \theta < 1/2$ — much weaker than the
  "balanced semiprimes at square-root scale" that the gap condition appeared
  to demand.
* **Proposition B** (§6): an explicit floor-quotient semiprime mechanism
  realizing the hypothesis, connecting the problem to the active literature
  on primes of the form $\lfloor x/n \rfloor$.
* **Lemma 2′ and Corollary 2″** (§3): a quantitative escape-rate lower bound
  (a transversal sharpening of the barrier lemma).
* §7: a precise scale analysis of why ladder ("multi-row") strategies stall
  exactly at the quadratic-versus-linear Jacobsthal gap, and why the chain
  route of Theorem A sidesteps interval-coprimality entirely.
* §8: computational evidence at heights up to $10^9$ (scripts in
  `erdos/scripts/`, outputs in `erdos/data/`).

## 1. Basic structure (prior results, restated)

**Lemma 1 (parity).** Let $(x,y)$ be visible with $x$ even. Then any
admissible neighbour differs in the $x$-coordinate. Symmetrically with the
roles of $x, y$ swapped.

*Proof.* $x$ even and $\gcd(x,y)=1$ force $y$ odd, so $y \pm 1$ are even and
$\gcd(x, y\pm 1) \ge 2$: the vertical neighbours are not visible. $\square$

Hence every change of direction of an admissible path occurs at an odd–odd
point, and (once both coordinates are unbounded, see §3) an infinite path
must turn infinitely often at odd–odd points.

**Lemma 2 (barrier).** An infinite admissible path cannot have a bounded
coordinate: if $2 \le y \le M$ along the path, then for
$Q = \operatorname{lcm}(2, \dots, M)$ every column $x \equiv 0 \pmod Q$
contains no visible point with $2 \le y \le M$, so the $x$-coordinate is
trapped between consecutive multiples of $Q$.

Section 3 sharpens this quantitatively.

## 2. The gap-condition chain and the L-path reduction (prior, restated)

**Condition (C1).** A strictly increasing sequence of composite integers
$a_0 < a_1 < a_2 < \cdots$ (finite or infinite) satisfies (C1) if for all $n$,

$$a_{n+2} - a_n \;<\; \min\bigl(P^-(a_n),\, P^-(a_{n+2})\bigr). \tag{C1}$$

**Proposition 1 (L-path reduction).** If an infinite (C1) sequence exists,
the answer to the problem is yes; indeed the monotone path

$$(a_n, a_{n+1}) \longrightarrow (a_n, a_{n+2}) \longrightarrow (a_{n+1}, a_{n+2}), \qquad n = 0, 1, 2, \dots$$

(vertical leg then horizontal leg, in unit steps) is admissible. If the
sequence has $m$ terms, the same construction gives an $(m-2)$-stage finite
monotone admissible path.

*Proof.* Write stage $n$ for the two legs above; the endpoint
$(a_{n+1}, a_{n+2})$ of stage $n$ is the start of stage $n+1$, so the stages
concatenate. Every step increases $x + y$ by exactly $1$, so the path is
simple, and $a_n \to \infty$ makes it leave every bounded region (in the
infinite case).

*Vertical leg of stage $n$*: points $(a_n, s)$, $a_{n+1} \le s \le a_{n+2}$.
Both coordinates exceed $1$, and $a_n$ is composite, so only visibility needs
checking. If a prime $p$ divides $\gcd(a_n, s)$ then $p \mid s - a_n$ and
$0 < a_{n+1} - a_n \le s - a_n$, so $s - a_n \ge p \ge P^-(a_n)$. But (C1)
gives $s - a_n \le a_{n+2} - a_n < P^-(a_n)$, a contradiction.

*Horizontal leg of stage $n$*: points $(u, a_{n+2})$, $a_n \le u \le a_{n+1}$,
with $a_{n+2}$ composite. If $p \mid \gcd(u, a_{n+2})$ then
$p \mid a_{n+2} - u$ and $0 < a_{n+2} - a_{n+1} \le a_{n+2} - u \le a_{n+2} - a_n < P^-(a_{n+2}) \le p$,
again a contradiction. $\square$

The prior CRT construction produces, for every $m$, an $m$-term (C1)
sequence, hence arbitrarily long finite monotone admissible paths — but at
height doubly exponential in $m$, and only *somewhere*. Theorem C below
improves both defects. The missing step for the full problem is purely the
passage from "arbitrarily long finite paths" to "one infinite path": the
finite paths constructed have no common starting vertex, so König's lemma
does not apply.

## 3. A quantitative escape rate (new)

For a finite set $R$ of integers $\ge 2$, call a finite set $S$ of primes a
**transversal** of $R$ if every $y \in R$ is divisible by some $p \in S$, and
put

$$\tau(R) \;=\; \min_{S \text{ transversal}} \prod_{p \in S} p
\;\le\; \prod_{y \in R} P^-(y).$$

**Lemma 2′ (blocking, transversal form).** Let $P$ be a path of visible
points (the composite condition is not needed here) whose $y$-coordinates all
lie in the finite set $R$. Then the $x$-coordinates of $P$ span an interval
of length $< \tau(R)$.

*Proof.* Let $S$ be a transversal and $M_S = \prod_{p \in S} p$. If a column
$c \equiv 0 \pmod{M_S}$ contained a point $(c, y)$ of $P$, pick $p \in S$
with $p \mid y$; then $p \mid \gcd(c,y)$, contradicting visibility. A unit-step
path whose $x$-range contains an interval of length $\ge M_S$ must visit
every column in it, in particular a multiple of $M_S$. Hence the $x$-span is
$< M_S$, for every transversal $S$. $\square$

**Corollary 2″ (escape rate).** There is an absolute constant $c > 0$ such
that any path of visible points **with all coordinates $> 1$** (as
admissibility requires — without this a visible path travels freely along
the row $y = 1$) whose $x$-coordinate spans an interval of length
$D \ge 16$ must contain a point with

$$y \;\ge\; c \,\frac{\log D}{\log\log D},$$

and symmetrically in $x$. In particular, on any infinite admissible path
both coordinates are unbounded (Lemma 2), with an explicit growth rate.

*Proof.* Let $R$ be the set of $y$-coordinates used and $Y = \max R$. By
Lemma 2′, $D < \tau(R) \le \prod_{y \in R} P^-(y) \le Y^{|R|} \le Y^{Y}$,
since $R \subseteq [2, Y]$. Taking logarithms twice gives the claim. $\square$

Remark. Lemma 2′ needs only visibility, so it also constrains hypothetical
*non-monotone* solutions and gives a concrete necessary growth profile that
any solution — or any counterexample argument — must respect.

## 4. Ubiquity of finite paths: an unconditional improvement (new)

We use two classical facts.

* **(S1) Rough numbers are dense.** There exist absolute constants
  $c_1 > 0$ and $X_1$ such that for $X \ge X_1$ and $5 \le z \le X^{1/3}$,
  $$\#\{n \in (X, 2X] : P^-(n) > z\} \;\ge\; c_1 \frac{X}{\log z}.$$
  This is a standard lower-bound sieve estimate (Buchstab's identity /
  the fundamental lemma of sieve theory; see e.g. Halberstam–Richert,
  *Sieve Methods*, or Tenenbaum, *Introduction to Analytic and Probabilistic
  Number Theory*, III.6; the density of $z$-rough numbers is
  $(e^{-\gamma} + o(1))/\log z$ uniformly in this range, and Theorem C only
  invokes (S1) with $z \ge 4\log X$, far from the small-$z$ edge cases).
  Any fixed admissible $c_1$ works below; the point is only that it is
  positive and absolute.
* **(S2) Chebyshev.** $\pi(2X) - \pi(X) \le C_2 X / \log X$ for an absolute
  $C_2$ and all $X \ge 2$.

**Theorem C (finite paths at every scale).** There are absolute constants
$C_0$ and $m_0$ such that for every $m \ge m_0$ and every
$X \ge \exp(C_0\, m \log m)$, the interval $(X, 2X]$ contains $m + 2$
composite integers $a_0 < a_1 < \cdots < a_{m+1}$ satisfying (C1).
Consequently (Proposition 1) the box $(X, 2X]^2$ contains an $m$-stage
monotone admissible path — in **every** dyadic window at sufficient height,
not merely somewhere.

*Proof.* It suffices to produce $M := m + 2$ chain elements. Put
$A = 2(C_2 + 2)/c_1$ and $z = X^{1/(AM)}$; we assume $m \ge m_0$ and
$X \ge \exp(C_0 m \log m)$ with $C_0 = 3A$, which for $m \ge m_0$ gives
$\log X \ge 2AM \log M$, and we check the size conditions at the end. Below
we write $m$ for $M$ to keep the notation light; only the absolute constants
are affected.

Let $R$ be the increasing sequence of $z$-rough numbers in $(X, 2X]$ (i.e.
$P^-(n) > z$; primes included for now). By (S1),
$|R| \ge c_1 X/\log z = c_1 A m\, X/\log X$.

Call a gap between consecutive elements of $R$ **big** if it exceeds $z/4$.
Since the gaps sum to at most $X$, there are at most $4X/z$ big gaps. Cut the
sequence $R$ at every big gap and at every prime element, and discard the
primes. This partitions the composite elements of $R$ into consecutive
**blocks**; within a block, consecutive elements differ by at most $z/4$.

Counting: the number of cut points is at most
$(\pi(2X) - \pi(X)) + 4X/z \le C_2 X/\log X + 4X/z$. The condition
$z \ge 4 \log X$ (verified below) makes $4X/z \le X/\log X$, so the number of
blocks is at most $(C_2 + 1)X/\log X + 1 \le (C_2 + 2) X/\log X$.

The number of composite elements of $R$ is at least
$c_1 A m X/\log X - C_2 X/\log X \ge \tfrac{1}{2} c_1 A m\, X/\log X$
for $m \ge m_0$ large. By pigeonhole some block contains at least

$$\frac{\tfrac12 c_1 A m\, X/\log X}{(C_2+2)X/\log X} \;=\; \frac{c_1 A}{2(C_2+2)}\, m \;=\; m$$

elements. Take $a_0 < \cdots < a_{m-1}$ to be $m$ consecutive elements of
that block: they are composite, $z$-rough, and satisfy
$a_{n+2} - a_n \le z/2 < z < \min(P^-(a_n), P^-(a_{n+2}))$, which is (C1).
Proposition 1 turns them into the path, whose coordinates all lie in
$[a_0, a_{m-1}] \subseteq (X, 2X]$.

Size conditions: $z = X^{1/(Am)} \le X^{1/3}$ is immediate from $Am \ge 3$.
For $z \ge 4\log X$, i.e. $\log X/(Am) \ge \log(4\log X)$: the function
$L \mapsto L/(Am) - \log(4L)$ is increasing in $L$ for $L > Am$, so it
suffices to check it is $\ge 0$ at the smallest allowed value
$L = \log X = 2Am\log m$, where $L/(Am) = 2\log m$ and
$\log(4L) = \log(8Am\log m) \le 2\log m$ for $m \ge m_0(A)$. $\square$

Remarks.

1. With the classical numerical inputs (any admissible $c_1$ in (S1), e.g.
   $c_1 = 2/5$ for $z \le X^{1/3}$ and $X$ large, and $C_2 = 3$) one may take
   $A = 25$, $C_0 = 75$; no attempt at optimization has been made.
2. The prior CRT construction required height
   $\exp\bigl((m-1) \prod_{p \le m} p\bigr) = \exp(e^{m(1+o(1))} m)$.
   Theorem C requires $\exp(O(m \log m))$ and delivers the path in every
   dyadic window from that height on. This "ubiquity at all scales" is
   precisely the raw material that any future nesting/gluing argument (the
   missing König step) would consume: candidate continuations of a partial
   path now exist in every window ahead of it. What is still missing is
   *reachability* of those continuations from a fixed partial path, not
   their existence.
3. The proof mechanism (Markov bound on gaps + pigeonhole on prime
   breakpoints) uses no worst-case short-interval information at all; that is
   why it cannot by itself produce an infinite chain — worst-case supply along
   *one specific* orbit is exactly what condition (C1) needs and what §5
   isolates.

## 5. A power-scale reduction (new)

**Hypothesis B($\theta$).** Fix $0 < \theta < 1/2$. There exists $x_\theta$
such that for every integer $x \ge x_\theta$ the window
$(x - x^\theta,\, x]$ contains a composite integer $a$ with
$P^-(a) > 10\, x^{\theta}$.

Note the self-consistency constraint: a composite $a \le x$ has
$P^-(a) \le \sqrt{a} \le \sqrt{x}$, so B($\theta$) can only hold when
$10 x^\theta < \sqrt x$, i.e. $\theta < 1/2$ — and for fixed
$\theta < 1/2$ it becomes non-vacuous only for $x > 10^{2/(1-2\theta)}$.
The candidate density is favorable: the expected number of certificates per
window is $\asymp_\theta x^\theta/\log x \to \infty$ (rough numbers of level
$10x^\theta$ have density $\sim e^{-\gamma}/(\theta \log x)$, primes only
$1/\log x$, and $e^{-\gamma}/\theta > 1$ for every $\theta < 1/2$).

**Theorem A.** If B($\theta$) holds for a single $\theta \in (0, 1/2)$, then
an infinite (C1) sequence exists, hence (Proposition 1) an infinite monotone
admissible path exists and the answer to the Erdős problem is **yes**.

*Proof.* Choose $x_1 \ge x_\theta$ with $x_1^\theta \ge 25$, and define
integers $x_{n+1} = x_n + 2\lceil x_n^\theta \rceil$. Since
$x_{n+1} \le x_n + 2x_n^\theta + 2 \le 2 x_n$ and $\theta \le 1/2$,

$$x_{n+1}^\theta \;\le\; 2^{\theta} x_n^{\theta} \;\le\; \sqrt2\, x_n^\theta. \tag{5.1}$$

By B($\theta$) pick a composite $a_n \in (x_n - x_n^\theta, x_n]$ with
$P^-(a_n) > 10 x_n^\theta$.

*Monotonicity.* Using (5.1),
$a_{n+1} > x_{n+1} - x_{n+1}^\theta \ge x_n + 2x_n^\theta - \sqrt2\,x_n^\theta > x_n \ge a_n$.

*Gap bound.* Again with (5.1),
$$a_{n+2} - a_n \;<\; x_{n+2} - (x_n - x_n^\theta)
\;\le\; 2x_n^\theta + 2 x_{n+1}^\theta + 4 + x_n^\theta
\;\le\; (3 + 2\sqrt2)\,x_n^\theta + 4 \;\le\; 6\,x_n^\theta,$$
the last step because $x_n^\theta \ge 25$ absorbs the additive $4$.

*Condition (C1).* $P^-(a_n) > 10x_n^\theta > 6x_n^\theta$ and
$P^-(a_{n+2}) > 10 x_{n+2}^\theta \ge 10 x_n^\theta > 6 x_n^\theta$, so
$a_{n+2} - a_n < \min(P^-(a_n), P^-(a_{n+2}))$. The $a_n$ are composite and
strictly increasing, and $a_n \to \infty$. $\square$

Three comments on why this reduction is sharper than it may look.

**(a) Any power scale suffices; no factor balance is needed.** The gap
condition (C1) superficially suggests chains of nearly-balanced semiprimes
with gaps below $\sqrt x$ — a statement far beyond current short-interval
technology. Theorem A shows the chain may instead be run at *any* fixed
power scale $x^\theta$, with certificates that are merely
"$10\!\cdot\!$window-rough". Smaller $\theta$ weakens both the interval
length and the roughness demanded, at no cost in the conclusion. The
certificates carry **no coprimality conditions against any other quantity**
— unlike every multi-row (ladder) scheme, see §7 — because the L-path's
visibility needs are absorbed entirely by the self-referential inequality
(C1).

**(b) Robustness to exceptional runs.** The proof consumes one certificate
per window of length $\approx 2x^\theta$. Hence B($\theta$) may fail on any
set of $x$'s that contains no run of consecutive integers of length
$\ge x^\theta$ (adjust the multiplier $10 \to 12$ and spacing $2 \to 3$):
what is really needed is only that the *exceptional set of* B($\theta$) *has
no gaps-structure clustering at scale* $x^\theta$. In particular a proof of
B($\theta$) "for all $x$ outside a set with bounded run lengths" already
closes the problem.

**(c) The scale cannot be pushed to polylogarithmic.** For fixed $K$, the
statement "every window $(x - K\log x,\, x]$ contains a composite with
$P^- > 10 K \log x$" is **false** for infinitely many $x$: by the
Westzynthius–Erdős–Rankin construction, gaps between consecutive $z$-rough
integers of size $z \cdot \omega(z)$ with $\omega(z) \to \infty$ occur at
heights $e^{O(z)}$, and at height $x = e^{O(z)}$ the demanded roughness
$10K\log x$ is comparable to $z$ while the window $K \log x$ is shorter than
the desert. So *power scale is forced* for worst-case chain supply: the
almost-all polylog-interval results of Matomäki–Radziwiłł/Teräväinen type can
never be upgraded to the all-$x$ statement at that scale. This delimits
where the remaining difficulty genuinely lives: worst-case supply at power
scale. There, no obstruction is known: the only known desert constructions
for $z$-rough integers live at heights exponential in $z$, and for
$z = 10x^\theta$ that is $e^{cx^\theta} \gg x$ — they say nothing about
heights polynomial in the roughness level. Whether deserts at power-coupled
scales exist is exactly the open content of B($\theta$).

## 6. A concrete mechanism: floor-quotient semiprimes (new)

B($\theta$) asks for rough composites in short windows. There is a canonical
supply: semiprimes of the form $p \lfloor x/p \rfloor$.

**Proposition B.** Let $0 < \theta < 1/2$ and let $x$ be large. Suppose
there is a prime $p \in (10x^\theta, 20 x^\theta]$ such that

1. $m = \lfloor x/p \rfloor$ is prime, and
2. $\{x/p\} < 1/20$ (fractional part).

Then $a = pm$ is a composite integer in $(x - x^\theta, x]$ with
$P^-(a) = p > 10x^\theta$; i.e. B($\theta$) holds at $x$ with certificate
$a$.

*Proof.* $a = p\lfloor x/p\rfloor \le x$ always, and
$x - a = p\{x/p\} < 20x^\theta \cdot \tfrac1{20} = x^\theta$, so
$a \in (x - x^\theta, x]$. Also $m \ge x/p - 1 \ge x^{1-\theta}/20 - 1 > p$
for large $x$ (as $1 - \theta > \theta$), so $a$ is a product of two primes
$p < m$, is composite, and $P^-(a) = p > 10x^\theta$. $\square$

The point of the mechanism: *the small factor $p$ is chosen first and gives
total control of the roughness*; the only arithmetic demand left is that the
quotient $\lfloor x/p \rfloor$ be prime for a single $p$ in a dyadic range of
$\asymp x^\theta/\log x$ primes, with a positive-proportion fractional-part
condition. Heuristically the number of certifying $p$ is
$\asymp x^{\theta}/\log^2 x \to \infty$; the numerics of §8 confirm a median
of $5$ certifying primes per $x$ already at $x \sim 10^8$–$10^9$ with
$\theta = 1/3$ (and a thin $0.45\%$ exceptional set at these small heights,
which the wider $p$-ranges and non-semiprime certificates cover).

This places the problem next to an active literature: distribution of primes
in the floor-quotient sequences $(\lfloor x/n \rfloor)_{n \le x}$ has seen
sustained recent progress (asymptotics for $\#\{n \le x : \lfloor x/n\rfloor
\text{ prime}\}$ and relatives — Bordellès–Dai–Heyman–Pan–Shparlinski–Wu and
subsequent work). What Theorem A + Proposition B need beyond that literature
is a *localized, all-$x$* statement: for every large $x$, at least one prime
$p$ in a prescribed dyadic block has $\lfloor x/p \rfloor$ prime with small
fractional part. Two natural intermediate targets:

* **(almost all $x$)** A second-moment computation over $x \in [X, 2X]$ of
  $N(x) = \#\{p \in (10x^\theta, 20x^\theta] : \lfloor x/p\rfloor \text{ prime},\ \{x/p\} < 1/20\}$.
  The mean is classical (PNT in the $m$-variable, summed over $p$); the
  second moment reduces to counting prime pairs $(m_1, m_2)$ with
  $p_1 m_1 \approx p_2 m_2$, for which *upper bounds* of the right order come
  from standard sieve upper bounds — plausibly enough for
  $N(x) > 0$ outside an exceptional set of density $o(1)$. We flag this as
  the realistic next analytic step; by Remark (b) of §5, the gap between
  "almost all" and "no long exceptional runs" is then the entire remaining
  difficulty of the problem along this route.
* **(all $x$, small $\theta$)** Nothing like an all-$x$ statement is known
  for double-prime conditions of this shape; but note that B($\theta$) does
  not require the semiprime mechanism — any rough composite certifies, and
  §8 shows the general supply is far more abundant than the semiprime count
  alone.

## 7. Why ladder (multi-row) schemes stall: the Jacobsthal mismatch (new analysis)

The computational picture (both the prior $[2,3000]^2$ component search and
§8) shows real paths hugging *pairs of nearby composite rows*, switching
rows to dodge divisibility obstructions. The natural formalization:

**Lemma 3 (twin-composite switch; prior observation, made precise).** Let
$y \ge 3$ be odd with $y$ and $y+2$ both composite, and let $x \ge 2$ satisfy
$\gcd(x,\, y(y+1)(y+2)) = 1$. Then the vertical switch
$(x,y) \to (x, y+1) \to (x, y+2)$ passes through admissible points only —
**even when $x$ is prime** (the middle point has $y + 1$ even and $\ge 4$,
hence composite).

*Proof.* Visibility at all three points is the coprimality hypothesis;
compositeness holds at heights $y$, $y+2$ by assumption and at $y+1$ since
$y+1 \ge 4$ is even. $\square$

**Lemma 4 (ladder lifetime).** Any path of visible points confined to a
finite row set $R$ has horizontal extent $< \tau(R) \le \prod_{y \in R} P^-(y)$
(Lemma 2′). For a "clean" ladder — rows pairwise coprime, each with
$P^-(y) \ge z$ — the lifetime bound is $\ge z^{|R|}$, i.e. exponential in the
number of rows; the barrier that ends it is the first column sharing a prime
factor with every row.

So a $k$-row ladder of $z$-rough composite rows survives horizontally for up
to $\sim z^k$ steps but must eventually climb. Making a ladder scheme run
forever requires, again and again, three kinds of *worst-case* supply:

| ingredient | needs | guaranteed today |
|---|---|---|
| next rows: $z$-rough composites near current height | one per window of height $O(z \log z)$ (density heuristic) | only per window $O(z^{2+\varepsilon})$ (linear sieve / Iwaniec-type) |
| switch/climb columns: $x$ coprime to *all* integers in the vertical span $V$ crossed | gaps $\lesssim$ row-block spacing $z$ | Jacobsthal-type bounds give $\ll (r \log r)^2$ with $r \approx \pi(V) + V\log X/\log V$ — **quadratic**, and carrying a $\log X$ from large prime factors of the window product |
| a clear row between consecutive switch columns | some row of the ladder unblocked across each switch gap | fails once switch gaps exceed $z$: each row has $\approx \log X/\log z$ primes, any of which may drop one block into the gap |

The three rows of the table interlock into a hierarchy: switch columns must
be *denser* than row blocks, but switch columns are constrained by
coprimality to an entire vertical window, which by the best known
worst-case sieve-gap bounds (Iwaniec: the Jacobsthal function of an integer
with $r$ prime factors is $\ll (r\log r)^2$) makes them *sparser* — by
exactly one power. Every variant we tried (twin rows, $k$-row stacks,
pairwise-coprime rough rows, compositeness anchors $Q \mid y$) reproduces the
same quadratic-versus-linear mismatch one level up. A *uniform linear
Jacobsthal hypothesis* (worst-case gaps of one-residue-per-prime sieves
within a polylog factor of the density prediction, uniformly with sparse
extra classes) would mesh the hierarchy; that hypothesis is believed but far
out of reach — and, notably, it is *stronger* in flavor than B($\theta$),
which needs no interval-coprimality at all. Conclusion of the analysis: the
ladder picture explains what paths *do* at accessible heights, but as a
proof strategy it is currently dominated by the chain route of §5. Its one
structural advantage — only *one of $k$ rows* needs to survive locally,
suggesting averaging/potential-function arguments rather than worst-case
supply — is recorded here as the most promising direction *if* B($\theta$)
resists.

## 8. Computational evidence

Scripts in `erdos/scripts/` (NumPy; exact integer sieves; conservative
rounding where floats appear). Outputs in `erdos/data/`.

**(i) Explicit verified path at height $10^9$**
(`build_explicit_path.py`). In the window $[10^9,\, 10^9 + 5\cdot 10^6)$
there are $144{,}488$ composite anchors with $P^-(a) \ge 1500$; consecutive
anchor gaps have mean $34.6$ and maximum $374$ — a factor $4$ below the
roughness floor even at the maximum. The greedy (C1) chain therefore absorbs
**every** anchor without a single dead end, and the resulting L-path — with
$144{,}486$ stages, $288{,}972$ turns and $9{,}999{,}882$ unit edges from
$(1000000013,\, 1000000051)$ to $(1004999953,\, 1004999993)$ — was verified
**pointwise** (every lattice point checked for $\gcd = 1$ and a composite
coordinate): zero violations. For comparison, the prior computational
evidence was a $3{,}358$-edge component path in $[2, 3000]^2$. At realistic
heights the chain mechanism is nowhere near tight; the problem's difficulty
is invisible below astronomically large scales, consistent with §5(c) (the
first genuine deserts require Rankin-type heights).

**(ii) Bridge hypothesis stress test to $10^8$**
(`verify_bridge_hypothesis.py`, `failure_run_lengths.py`). For
$\theta \in \{1/3,\, 0.30,\, 1/4,\, 1/5\}$, every integer window
$(x - x^\theta, x]$ up to $10^8$ was checked for a composite certificate with
$P^- > 10x^\theta$ (segmented least-prime-factor sieve). Below the
feasibility threshold $10^{2/(1-2\theta)}$ every $x$ fails, exactly as the
constraint $P^-(a) \le \sqrt a$ dictates ($10^6$ for $\theta = 1/3$, $10^5$
for $0.30$, $10^4$ for $1/4$); above it the failure fraction decays: for
$\theta = 1/3$ from $100\%$ below $10^6$ to $6.2\%$ on $[10^7, 10^8]$ and
$1.46\%$ on $[9\cdot 10^7, 10^8]$. Two honest observations. First, failures
are $\approx 4\times$ more frequent than a mean-field Poisson model of
certificate counts predicts ($1.46\%$ observed on the top segment against
$e^{-5.6} \approx 0.37\%$ from the mean certificate count $5.6$ per window)
— certificate-free stretches cluster (a single rough-composite desert of
length $\ell$ fails $\approx \ell$ consecutive windows), a small-scale echo
of the worst-case-versus-average theme of §5(c).
Second, and directly relevant to the run-robust form of the hypothesis
(§5(b)): on $[9\cdot 10^7, 10^8]$ the **longest failing run** is
$781 \approx 1.70\, x^\theta$ for $\theta = 1/3$ (25 runs exceed $x^\theta$), and
$1.89\, x^\theta$ for $\theta = 0.30$ — the run-robust hypothesis holds at
these heights with a modest constant, while the raw all-$x$ form of
B($\theta$, $10$) does not yet. For $\theta = 1/5$ windows are still so
short ($\approx 40$) that $18\%$ of $x$ fail there; the asymptotic regime
(mean certificates $\asymp x^\theta/\log x$) sets in very slowly for small
$\theta$. Data: `data/bridge_results.json`, `data/failure_runs.json`.

**(iii) Floor-quotient mechanism** (`floor_mechanism_stats.py`). For
$\theta = 1/3$ and $4000$ random $x \in [10^8, 10^9]$: the number of primes
$p \in (10x^{1/3}, 20x^{1/3}]$ with $\lfloor x/p \rfloor$ prime and
$p\{x/p\} < x^{1/3}$ has median $5$, mean $5.49$, max $15$; $18$ of $4000$
samples ($0.45\%$) had none (the general certificates of (ii) cover these).
The narrow mechanism alone already certifies $99.5\%$ of windows at these
heights.

## 9. What would close the problem

1. **Prove B($\theta$) for one $\theta \in (0, 1/2)$** — or its run-robust
   weakening (§5(b)). Realistic ladder of sub-targets: mean value of
   certificates (classical) → second moment / almost-all $x$ (§6, plausibly
   current technology) → quantitative exceptional-set clustering (open core).
2. **Fixed-origin finite paths.** Theorem C gives $m$-stage paths in every
   dyadic window; if one could additionally *connect* a fixed admissible
   vertex to some vertex of each such path (a reachability, not existence,
   question), König's lemma finishes. Nothing in §3 forbids this: the escape
   lemma forces any such connector to climb at rate $\ge \log D/\log\log D$,
   which monotone L-paths do easily.
3. **Averaged ladder arguments** (§7): replace worst-case switch-column
   supply by a potential-function argument exploiting that only one of $k$
   rows must survive locally.
4. **Negative direction.** Any proof of impossibility must, by Theorem C,
   destroy connectivity *between* dyadic scales while every scale is locally
   saturated with long monotone paths — and, by Corollary 2″, must do so
   using barrier structures spanning unboundedly many rows and columns
   simultaneously. We know of no candidate mechanism.

## 10. Formalization plan (Lean 4 / Mathlib)

The Lean toolchain could not be downloaded in this working session (network
policy), so nothing below is formalized yet; the plan is recorded for the
repository's formalization lane.

* `Nat.minFac` is Mathlib's $P^-$; `Nat.Coprime` handles visibility;
  admissibility is a three-clause structure on `ℕ × ℕ`.
* **Easy targets** (elementary, no analytic input): Lemma 1; Lemma 2′ and
  Corollary 2″ (finite products over transversals; the pigeonhole is
  `Finset`-level); Lemma 3; Proposition 1 (define the L-path as an explicit
  `ℕ → ℕ × ℕ` from the stage decomposition; the two visibility contradictions
  are the divisor-gap argument `p ∣ a → p ∣ s → a < s → a + p ≤ s`).
* **Theorem A** formalizes cleanly *as a conditional*: take B($\theta$) as a
  hypothesis (a `∀ x ≥ x₀, ∃ a, ...` statement) and produce the infinite
  path; everything is elementary induction plus the $2^\theta \le \sqrt 2$
  numerics (`Real.rpow` lemmas).
* **Theorem C** is the interesting case: its only analytic inputs are (S1)
  and (S2). (S2) at Chebyshev strength is within Mathlib's reach
  (`Nat.primeCounting`, Bertrand-postulate infrastructure). For (S1), a
  formalization-friendly substitute avoids sieve theory entirely: fix the
  roughness bound $B$ *constant*, count $B$-rough integers in $(X, 2X]$
  *exactly* by periodicity modulo $\prod_{p\le B} p$ (an exact
  `Finset` computation, error $O(P/X)$), and rerun the block-pigeonhole of
  §4 with $z = B(m)$ chosen by an explicit elementary Mertens-type lower
  bound on $\prod_{p \le B}(1 - 1/p)$. This yields a fully elementary,
  Mathlib-compatible proof skeleton of Theorem C at the cost of a worse (but
  still explicit) height threshold.
* Suggested module layout: `Erdos/Admissible.lean` (definitions, Lemma 1),
  `Erdos/Blocking.lean` (Lemma 2′, Corollary 2″), `Erdos/LPath.lean`
  (Proposition 1), `Erdos/ChainFromBridges.lean` (Theorem A),
  `Erdos/RoughRuns.lean` (Theorem C, elementary variant).

## References (indicative)

* H. Iwaniec, on Jacobsthal's problem: worst-case gaps in one-residue-per-
  prime sieves are $\ll (r \log r)^2$ for $r$ prime moduli.
* R. A. Rankin (after Westzynthius, Erdős), long gaps between consecutive
  primes / $z$-rough numbers near primorial heights.
* Halberstam–Richert, *Sieve Methods*; Tenenbaum, *Introduction to Analytic
  and Probabilistic Number Theory* (Buchstab, fundamental lemma — input (S1)).
* K. Matomäki, M. Radziwiłł; J. Teräväinen — multiplicative functions and
  $E_k$ numbers in (almost all) short intervals: the reason almost-all
  statements at polylog scale are known while all-$x$ statements are not,
  and (§5(c)) provably cannot hold at polylog scale here.
* O. Bordellès et al., and subsequent work on primes in floor-quotient
  sequences $\lfloor x/n \rfloor$ (§6 mechanism).
* The Erdős problems database (erdosproblems.com) for the problem statement
  and status; the problem remains listed as open as of July 2026.
