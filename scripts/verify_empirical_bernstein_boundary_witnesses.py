#!/usr/bin/env python3
"""Fraction mirror for the declared Lean forward-Bessel witness domain.

The mirror deliberately uses only :class:`fractions.Fraction`.  In
particular, it does not evaluate ``log`` with floating-point arithmetic.  The
logarithmic cumulant is enclosed by the same finite atanh series and
exact-rational remainder upper bound used by the Lean proofs.

The declared witness domain is the sequence of structured markers in
``examples/CheckEmpiricalBernsteinBoundaryWitnessBattery.lean``.  Each marker
must occur exactly once in the doc comment immediately preceding its named
theorem.  The parser checks the theorem's top-level relation and its direct or
embedded rational pin.  It also binds the whitespace-normalized full
proposition to a pinned SHA-256 fingerprint, so changes to an unpinned side of
the theorem cannot pass as the same witness.  Those bindings are then compared
with the independently recomputed Python values.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
LEAN_WITNESS_FILE = (
    ROOT / "examples" / "CheckEmpiricalBernsteinBoundaryWitnessBattery.lean"
)
MARKER_PREFIX = "BOUNDARY_WITNESS|"
MARKER_PATTERN = re.compile(
    r"^BOUNDARY_WITNESS\|"
    r"id=(?P<witness_id>[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*)\|"
    r"theorem=(?P<theorem>[A-Za-z_][A-Za-z0-9_]*)\|"
    r"relation=(?P<relation>eq|le|lt)\|"
    r"pin=(?P<pin_kind>left|right|derived|right_factor):"
    r"(?P<pin>-?\d+(?:/\d+)?)$"
)
THEOREM_PATTERN = re.compile(r"theorem\s+([A-Za-z_][A-Za-z0-9_]*)\b")
PROOF_START_PATTERN = re.compile(r"\s*:=\s*by\b")
LEAN_RATIONAL_PATTERN = re.compile(
    r"^\s*(?:\(\s*(?P<cast>-?\d+)\s*:\s*ℝ\s*\)|(?P<plain>-?\d+))"
    r"(?:\s*/\s*(?P<denominator>\d+))?\s*$"
)

F = Fraction


@dataclass(frozen=True)
class RationalEnclosure:
    """Closed rational enclosure of a real-valued expression."""

    lower: Fraction
    upper: Fraction

    def __post_init__(self) -> None:
        if self.upper < self.lower:
            raise ValueError("enclosure upper endpoint is below its lower endpoint")


@dataclass(frozen=True)
class LeanWitnessBinding:
    """One structured marker after checking its adjacent Lean theorem."""

    witness_id: str
    theorem: str
    relation: str
    pin_kind: str
    pin: Fraction
    proposition_sha256: str = ""


def _proposition_sha256(statement: str) -> str:
    """Fingerprint a theorem proposition after whitespace normalization."""

    normalized = " ".join(statement.split())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def _fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else str(value)


def _parse_fraction(text: str, where: str) -> Fraction:
    try:
        value = F(text)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(f"{where}: invalid rational {text!r}") from error
    return value


def _top_level_colon(header: str, start: int, where: str) -> int:
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    for index in range(start, len(header)):
        char = header[index]
        if char in depths:
            depths[char] += 1
        elif char in closing:
            opener = closing[char]
            depths[opener] -= 1
            if depths[opener] < 0:
                raise ValueError(f"{where}: unbalanced theorem header")
        elif char == ":" and all(depth == 0 for depth in depths.values()):
            return index
    raise ValueError(f"{where}: theorem has no top-level statement colon")


def _split_top_level_relation(statement: str, where: str) -> tuple[str, str, str]:
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    relations: list[tuple[int, str]] = []
    for index, char in enumerate(statement):
        if char in depths:
            depths[char] += 1
        elif char in closing:
            opener = closing[char]
            depths[opener] -= 1
            if depths[opener] < 0:
                raise ValueError(f"{where}: unbalanced theorem statement")
        elif all(depth == 0 for depth in depths.values()) and char in "=≤<":
            relations.append((index, char))
    if any(depth != 0 for depth in depths.values()):
        raise ValueError(f"{where}: unbalanced theorem statement")
    if len(relations) != 1:
        raise ValueError(
            f"{where}: expected one top-level relation, found {len(relations)}"
        )
    index, symbol = relations[0]
    relation = {"=": "eq", "≤": "le", "<": "lt"}[symbol]
    return statement[:index].strip(), relation, statement[index + 1 :].strip()


def _parse_direct_lean_rational(expression: str, where: str) -> Fraction:
    match = LEAN_RATIONAL_PATTERN.fullmatch(expression)
    if match is None:
        compact = " ".join(expression.split())
        raise ValueError(f"{where}: expected a direct rational, found {compact!r}")
    numerator = match.group("cast") or match.group("plain")
    denominator = match.group("denominator") or "1"
    return F(int(numerator), int(denominator))


def _parse_right_factor(expression: str, where: str) -> Fraction:
    matches = re.findall(r"\bdelta\s*/\s*(\d+)\b", expression)
    if len(matches) != 1:
        raise ValueError(
            f"{where}: expected exactly one embedded right-side delta / n factor"
        )
    return F(1, int(matches[0]))


def _parse_adjacent_theorem(
    source: str, comment_end: int, marker: re.Match[str]
) -> LeanWitnessBinding:
    where = f"marker {marker.group('witness_id')}"
    suffix = source[comment_end:]
    theorem_match = re.match(
        r"\s*(theorem\s+([A-Za-z_][A-Za-z0-9_]*)\b)", suffix
    )
    if theorem_match is None:
        raise ValueError(f"{where}: marker must immediately precede a theorem")
    actual_theorem = theorem_match.group(2)
    declared_theorem = marker.group("theorem")
    if actual_theorem != declared_theorem:
        raise ValueError(
            f"{where}: marker names theorem {declared_theorem}, "
            f"but immediately precedes {actual_theorem}"
        )

    theorem_start = comment_end + theorem_match.start(1)
    proof_match = PROOF_START_PATTERN.search(source, theorem_start)
    if proof_match is None:
        raise ValueError(f"{where}: adjacent theorem has no ':= by' proof delimiter")
    header = source[theorem_start : proof_match.start()]
    name_match = THEOREM_PATTERN.match(header)
    if name_match is None:
        raise ValueError(f"{where}: could not parse adjacent theorem header")
    colon = _top_level_colon(header, name_match.end(), where)
    proposition = header[colon + 1 :]
    left, actual_relation, right = _split_top_level_relation(proposition, where)
    declared_relation = marker.group("relation")
    if actual_relation != declared_relation:
        raise ValueError(
            f"{where}: marker relation {declared_relation}, "
            f"but theorem relation is {actual_relation}"
        )

    pin_kind = marker.group("pin_kind")
    declared_pin = _parse_fraction(marker.group("pin"), where)
    if pin_kind == "left":
        actual_pin = _parse_direct_lean_rational(left, where)
    elif pin_kind == "right":
        actual_pin = _parse_direct_lean_rational(right, where)
    elif pin_kind == "right_factor":
        actual_pin = _parse_right_factor(right, where)
    else:
        # A derived pin records an independently recomputed separation margin.
        # Only the stated relation is read from Lean; no direct rational side is
        # attributed to that theorem.
        actual_pin = declared_pin
    if actual_pin != declared_pin:
        raise ValueError(
            f"{where}: marker pins {_fraction_text(declared_pin)}, "
            f"but theorem statement has {_fraction_text(actual_pin)}"
        )
    return LeanWitnessBinding(
        marker.group("witness_id"),
        declared_theorem,
        declared_relation,
        pin_kind,
        declared_pin,
        _proposition_sha256(proposition),
    )


def parse_lean_witnesses(source: str) -> tuple[LeanWitnessBinding, ...]:
    """Parse ordered, theorem-bound witness markers from Lean source."""

    marker_offsets = [
        match.start() for match in re.finditer(re.escape(MARKER_PREFIX), source)
    ]
    bindings: list[LeanWitnessBinding] = []
    seen_ids: set[str] = set()
    consumed_comments: set[tuple[int, int]] = set()
    for offset in marker_offsets:
        line_end = source.find("\n", offset)
        if line_end < 0:
            line_end = len(source)
        marker_line = source[offset:line_end].strip()
        marker = MARKER_PATTERN.fullmatch(marker_line)
        if marker is None:
            raise ValueError(f"malformed structured marker: {marker_line!r}")

        comment_start = source.rfind("/--", 0, offset)
        previous_close = source.rfind("-/", 0, offset)
        if comment_start < 0 or comment_start < previous_close:
            raise ValueError(
                f"marker {marker.group('witness_id')}: marker must be in a theorem "
                "doc comment and must immediately precede a theorem"
            )
        comment_end = source.find("-/", line_end)
        if comment_end < 0:
            raise ValueError(f"marker {marker.group('witness_id')}: unclosed doc comment")
        comment_span = (comment_start, comment_end)
        comment = source[comment_start:comment_end]
        if comment.count(MARKER_PREFIX) != 1:
            raise ValueError(
                f"marker {marker.group('witness_id')}: theorem doc comment must "
                "contain exactly one structured marker"
            )
        if comment_span in consumed_comments:
            raise ValueError(
                f"marker {marker.group('witness_id')}: theorem doc comment must "
                "contain exactly one structured marker"
            )
        consumed_comments.add(comment_span)

        binding = _parse_adjacent_theorem(source, comment_end + 2, marker)
        if binding.witness_id in seen_ids:
            raise ValueError(f"duplicate witness id {binding.witness_id}")
        seen_ids.add(binding.witness_id)
        bindings.append(binding)
    return tuple(bindings)


def _require_prefix(values: Sequence[Fraction], n: int) -> None:
    if n <= 0:
        raise ValueError("the witness mirror only evaluates positive prefixes")
    if len(values) < n:
        raise ValueError(f"prefix length {n} exceeds sequence length {len(values)}")


def prefix_mean(values: Sequence[Fraction], n: int) -> Fraction:
    """Mirror ``forwardPrefixMean`` on the first ``n`` entries."""

    _require_prefix(values, n)
    return sum(values[:n], F(0)) / n


def bessel_q(values: Sequence[Fraction], n: int) -> Fraction:
    """Mirror the unnormalised centered sum ``forwardBesselQ``."""

    mean = prefix_mean(values, n)
    return sum(((value - mean) ** 2 for value in values[:n]), F(0))


def predictable_quadratic(values: Sequence[Fraction], n: int) -> Fraction:
    """Mirror the seeded, preceding-prefix prediction residual sum."""

    _require_prefix(values, n)
    total = F(0)
    for k, value in enumerate(values[:n]):
        predictor = F(1, 2) if k == 0 else prefix_mean(values, k)
        total += (value - predictor) ** 2
    return total


def harmonic(n: int) -> Fraction:
    if n < 0:
        raise ValueError("harmonic index must be nonnegative")
    return sum((F(1, k) for k in range(1, n + 1)), F(0))


def hybrid_components(
    values: Sequence[Fraction], n: int
) -> tuple[Fraction, Fraction]:
    """Return the affine and harmonic branches of the Lean hybrid penalty."""

    if n < 2:
        raise ValueError("the hybrid witness domain starts at n = 2")
    q = bessel_q(values, n)
    affine = F(1, 2) + F(3, 2) * q
    harmonic_branch = F(n, n - 1) * q + F(1, 4) * (1 + harmonic(n - 2))
    return affine, harmonic_branch


def hybrid_penalty(values: Sequence[Fraction], n: int) -> Fraction:
    return min(hybrid_components(values, n))


def empirical_bernstein_cgf(b: Fraction, lam: Fraction) -> Fraction:
    """Mirror ``empiricalBernsteinCgf`` exactly."""

    denominator = 2 * (1 - b * lam / 3)
    if denominator == 0:
        raise ZeroDivisionError("empirical-Bernstein cgf denominator is zero")
    return lam**2 / denominator


def forward_psi_enclosure(lam: Fraction, terms: int) -> RationalEnclosure:
    """Enclose ``-log(1-lam)-lam`` with the Lean atanh bounds.

    With ``x = lam / (2-lam)``, ``-log(1-lam)`` is
    ``log((1+x)/(1-x))``.  The lower endpoint is twice the first ``terms``
    atanh-series terms.  The upper endpoint uses the same exact-rational
    remainder upper bound as ``Real.log_div_le_sum_range_add``:

    ``2 * x^(2*terms+1) / (1-x^2)``.
    """

    if not F(0) <= lam < F(1):
        raise ValueError("forward psi enclosure requires 0 <= lambda < 1")
    if terms <= 0:
        raise ValueError("atanh enclosure requires at least one term")
    x = lam / (2 - lam)
    partial = sum(
        (x ** (2 * k + 1) / (2 * k + 1) for k in range(terms)), F(0)
    )
    lower = 2 * partial - lam
    upper = 2 * (partial + x ** (2 * terms + 1) / (1 - x**2)) - lam
    return RationalEnclosure(lower, upper)


def forward_psi_quadratic_upper(lam: Fraction) -> Fraction:
    """Rational majorant used by ``forwardEmpiricalBernsteinPsi_le_quadratic``."""

    if not F(0) <= lam < F(1):
        raise ValueError("forward psi quadratic bound requires 0 <= lambda < 1")
    return lam**2 / (2 * (1 - lam))


def closed_boundary(
    variance_sum: Fraction,
    cgf: Fraction,
    log_budget: Fraction,
    n: int,
    lam: Fraction,
) -> Fraction:
    """Mirror ``empiricalBernsteinClosedFormBoundary`` exactly."""

    denominator = F(n) * lam
    if denominator == 0:
        raise ZeroDivisionError("boundary denominator n * lambda is zero")
    return cgf * variance_sum / denominator + log_budget / denominator


SKEW_FOUR = (F(0), F(1, 4), F(1, 2), F(1), F(37, 5))
BALANCED_FOUR = (F(0), F(0), F(1), F(1), F(19, 7))
SPLIT_FIVE = (F(0), F(0), F(0), F(1), F(1), F(23, 9))
BOOLEAN_TWO = (F(0), F(1), F(29, 11))
CONSTANT_THREE = (F(1, 3), F(1, 3), F(1, 3), F(31, 7))


# These are the direct rational pins, embedded factors, and one explicitly
# derived separation margin in the declared Lean witness domain.  The values
# are intentionally separate from the formula implementation above.
EXPECTED_WITNESS_VALUES: dict[str, Fraction] = {
    "PM-01": F(7, 16),
    "Q-01": F(35, 64),
    "PRED-01": F(65, 64),
    "HYB-A": F(169, 128),
    "Q-02": F(1),
    "HYB-H4": F(47, 24),
    "Q-03": F(6, 5),
    "HYB-H5": F(53, 24),
    "Q-N2": F(1, 2),
    "HARM-N2": F(5, 4),
    "HYB-N2": F(5, 4),
    "Q-ZERO": F(0),
    "HYB-ZERO": F(1, 2),
    "CGF-01": F(3, 20),
    "CGF-02": F(3, 80),
    "PSI-LOWER": F(37999, 1008420),
    "PSI-UPPER": F(76003, 2016840),
    # Derived margin; Lean directly states only the strict comparison.
    "PSI-DISTINCT": F(79663, 22185240),
    "BND-VAR": F(21, 512),
    "BND-BUDGET": F(28, 45),
    "BND-JOINT-A": F(1307, 5120),
    "BND-JOINT-H": F(127, 640),
    "BND-FWD": F(25, 144),
    "BND-FWD-LOWER": F(1, 10),
    "BND-TWO-SIDED-SHAPE": F(1, 2),
    "BND-TWO-SIDED": F(629, 720),
    "BND-CATALOG-SHAPE": F(1, 2),
    "BND-CATALOG": F(629, 720),
    "BND-CATALOG-LOWER": F(4, 5),
}


_EXPECTED_LEAN_BINDING_METADATA: tuple[LeanWitnessBinding, ...] = (
    LeanWitnessBinding("PM-01", "skewFour_prefixMean_eq", "eq", "right", F(7, 16)),
    LeanWitnessBinding("Q-01", "skewFour_besselQ_eq", "eq", "right", F(35, 64)),
    LeanWitnessBinding(
        "PRED-01", "skewFour_predictableQuadratic_eq", "eq", "right", F(65, 64)
    ),
    LeanWitnessBinding(
        "HYB-A", "skewFour_hybridPenalty_eq", "eq", "right", F(169, 128)
    ),
    LeanWitnessBinding("Q-02", "balancedFour_besselQ_eq", "eq", "right", F(1)),
    LeanWitnessBinding(
        "HYB-H4", "balancedFour_hybridPenalty_eq", "eq", "right", F(47, 24)
    ),
    LeanWitnessBinding("Q-03", "splitFive_besselQ_eq", "eq", "right", F(6, 5)),
    LeanWitnessBinding(
        "HYB-H5", "splitFive_hybridPenalty_eq", "eq", "right", F(53, 24)
    ),
    LeanWitnessBinding("Q-N2", "booleanTwo_besselQ_eq", "eq", "right", F(1, 2)),
    LeanWitnessBinding(
        "HARM-N2", "booleanTwo_harmonicCandidate_eq", "eq", "right", F(5, 4)
    ),
    LeanWitnessBinding(
        "HYB-N2", "booleanTwo_hybridPenalty_eq", "eq", "right", F(5, 4)
    ),
    LeanWitnessBinding("Q-ZERO", "constantThree_besselQ_eq", "eq", "right", F(0)),
    LeanWitnessBinding(
        "HYB-ZERO", "constantThree_hybridPenalty_eq", "eq", "right", F(1, 2)
    ),
    LeanWitnessBinding("CGF-01", "cgf_one_half_eq", "eq", "right", F(3, 20)),
    LeanWitnessBinding("CGF-02", "cgf_two_quarter_eq", "eq", "right", F(3, 80)),
    LeanWitnessBinding(
        "PSI-LOWER",
        "forwardPsi_quarter_lower",
        "le",
        "left",
        F(37999, 1008420),
    ),
    LeanWitnessBinding(
        "PSI-UPPER",
        "forwardPsi_quarter_upper",
        "le",
        "right",
        F(76003, 2016840),
    ),
    LeanWitnessBinding(
        "PSI-DISTINCT",
        "cgf_one_quarter_lt_forwardPsi",
        "lt",
        "derived",
        F(79663, 22185240),
    ),
    LeanWitnessBinding(
        "BND-VAR", "closedBoundary_varianceOnly_eq", "eq", "right", F(21, 512)
    ),
    LeanWitnessBinding(
        "BND-BUDGET", "closedBoundary_budgetOnly_eq", "eq", "right", F(28, 45)
    ),
    LeanWitnessBinding(
        "BND-JOINT-A",
        "closedBoundary_jointAffine_eq",
        "eq",
        "right",
        F(1307, 5120),
    ),
    LeanWitnessBinding(
        "BND-JOINT-H",
        "closedBoundary_jointHarmonic_eq",
        "eq",
        "right",
        F(127, 640),
    ),
    LeanWitnessBinding(
        "BND-FWD", "forwardBoundary_splitFive_le", "le", "right", F(25, 144)
    ),
    LeanWitnessBinding(
        "BND-FWD-LOWER", "forwardBoundary_splitFive_ge", "le", "left", F(1, 10)
    ),
    LeanWitnessBinding(
        "BND-TWO-SIDED-SHAPE",
        "twoSidedFailure_halfBudget_eq",
        "eq",
        "right_factor",
        F(1, 2),
    ),
    LeanWitnessBinding(
        "BND-TWO-SIDED",
        "twoSidedBoundary_splitFive_le",
        "le",
        "right",
        F(629, 720),
    ),
    LeanWitnessBinding(
        "BND-CATALOG-SHAPE",
        "catalogBoundary_halfWeight_eq",
        "eq",
        "right_factor",
        F(1, 2),
    ),
    LeanWitnessBinding(
        "BND-CATALOG",
        "catalogBoundary_splitFive_le",
        "le",
        "right",
        F(629, 720),
    ),
    LeanWitnessBinding(
        "BND-CATALOG-LOWER",
        "catalogBoundary_splitFive_ge",
        "le",
        "left",
        F(4, 5),
    ),
)


# These fingerprints bind the complete whitespace-normalized propositions in
# the declared witness file.  They are intentionally kept in this independent
# Python manifest rather than repeated as opaque hashes in Lean prose.
EXPECTED_PROPOSITION_SHA256: dict[str, str] = {
    "PM-01": "3798a5721ec09e5ab948a91286a6e893b6a3ab993866d9162d058c17fcaa6ee0",
    "Q-01": "8247ada2c9209d650f4eb586129381ef715eabb0da0a4dc489622e7b613fc4ae",
    "PRED-01": "7e22f2a469dfe45a15acef326b6328db2c14328520140ae8c78d1a2d8a32e327",
    "HYB-A": "1a243c2628093af907dce150b6d0d868c2a83f7d08a7dc6236a4ba79cc598a21",
    "Q-02": "c7e3212d09b249aa386efd2c1b566521635b3610c288fcd999458ef6fc8e3e16",
    "HYB-H4": "9fcfdb8966c98d43181f7ca77b0f443b5273c6631e01069456ffe522e2f19cef",
    "Q-03": "b06ad6c3badc45ddcb12c1827ffa8ea85216c12f7c6766b9db0251cc0ef65346",
    "HYB-H5": "a203ed8a2d8d57b89f68a0a49dbb3cdd9aa70dbab7f0f72b6650798971440753",
    "Q-N2": "8cf3ac06efbd9a2cea73b44a354eaa1c13d342fe23985fc18f8b3e4dbc572b9f",
    "HARM-N2": "8f5dc178be535949614e0b59e0c14193d9b5a1ae48a2fd42701b64ab1121c06a",
    "HYB-N2": "af9d0dfd4d64807873befa55ae263346fc61724bc56965c669a45dc06e83992a",
    "Q-ZERO": "301efc22a29d1cf613dcb8ae9a81b678a078ed125631c8c468abf409a13bcacf",
    "HYB-ZERO": "34b284babdd5366c6450cbfc1aef9599c11646da542d15b71cafc349cf2ff307",
    "CGF-01": "13ad7c72dd04bf1ada733ea77b5282700360a9aa53d54a009f20fd57bd4308df",
    "CGF-02": "dbe585b85bca522e72fd1fb55a7c5a11d603deb68eb15e1a782e1ae057697689",
    "PSI-LOWER": "30a80b1f9851c5a086b33956e4783c2c1245f5c893926ae9ad0a7f85ac447c85",
    "PSI-UPPER": "2dc87a8f35d2680fd2e167f533f2de96099ebab693528443bc3ceeaef4a6ffc7",
    "PSI-DISTINCT": "4c6c03e108399febfd375e05ffaaf2cbc0f0769c8410f4396cc5d1ccf8e2c437",
    "BND-VAR": "8f5c05d5fc5d46cc5c735effaafa1cad6eadf9a314d8354ee3d3d8bdb3d99f2e",
    "BND-BUDGET": "ede921d94e81d3de6e3b08149edb527e082cffc7643ce290ebedad0ab88df954",
    "BND-JOINT-A": "9e57bdab262a35100408c04471abdadab9356a0b751037cd53aecb51c89f963c",
    "BND-JOINT-H": "b16ddc26ea923a694aad86e07388e44918887a812d4077eb85ee10393bed680a",
    "BND-FWD": "1a2cd053e541f17ddc7c9f2b9c0008b3a79a646ed9f77464b80ae2a4de70d5bb",
    "BND-FWD-LOWER": "2d1599f57a0eb04af8b567fc189c90e6f0f48ab2104ac30b8df3739eb73669cc",
    "BND-TWO-SIDED-SHAPE": "fac867bc27b20a3ae813dfaba44d2b54630dc011c50cfdb4fe9e107a887cff4f",
    "BND-TWO-SIDED": "4eaf746d508ef5b4e2d9993e0306895ea2dee14bac18ca456c25c99985e2862b",
    "BND-CATALOG-SHAPE": "aab657d9dd12c3c49b90b1885452c746bf2c53bd14f15e45754ddc88af8a4068",
    "BND-CATALOG": "57fa167a410a9fa17dc95337749a0afa3e26ac7643de5736d5117c56584c42e4",
    "BND-CATALOG-LOWER": "f4584d85ad89d757ba033757597174311c611df29530cad050414f847f5c2c82",
}


EXPECTED_LEAN_BINDINGS: tuple[LeanWitnessBinding, ...] = tuple(
    LeanWitnessBinding(
        binding.witness_id,
        binding.theorem,
        binding.relation,
        binding.pin_kind,
        binding.pin,
        EXPECTED_PROPOSITION_SHA256[binding.witness_id],
    )
    for binding in _EXPECTED_LEAN_BINDING_METADATA
)


def computed_witness_values() -> dict[str, Fraction]:
    """Recompute every ID from the mirrored formulas."""

    skew_q = bessel_q(SKEW_FOUR, 4)
    skew_hybrid = hybrid_penalty(SKEW_FOUR, 4)
    balanced_hybrid = hybrid_penalty(BALANCED_FOUR, 4)
    split_hybrid = hybrid_penalty(SPLIT_FIVE, 5)
    boolean_affine, boolean_harmonic = hybrid_components(BOOLEAN_TWO, 2)
    cgf_half = empirical_bernstein_cgf(F(1), F(1, 2))
    cgf_quarter_b2 = empirical_bernstein_cgf(F(2), F(1, 4))
    psi = forward_psi_enclosure(F(1, 4), terms=3)
    psi_quadratic = forward_psi_quadratic_upper(F(1, 4))

    fixed_boundary_lower = closed_boundary(
        split_hybrid, F(0), F(1, 8), 5, F(1, 4)
    )
    fixed_boundary_upper = closed_boundary(
        split_hybrid, psi_quadratic, F(1, 8), 5, F(1, 4)
    )
    catalog_boundary_lower = closed_boundary(
        split_hybrid, F(0), F(1), 5, F(1, 4)
    )
    catalog_boundary_upper = closed_boundary(
        split_hybrid, psi_quadratic, F(1), 5, F(1, 4)
    )

    return {
        "PM-01": prefix_mean(SKEW_FOUR, 4),
        "Q-01": skew_q,
        "PRED-01": predictable_quadratic(SKEW_FOUR, 4),
        "HYB-A": skew_hybrid,
        "Q-02": bessel_q(BALANCED_FOUR, 4),
        "HYB-H4": balanced_hybrid,
        "Q-03": bessel_q(SPLIT_FIVE, 5),
        "HYB-H5": split_hybrid,
        "Q-N2": bessel_q(BOOLEAN_TWO, 2),
        "HARM-N2": boolean_harmonic,
        "HYB-N2": min(boolean_affine, boolean_harmonic),
        "Q-ZERO": bessel_q(CONSTANT_THREE, 3),
        "HYB-ZERO": hybrid_penalty(CONSTANT_THREE, 3),
        "CGF-01": cgf_half,
        "CGF-02": cgf_quarter_b2,
        "PSI-LOWER": psi.lower,
        "PSI-UPPER": psi.upper,
        "PSI-DISTINCT": psi.lower - empirical_bernstein_cgf(F(1), F(1, 4)),
        "BND-VAR": closed_boundary(skew_q, cgf_half, F(0), 4, F(1, 2)),
        "BND-BUDGET": closed_boundary(F(0), cgf_half, F(7, 9), 5, F(1, 4)),
        "BND-JOINT-A": closed_boundary(
            skew_hybrid, cgf_half, F(5, 16), 4, F(1, 2)
        ),
        "BND-JOINT-H": closed_boundary(
            balanced_hybrid, cgf_quarter_b2, F(1, 8), 4, F(1, 4)
        ),
        "BND-FWD": fixed_boundary_upper,
        "BND-FWD-LOWER": fixed_boundary_lower,
        # With total delta = 2*exp(-1), the two-sided delta/2 endpoint has
        # log-budget 1 and therefore the same rational upper certificate.
        "BND-TWO-SIDED-SHAPE": F(1, 2),
        "BND-TWO-SIDED": catalog_boundary_upper,
        # The selected catalog atom has weight 1/2, hence budget delta / 2.
        "BND-CATALOG-SHAPE": F(1, 2),
        "BND-CATALOG": catalog_boundary_upper,
        "BND-CATALOG-LOWER": catalog_boundary_lower,
    }


def lean_witness_ids(path: Path = LEAN_WITNESS_FILE) -> tuple[str, ...]:
    """Return theorem-bound IDs in source order, preserving multiplicity."""

    return tuple(
        binding.witness_id
        for binding in parse_lean_witnesses(path.read_text(encoding="utf-8"))
    )


def validate() -> list[str]:
    """Return human-readable failures; an empty list means the mirror passed."""

    failures: list[str] = []
    source = LEAN_WITNESS_FILE.read_text(encoding="utf-8")
    try:
        bindings = parse_lean_witnesses(source)
    except ValueError as error:
        return [str(error)]

    if bindings != EXPECTED_LEAN_BINDINGS:
        failures.append("Lean witness marker sequence differs from the declared manifest")
        if len(bindings) != len(EXPECTED_LEAN_BINDINGS):
            failures.append(
                f"Lean marker count {len(bindings)}, "
                f"expected {len(EXPECTED_LEAN_BINDINGS)}"
            )
        for index, (actual, expected) in enumerate(
            zip(bindings, EXPECTED_LEAN_BINDINGS, strict=False), start=1
        ):
            if actual != expected:
                failures.append(
                    f"Lean marker {index}: parsed {actual}, expected {expected}"
                )

    expected_ids = tuple(EXPECTED_WITNESS_VALUES)
    binding_ids = tuple(binding.witness_id for binding in bindings)
    if binding_ids != expected_ids:
        failures.append(
            f"Lean marker ID order {binding_ids}, expected {expected_ids}"
        )

    computed = computed_witness_values()
    computed_ids = tuple(computed)
    if computed_ids != expected_ids:
        failures.append(
            f"computed ID order {computed_ids}, expected {expected_ids}"
        )

    for binding in bindings:
        actual = computed.get(binding.witness_id)
        if actual != binding.pin:
            failures.append(
                f"{binding.witness_id}: computed {actual}, "
                f"Lean-bound pin {binding.pin}"
            )

    affine_skew, harmonic_skew = hybrid_components(SKEW_FOUR, 4)
    if not affine_skew < harmonic_skew:
        failures.append("HYB-A: affine branch is not strictly selected")
    affine_balanced, harmonic_balanced = hybrid_components(BALANCED_FOUR, 4)
    if not harmonic_balanced < affine_balanced:
        failures.append("HYB-H4: harmonic branch is not strictly selected")
    affine_split, harmonic_split = hybrid_components(SPLIT_FIVE, 5)
    if not harmonic_split < affine_split:
        failures.append("HYB-H5: harmonic branch is not strictly selected")
    if computed.get("PSI-DISTINCT", F(0)) <= 0:
        failures.append("PSI-DISTINCT: cumulant separation margin is not positive")

    return failures


def main() -> int:
    failures = validate()
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}")
        return 1
    print(
        "boundary witness mirror passed: "
        f"{len(EXPECTED_WITNESS_VALUES)} declared cases, "
        "exact Fraction arithmetic on the declared witness domain"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
