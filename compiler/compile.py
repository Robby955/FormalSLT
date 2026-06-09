#!/usr/bin/env python3
"""Verified PAC-Bayes certificate compiler.

The compiler turns a small finite-hypothesis PAC-Bayes JSON specification into
a Lean certificate module and a matching axiom-check example. It can also run a
directory sweep through ``compiler/sweep_runner.py``.

The emitted Lean theorem instantiates
``FormalSLT.PACBayesBoundedLoss.finiteMcAllesterBoundedComplexity_badEventMass_le_delta``
with concrete finite data, finite prior, bounded loss, confidence, and a
numeric complexity budget. The CSV records the posterior KL supplied or implied
by the spec and the corresponding square-root bound.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
GENERATED_DIR = REPO_ROOT / "FormalSLT" / "PACBayes" / "Generated"
EXAMPLES_DIR = REPO_ROOT / "examples"
COMPLEXITY_DENOMINATOR = 10**12


def to_fraction(value) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, float):
        return Fraction(str(value))
    text = str(value).strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num.strip()), int(den.strip()))
    return Fraction(text)


def frac_to_lean(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return f"({value.numerator} : ℝ)"
    return f"(({value.numerator} : ℝ) / {value.denominator})"


def frac_to_decimal(value: Fraction, digits: int = 12) -> str:
    return f"{float(value):.{digits}g}"


def sanitize_spec_id(spec_id: str) -> str:
    cleaned = re.sub(r"[^0-9A-Za-z_]", "_", spec_id)
    if not cleaned or not (cleaned[0].isalpha() or cleaned[0] == "_"):
        cleaned = f"Cert_{cleaned}"
    return cleaned


def normalize_weights(weights: list[Fraction], *, full_support: bool, label: str) -> list[Fraction]:
    if not weights:
        raise ValueError(f"{label}: expected at least one weight")
    if any(w < 0 for w in weights):
        raise ValueError(f"{label}: weights must be nonnegative")
    total = sum(weights, Fraction(0))
    if total == 0:
        raise ValueError(f"{label}: weights must not sum to zero")
    normalized = [w / total for w in weights]
    if full_support and any(w <= 0 for w in normalized):
        raise ValueError(f"{label}: full support requires all weights positive")
    return normalized


def uniform_distribution(size: int) -> list[Fraction]:
    return [Fraction(1, size) for _ in range(size)]


def geometric_distribution(size: int) -> list[Fraction]:
    weights = [Fraction(2 ** (size - 1 - i), 1) for i in range(size)]
    return normalize_weights(weights, full_support=True, label="geometric prior")


def delta_distribution(size: int, index: int) -> list[Fraction]:
    if not (0 <= index < size):
        raise ValueError(f"delta posterior index {index} outside 0..{size - 1}")
    return [Fraction(1 if i == index else 0, 1) for i in range(size)]


def softmax_like_distribution(size: int) -> list[Fraction]:
    # A deterministic rational softmax-shaped profile. The certified KL is
    # supplied by the spec because exact logarithmic KL is not a rational input.
    weights = [Fraction(size - i, 1) for i in range(size)]
    return normalize_weights(weights, full_support=True, label="softmax posterior")


def distribution_from_spec(raw, size: int, *, label: str, full_support: bool) -> list[Fraction]:
    if isinstance(raw, list):
        if len(raw) != size:
            raise ValueError(f"{label}: expected {size} weights, got {len(raw)}")
        return normalize_weights([to_fraction(x) for x in raw],
                                 full_support=full_support, label=label)
    if not isinstance(raw, dict):
        raise ValueError(f"{label}: expected distribution object or weight list")
    kind = raw.get("kind")
    if kind == "uniform":
        return uniform_distribution(size)
    if kind == "geometric":
        return geometric_distribution(size)
    if kind == "delta":
        return delta_distribution(size, int(raw.get("index", 0)))
    if kind == "softmax":
        return softmax_like_distribution(size)
    raise ValueError(f"{label}: unsupported distribution kind {kind!r}")


def kl_divergence(posterior: list[Fraction], prior: list[Fraction]) -> float:
    total = 0.0
    for rho, pi in zip(posterior, prior, strict=True):
        if rho == 0:
            continue
        if pi <= 0:
            raise ValueError("KL undefined for non-full-support prior")
        total += float(rho) * math.log(float(rho / pi))
    return total


def ceil_fraction(value: float, denominator: int = COMPLEXITY_DENOMINATOR) -> Fraction:
    return Fraction(math.ceil(value * denominator), denominator)


@dataclass(frozen=True)
class NormalizedSpec:
    spec_id: str
    H: int
    Zsize: int
    n: int
    B: Fraction
    delta: Fraction
    prior: list[Fraction]
    posterior: list[Fraction]
    kl: float
    complexity_bound: Fraction
    computed_bound: float
    prior_label: str
    posterior_label: str

    @property
    def module(self) -> str:
        return f"FormalSLT.PACBayes.Generated.{self.spec_id}"

    @property
    def theorem_name(self) -> str:
        lower = self.spec_id[:1].lower() + self.spec_id[1:]
        return f"{lower}_generalization_certificate"

    @property
    def theorem_fqn(self) -> str:
        return f"{self.module}.{self.theorem_name}"

    @property
    def lean_path(self) -> Path:
        return GENERATED_DIR / f"{self.spec_id}.lean"

    @property
    def check_path(self) -> Path:
        return EXAMPLES_DIR / f"Check_{self.spec_id}.lean"


def normalize_spec(spec: dict) -> NormalizedSpec:
    spec_id = sanitize_spec_id(str(spec["spec_id"]))
    H = int(spec.get("H", spec.get("hypothesis_count")))
    Zsize = int(spec.get("Zsize", spec.get("data_domain_size", 2)))
    n = int(spec.get("n", spec.get("sample_size")))
    B = to_fraction(spec.get("B", spec.get("loss_bound", "1")))
    delta = to_fraction(spec["delta"])
    if H < 1:
        raise ValueError("H must be positive")
    if Zsize != 2:
        raise ValueError("compiler v2 generated losses are currently fixed to Zsize=2")
    if n < 1:
        raise ValueError("sample size n must be positive")
    if B != 1:
        raise ValueError("compiler v2 is scoped to B=1 bounded losses")
    if not (0 < delta < 1):
        raise ValueError("delta must be in (0,1)")

    prior_raw = spec.get("prior", {"kind": "uniform"})
    posterior_raw = spec.get("posterior", {"kind": "uniform"})
    prior = distribution_from_spec(prior_raw, H, label="prior", full_support=True)
    posterior = distribution_from_spec(posterior_raw, H, label="posterior", full_support=False)
    prior_label = prior_raw.get("kind", "explicit") if isinstance(prior_raw, dict) else "explicit"
    posterior_label = posterior_raw.get("kind", "explicit") if isinstance(posterior_raw, dict) else "explicit"

    if "KL" in spec or "kl" in spec:
        kl_supplied = float(to_fraction(spec["KL"] if "KL" in spec else spec["kl"]))
        kl_actual = kl_divergence(posterior, prior)
        if kl_supplied < kl_actual - 1e-9:
            raise ValueError(
                f"KL upper-bound violated: supplied {kl_supplied!r} < "
                f"kl_divergence(posterior, prior) = {kl_actual!r}. "
                "The supplied KL must be an upper bound on the true posterior/prior KL."
            )
        kl = kl_supplied
    else:
        kl = kl_divergence(posterior, prior)
    if kl < -1e-12:
        raise ValueError("KL must be nonnegative")
    kl = max(0.0, kl)

    complexity_float = kl + math.log(1.0 / float(delta))
    complexity_bound = ceil_fraction(complexity_float)
    computed_bound = float(B) * math.sqrt(float(complexity_bound) / (2.0 * n))

    return NormalizedSpec(
        spec_id=spec_id,
        H=H,
        Zsize=Zsize,
        n=n,
        B=B,
        delta=delta,
        prior=prior,
        posterior=posterior,
        kl=kl,
        complexity_bound=complexity_bound,
        computed_bound=computed_bound,
        prior_label=prior_label,
        posterior_label=posterior_label,
    )


def if_chain(var: str, values: list[Fraction]) -> str:
    rendered = [frac_to_lean(v) for v in values]
    if len(rendered) == 1:
        return rendered[0]
    pieces = [f"if {var} = {i} then {rendered[i]} else " for i in range(len(rendered) - 1)]
    return "".join(pieces) + rendered[-1]


PMF_SUM_TACTIC = (
    "simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue, "
    "Fin.succ_zero_eq_one]\n    norm_num [Fin.ext_iff]"
)


def emit_lean(spec: NormalizedSpec) -> str:
    lower = spec.spec_id[:1].lower() + spec.spec_id[1:]
    if spec.prior_label == "uniform":
        prior_var = "_"
        prior_body = f"((1 : ℝ) / {spec.H})"
        prior_sum_proof = "simp [prior]"
        prior_nonneg_proof = "intro _; norm_num [prior]"
        prior_pos_proof = "intro _; norm_num [prior]"
    else:
        prior_var = "i"
        prior_body = if_chain("i", spec.prior)
        prior_sum_proof = f"simp only [prior]\n    {PMF_SUM_TACTIC}"
        prior_nonneg_proof = "intro i; fin_cases i <;> norm_num [prior, Fin.ext_iff]"
        prior_pos_proof = "intro i; fin_cases i <;> norm_num [prior, Fin.ext_iff]"
    data_body = "if z = 0 then ((1 : ℝ) / 2) else ((1 : ℝ) / 2)"
    complexity = frac_to_lean(spec.complexity_bound)

    return f'''/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import FormalSLT.PACBayesBoundedLoss

/-!
# PAC-Bayes generalization certificate - compiler output `{spec.spec_id}`

This file was generated by `compiler/compile.py` from
`compiler/specs/{spec.spec_id}.json`. It is a machine-checkable finite
PAC-Bayes bounded-loss certificate.

## Instance statistics
* hypothesis class: `Fin {spec.H}`
* data domain: `Fin 2`
* sample size: `n = {spec.n}`
* bounded loss width: `B = {frac_to_decimal(spec.B)}`
* prior: {spec.prior_label}
* posterior summary: {spec.posterior_label}
* posterior KL recorded by the sweep: `{spec.kl:.12g}`
* confidence delta: `{frac_to_decimal(spec.delta)}`
* complexity budget used in Lean: `{frac_to_decimal(spec.complexity_bound)}`
* computed McAllester bound: `{spec.computed_bound:.12g}`

The certificate instantiates
`FormalSLT.PACBayesBoundedLoss.finiteMcAllesterBoundedComplexity_badEventMass_le_delta`.
It proves that the finite product-sample mass of samples admitting a posterior
inside the stated complexity budget but violating the corresponding
square-root PAC-Bayes bound is at most `delta`.
-/

namespace FormalSLT.PACBayes.Generated.{spec.spec_id}

open FormalSLT.PACBayesKL FormalSLT.PACBayesBoundedLoss
open FormalSLT.PACBayesFiniteProductMGF
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Data law on the two-point data domain. -/
def dataLaw : Fin 2 → ℝ := fun z => {data_body}

/-- Full-support prior over the finite hypothesis class. -/
def prior : Fin {spec.H} → ℝ := fun {prior_var} => {prior_body}

/-- Bounded zero-one loss pattern used for the generated classification spec. -/
def loss : Fin {spec.H} → Fin 2 → ℝ := fun _ z =>
  if z = 0 then (0 : ℝ) else (1 : ℝ)

/-- Sample size. -/
def sampleSize : ℕ := {spec.n}

/-- Confidence parameter. -/
def delta : ℝ := {frac_to_lean(spec.delta)}

/-- Concrete positive complexity budget for the generated McAllester shell. -/
def complexityBound : ℝ := {complexity}

/-- Numeric square-root term appearing in the emitted certificate. -/
def computedBound : ℝ :=
  Real.sqrt (complexityBound / (2 * (sampleSize : ℝ)))

/-- `dataLaw` is a probability mass function. -/
theorem dataLaw_isPMF : IsPMF dataLaw := by
  refine ⟨?_, ?_⟩
  · intro z; fin_cases z <;> norm_num [dataLaw, Fin.ext_iff]
  · show (∑ z : Fin 2, dataLaw z) = 1
    simp only [dataLaw]
    {PMF_SUM_TACTIC}

/-- `prior` is a full-support probability mass function. -/
theorem prior_isFullSupportPMF : IsFullSupportPMF prior := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · {prior_nonneg_proof}
  · show (∑ i : Fin {spec.H}, prior i) = 1
    {prior_sum_proof}
  · {prior_pos_proof}

/-- Every generated loss entry lies in `[0, 1]`. -/
theorem loss_mem_unitInterval :
    ∀ i : Fin {spec.H}, ∀ z : Fin 2, 0 ≤ loss i z ∧ loss i z ≤ 1 := by
  intro i z
  fin_cases z <;> norm_num [loss, Fin.ext_iff]

/-- Machine-checked PAC-Bayes certificate for `{spec.spec_id}`. -/
theorem {lower}_generalization_certificate :
    (∑ S ∈ (Finset.univ.filter fun S : Fin sampleSize → Fin 2 =>
        ∃ ρ : Fin {spec.H} → ℝ,
          IsPMF ρ ∧
            klDiv ρ prior + Real.log (1 / delta) ≤ complexityBound ∧
            posteriorPopulationRisk dataLaw loss ρ >
              posteriorEmpiricalRisk loss ρ S + computedBound),
        finiteProductSampleWeight dataLaw S) ≤ delta := by
  unfold computedBound
  exact
    finiteMcAllesterBoundedComplexity_badEventMass_le_delta
      (n := sampleSize)
      (by norm_num [sampleSize])
      dataLaw dataLaw_isPMF
      prior prior_isFullSupportPMF
      loss
      (hcomplexityBound := by norm_num [complexityBound])
      (hdelta := by norm_num [delta])
      loss_mem_unitInterval

end

end FormalSLT.PACBayes.Generated.{spec.spec_id}
'''


def emit_check_example(spec: NormalizedSpec) -> str:
    return f'''import {spec.module}

/-!
# Axiom audit for generated PAC-Bayes certificate `{spec.spec_id}`
-/

#print axioms {spec.theorem_fqn}
'''


def write_certificate(spec: NormalizedSpec) -> tuple[Path, Path]:
    GENERATED_DIR.mkdir(parents=True, exist_ok=True)
    EXAMPLES_DIR.mkdir(parents=True, exist_ok=True)
    spec.lean_path.write_text(emit_lean(spec))
    spec.check_path.write_text(emit_check_example(spec))
    return spec.lean_path, spec.check_path


def load_spec(path: Path) -> NormalizedSpec:
    with path.open() as handle:
        return normalize_spec(json.load(handle))


def run_lake_build(module: str, timeout: int = 900) -> tuple[bool, str]:
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    proc = subprocess.run(
        ["lake", "build", module],
        cwd=REPO_ROOT,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    return proc.returncode == 0, proc.stdout + proc.stderr


def run_axiom_check(check_path: Path, timeout: int = 300) -> tuple[bool, str]:
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    proc = subprocess.run(
        ["lake", "env", "lean", str(check_path)],
        cwd=REPO_ROOT,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    out = proc.stdout + proc.stderr
    return proc.returncode == 0 and axiom_output_clean(out), out


def axiom_output_clean(output: str) -> bool:
    if "error:" in output.lower() or "sorry" in output.lower() or "admit" in output.lower():
        return False
    match = re.search(r"depends on axioms:\s*\[(.*?)\]", output, re.S)
    if not match:
        return False
    found = {part.strip() for part in match.group(1).replace("\n", " ").split(",") if part.strip()}
    return found == {"propext", "Classical.choice", "Quot.sound"}


def compile_one(spec_path: Path, *, build: bool = False) -> int:
    spec = load_spec(spec_path)
    lean_path, check_path = write_certificate(spec)
    print(f"[compiler] wrote {lean_path.relative_to(REPO_ROOT)}")
    print(f"[compiler] wrote {check_path.relative_to(REPO_ROOT)}")
    print(f"[compiler] module {spec.module}")
    print(f"[compiler] theorem {spec.theorem_fqn}")
    print(f"[compiler] KL={spec.kl:.12g}")
    print(f"[compiler] computed_bound={spec.computed_bound:.12g}")
    if not build:
        return 0
    ok, build_out = run_lake_build(spec.module)
    print(build_out)
    if not ok:
        return 1
    clean, axiom_out = run_axiom_check(check_path)
    print(axiom_out)
    return 0 if clean else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Compile verified PAC-Bayes certificates")
    parser.add_argument("--spec", type=Path, help="single JSON spec to compile")
    parser.add_argument("--sweep", type=Path, help="directory of JSON specs to compile and verify")
    parser.add_argument("--build", action="store_true", help="build and axiom-check a single spec")
    args = parser.parse_args()

    if args.sweep:
        from sweep_runner import run_sweep
        csv_path = run_sweep(args.sweep)
        print(csv_path)
        return 0
    if not args.spec:
        parser.error("provide --spec or --sweep")
    return compile_one(args.spec, build=args.build)


if __name__ == "__main__":
    raise SystemExit(main())
