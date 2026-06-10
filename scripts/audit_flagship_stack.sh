#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

LAKE="${LAKE:-$HOME/.elan/bin/lake}"

echo "== cache =="
"$LAKE" exe cache get

echo "== focused builds =="
"$LAKE" build FormalSLT.TestTimeMeta.Flagship
"$LAKE" build FormalSLT.PACBayes.GaussianKL
"$LAKE" build FormalSLT.OnlineToPAC.IIDConcentration
"$LAKE" build FormalSLT.Concentration.SubGamma.BennettBound
"$LAKE" build FormalSLT.Concentration.SubGamma.BoundedExpIntegrable
"$LAKE" build FormalSLT.Concentration.SubGamma.CondExpProduct
"$LAKE" build FormalSLT.Concentration.SubGamma.CondJensen
"$LAKE" build FormalSLT.Concentration.SubGamma.CondMarkov
"$LAKE" build FormalSLT.Concentration.SubGamma.CondVarianceFromSquare
"$LAKE" build FormalSLT.Concentration.SubGamma.Extractor
"$LAKE" build FormalSLT.TestTimeMeta.FlagshipComposition

echo "== public axiom audits =="
"$LAKE" env lean examples/CheckFlagship.lean
"$LAKE" env lean examples/CheckGaussianKL.lean
"$LAKE" env lean examples/CheckOnlineToPACIID.lean
"$LAKE" env lean examples/CheckSubGammaExtractor.lean
"$LAKE" env lean examples/CheckFlagshipComposition.lean

echo "== repository hygiene =="
python3 scripts/generate_proof_frontier_manifest.py --check
rg -n --pcre2 '^\s*(?:by\s+)?(?:sorry|admit)\b|:=\s*(?:by\s+)?(?:sorry|admit)\b' FormalSLT examples && exit 1 || true
rg -n --pcre2 '^\s*(?:axiom|constant)\s+[A-Za-z_]' FormalSLT examples && exit 1 || true
git diff --check

echo "flagship stack audit passed"
