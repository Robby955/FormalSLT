from __future__ import annotations

from scripts.generate_proof_frontier_manifest import build_manifest


def test_manifest_describes_live_axiom_gate_without_claiming_cached_result() -> None:
    audit = build_manifest()["audit"]

    assert "expected_public_axioms" not in audit
    assert audit["transitive_axiom_policy"] == {
        "allowed": ["propext", "Classical.choice", "Quot.sound"],
        "command": "bash scripts/check_axioms.sh",
        "coverage": "curated public theorem allowlist in scripts/check_axioms.sh",
        "mechanism": "live Lean #print axioms with fail-closed target accounting",
        "result_embedded": False,
        "result_note": (
            "The manifest records policy, not a cached pass result. CI queries every "
            "allowlisted theorem and rejects missing reports or axioms outside the "
            "allowed set."
        ),
    }
