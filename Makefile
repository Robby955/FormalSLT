sweep:
	python3 compiler/compile.py --sweep compiler/specs/

# Build the library.
build:
	lake build FormalSLT

# Type-check every example and tutorial (the same loop CI runs).
examples:
	lake build FormalSLT.Applications
	@for f in $$(find examples -name '*.lean' | sort); do \
		echo "$$f"; \
		lake env lean "$$f" || exit 1; \
	done

# Type-check just the getting-started tutorials.
tutorials:
	@for f in $$(find examples/tutorials -name '*.lean' | sort); do \
		echo "$$f"; \
		lake env lean "$$f" || exit 1; \
	done

# Build and type-check the complete twenty-state application slice.
verify-random-refresh-load:
	lake build FormalSLT.Applications
	@for f in \
		examples/CheckRandomRefreshLoadModel.lean \
		examples/CheckRandomRefreshLoadCertificate.lean \
		examples/CheckRandomRefreshLoadPath.lean \
		examples/CheckRandomRefreshLoadReceipt.lean \
		examples/CheckRandomRefreshLoadAdaptiveSelection.lean \
		examples/CheckRandomRefreshLoadBaselines.lean \
		examples/CheckRandomRefreshLoadOracleCertificate.lean \
		examples/CheckRandomRefreshLoadApplication.lean; do \
		echo "$$f"; \
		lake env lean "$$f" || exit 1; \
	done

# Regenerate the concept-keyed searchable theorem index (docs/INDEX.html, docs/INDEX.md).
index:
	python3 scripts/generate_proof_frontier_manifest.py
	python3 scripts/generate_theorem_index.py

# Check the candidate v0.2 signatures and exact v0.1 example compatibility.
api:
	bash scripts/check_public_api_snapshot.sh
	lake env lean examples/CheckShowcaseTheorems.lean
	lake env lean examples/CheckV01Usability.lean
	bash scripts/check_v01_tag_examples.sh

# Build a separate Lake package that consumes the four public topic imports.
downstream:
	cd tests/downstream && lake exe cache get && lake build Downstream

# Run the Python self-tests for repository audit tooling.
python-tests:
	python3 -m pytest -q tests

# Regenerate exact rational tables for the controlled-queue preprocessing slice.
generate-controlled-queue-model:
	python3 scripts/generate_controlled_queue_model.py

# Fail immediately when generated data or its SHA-256 manifest is stale.
check-controlled-queue-model:
	python3 scripts/generate_controlled_queue_model.py --check

# Check generated-model freshness and arithmetic, then build and audit the
# controlled-queue model, score, contraction, confidence, OPE, and risk chain.
verify-controlled-queue-model: check-controlled-queue-model
	python3 -m pytest -q tests/test_generate_controlled_queue_model.py
	lake build FormalSLT.Applications.ControlledQueueData
	lake build FormalSLT.Applications.ControlledQueueReindex
	lake build FormalSLT.Applications.ControlledQueueTypedModel
	lake build FormalSLT.Applications.ControlledQueueTargetPolicyScores
	lake build FormalSLT.Applications.ControlledQueueContraction
	lake build FormalSLT.Applications.ControlledQueuePersistenceConfidence
	lake build FormalSLT.Applications.ControlledQueueOPECatalog
	lake build FormalSLT.Applications.ControlledQueueStructuredOPE
	lake build FormalSLT.Applications.ControlledQueueInvariantRisk
	lake build FormalSLT.Applications.ControlledQueueRefreshSensitivity
	lake build FormalSLT.Applications.ControlledQueueSharpStructuredOPE
	lake build FormalSLT.Applications.ControlledQueueSharpStructuredReceiptCore
	lake env lean examples/CheckControlledQueueReindex.lean
	lake env lean examples/CheckControlledQueueTypedModel.lean
	lake env lean examples/CheckControlledQueueTargetPolicyScores.lean
	lake env lean examples/CheckControlledQueueContraction.lean
	lake env lean examples/CheckControlledQueuePersistenceConfidence.lean
	lake env lean examples/CheckControlledQueueOPECatalog.lean
	lake env lean examples/CheckControlledQueueStructuredOPE.lean
	lake env lean examples/CheckControlledQueueInvariantRisk.lean
	lake env lean examples/CheckControlledQueueSharpStructuredOPE.lean
	lake env lean examples/CheckControlledQueueSharpStructuredReceiptCore.lean

# Regenerate the deterministic trace, counts, and trace SHA-256 manifest.
generate-controlled-queue-trace:
	python3 scripts/generate_controlled_queue_trace.py

# Check fresh generation, then independently replay every draw and causal update.
check-controlled-queue-trace:
	python3 scripts/generate_controlled_queue_trace.py --check
	python3 scripts/verify_controlled_queue_trace.py --check

# Run the byte/replay gate and its focused tamper and determinism tests.
verify-controlled-queue-trace: check-controlled-queue-trace
	python3 -m pytest -q tests/test_generate_controlled_queue_trace.py

# Regenerate the aligned known-kernel OPE receipt and generated Lean data.
generate-controlled-queue-known-kernel-receipt:
	python3 scripts/generate_controlled_queue_known_kernel_receipt.py

# Check exact bytes, provenance, independent arithmetic, and generated Lean.
check-controlled-queue-known-kernel-receipt:
	python3 scripts/generate_controlled_queue_known_kernel_receipt.py --check
	python3 scripts/verify_controlled_queue_known_kernel_receipt.py --check

# Run adversarial preprocessing tests and the checked Lean endpoint.
verify-controlled-queue-known-kernel-receipt: check-controlled-queue-known-kernel-receipt
	python3 -m pytest -q tests/test_generate_controlled_queue_known_kernel_receipt.py
	lake build FormalSLT.Applications.ControlledQueueKnownKernelReceipt
	lake env lean examples/CheckControlledQueueKnownKernelReceipt.lean

# Validate the prospective structured-OPE preregistration and fail if any
# declared fresh trace, receipt, manifest, or generated Lean output exists.
check-controlled-queue-structured-ope-protocol:
	python3 scripts/check_controlled_queue_structured_ope_protocol.py

# Run the fail-closed schema/binding/chronology mutation suite. This target
# never fetches a beacon or generates a trace.
verify-controlled-queue-structured-ope-protocol: check-controlled-queue-structured-ope-protocol
	python3 -m pytest -q tests/test_check_controlled_queue_structured_ope_protocol.py

# Verify the complete pre-beacon code freeze without fetching evidence or
# creating any prospective output. The two Lean streams exercise both future
# generated-data branches using local, already-observed arithmetic fixtures.
verify-controlled-queue-structured-ope-code-freeze: verify-controlled-queue-structured-ope-protocol
	python3 -m py_compile \
		scripts/generate_controlled_queue_prospective_trace.py \
		scripts/verify_controlled_queue_prospective_trace.py \
		scripts/generate_controlled_queue_prospective_receipt.py \
		scripts/verify_controlled_queue_prospective_receipt.py
	python3 -m pytest -q \
		tests/test_generate_controlled_queue_prospective_trace.py \
		tests/test_verify_controlled_queue_prospective_trace.py \
		tests/test_generate_controlled_queue_prospective_receipt.py \
		tests/test_verify_controlled_queue_prospective_receipt.py
	env LEAN_NUM_THREADS=2 lake build \
		FormalSLT.Applications.ControlledQueueSharpStructuredReceiptCore
	env LEAN_NUM_THREADS=2 lake env lean \
		examples/CheckControlledQueueSharpStructuredReceiptCore.lean
	python3 -c 'import runpy,sys; from fractions import Fraction; d=runpy.run_path("tests/test_generate_controlled_queue_prospective_receipt.py"); g=d["generator"]; r=d["_minimal_render_receipt"](); assert Fraction(r["reporting_rows"][0]["total_certified_rhs"]["rational"]) >= g.PRIMARY_THRESHOLD; sys.stdout.buffer.write(g.render_lean(r))' | \
		env LEAN_NUM_THREADS=2 lake env lean -DmaxErrors=20 /dev/stdin
	python3 -c 'import json,runpy,sys; from fractions import Fraction; from pathlib import Path; d=runpy.run_path("tests/test_generate_controlled_queue_prospective_receipt.py"); g=d["generator"]; h=json.loads(Path("applications/controlled_queue/generated/trace-v1-counts.json").read_text())["counts"]["edge_counts"]; r=d["_minimal_render_receipt"](histogram=h); assert Fraction(r["reporting_rows"][0]["total_certified_rhs"]["rational"]) < g.PRIMARY_THRESHOLD; sys.stdout.buffer.write(g.render_lean(r))' | \
		env LEAN_NUM_THREADS=2 lake env lean -DmaxErrors=20 /dev/stdin
	python3 scripts/check_controlled_queue_structured_ope_protocol.py

# Verify the authorized post-beacon artifacts in their required order. This
# target is expected to fail before the immutable registration, evidence, and
# single prospective generation exist; it never generates or overwrites them.
verify-controlled-queue-structured-ope-prospective-receipt:
	python3 scripts/generate_controlled_queue_prospective_trace.py --check
	python3 scripts/verify_controlled_queue_prospective_trace.py
	python3 scripts/generate_controlled_queue_prospective_receipt.py --check
	python3 scripts/verify_controlled_queue_prospective_receipt.py
	env LEAN_NUM_THREADS=2 lake env lean \
		FormalSLT/Applications/ControlledQueueProspectiveStructuredOPEData.lean

.PHONY: sweep build examples tutorials verify-random-refresh-load index api downstream python-tests \
	generate-controlled-queue-model check-controlled-queue-model verify-controlled-queue-model \
	generate-controlled-queue-trace check-controlled-queue-trace verify-controlled-queue-trace \
	generate-controlled-queue-known-kernel-receipt \
	check-controlled-queue-known-kernel-receipt \
	verify-controlled-queue-known-kernel-receipt \
	check-controlled-queue-structured-ope-protocol \
	verify-controlled-queue-structured-ope-protocol \
	verify-controlled-queue-structured-ope-code-freeze \
	verify-controlled-queue-structured-ope-prospective-receipt
