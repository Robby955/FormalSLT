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
	lake env lean examples/CheckControlledQueueReindex.lean
	lake env lean examples/CheckControlledQueueTypedModel.lean
	lake env lean examples/CheckControlledQueueTargetPolicyScores.lean
	lake env lean examples/CheckControlledQueueContraction.lean
	lake env lean examples/CheckControlledQueuePersistenceConfidence.lean
	lake env lean examples/CheckControlledQueueOPECatalog.lean
	lake env lean examples/CheckControlledQueueStructuredOPE.lean
	lake env lean examples/CheckControlledQueueInvariantRisk.lean

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

.PHONY: sweep build examples tutorials verify-random-refresh-load index api downstream python-tests \
	generate-controlled-queue-model check-controlled-queue-model verify-controlled-queue-model \
	generate-controlled-queue-trace check-controlled-queue-trace verify-controlled-queue-trace \
	generate-controlled-queue-known-kernel-receipt \
	check-controlled-queue-known-kernel-receipt \
	verify-controlled-queue-known-kernel-receipt
