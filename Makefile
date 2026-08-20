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

# Check the stale-artifact gate, exact arithmetic tests, and generated Lean module.
verify-controlled-queue-model: check-controlled-queue-model
	python3 -m pytest -q tests/test_generate_controlled_queue_model.py
	lake build FormalSLT.Applications.ControlledQueueData
	lake build FormalSLT.Applications.ControlledQueueReindex
	lake env lean examples/CheckControlledQueueReindex.lean

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

.PHONY: sweep build examples tutorials verify-random-refresh-load index api downstream python-tests \
	generate-controlled-queue-model check-controlled-queue-model verify-controlled-queue-model \
	generate-controlled-queue-trace check-controlled-queue-trace verify-controlled-queue-trace
