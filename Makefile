sweep:
	python3 compiler/compile.py --sweep compiler/specs/

# Build the library.
build:
	lake build FormalSLT

# Type-check every example and tutorial (the same loop CI runs).
examples:
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

# Regenerate the concept-keyed searchable theorem index (docs/INDEX.html, docs/INDEX.md).
index:
	python3 scripts/generate_proof_frontier_manifest.py
	python3 scripts/generate_theorem_index.py

.PHONY: sweep build examples tutorials index
