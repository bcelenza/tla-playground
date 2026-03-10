# TLA+ Model Checking Makefile
#
# Usage:
#   make check MODEL=ThreePhaseCommitMajority   # Check a specific model
#   make check-all                              # Check all models
#   make list                                   # List available models
#
# Requirements:
#   - Java runtime
#   - tla2tools.jar at ~/lib/tla2tools.jar (or set TLA2TOOLS)

TLA2TOOLS ?= $(HOME)/lib/tla2tools.jar
JAVA_OPTS ?= -XX:+UseParallelGC -Xmx4g

# All .tla files that have a matching .cfg file
MODELS := $(basename $(wildcard *.cfg))

# Default target
.PHONY: help
help:
	@echo "TLA+ Model Checking"
	@echo ""
	@echo "Usage:"
	@echo "  make check MODEL=<name>   Check a specific model"
	@echo "  make check-all            Check all models"
	@echo "  make list                 List available models"
	@echo "  make clean                Remove generated files"
	@echo ""
	@echo "Available models:"
	@for m in $(MODELS); do echo "  - $$m"; done

# List available models
.PHONY: list
list:
	@echo "Available models:"
	@for m in $(MODELS); do echo "  $$m"; done

# Check a specific model (MODEL must be set)
.PHONY: check
check:
ifndef MODEL
	$(error MODEL is not set. Usage: make check MODEL=ThreePhaseCommitMajority)
endif
	@echo "=== Checking $(MODEL) ==="
	java $(JAVA_OPTS) -jar $(TLA2TOOLS) -config $(MODEL).cfg $(MODEL).tla

# Check all models
.PHONY: check-all
check-all: $(addprefix check-,$(MODELS))

.PHONY: check-%
check-%:
	@echo ""
	@echo "=== Checking $* ==="
	@java $(JAVA_OPTS) -jar $(TLA2TOOLS) -config $*.cfg $*.tla && \
		echo "✓ $* passed" || echo "✗ $* failed"

# Clean generated files
.PHONY: clean
clean:
	rm -rf states/
	rm -f *.out
	rm -f *_trace_*.tlc
