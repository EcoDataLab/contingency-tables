PYTHON ?= $(if $(wildcard .venv/bin/python),.venv/bin/python,python3)
REPORT_DIR ?= .local/reports
LEAN_MODE ?= --serial
# Run directly from the checkout, including subprocesses that change directory.
export PYTHONPATH := $(CURDIR)/src

.PHONY: test audit verify sources sources-bundle crosscheck replay-mixtures \
	sparse-example linear-example lean lean-baseline lean-plan test-full test-core \
	reports reports-local reports-publish claims claims-check
test: test-full

test-full:
	"$(PYTHON)" scripts/run_python_tests.py

test-core:
	"$(PYTHON)" scripts/run_python_tests.py --core

audit:
	mkdir -p "$(REPORT_DIR)"
	"$(PYTHON)" 115/audit115.py --output "$(REPORT_DIR)/audit115-rerun.json"

claims:
	"$(PYTHON)" scripts/claims_ledger.py --write-readme

claims-check:
	"$(PYTHON)" scripts/claims_ledger.py --check-readme

verify: test audit claims-check sources-bundle crosscheck replay-mixtures

sources-bundle:
	"$(PYTHON)" scripts/verify_sources.py --bundle-only

crosscheck:
	"$(PYTHON)" experiments/independent_crosscheck.py --output "$(REPORT_DIR)/independent-crosscheck.json"

replay-mixtures:
	"$(PYTHON)" -S experiments/cycle_mixtures.py --replay reports/cycle-mixtures.json

sparse-example:
	"$(PYTHON)" examples/sparse_commute.py --output "$(REPORT_DIR)/sparse-commute.json"

linear-example:
	"$(PYTHON)" examples/linear_metric_bounds.py --output "$(REPORT_DIR)/linear-bounds.json"

sources:
	"$(PYTHON)" scripts/verify_sources.py

lean:
	bash scripts/verify_main.sh "$(LEAN_MODE)"

lean-baseline:
	bash scripts/verify_lean.sh focused "$(LEAN_MODE)"

lean-plan:
	"$(PYTHON)" research/repair-accept/verify.py --scope integration-sampler --plan

# Ordinary report reruns write local copies; publication generation is explicit.
reports: reports-local

reports-local:
	"$(PYTHON)" experiments/scale_report.py --output "$(REPORT_DIR)/scale-certificates.json"
	"$(PYTHON)" experiments/budget_report.py --output "$(REPORT_DIR)/budget-comparison.json"
	"$(PYTHON)" examples/sparse_commute.py --spectral --output "$(REPORT_DIR)/sparse-commute.json"
	"$(PYTHON)" examples/linear_metric_bounds.py --output "$(REPORT_DIR)/linear-bounds.json"
	"$(PYTHON)" experiments/padding_barrier.py --output "$(REPORT_DIR)/padding-barrier.json"
	"$(PYTHON)" experiments/worker_baseline.py --output "$(REPORT_DIR)/worker-baseline.json"
	"$(PYTHON)" experiments/commute_scaling.py --output "$(REPORT_DIR)/commute-scaling.json"
	"$(PYTHON)" experiments/cycle_mixtures.py --output "$(REPORT_DIR)/cycle-mixtures.json"

reports-publish:
	$(MAKE) reports-local REPORT_DIR=reports
