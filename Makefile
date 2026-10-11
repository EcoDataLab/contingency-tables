PYTHON ?= python3
REPORT_DIR ?= .local/reports
# Run directly from the checkout, including subprocesses that change directory.
export PYTHONPATH := $(CURDIR)/src

.PHONY: test audit verify sources sources-bundle crosscheck replay-mixtures \
	sparse-example linear-example lean reports reports-local reports-publish claims claims-check
test:
	$(PYTHON) -m unittest discover -s tests -v

audit:
	mkdir -p "$(REPORT_DIR)"
	$(PYTHON) 115/audit115.py --output "$(REPORT_DIR)/audit115-rerun.json"

claims:
	$(PYTHON) scripts/claims_ledger.py --write-readme

claims-check:
	$(PYTHON) scripts/claims_ledger.py --check-readme

verify: test audit claims-check sources-bundle crosscheck replay-mixtures

sources-bundle:
	$(PYTHON) scripts/verify_sources.py --bundle-only

crosscheck:
	$(PYTHON) experiments/independent_crosscheck.py --output "$(REPORT_DIR)/independent-crosscheck.json"

replay-mixtures:
	$(PYTHON) -S experiments/cycle_mixtures.py --replay reports/cycle-mixtures.json

sparse-example:
	$(PYTHON) examples/sparse_commute.py --output "$(REPORT_DIR)/sparse-commute.json"

linear-example:
	$(PYTHON) examples/linear_metric_bounds.py --output "$(REPORT_DIR)/linear-bounds.json"

sources:
	$(PYTHON) scripts/verify_sources.py

lean:
	bash scripts/verify_lean.sh focused

# Ordinary report reruns write local copies; publication generation is explicit.
reports: reports-local

reports-local:
	$(PYTHON) experiments/scale_report.py --output "$(REPORT_DIR)/scale-certificates.json"
	$(PYTHON) experiments/budget_report.py --output "$(REPORT_DIR)/budget-comparison.json"
	$(PYTHON) examples/sparse_commute.py --spectral --output "$(REPORT_DIR)/sparse-commute.json"
	$(PYTHON) examples/linear_metric_bounds.py --output "$(REPORT_DIR)/linear-bounds.json"
	$(PYTHON) experiments/padding_barrier.py --output "$(REPORT_DIR)/padding-barrier.json"
	$(PYTHON) experiments/worker_baseline.py --output "$(REPORT_DIR)/worker-baseline.json"
	$(PYTHON) experiments/commute_scaling.py --output "$(REPORT_DIR)/commute-scaling.json"
	$(PYTHON) experiments/cycle_mixtures.py --output "$(REPORT_DIR)/cycle-mixtures.json"

reports-publish:
	$(MAKE) reports-local REPORT_DIR=reports
