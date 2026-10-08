PYTHON ?= python3
export PYTHONPATH := src

.PHONY: test audit verify sources lean reports
test:
	$(PYTHON) -m unittest discover -s tests -v

audit:
	mkdir -p .local
	$(PYTHON) 115/audit115.py --output .local/audit115-rerun.json

verify: test audit
	$(PYTHON) scripts/verify_sources.py --bundle-only
	$(PYTHON) experiments/independent_crosscheck.py

sources:
	$(PYTHON) scripts/verify_sources.py

lean:
	bash scripts/verify_lean.sh focused

reports:
	$(PYTHON) experiments/scale_report.py --output reports/scale-certificates.json
	$(PYTHON) experiments/budget_report.py --output reports/budget-comparison.json
	$(PYTHON) examples/sparse_commute.py --spectral --output reports/sparse-commute.json
	$(PYTHON) examples/linear_metric_bounds.py --output reports/linear-bounds.json
