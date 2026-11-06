# Python 3.10 fixture compatibility repair

[Hosted run 42305845614](https://github.com/EcoDataLab/contingency-tables/actions/runs/42305845614), at commit `d34ccab05d547b8da4a41d203a4f05f6c85d3b99`, reached the full Python suite. Its [Python 3.10 job](https://github.com/EcoDataLab/contingency-tables/actions/runs/42305845614/job/128194814110) ran 468 tests: 457 passed, seven failed, one errored and three were explicitly skipped. The other Python lanes were canceled by matrix fail-fast; they are not recorded as passes.

All eight failures came from the frozen Comparator fixture modules calling `hashlib.file_digest`, which [was introduced in Python 3.11](https://docs.python.org/3.11/library/hashlib.html#hashlib.file_digest). The Python 3.10.22 environment had NumPy 2.2.6 and SciPy 1.15.3. All eight real SciPy worker-library tests and both SciPy preflight tests passed. Its three skips concerned the absent pinned formal bootstrap and optional Rscript, rather than SciPy.

The repair changes the [normal-suite test bridge](../../tests/test_comparator_observer.py). When the native API is absent, it temporarily binds a delegating hash adapter into five private module instances loaded by the offline fixtures. The adapter reads the fixtures' freshly opened blocking binary streams in 1 MiB chunks and computes real digests using `hashlib.new` and `update`. It delegates other hash attributes unchanged. Module bindings are restored after the suite, including when debug execution raises. The bridge never modifies the global `hashlib` module. Python 3.11+ retains the native API.

The frozen checker, installer, guest and supervisor files remain byte-for-byte unchanged. All 11 frozen Python sources and all 25 files pinned by the public observer packet were checked. This repair changes no active VM assets, guest Python 3.12 runtime, source pins, admission rules, watchdogs or acceptance checks. The adapter is scoped to ordinary blocking binary fixture files; it does not claim full compatibility with every file-like object supported by the native API.

| Local check, using Python 3.14.3 | Tests run | Passed | Failures | Errors | Skips |
|---|---:|---:|---:|---:|---:|
| Historical bridge, native API deliberately absent | 36 | 28 | 7 | 1 | 0 |
| Repaired bridge, native API deliberately absent | 36 | 36 | 0 | 0 | 0 |
| Repaired normal discovery: 36 fixtures plus four compatibility regressions | 40 | 40 | 0 | 0 | 0 |

The forced-absence baseline reproduces the same eight failing cases as the hosted job. The [four new regressions](../../tests/test_comparator_hash_compat.py) check known SHA-256 vectors, multi-chunk files against the native API, short reads, callable constructors, sensitivity to changed bytes, binding restoration, and all 36 fixtures with the API absent. The temporary removal of the native API occurs only inside regression-test patch scopes and is restored afterward.

Run the affected tests with:

```sh
.venv/bin/python scripts/run_python_tests.py -p 'test_comparator*.py'
```

The workflow now sets `fail-fast: false` so each independent Python lane can finish. Both workflow YAML files parsed successfully, and all 15 shell blocks passed `bash -n`. The local checks did not rerun the full suite. No local Python 3.10 executable was available on PATH; the repaired hosted Python 3.10 run remains pending.

[verification.json](verification.json) binds the changed bridge, new tests, workflow, metadata annotation and unchanged frozen source files. It also records commands, exact results, syntax checks, hashes and four compressed logs. The hosted log is an explicitly selected excerpt containing environment/scientific/skip lines and the complete failure section; local logs retain the affected test executions. Machine-specific roots were replaced by placeholders.

The public observer manifest's old bridge hash now has an explicit historical commit/status annotation. Its old SHA and every frozen-file binding remain intact. The [earlier Python reliability receipts](../python-reliability-2026-11-06/README.md) and their 125-entry source manifest are unchanged: their completed local 468-test runs predate this adapter. This addendum makes no new hosted-pass, full-suite, formal-build or live Comparator acceptance claim.

Follow-up: the repair above was published at commit `d52b7fea705f292aef4fe6f6fd0fb3e740a9065f`. Its [Python 3.10 hosted rerun](https://github.com/EcoDataLab/contingency-tables/actions/runs/42307905742/job/128201819562) passed all 36 normal frozen fixtures, all SciPy worker tests and the three Make path regressions, but the two new absence-simulation tests errored during cleanup: Python 3.10's mock cleanup tried to delete an already absent attribute. A narrow test-only follow-up replaces that cleanup with a sentinel-based context manager and checks originally absent, present-with-`None` and present-callable states on normal and exceptional exits. All 41 affected tests now pass both normally and with the API absent before the suite starts, with zero skips and exact API restoration. The adapter and frozen sources are unchanged. The original verification file and hashes remain historical; a successful hosted Python 3.10 run of this follow-up is still pending.
