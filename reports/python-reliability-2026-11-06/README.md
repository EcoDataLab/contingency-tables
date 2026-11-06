# Python test environment verification

The complete Python suite passed in both environments below. These are completed local runs of `make test`, with the real NumPy/SciPy backend required by the new launcher. No full test run was repeated to publish this receipt.

| Environment | Python | NumPy | SciPy | Tests run | Passed | Skipped | Failures/errors | Test time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Existing isolated environment | 3.14.3 | 2.5.3 | 1.18.1 | 468 | 468 | 0 | 0 | 94.746 s |
| Fresh isolated source checkout | 3.12.8 | 2.5.4 | 1.18.1 | 468 | 467 | 1 | 0 | 103.989 s |

Both runs executed all eight real SciPy worker-library tests, both SciPy preflight tests, and all 36 observer/supervisor/progress fixtures. Both environments passed `pip check`. The observer tests mock OS, service and compiler calls; their success is fixture coverage, rather than a new live supervisor run.

The fresh run's sole skip was `IntegrationPlanTests.test_public_hybrid_closure_resolves_in_dependency_order_without_execution`: its public source-plan check requires the normal pinned Lean/upstream/package bootstrap. The fresh checkout had no copied `.tools`, `.upstream`, `.local`, `.venv` or `formal/.lake` caches. No scientific test was skipped. This receipt covers Python execution; the formal build is verified separately.

The fresh checkout was a shallow local clone at the base commit recorded in [verification.json](verification.json), with the current public working changes applied before installation. It was not a clean checkout of the base commit alone. [source-manifest.json](source-manifest.json) binds 125 relevant Python, workflow, fixture and setup files to their tested SHA-256 hashes; every listed file also matched the main checkout when this receipt was projected. The manifest does not cover every non-Python asset the tests read.

Reproduce the environment from the checkpoint containing those changes:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install --no-cache-dir --only-binary=:all: -e '.[test]'
make test
.venv/bin/python -m pip check
```

Use the virtual environment's executable path without resolving its symlink. See [the environment guide](../../docs/python-environment.md) for the strict default, explicit core mode and interface edge contracts. Dependency ranges allow compatible versions; they are not a version lock. Hosted CI was configured but was not executed by these local runs.

The retained [existing test log](existing-full-tests.log.gz), [fresh test log](fresh-full-tests.log.gz) and [fresh installation log](fresh-wheel-install.log.gz) are full gzip-compressed outputs. Machine-specific roots were replaced by `<checkout>` and `<temporary-wheel-cache>`. Compressed and uncompressed SHA-256 hashes, commands, versions, durations, numerical thread limits and exact skip details are recorded in [verification.json](verification.json). No private working patch, transcripts, unrelated research memo or cache contents are included. The final historical producer-drift message in each test log is retained; the suite exited successfully.
