# Reproduce the complete Python test suite

The complete suite requires the `test` extra, which installs NumPy and SciPy. The base package remains dependency-free, and `research` continues to install NumPy alone. The SciPy worker tests exercise the real `scipy.stats.random_table` backend; the default test command now fails if that lane is unavailable or skipped.

## Isolated setup

From the repository root, create a local environment and install into that environment explicitly:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install --only-binary=:all: -e '.[test]'
make test
# Equivalent, without Make:
.venv/bin/python scripts/run_python_tests.py
```

Python 3.10 or newer is supported. The binary-wheel option prevents an accidental NumPy/SciPy source build. If the selected Python/platform has no compatible wheel, use a supported Python with available wheels, such as Python 3.12, in a separate virtual environment. No system package installation or `sudo` is needed. On Windows, use `.venv\Scripts\python.exe` in place of `.venv/bin/python` and invoke the runner directly.

Make prefers `.venv/bin/python` when it exists. An explicit interpreter remains available, for example `make PYTHON=/path/to/venv/bin/python test`. Use the environment's Python path itself; resolving its symlink to the underlying system executable can bypass the virtual environment.

The runner prints its interpreter and installed NumPy/SciPy versions before discovery. Missing dependencies fail before optional-library decorators can turn the SciPy tests into skips. A scientific skip found after discovery also makes the full run fail. The runner installs nothing and does not download formal dependencies.

To check an interpreter directly:

```sh
.venv/bin/python -c 'import sys, numpy, scipy; from scipy.stats import random_table; print(sys.executable, numpy.__version__, scipy.__version__)'
```

The declared minimum SciPy version is 1.10, when [`random_table` was added](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.random_table.html). Pip selects compatible releases for each Python version. This extra is a compatibility range, rather than a cross-platform version lock. Keep the version line from the test output with a reproduction report; seeded numerical samples depend on the installed library versions as well as seed and call sequence.

## Explicit core mode and other skips

```sh
make test-core
# Or:
python3 scripts/run_python_tests.py --core
```

Core mode permits unavailable optional numerical libraries and reports their skips. It does not disable an installed backend or convert real failures into skips. The full runner can still report explicit skips for unrelated optional facilities, such as R or a missing pinned formal-source bootstrap; it does not claim those facilities were exercised. Python tests never start Lean or Lake builds. The formal integration checks have their own documented bootstrap and verification commands.

A single file can be run without losing the scientific dependency requirement:

```sh
.venv/bin/python scripts/run_python_tests.py -p test_scipy_workers.py
```

CI installs `.[test]` and runs the complete command on each configured Python lane, including the real SciPy tests. `make verify` uses the same strict default tests before the other source/audit/example checks.

## Edge contracts differ by interface

The Python reference tools and the Lean all-input list program expose different interfaces. Tests should preserve those contracts rather than silently expand their domains.

| Case | Python reference/API contract |
|---|---|
| Empty margin vector | `TableProblem` and both worker samplers require at least one row and one column; empty axes are rejected. The Lean executable sampler separately covers empty lists. |
| Nonempty zero margins or zero total | Exact and worker samplers retain the zero axes and return the unique deterministic table where applicable. The SciPy wrapper bypasses native draws for deterministic shapes and preserves its RNG state. |
| Unequal totals | Worker samplers reject them with `InfeasibleTableError`. `TableProblem` can represent an infeasible problem whose exact fibre is empty. |
| One positive row or column | Worker outputs are deterministic, including zero restoration; no worker random draws are needed. This is distinct from an absent axis. |
| Zero acceptance bits | The repair/correction interfaces accept zero-bit precision, with their documented rejection/fallback behavior. The Lean `t=0` all-input accuracy theorem is a separate contract. |
| Invalid or exhausted custom random source | Python random-source methods must return values in the requested range. Invalid values are rejected; exhaustion is not an implicit zero-padding or arbitrary-short-word guarantee. The Lean list-code theorem requires the complete reserved word. |

The scientific tests check the worker law, which is proportional to inverse cell factorials. It is a different target from uniform aggregate tables. Installing SciPy enables that practical backend's checks; it does not establish a runtime result for the newer Lean uniform-table sampler.
