#!/usr/bin/env python3
"""Run checkout tests with a required scientific lane unless --core is explicit.

This does not install packages. Use the isolated environment documented in
``docs/python-environment.md`` or install the project's ``test`` extra.
"""
from __future__ import annotations

import argparse
import importlib
import os
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]


def configure_checkout() -> None:
    """Keep imports and subprocesses on this checkout, even from another cwd."""
    source = str(ROOT / "src")
    checkout = str(ROOT)
    sys.path[:] = [source, checkout, *[p for p in sys.path if p not in (source, checkout)]]
    inherited = [p for p in os.environ.get("PYTHONPATH", "").split(os.pathsep)
                 if p and p not in (source, checkout)]
    os.environ["PYTHONPATH"] = os.pathsep.join([source, checkout, *inherited])


def scientific_backend() -> dict[str, str]:
    """Import the real optional API before discovery can mark it skipped."""
    numpy = importlib.import_module("numpy")
    scipy = importlib.import_module("scipy")
    random_table = importlib.import_module("scipy.stats").random_table
    if not all(callable(getattr(random_table, method, None)) for method in ("pmf", "rvs")):
        raise ImportError("scipy.stats.random_table must provide pmf and rvs")
    return {"numpy": numpy.__version__, "scipy": scipy.__version__}


def scientific_skips(result: unittest.TestResult) -> list[tuple[unittest.TestCase, str]]:
    return [(test, reason) for test, reason in result.skipped
            if any(name in (test.id() + " " + reason).lower() for name in ("numpy", "scipy"))]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", action="store_true",
                        help="allow unavailable optional numerical libraries; report skips explicitly")
    parser.add_argument("-p", "--pattern", default="test*.py", help="unittest discovery pattern")
    parser.add_argument("-q", "--quiet", action="store_true", help="compact unittest output")
    args = parser.parse_args(argv)
    configure_checkout()
    print(f"Test interpreter: {sys.executable}", file=sys.stderr)
    if not args.core:
        try:
            versions = scientific_backend()
        except (ImportError, AttributeError, OSError) as error:
            print(f"Full test environment unavailable: {type(error).__name__}: {error}", file=sys.stderr)
            print("Create .venv and install the test extra before running the full suite:", file=sys.stderr)
            print("  python3 -m venv .venv", file=sys.stderr)
            print("  .venv/bin/python -m pip install --only-binary=:all: -e '.[test]'", file=sys.stderr)
            print("Use --core only when optional-library skips are intentional.", file=sys.stderr)
            return 2
        print(f"Required scientific backend: NumPy {versions['numpy']}, SciPy {versions['scipy']} "
              "(scipy.stats.random_table)", file=sys.stderr)
    else:
        print("Core mode: unavailable optional backends may be reported as skipped.", file=sys.stderr)
    suite = unittest.TestLoader().discover(str(ROOT / "tests"), pattern=args.pattern)
    result = unittest.TextTestRunner(verbosity=1 if args.quiet else 2).run(suite)
    forbidden_skips = scientific_skips(result) if not args.core else []
    if forbidden_skips:
        print("Full test run failed: a required scientific lane was skipped:", file=sys.stderr)
        for test, reason in forbidden_skips:
            print(f"  {test.id()}: {reason}", file=sys.stderr)
    return 0 if result.wasSuccessful() and not forbidden_skips else 1


if __name__ == "__main__":
    raise SystemExit(main())
