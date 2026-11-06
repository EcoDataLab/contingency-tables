"""Make recipes accept a Python executable path containing spaces."""
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
MAKEFILE = ROOT / "Makefile"


@unittest.skipUnless(os.name == "posix" and shutil.which("make"),
                     "requires POSIX Make and shell recipes")
class MakePythonPathTests(unittest.TestCase):
    def check_bundle(self, *arguments):
        # A parent `make PYTHON=... test` must not override the default-path case.
        environment = {key: value for key, value in os.environ.items()
                       if key not in {"PYTHON", "MAKEFLAGS", "MFLAGS", "MAKELEVEL",
                                      "MAKEOVERRIDES"}}
        result = subprocess.run(
            [shutil.which("make"), "-f", str(MAKEFILE), *arguments, "sources-bundle"],
            cwd=ROOT, env=environment, capture_output=True, text=True, timeout=30,
            check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(result.stdout[result.stdout.index("{"):])
        expected = len((ROOT / "115/SHA256SUMS").read_text().splitlines())
        self.assertEqual(report, {"bundle_sha256_verified": expected})

    def test_default_interpreter(self):
        self.check_bundle()

    def test_relative_interpreter(self):
        self.check_bundle("PYTHON=" + os.path.relpath(sys.executable, ROOT))

    def test_absolute_executable_path_with_spaces(self):
        with tempfile.TemporaryDirectory(prefix="make python ") as directory:
            executable = Path(directory) / "python executable"
            executable.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + ' "$@"\n')
            executable.chmod(0o700)
            self.check_bundle("PYTHON=" + str(executable))


if __name__ == "__main__":
    unittest.main()
