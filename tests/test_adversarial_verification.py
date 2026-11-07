"""Fresh control-boundary counterexamples. No Lean/Lake process is invoked."""
import importlib.util
import hashlib
import json
import signal
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

SCRIPTS = Path(os.environ.get("VERIFY_SCRIPT_DIR", Path(__file__).resolve().parents[1] / "scripts"))
spec = importlib.util.spec_from_file_location("adversarial_audit_runner", SCRIPTS / "run_environment_audit.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class NamedAuditOutputTests(unittest.TestCase):
    def invoke_named_audit(self, stderr="", code=0):
        with tempfile.TemporaryDirectory(prefix="named audit adversary ") as temporary:
            root = Path(temporary)
            (root / "scripts").mkdir()
            (root / "scripts/check_lean_axioms.py").write_bytes((SCRIPTS / "check_lean_axioms.py").read_bytes())
            lake = root / "elan/bin/lake"
            lake.parent.mkdir(parents=True)
            lake.write_text("#!/usr/bin/env python3\nimport sys\n"
                "print(\"'Demo.safe' does not depend on any axioms\")\n"
                f"sys.stderr.write({stderr!r})\nraise SystemExit({code})\n")
            lake.chmod(0o755)
            driver = root / "fixture.lean"
            driver.write_text("import Init\n#print axioms Demo.safe\n")
            source = (SCRIPTS / "verify_lean.sh").read_text()
            function = re.search(r"^audit_axioms\(\) \{.*?^\}", source, re.M | re.S).group()
            command = "set -euo pipefail\n" + function + '\naudit_axioms "$AUDIT_FILE"\n'
            return subprocess.run(["bash", "-c", command], capture_output=True, text=True,
                env={**os.environ, "TASK_ROOT": str(root), "ELAN_HOME": str(root / "elan"),
                     "AUDIT_FILE": str(driver)}, timeout=5)

    def test_unexpected_stderr_cannot_receive_a_passed_named_audit(self):
        result = self.invoke_named_audit("warning: unexpected compiler diagnostics\n")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_clean_named_audit_remains_accepted(self):
        result = self.invoke_named_audit()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_valid_stdout_cannot_hide_a_nonzero_compiler_exit(self):
        result = self.invoke_named_audit(code=9)
        self.assertNotEqual(result.returncode, 0)


class AuditChildOwnershipTests(unittest.TestCase):
    def test_normal_completion_preserves_output_exit_status_and_hashes(self):
        for code in [0, 7]:
            with self.subTest(exit_code=code), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                record = audit.execute([sys.executable, "-c",
                    "import sys; print('ordinary stdout'); print('ordinary stderr', file=sys.stderr); sys.exit(" + str(code) + ")"],
                    root, dict(os.environ), root, "ordinary", 5)
                self.assertEqual(record["exit_code"], code)
                self.assertFalse(record["timed_out"])
                for stream, expected in [("stdout", b"ordinary stdout\n"), ("stderr", b"ordinary stderr\n")]:
                    actual = (root / ("ordinary." + stream)).read_bytes()
                    self.assertEqual(actual, expected)
                    self.assertEqual(record[stream + "_sha256"], hashlib.sha256(expected).hexdigest())

    @unittest.skipUnless(os.name == "posix", "POSIX CLI signal and process-group fixture")
    def test_cli_sigterm_exits_143_and_stops_its_compiler_and_descendant(self):
        with tempfile.TemporaryDirectory(prefix="audit cli adversary ") as temporary:
            root = Path(temporary)
            (root / "bin").mkdir()
            (root / "lib/lean").mkdir(parents=True)
            helper = root / "helper.lean"
            helper.write_text("import Init\n")
            compiler = root / "bin/fake-lean"
            child_pid, grandchild_pid = root / "compiler.pid", root / "descendant.pid"
            grandchild = "import os,time; from pathlib import Path; Path(" + repr(str(grandchild_pid)) + ").write_text(str(os.getpid())); time.sleep(30)"
            (root / "bin/python3").symlink_to(Path(sys.executable).resolve())
            compiler.write_text("#!/usr/bin/env python3\nimport os,subprocess,sys,time\nfrom pathlib import Path\n"
                + "Path(" + repr(str(child_pid)) + ").write_text(str(os.getpid()))\n"
                + "subprocess.Popen([sys.executable,'-c'," + repr(grandchild) + "])\ntime.sleep(30)\n")
            compiler.chmod(0o755)
            digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
            config = dict(schema_version=1, scope="fake compiler CLI cancellation fixture",
                imports=["Demo"], prefixes=["Demo"], source_bound_prefixes=["Demo"],
                expected_modules=["Demo"], headlines=[], compiler_version="fake",
                lean_path=[str(root / "lib/lean")], inventory_roots=[str(root)],
                compiler=str(compiler), compiler_sha256=digest(compiler), helper_source=str(helper),
                helper_sha256=digest(helper), builtin_library=str(root / "lib/lean"),
                working_directory=str(root), pins={"helper":dict(path=str(helper),sha256=digest(helper))},
                timeout_seconds=5,threads=2)
            config_path=root / "config.json"
            config_path.write_text(json.dumps(config))
            cli = subprocess.Popen([sys.executable, str(SCRIPTS / "run_environment_audit.py"),
                "--config",str(config_path),"--output",str(root / "attempt")],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], start_new_session=True)
            owned=[]
            try:
                deadline=time.monotonic()+5
                while not owned:
                    try: owned=[int(child_pid.read_text()),int(grandchild_pid.read_text())]
                    except (FileNotFoundError,ValueError): pass
                    if cli.poll() is not None:
                        self.fail("CLI exited before fake compiler readiness: " + repr(cli.communicate()))
                    if time.monotonic()>deadline: self.fail("fake compiler did not become ready")
                    time.sleep(0.01)
                cli.send_signal(signal.SIGTERM)
                stdout,stderr=cli.communicate(timeout=5)
                self.assertEqual(cli.returncode,143,(stdout,stderr))
                for index,pid in enumerate(owned):
                    deadline=time.monotonic()+2
                    while True:
                        try: os.kill(pid,0)
                        except ProcessLookupError: break
                        if index == 1 and sys.platform.startswith("linux"):
                            # Only the grandchild is externally reaped. A zombie
                            # has exited; the direct child must be reaped here.
                            try: state=Path("/proc/" + str(pid) + "/stat").read_text().rsplit(")",1)[1].split()[0]
                            except FileNotFoundError: break
                            if state == "Z": break
                        if time.monotonic()>deadline: self.fail("owned process did not exit: " + str(pid))
                        time.sleep(0.01)
                self.assertIsNone(unrelated.poll(), "CLI cancellation signaled an unrelated process group")
                receipt=json.loads((root / "attempt/receipt.json").read_text())
                self.assertEqual(receipt["status"],"failed")
            finally:
                if cli.poll() is None: cli.kill()
                cli.communicate()
                if unrelated.poll() is None: unrelated.kill()
                unrelated.wait()
                for pid in owned:
                    try: os.kill(pid,signal.SIGKILL)
                    except ProcessLookupError: pass

    def test_interrupt_reaps_the_owned_child_before_returning(self):
        real_popen = subprocess.Popen
        children = []
        class InterruptedWait:
            def __init__(self, *args, **kwargs):
                self.child = real_popen(*args, **kwargs)
                children.append(self.child)
                self.first = True
            @property
            def pid(self): return self.child.pid
            @property
            def returncode(self): return self.child.returncode
            def wait(self, *args, **kwargs):
                if self.first:
                    self.first = False
                    raise KeyboardInterrupt
                return self.child.wait(*args, **kwargs)
            def kill(self): return self.child.kill()
        try:
            with tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                with patch.object(audit.subprocess, "Popen", InterruptedWait):
                    with self.assertRaises(KeyboardInterrupt):
                        audit.execute([sys.executable, "-c", "import time; time.sleep(30)"],
                            root, dict(os.environ), root, "cancelled", 5)
                self.assertIsNotNone(children[0].poll(), "cancelled audit child remains alive")
        finally:
            for child in children:
                if child.poll() is None: child.kill()
                child.wait()

    @unittest.skipUnless(os.name == "posix", "POSIX process-group ownership fixture")
    def test_timeout_prevents_descendant_writes_after_return(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            marker = root / "late-write"
            code = ("import subprocess,sys,time; "
                "subprocess.Popen([sys.executable,'-c',"
                + repr("import time; from pathlib import Path; time.sleep(0.5); Path(" + repr(str(marker)) + ").write_text('orphan')")
                + "]); time.sleep(30)")
            record = audit.execute([sys.executable, "-c", code], root, dict(os.environ), root, "timeout", 0.2)
            self.assertTrue(record["timed_out"])
            time.sleep(0.7)
            self.assertFalse(marker.exists(), "timed-out audit descendant wrote after return")

    @unittest.skipUnless(os.name == "posix", "POSIX process-group ownership fixture")
    def test_cancel_stops_its_group_even_after_parent_exits_and_leaves_other_groups_alone(self):
        real_popen = subprocess.Popen
        children = []
        class ExitedParentWait:
            def __init__(self, *args, **kwargs):
                self.child = real_popen(*args, **kwargs)
                children.append(self.child)
                self.first = True
            @property
            def pid(self): return self.child.pid
            @property
            def returncode(self): return self.child.returncode
            def wait(self, *args, **kwargs):
                result = self.child.wait(*args, **kwargs)
                if self.first:
                    self.first = False
                    raise KeyboardInterrupt
                return result
            def kill(self): return self.child.kill()
        unrelated = real_popen([sys.executable, "-c", "import time; time.sleep(30)"],
                               start_new_session=True)
        try:
            with tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                marker = root / "cancelled-grandchild-write"
                grandchild = "import time; from pathlib import Path; time.sleep(0.5); Path(" + repr(str(marker)) + ").write_text('orphan')"
                parent = "import subprocess,sys; subprocess.Popen([sys.executable,'-c'," + repr(grandchild) + "])"
                with patch.object(audit.subprocess, "Popen", ExitedParentWait):
                    with self.assertRaises(KeyboardInterrupt):
                        audit.execute([sys.executable, "-c", parent], root, dict(os.environ), root, "exited-parent", 5)
                self.assertEqual(children[0].poll(), 0, "fixture parent must have exited before cancellation")
                time.sleep(0.7)
                self.assertFalse(marker.exists(), "cancelled audit descendant survived exited parent")
                self.assertIsNone(unrelated.poll(), "cleanup signaled an unrelated process group")
        finally:
            if unrelated.poll() is None: unrelated.kill()
            unrelated.wait()
            for child in children:
                if child.poll() is None: child.kill()
                child.wait()


if __name__ == "__main__":
    unittest.main()
