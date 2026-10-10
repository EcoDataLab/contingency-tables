"""Offline failure-boundary tests; never invoke Lean, Lake, systemd, or a VM."""
from pathlib import Path
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
ROOT = HERE / "reviewed-helper"

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

serial = load("strict_serial_candidate", HERE / "strict_serial_check.py")
adapter = load("no_rebuild_candidate", HERE / "no_rebuild_landrun.py")
reviewed = serial.reviewed_planner(ROOT)
ACCEPTANCE = "\n".join(("Running Lean default kernel on solution.",
                         "Lean default kernel accepts the solution", "Your solution is okay!"))

class AdapterTests(unittest.TestCase):
    lake = "/trusted/pinned/bin/lake"
    exporter = "/trusted/lean4export"
    options = ["--best-effort", "--ro", "/", "--rw", "/dev", "--rwx", "/work/.lake", "--"]

    def rewrite(self, command, options=None):
        return adapter.rewrite(self.options if options is None else options,
                               self.lake, serial.ROOTS, self.exporter) if command is None else adapter.rewrite(
                                   [*(self.options if options is None else options), *command],
                                   self.lake, serial.ROOTS, self.exporter)

    def test_exact_original_builds_use_real_lake_no_build(self):
        for executable in ("lake", self.lake):
            for root in serial.ROOTS:
                self.assertEqual(self.rewrite([executable, "build", root]),
                    [*self.options, self.lake, "--no-cache", "--no-build", "build", root])

    def test_unknown_or_expanded_lake_commands_refused(self):
        for command in (("lake", "build", "Another.Root"), ("lake", "build", *serial.ROOTS),
                        ("lake", "build", serial.ROOTS[0], "--jobs=1"),
                        ("lake", "env", "lean"), ("/other/lake", "build", serial.ROOTS[0])):
            with self.subTest(command=command), self.assertRaises(adapter.AdapterError):
                self.rewrite(command)

    def test_export_argv_and_all_sandbox_options_preserved(self):
        command = [self.exporter, serial.ROOTS[1], "--", "OAI.ContingencyTables.exactSampling"]
        self.assertEqual(self.rewrite(command), [*self.options, *command])

    def test_weakening_option_not_consumed_before_original_strict_adapter(self):
        options = ["--unrestricted-network", "--best-effort=true", "--"]
        self.assertEqual(self.rewrite(["lake", "build", serial.ROOTS[0]], options)[:3], options)
        # They are deliberately delegated to the unchanged adapter, whose
        # byte-pinned body rejects these spellings; this adapter never runs real
        # Landrun itself and never swallows a weakening flag.

    def test_malformed_command_or_unknown_export_refused(self):
        for args in ([], ["--"], ["--", self.exporter, "Other", "--"],
                     ["--", self.exporter, serial.ROOTS[0], "wrong"], ["--", "bash", "-c", "true"]):
            with self.subTest(args=args), self.assertRaises(adapter.AdapterError):
                adapter.rewrite(args, self.lake, serial.ROOTS, self.exporter)

class SerialRunTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "formal/.lake").mkdir(parents=True)
        self.out = self.root / ".tools/linux-verification/test-run"
        self.out.mkdir(parents=True)
        self.source = self.root / "formal/source.lean"
        self.source.write_text("def x := 1\n")
        self.snapshot = reviewed.Snapshot(self.root)
        self.snapshot.add(self.source)
        self.modules = [reviewed.Module("OAI.A", self.source, ()),
                        reviewed.Module("OAI.B", self.source, ("OAI.A",))]
        self.plan = {"commands": []}
        self.calls = []
        self.custom = None
        self.active = self.maximum_active = 0

    def write_object(self, name, suffix=".olean", content="compiled by mock"):
        path = self.root / "formal/.lake/build/lib/lean" / (name.replace(".", "/") + suffix)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def runner(self, argv, label):
        self.active += 1
        self.maximum_active = max(self.maximum_active, self.active)
        try:
            self.calls.append((argv, label))
            if self.custom:
                override = self.custom(argv, label)
                if override is not None:
                    return override
            if label.endswith("_module_build"):
                name = argv[-1][1:].removesuffix(":olean")
                self.write_object(name)
                self.write_object(name, ".olean.server")
                self.write_object(name, ".olean.private")
            return subprocess.CompletedProcess(argv, 0, ACCEPTANCE if label == "unchanged_comparator" else "", "")
        finally:
            self.active -= 1

    def run_check(self, **kwargs):
        serial.run_check(self.root, self.plan, self.snapshot, self.modules, self.out, self.runner, **kwargs)

    def test_success_is_serial_real_facets_and_kernel_evidence(self):
        self.run_check()
        labels = [label for argv, label in self.calls]
        self.assertEqual(labels, ["original_linux_and_landrun_preflight", "0000_dependencies_current",
            "0000_module_build", "0001_dependencies_current", "0001_module_build",
            "comparator_targets_no_rebuild", "original_precomparison_landrun_preflight", "unchanged_comparator"])
        self.assertEqual(self.maximum_active, 1)
        self.assertEqual(self.plan["status"], "comparison_passed")
        self.assertEqual(self.plan["fresh_start"]["project_proof_objects"], 0)
        for argv, label in self.calls:
            if label.endswith("dependencies_current") or label == "comparator_targets_no_rebuild":
                self.assertIn("--no-build", argv)
            if label.endswith("module_build"):
                self.assertNotIn("--no-build", argv)
                self.assertTrue(argv[-1].endswith(":olean"))
                self.assertEqual(len([a for a in argv if a.startswith("+")]), 1)
                self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", argv)
                self.assertIn("--property=NoNewPrivileges=yes", argv)
        self.assertEqual(len(self.plan["commands"][2]["output_sha256"]), 3)
        self.assertTrue((self.out / "no-rebuild-config.json").is_file())

    def test_any_preexisting_project_file_refuses_before_preflight(self):
        for suffix in (".olean", ".olean.server", ".olean.private", ".trace", ".c"):
            with self.subTest(suffix=suffix):
                file = self.write_object("Old", suffix)
                with self.assertRaisesRegex(serial.CheckError, "empty project"):
                    self.run_check()
                self.assertEqual(self.calls, [])
                self.assertEqual(self.plan["status"], "failed")
                file.unlink()

    def test_symlink_parent_refused_before_preflight(self):
        (self.root / "formal/.lake").rmdir()
        (self.root / "redirect").mkdir()
        (self.root / "formal/.lake").symlink_to(self.root / "redirect", target_is_directory=True)
        with self.assertRaisesRegex(serial.CheckError, "symlink"):
            self.run_check()
        self.assertEqual(self.calls, [])

    def test_stale_dependencies_stop_before_selected_compiler(self):
        self.custom = lambda argv, label: subprocess.CompletedProcess(argv, 3, "", "stale") if label.endswith("dependencies_current") else None
        with self.assertRaisesRegex(serial.CheckError, "dependencies_current failed"):
            self.run_check()
        self.assertEqual(len(self.calls), 2)
        self.assertFalse(any(l.endswith("module_build") for a, l in self.calls))

    def test_failed_module_stops_every_later_stage(self):
        self.custom = lambda argv, label: subprocess.CompletedProcess(argv, 1, "", "proof failure") if label.endswith("module_build") else None
        with self.assertRaisesRegex(serial.CheckError, "module_build failed"):
            self.run_check()
        self.assertEqual(len(self.calls), 3)
        self.assertEqual(self.plan["status"], "failed")

    def test_input_changed_by_compiler_blocks_next_stage(self):
        def change(argv, label):
            if label.endswith("module_build"):
                self.source.write_text("def x := 2\n")
            return None
        self.custom = change
        with self.assertRaisesRegex(reviewed.BuildError, "changed"):
            self.run_check()
        self.assertEqual(len(self.calls), 3)

    def test_dependency_gate_cannot_inject_project_object(self):
        def change(argv, label):
            if label.endswith("dependencies_current"):
                self.write_object("Unrecorded")
            return None
        self.custom = change
        with self.assertRaisesRegex(serial.CheckError, "outside the recorded"):
            self.run_check()
        self.assertEqual(len(self.calls), 2)

    def test_another_project_module_output_refused(self):
        def change(argv, label):
            if label.endswith("module_build"):
                self.write_object("OAI.Unscheduled", ".olean.private")
            return None
        self.custom = change
        with self.assertRaisesRegex(serial.CheckError, "another project"):
            self.run_check()
        self.assertEqual(len(self.calls), 3)

    def test_deleted_prior_artifact_refused(self):
        def change(argv, label):
            if label == "0001_module_build":
                self.write_object("OAI.A").unlink()
            return None
        self.custom = change
        with self.assertRaisesRegex(serial.CheckError, "removed"):
            self.run_check()
        self.assertEqual(len(self.calls), 5)

    def test_no_project_output_refuses_fake_success(self):
        self.custom = lambda argv, label: subprocess.CompletedProcess(argv, 0, "", "") if label.endswith("module_build") else None
        with self.assertRaisesRegex(serial.CheckError, "no recorded"):
            self.run_check()
        self.assertEqual(len(self.calls), 3)

    def test_default_target_trace_failure_blocks_comparator(self):
        self.custom = lambda argv, label: subprocess.CompletedProcess(argv, 2, "", "trace mismatch") if label == "comparator_targets_no_rebuild" else None
        with self.assertRaisesRegex(serial.CheckError, "no_rebuild failed"):
            self.run_check()
        self.assertFalse(any(label == "unchanged_comparator" for argv, label in self.calls))

    def test_no_build_target_mutation_refused(self):
        def change(argv, label):
            if label == "comparator_targets_no_rebuild":
                self.write_object("OAI.A", content="unexpected modification")
            return None
        self.custom = change
        with self.assertRaisesRegex(serial.CheckError, "trace check modified"):
            self.run_check()

    def test_zero_without_kernel_and_comparison_evidence_refused(self):
        for output in ("", "Your solution is okay!", "Lean default kernel accepts the solution"):
            with self.subTest(output=output):
                # Fresh separate fixture for each total run.
                self.setUp()
                self.custom = lambda argv, label: subprocess.CompletedProcess(argv, 0, output, "") if label == "unchanged_comparator" else None
                with self.assertRaisesRegex(serial.CheckError, "acceptance evidence"):
                    self.run_check()

    def test_comparator_cannot_change_prebuilt_project_objects(self):
        def change(argv, label):
            if label == "unchanged_comparator":
                self.write_object("OAI.A", content="late rebuild")
            return None
        self.custom = change
        with self.assertRaisesRegex(serial.CheckError, "despite no-build"):
            self.run_check()

    def test_total_deadline_prevents_any_stage(self):
        with self.assertRaisesRegex(serial.CheckError, "wall-clock"):
            self.run_check(wall_seconds=0)
        self.assertEqual(self.calls, [])

class ProvenanceAndTelemetryTests(unittest.TestCase):
    def test_reviewed_implicit_init_is_not_an_extra_project_root(self):
        modules = [reviewed.Module(serial.ROOTS[0], Path("spec.lean"), ("Init",)),
                   reviewed.Module(serial.ROOTS[1], Path("solution.lean"), ("Init", "OAI.A")),
                   reviewed.Module("OAI.A", Path("A.lean"), ("Init",))]
        closure = serial.descriptor_closure({"roots": [*serial.ROOTS, "Init"]}, modules, reviewed)
        self.assertEqual([m.name for m in closure], [serial.ROOTS[0], "OAI.A", serial.ROOTS[1]])

    def test_extra_audit_root_or_unreachable_module_refused(self):
        modules = [reviewed.Module(name, Path(name), ()) for name in serial.ROOTS]
        with self.assertRaisesRegex(serial.CheckError, "added roots"):
            serial.descriptor_closure({"roots": [*serial.ROOTS, "Math115.New"]}, modules, reviewed)
        with self.assertRaisesRegex(serial.CheckError, "outside the descriptor's closure"):
            serial.descriptor_closure({"roots": list(serial.ROOTS)},
                [*modules, reviewed.Module("OAI.Unreachable", Path("unused"), ())], reviewed)

    def provenance(self):
        return {"comparator_revision": serial.PINS[".tools/comparator"],
                "lean4export_revision": serial.PINS[".tools/comparator/.lake/packages/lean4export"],
                "landrun_revision": serial.PINS[".tools/landrun"], "go_version": "go1.27.2",
                "actual_build_toolchain": reviewed.TOOLCHAIN,
                "checker_declared_toolchain": "leanprover/lean4:v4.34.0",
                "binary_sha256": {name: "0" * 64 for name in ("comparator", "lean4export", "landrun", "landrun-real")}}

    def test_complete_original_checker_provenance_accepted(self):
        serial.validate_provenance(self.provenance(), reviewed.TOOLCHAIN)

    def test_source_or_toolchain_pin_changes_refused(self):
        for key in ("comparator_revision", "lean4export_revision", "landrun_revision",
                    "go_version", "actual_build_toolchain", "checker_declared_toolchain"):
            with self.subTest(key=key):
                record = self.provenance()
                record[key] = "different"
                with self.assertRaisesRegex(serial.CheckError, "pin mismatch"):
                    serial.validate_provenance(record, reviewed.TOOLCHAIN)

    def test_missing_binary_receipt_refused(self):
        record = self.provenance()
        del record["binary_sha256"]["landrun-real"]
        with self.assertRaisesRegex(serial.CheckError, "all four"):
            serial.validate_provenance(record, reviewed.TOOLCHAIN)

    def test_original_bootstrap_tamper_fails_before_dependency_planning(self):
        planner = mock.Mock()
        with mock.patch.object(serial, "reviewed_planner", return_value=planner), mock.patch.object(serial, "digest", return_value="tampered"):
            with self.assertRaisesRegex(serial.CheckError, "bootstrap script bytes changed"):
                serial.make_plan(ROOT, serial.PROJECT_REV)
            planner.make_plan.assert_not_called()

    def test_only_original_immutable_revision_accepted(self):
        for revision in ("main", "HEAD", "f" * 40):
            with self.subTest(revision=revision), mock.patch.object(serial, "reviewed_planner") as loader:
                with self.assertRaises(serial.CheckError):
                    serial.make_plan(ROOT, revision)
                loader.assert_not_called()

    def test_reviewed_planner_bytes_are_required(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "scripts").mkdir()
            (root / "scripts/build_lean_serial.py").write_text("raise Exception('must not import')")
            with self.assertRaisesRegex(serial.CheckError, "bytes changed"):
                serial.reviewed_planner(root)

    def test_observer_sees_only_own_cgroup_pinned_compilers(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            proc, cgroup, binary = root / "proc", root / "cgroup", root / "lean"
            binary.write_text("test")
            binary = binary.resolve()
            cgroup.mkdir()
            (cgroup / "cgroup.procs").write_text("17\n18\n19\n")
            for pid in (17, 18, 20):
                (proc / str(pid)).mkdir(parents=True)
                (proc / str(pid) / "exe").symlink_to(binary)
            self.assertEqual(serial.compiler_pids(cgroup, {binary}, proc), [17, 18])
            self.assertEqual(serial.compiler_pids(cgroup, {root / "other"}, proc), [])
            self.assertEqual(serial.compiler_pids(root / "missing", {binary}, proc), [])

    def test_original_probe_functions_called_without_bootstrap_or_verify(self):
        command = serial.original_probe_command(Path("/checkout"))
        self.assertEqual(command[2], 'source "$1" preflight; configure_paths; strict_landrun_probe')
        self.assertEqual(command[-1], "/checkout/scripts/bootstrap_comparator.sh")

class StageRunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.out = self.root / "reports"
        self.out.mkdir()
        self.plan = {"commands": [{"stage": "test"}]}

    def fake_process(self):
        process = mock.Mock()
        process.pid = 1729
        process.poll.side_effect = [None, 0]
        process.wait.return_value = 0
        return process

    def test_owned_unit_deadline_and_streamed_log_hashes(self):
        process = self.fake_process()
        runner = serial.MeasuredRunner(self.root, self.out, self.plan, 60)
        with mock.patch.object(serial.subprocess, "Popen", return_value=process) as spawn, \
             mock.patch.object(serial.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "/user.slice/test", "")), \
             mock.patch.object(serial, "compiler_pids", return_value=[17]), \
             mock.patch.object(serial.time, "sleep"):
            result = runner(["systemd-run", "--user", "--wait", "--", "/pinned/lake", "build", "+A:olean"], "module_build")
        self.assertEqual(result.returncode, 0)
        argv = spawn.call_args.args[0]
        self.assertTrue(any(a.startswith("--unit=math115-serial-") for a in argv))
        self.assertTrue(any(a.startswith("--property=RuntimeMaxSec=") for a in argv))
        entry = self.plan["commands"][0]
        self.assertEqual(entry["sampled_heavy_compiler_peak"], 1)
        self.assertEqual(entry["stdout_sha256"], serial.digest(self.out / "module_build.stdout.log"))
        self.assertEqual(entry["stderr_sha256"], serial.digest(self.out / "module_build.stderr.log"))

    def test_overlap_stops_only_exact_owned_service(self):
        process = self.fake_process()
        runner = serial.MeasuredRunner(self.root, self.out, self.plan, 60)
        with mock.patch.object(serial.subprocess, "Popen", return_value=process), \
             mock.patch.object(serial.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "/user.slice/test", "")) as command, \
             mock.patch.object(serial, "compiler_pids", return_value=[17, 18]):
            with self.assertRaisesRegex(serial.CheckError, "overlapping"):
                runner(["systemd-run", "--user", "--wait", "--", "/pinned/lake"], "module_build")
        stops = [c.args[0] for c in command.call_args_list if "stop" in c.args[0]]
        self.assertEqual(stops, [["systemctl", "--user", "stop", self.plan["commands"][0]["owned_unit"]]])
        self.assertEqual(self.plan["commands"][0]["overlap_pids"], [17, 18])

    def test_expired_budget_dispatches_no_process(self):
        runner = serial.MeasuredRunner(self.root, self.out, self.plan, 0)
        with mock.patch.object(serial.subprocess, "Popen") as spawn:
            with self.assertRaisesRegex(serial.CheckError, "wall-clock"):
                runner(["systemd-run", "--user"], "module_build")
        spawn.assert_not_called()

if __name__ == "__main__":
    unittest.main()
