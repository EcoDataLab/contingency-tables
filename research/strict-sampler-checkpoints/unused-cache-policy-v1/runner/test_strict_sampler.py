"""Offline filesystem and mocked dispatch tests; no compiler or service runs."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
spec = importlib.util.spec_from_file_location("strict_sampler_tested", HERE / "strict_sampler.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
serial, parser = m.load_assets()
FREEZE = m.read(HERE / "source-freeze.json")
SOURCE_PLAN = m.read(HERE.parent / "source-plan.json")

def configuration_fixture(root, put, tools):
    for name in m.CONFIG_SOURCES: put(name, (REPO / name).read_bytes())
    provenance = {"schema_version":1,"status":"authenticated_readonly_retained_configuration_capture",
                  "source_freeze_sha256":m.SOURCE_SHA,
                  "origin":{"retained_bootstrap_sha256":"da762be8cf147ef834961359511d3cf7cf5d47e04da2ed440f2c898befca9a91","readonly_capture_manifest_sha256":"a"*64},
                  "platform":"x86_64-unknown-linux-gnu", "package_revisions":FREEZE["package_revisions"],
                  "source_sha256":dict(m.CONFIG_SOURCES), "tool_sha256":{n:tools[n] for n in m.CONFIG_TOOLS}, "slots":{}}
    for slot,(name,source,config_hash,options) in m.CONFIG_SLOTS.items():
        trace={"idx":int(slot),"name":name,"platform":provenance["platform"],"leanHash":m.LEAN_COMMIT,"configHash":config_hash,"options":options}
        values={"lakefile.olean":("synthetic separately approved configuration "+slot).encode(),
                "lakefile.olean.trace":json.dumps(trace).encode(),"lakefile.olean.lock":b""}
        hashes={n:m.sha(put("formal/.lake/config/"+slot+"/"+n,raw)) for n,raw in values.items()}
        provenance["slots"][slot]={"source":source,"source_sha256":m.CONFIG_SOURCES[source],"trace":trace,"artifacts_sha256":hashes}
    return provenance

class DescriptorTests(unittest.TestCase):
    def setUp(self):
        self.d = m.read(HERE.parent / "challenge/StrictSampler.json")
    def test_exact_revised_descriptor(self):
        m.validate_descriptor(self.d)
    def test_old_descriptor_rejected(self):
        self.d["challenge_module"] = "ComparatorChallenges.ContingencyTables"
        with self.assertRaises(m.Reject): m.validate_descriptor(self.d)
    def test_definition_hole_rejected(self):
        self.d["definition_names"] = ["Math115.PublicLatticeSampler.machine"]
        with self.assertRaises(m.Reject): m.validate_descriptor(self.d)
    def test_extra_axiom_or_kernel_override_rejected(self):
        for key, value in [("permitted_axioms", ["sorryAx"]), ("enable_nanoda", True), ("external_kernel_commands", {})]:
            d = copy.deepcopy(self.d); d[key] = value
            with self.assertRaises(m.Reject): m.validate_descriptor(d)

class SourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = Path(cls.tmp.name)
        for row, original in zip(FREEZE["modules"], SOURCE_PLAN["modules"]):
            dst = cls.root / row["source"]; dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / original["source"], dst)
    @classmethod
    def tearDownClass(cls): cls.tmp.cleanup()
    def test_exact_679_graph_and_separate_roots(self):
        modules = m.validate_sources(self.root, FREEZE, parser)
        self.assertEqual(len(modules), 679)
        self.assertEqual(modules[-1].name, m.ROOTS[1])
    def test_changed_source_rejected(self):
        path = self.root / m.source_path(m.ROOTS[0]); original = path.read_bytes()
        try:
            path.write_bytes(original + b"\n-- changed\n")
            with self.assertRaises(m.Reject): m.validate_sources(self.root, FREEZE, parser)
        finally: path.write_bytes(original)
    def test_header_metadata_mismatch_rejected(self):
        f = copy.deepcopy(FREEZE); f["modules"][-1]["imports"] = ["Init"]
        with self.assertRaises(m.Reject): m.validate_sources(self.root, f, parser)
    def test_source_resolution_override_rejected(self):
        f = copy.deepcopy(FREEZE); f["modules"][-1]["source"] = "formal/Other.lean"
        with self.assertRaises(m.Reject): m.validate_sources(self.root, f, parser)
    def test_wrong_old_source_base_rejected(self):
        f = copy.deepcopy(FREEZE); f["base_commit"] = serial.PROJECT_REV
        with self.assertRaises(m.Reject): m.validate_sources(self.root, f, parser)
    def test_graph_extra_or_missing_node_rejected(self):
        for rows in [FREEZE["modules"][:-1], FREEZE["modules"] + [FREEZE["modules"][0]]]:
            f = copy.deepcopy(FREEZE); f["modules"] = rows
            with self.assertRaises(m.Reject): m.validate_sources(self.root, f, parser)
    def test_statement_importing_proved_final_theorem_rejected_even_if_header_hash_rebound(self):
        f = copy.deepcopy(FREEZE)
        row = next(x for x in f["modules"] if x["name"] == m.ROOTS[0])
        path = self.root / row["source"]; original = path.read_bytes()
        try:
            path.write_text(path.read_text().replace("import Math115.PublicLatticeSampler", "import Math115.LatticeBoundedSampling"))
            row["sha256"] = m.sha(path); row["imports"] = list(parser.lean_imports(path.read_text()))
            with self.assertRaises(m.Reject): m.validate_sources(self.root, f, parser)
        finally: path.write_bytes(original)
    def test_cross_root_import_rejected(self):
        f = copy.deepcopy(FREEZE)
        row = next(x for x in f["modules"] if x["name"] == m.ROOTS[1])
        path = self.root / row["source"]; original = path.read_bytes()
        try:
            path.write_text(path.read_text().replace("import Math115.LatticeBoundedSampling", "import Math115.LatticeBoundedSampling\nimport Math115.StrictSamplerStatement"))
            row["sha256"] = m.sha(path); row["imports"] = list(parser.lean_imports(path.read_text()))
            with self.assertRaises(m.Reject): m.validate_sources(self.root, f, parser)
        finally: path.write_bytes(original)

class ObjectAndCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.root = Path(self.tmp.name).resolve()
        (self.root / "formal/.lake").mkdir(parents=True)
    def tearDown(self): self.tmp.cleanup()
    def file(self, name):
        p = self.root / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(b"object"); return p
    def test_source_adjacent_upstream_and_old_build_proof_objects_rejected(self):
        for name in ["formal/Math115/Bad.olean", ".upstream/openai-math/lean/OAI/Bad.olean.private", "formal/.lake/build/lib/lean/Math115/Bad.olean"]:
            p = self.file(name)
            with self.assertRaises(m.Reject): m.no_hidden_objects(self.root, [])
            p.unlink()
    def test_package_hidden_submission_rejected(self):
        cache = "formal/.lake/packages/mathlib/.lake/build/lib/lean"
        self.file(cache + "/Math115/Bad.olean")
        with self.assertRaises(m.Reject): m.no_hidden_objects(self.root, [cache])
    def test_only_owned_build_allowed_after_fresh_start(self):
        self.file("formal/.lake/build/lib/lean/Math115/Own.olean")
        m.no_hidden_objects(self.root, [], allow_own_build=True)
        self.file("formal/Math115/Other.olean")
        with self.assertRaises(m.Reject): m.no_hidden_objects(self.root, [], allow_own_build=True)
    def test_symlinked_source_or_cache_rejected(self):
        p = self.file("formal/Real.lean"); (self.root / "formal/Link.lean").symlink_to(p)
        with self.assertRaises(m.Reject): m.relative(self.root, "formal/Link.lean")
        with self.assertRaises(m.Reject): m.cache_inventory(self.root, ["formal"])
    def test_changed_lake_configuration_inventory_rejected(self):
        p = self.file("formal/.lake/lakefile.olean")
        values = m.configuration_inventory(self.root, ["formal/.lake"])
        g = m.Guard(self.root, {}, {}, {}, serial, ["formal/.lake"], values)
        g.check(); self.file("formal/.lake/lakefile.extra.olean")
        with self.assertRaises(m.Reject): g.check()
    def test_cache_metadata_drift_rejected(self):
        p = self.file("cache/Init.olean"); stat = p.stat()
        g = m.Guard(self.root, {}, {}, {"cache/Init.olean": (m.sha(p), (stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_ino))}, serial)
        g.check(); p.write_bytes(b"mutated")
        with self.assertRaises(m.Reject): g.check()

class AuditTests(unittest.TestCase):
    def setUp(self):
        indexed = {x["name"]: x["sha256"] for x in FREEZE["modules"]}
        self.audit = {"status": "compiled_and_standard_axiom_audited", "sources_sha256": {n: indexed[n] for n in m.ROOTS}, "target_axioms": {n: ["propext"] for n in m.TARGETS}, "evidence_manifest_sha256": "a"*64}
    def test_correct_named_source_axiom_binding(self): m.validate_entrypoint_audit(FREEZE, self.audit)
    def test_different_entrypoint_or_forbidden_axiom_rejected(self):
        a = copy.deepcopy(self.audit); a["sources_sha256"][m.ROOTS[0]] = "0"*64
        with self.assertRaises(m.Reject): m.validate_entrypoint_audit(FREEZE, a)
        a = copy.deepcopy(self.audit); a["target_axioms"][m.TARGETS[1]] = ["sorryAx"]
        with self.assertRaises(m.Reject): m.validate_entrypoint_audit(FREEZE, a)
    def test_template_not_admitted(self):
        with self.assertRaises(m.Reject): m.admit(Path("/no-such-checkout"), FREEZE, {"status":"pending"}, serial, parser, ambient={})
    def test_python_optimization_override_rejected_before_any_git_or_child(self):
        with self.assertRaises(m.Reject): m.admit(Path("/no-such-checkout"), FREEZE, {}, serial, parser, ambient={"PYTHONOPTIMIZE":"1"})

class ToolAliasTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.root = Path(self.tmp.name).resolve()
        for name, target in m.TOOL_ALIASES.items():
            path = self.root / target; path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(name.encode())
            alias = self.root / name; alias.parent.mkdir(parents=True, exist_ok=True); alias.symlink_to(path)
        self.name = next(iter(m.TOOL_ALIASES)); self.alias = self.root / self.name
        self.target = self.root / m.TOOL_ALIASES[self.name]
    def tearDown(self): self.tmp.cleanup()
    def guard(self):
        tools, aliases = m.freeze_runtime_tools(self.root, m.TOOL_ALIASES)
        return m.Guard(self.root, {}, tools, {}, serial, tool_aliases=aliases)
    def test_exact_bootstrap_aliases_freeze_and_guard_pass(self):
        tools, aliases = m.freeze_runtime_tools(self.root, m.TOOL_ALIASES)
        self.assertEqual(set(aliases), set(m.TOOL_ALIASES))
        self.assertEqual(tools[self.name], m.sha(self.target))
        self.assertEqual(aliases[self.name]["link_identity"]["ino"], self.alias.lstat().st_ino)
        self.guard().check()
    def test_generic_relative_still_rejects_official_tool_alias(self):
        with self.assertRaises(m.Reject): m.relative(self.root, self.name)
    def test_wrong_or_escaping_or_relative_target_rejected(self):
        for target in [str(self.root / "wrong"), "/bin/sh", "../comparator/.lake/build/bin/comparator"]:
            self.alias.unlink(); self.alias.symlink_to(target)
            with self.assertRaises(m.Reject): m.tool_alias_inventory(self.root)
    def test_regular_file_in_place_of_official_alias_rejected(self):
        self.alias.unlink(); self.alias.write_bytes(self.target.read_bytes())
        with self.assertRaises(m.Reject): m.tool_alias_inventory(self.root)
    def test_alias_parent_symlink_rejected(self):
        parent = self.alias.parent; replacement = parent.with_name("other-bin")
        parent.rename(replacement); parent.symlink_to(replacement)
        with self.assertRaises(m.Reject): m.tool_alias_inventory(self.root)
    def test_target_parent_symlink_rejected(self):
        parent = self.target.parent; replacement = parent.with_name("other-bin")
        parent.rename(replacement); parent.symlink_to(replacement)
        with self.assertRaises(m.Reject): m.tool_alias_inventory(self.root)
    def test_target_symlink_chain_rejected(self):
        replacement = self.target.with_name("actual-binary")
        self.target.rename(replacement); self.target.symlink_to(replacement)
        with self.assertRaises(m.Reject): m.tool_alias_inventory(self.root)
    def test_new_alias_identity_same_target_and_bytes_rejected_by_guard(self):
        guard = self.guard(); old = self.alias.with_name("previous-link")
        self.alias.rename(old); self.alias.symlink_to(self.target)
        with self.assertRaises(m.Reject): guard.check()
    def test_changed_target_binary_rejected_by_guard(self):
        guard = self.guard(); self.target.write_bytes(b"changed")
        with self.assertRaises(m.Reject): guard.check()
    def test_retargeted_alias_rejected_by_guard(self):
        guard = self.guard(); other = self.root / list(m.TOOL_ALIASES.values())[1]
        self.alias.unlink(); self.alias.symlink_to(other)
        with self.assertRaises(m.Reject): guard.check()
    def test_alias_changed_during_hash_is_rejected(self):
        real = m.sha
        def hashing(path):
            value = real(path)
            if path == self.target:
                self.alias.rename(self.alias.with_name("previous-link")); self.alias.symlink_to(self.target)
            return value
        with patch.object(m, "sha", side_effect=hashing):
            with self.assertRaises(m.Reject): m.tool_alias_inventory(self.root)
    def test_target_changed_during_hash_is_rejected(self):
        real = m.sha
        def hashing(path):
            value = real(path)
            if path == self.target: self.target.write_bytes(b"changed while hashing")
            return value
        with patch.object(m, "sha", side_effect=hashing):
            with self.assertRaises(m.Reject): m.tool_alias_inventory(self.root)
    def test_nonapproved_tool_alias_and_elan_proxy_symlink_rejected(self):
        for name in [".tools/verification-bin/landrun", ".tools/elan/bin/lake"]:
            path = self.root / name; path.parent.mkdir(parents=True, exist_ok=True); path.symlink_to(self.target)
            with self.assertRaises(m.Reject): m.trusted_runtime_path(self.root, name)
    def test_elan_regular_hardlink_is_accepted_without_path_exception(self):
        elan = self.root / ".tools/elan/bin/elan"; elan.parent.mkdir(parents=True); elan.write_bytes(b"elan")
        lake = elan.with_name("lake"); os.link(elan, lake)
        self.assertEqual(m.trusted_runtime_path(self.root, ".tools/elan/bin/lake"), lake)
        self.assertEqual(elan.stat().st_ino, lake.stat().st_ino)
    def test_unbound_alias_guard_rejected(self):
        with self.assertRaises(m.Reject): m.Guard(self.root, {}, {self.name:m.sha(self.target)}, {}, serial)

class PipelineTests(unittest.TestCase):
    def exercise(self, mode):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); out = root / ".tools/linux-verification/attempt"; out.mkdir(parents=True)
            (root / "formal/.lake").mkdir(parents=True)
            descriptor = root / "descriptor.json"; descriptor.write_text("{}")
            guard = m.Guard(root, {}, {}, {}, serial)
            modules = [SimpleNamespace(name=n) for n in m.ROOTS]
            called = []
            def factory(plan):
                def fake(argv, label):
                    called.append(label)
                    if label.endswith("_module_build"):
                        name = argv[-1][1:-6]
                        path = root / "formal/.lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
                        path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(label.encode())
                        if mode == "compiler_failure": return subprocess.CompletedProcess(argv, 1, "", "")
                        if mode == "other_object":
                            (path.parent / "Other.olean").write_bytes(b"bad")
                    if mode == "deps_build" and label.endswith("_dependencies_current"):
                        path = root / "formal/.lake/build/bad"; path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(b"bad")
                    if mode == "comparator_build" and label == "unchanged_comparator":
                        (root / "formal/.lake/build/bad").write_bytes(b"bad")
                    markers = "Running Lean default kernel on solution. Lean default kernel accepts the solution Your solution is okay!"
                    return subprocess.CompletedProcess(argv, 0, "" if mode == "missing_kernel" else markers, "")
                return fake
            if mode == "pass":
                m.run(root, out, FREEZE, {"trusted_cache_files_sha256":{}}, modules, guard, descriptor, [], serial, 10, factory)
                self.assertEqual(m.read(out / "receipt.json")["status"], "revised_sampler_comparison_passed")
                self.assertEqual(called[-1], "unchanged_comparator")
                self.assertIn("Math115.StrictSamplerStatement", str(m.read(out / "no-rebuild-config.json")))
            else:
                with self.assertRaises(m.Reject): m.run(root, out, FREEZE, {"trusted_cache_files_sha256":{}}, modules, guard, descriptor, [], serial, 10, factory)
                self.assertEqual(m.read(out / "receipt.json")["status"], "failed")
                if mode in {"compiler_failure", "other_object", "deps_build"}: self.assertNotIn("unchanged_comparator", called)
    def test_mock_pipeline_preserves_exact_root_commands_and_success_markers(self): self.exercise("pass")
    def test_failed_compiler_stops_before_comparator(self): self.exercise("compiler_failure")
    def test_no_build_stage_creating_objects_is_rejected(self): self.exercise("deps_build")
    def test_wrong_module_proof_object_is_rejected(self): self.exercise("other_object")
    def test_comparator_object_changes_are_rejected(self): self.exercise("comparator_build")
    def test_zero_exit_without_kernel_acceptance_is_rejected(self): self.exercise("missing_kernel")

class FullAdmissionTests(unittest.TestCase):
    """Synthetic runtime plus real 679 source files; Git/PATH resolver mocked."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.root = Path(self.tmp.name).resolve()
        def put(name, raw):
            p = self.root / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(raw); return p
        self.put = put
        for row, original in zip(FREEZE["modules"], SOURCE_PLAN["modules"]): put(row["source"], (REPO / original["source"]).read_bytes())
        published = m.read(REPO / "formal/results/native-sampler-checkpoint/checkpoint.json")
        for x in published["latest_sources"]: put(m.source_path(x["module"]), (REPO / "formal/results/native-sampler-checkpoint" / x["source"]).read_bytes())
        for name in FREEZE["config_sha256"]: put(name, (REPO / name).read_bytes())
        put(FREEZE["descriptor_path"], (HERE.parent / "challenge/StrictSampler.json").read_bytes())
        self.tracked = {n: [] for n in FREEZE["package_revisions"]}
        self.cache_roots = sorted([m.PREFIX + "/lib/lean", *["formal/.lake/packages/" + n + "/.lake/build/lib/lean" for n in self.tracked]])
        for name in self.cache_roots:
            if name != m.CLI_CACHE: (self.root / name).mkdir(parents=True, exist_ok=True)
        resolution = {}
        for name in FREEZE["external_imports"]:
            rel = name.replace(".", "/")
            if name == "Init" or name.startswith("Lean."):
                obj, src = m.PREFIX + "/lib/lean/" + rel + ".olean", None
            else:
                owner = {"Mathlib":"mathlib", "Batteries":"batteries", "Aesop":"aesop", "Qq":"Qq"}[name.split(".")[0]]
                package = "formal/.lake/packages/" + owner
                obj, src = package + "/.lake/build/lib/lean/" + rel + ".olean", package + "/" + rel + ".lean"
                put(src, b"-- synthetic package source\n")
                self.tracked[owner].append(rel + ".lean")
            put(obj, b"synthetic trusted object")
            resolution[name] = {"olean": obj, "source": src}
        tools = {}
        for name in [*(m.PREFIX + "/bin/" + n for n in ("lean","leanir","lake")), ".tools/elan/bin/elan", ".tools/elan/bin/lake", *(".tools/verification-bin/" + n for n in ("comparator","lean4export","landrun","landrun-real"))]:
            target = m.TOOL_ALIASES.get(name, name)
            path = put(target, ("synthetic binary " + name).encode())
            if name in m.TOOL_ALIASES:
                alias = self.root / name; alias.parent.mkdir(parents=True, exist_ok=True); alias.symlink_to(path)
            tools[name] = m.sha(path)
        provenance = {"comparator_revision":serial.PINS[".tools/comparator"], "lean4export_revision":serial.PINS[".tools/comparator/.lake/packages/lean4export"], "landrun_revision":serial.PINS[".tools/landrun"], "go_version":"go1.27.2", "actual_build_toolchain":parser.TOOLCHAIN, "checker_declared_toolchain":"leanprover/lean4:v4.34.0", "binary_sha256": {n:tools[".tools/verification-bin/"+n] for n in ("comparator","lean4export","landrun","landrun-real")}}
        tools[m.PROVENANCE] = m.sha(put(m.PROVENANCE, json.dumps(provenance).encode()))
        self.config_provenance=configuration_fixture(self.root,put,tools)
        self.config_file=put(".tools/linux-verification/configuration-provenance.json",json.dumps(self.config_provenance).encode())
        system = {}
        for name in m.SYSTEM_COMMANDS:
            path = put("synthetic-system-bin/" + name, ("synthetic system binary " + name).encode())
            system[name] = {"path":str(path.resolve()),"sha256":m.sha(path)}
        mock = patch.object(m.shutil, "which", side_effect=lambda name, **kwargs: system[name]["path"])
        mock.start(); self.addCleanup(mock.stop)
        config_roots = ["formal/.lake", *["formal/.lake/packages/"+n+"/.lake" for n in sorted(self.tracked)]]
        self.policy=m.read(HERE.parent/"unused-cache-policy-candidate.json")
        self.policy_file=put(".tools/linux-verification/unused-cache-policy.json",json.dumps(self.policy).encode())
        self.owners=["<toolchain>","mathlib"]
        self.states=m.cache_root_states(self.root,self.cache_roots,self.owners,self.policy)
        self.runtime = {"schema_version":2,"entrypoint_native_audit":{},"trusted_cache_states":self.states,
                        "external_import_owners":self.owners,"unused_cache_policy":self.policy,
                        "unused_cache_policy_binding":{"path":str(self.policy_file.relative_to(self.root)),"sha256":m.sha(self.policy_file)},
                        "status":"authenticated_linux_runtime_for_strict_sampler", "source_freeze_sha256":m.SOURCE_SHA, "trusted_files_sha256":tools, "trusted_tool_aliases":m.tool_alias_inventory(self.root), "system_executables":system, "lake_configuration_artifacts_sha256":m.configuration_inventory(self.root,config_roots), "trusted_cache_roots":self.cache_roots, "trusted_cache_files_sha256":m.cache_inventory(self.root,self.cache_roots,self.states), "external_import_resolution":resolution}
        configuration=m.indexed_configuration_inventory(self.root,self.config_provenance)
        self.runtime.update(lake_configuration_provenance=self.config_provenance,
                            lake_configuration_provenance_binding={"path":str(self.config_file.relative_to(self.root)),"sha256":m.sha(self.config_file)},
                            lake_configuration_artifacts_sha256=configuration,lake_configuration_artifacts_stat=m.configuration_stats(self.root,configuration))
    def tearDown(self): self.tmp.cleanup()
    def git_read(self, root, *args):
        if args == ("rev-parse","HEAD"):
            if root == self.root: return FREEZE["base_commit"]
            rel = str(root.relative_to(self.root))
            if rel == ".upstream/openai-math": return FREEZE["upstream_revision"]
            if rel in serial.PINS: return serial.PINS[rel]
            return FREEZE["package_revisions"][root.name]
        if args == ("ls-files",): return "\n".join(self.tracked[root.name])
        return ""
    def admit(self): return m.admit(self.root, FREEZE, self.runtime, serial, parser, self.git_read, {})
    def rebind_config(self):
        self.config_file.write_text(json.dumps(self.config_provenance))
        self.runtime["lake_configuration_provenance_binding"]["sha256"] = m.sha(self.config_file)
    def test_complete_admission_with_synthetic_runtime_and_real_source_graph(self):
        modules, guard, _, _ = self.admit(); self.assertEqual(len(modules),679); guard.check()
    def test_authenticator_main_freezes_aliases_and_independently_admits(self):
        spec = importlib.util.spec_from_file_location("authenticate_tested", HERE / "authenticate_runtime.py")
        auth = importlib.util.module_from_spec(spec); spec.loader.exec_module(auth)
        audit = self.put(".tools/linux-verification/native-audit.json", b"{}")
        out = self.root / ".tools/linux-verification/authenticated-test.json"
        def git_command(argv, **kwargs):
            self.assertIn("-C", argv)
            index = argv.index("-C")
            return subprocess.CompletedProcess(argv, 0, self.git_read(Path(argv[index+1]), *argv[index+2:]), "")
        argv = ["authenticate_runtime.py", "--root", str(self.root), "--runner", str(HERE / "strict_sampler.py"), "--output", str(out), "--native-audit", str(audit),"--lake-config-provenance",str(self.config_file),"--lake-config-provenance-sha256",m.sha(self.config_file),"--unused-cache-policy",str(self.policy_file),"--unused-cache-policy-sha256",m.sha(self.policy_file)]
        with patch.object(sys, "argv", argv), patch.dict(os.environ, {}, clear=True), patch.object(auth.subprocess, "run", side_effect=git_command):
            auth.main()
        actual = m.read(out)
        self.assertEqual(actual["trusted_tool_aliases"], self.runtime["trusted_tool_aliases"])
        self.assertEqual(actual["trusted_files_sha256"], self.runtime["trusted_files_sha256"])
    def test_runtime_binary_hash_mismatch_rejected(self):
        self.runtime["trusted_files_sha256"][m.PREFIX+"/bin/lake"] = "0"*64
        with self.assertRaises(m.Reject): self.admit()
    def test_missing_or_changed_alias_binding_rejected(self):
        for value in [None, {}]:
            self.runtime["trusted_tool_aliases"] = value
            with self.assertRaises(m.Reject): self.admit()
    def test_added_trusted_cache_file_rejected(self):
        self.put(self.cache_roots[0]+"/Extra.olean",b"unbound")
        with self.assertRaises(m.Reject): self.admit()
    def test_wrong_package_git_revision_rejected(self):
        original = self.git_read
        def wrong(root,*args):
            return "0"*40 if root.name=="mathlib" and args==("rev-parse","HEAD") else original(root,*args)
        with self.assertRaises(m.Reject): m.admit(self.root,FREEZE,self.runtime,serial,parser,wrong,{})
    def test_external_resolution_override_rejected(self):
        self.runtime["external_import_resolution"]["Init"]["olean"] = "wrong.olean"
        with self.assertRaises(m.Reject): self.admit()
    def test_missing_independent_configuration_provenance_rejected(self):
        self.runtime.pop("lake_configuration_provenance_binding")
        with self.assertRaises(m.Reject):self.admit()
    def test_pending_configuration_template_rejected(self):
        self.config_provenance["status"]="pending_actual_linux_capture";self.rebind_config()
        with self.assertRaises(m.Reject):self.admit()
    def test_arbitrary_renamed_proof_cannot_authenticate_by_runtime_hash(self):
        name="formal/.lake/config/5/lakefile.olean"
        self.put(name,b"renamed submitted proof object")
        self.runtime["lake_configuration_artifacts_sha256"][name]=m.sha(self.root/name)
        with self.assertRaises(m.Reject):self.admit()
    def test_extra_indexed_artifact_file_rejected(self):
        for name in ["Proof.olean","lakefile.olean.private","extra.txt"]:
            p=self.put("formal/.lake/config/5/"+name,b"arbitrary")
            with self.assertRaises(m.Reject):self.admit()
            p.unlink()
    def test_extra_configuration_slot_rejected(self):
        self.put("formal/.lake/config/4/lakefile.olean",b"arbitrary")
        with self.assertRaises(m.Reject):self.admit()
    def test_missing_configuration_trace_rejected(self):
        (self.root/"formal/.lake/config/5/lakefile.olean.trace").unlink()
        with self.assertRaises(m.Reject):self.admit()
    def test_legacy_top_level_renamed_object_is_not_exempt(self):
        self.put("formal/.lake/lakefile.olean",b"arbitrary")
        with self.assertRaises(m.Reject):self.admit()
    def test_indexed_source_binding_allows_no_TOML_mutation(self):
        p=self.root/"formal/.lake/packages/batteries/lakefile.toml";p.write_bytes(p.read_bytes()+b"\n# changed\n")
        with self.assertRaises(m.Reject):self.admit()
    def test_configuration_source_symlink_rejected(self):
        p=self.root/"formal/.lake/packages/proofwidgets/lakefile.lean";original=p.read_bytes();p.unlink()
        other=self.put(".tools/other-source",original);p.symlink_to(other)
        with self.assertRaises(m.Reject):self.admit()
    def test_configuration_artifact_symlink_rejected(self):
        p=self.root/"formal/.lake/config/5/lakefile.olean";raw=p.read_bytes();p.unlink()
        other=self.put(".tools/other-object",raw);p.symlink_to(other)
        with self.assertRaises(m.Reject):self.admit()
    def test_configuration_parent_symlink_rejected(self):
        p=self.root/"formal/.lake/config";other=self.root/".tools/other-config";p.rename(other);p.symlink_to(other)
        with self.assertRaises(m.Reject):self.admit()
    def test_mutated_compiler_even_rebound_runtime_hash_rejected(self):
        name=m.CONFIG_TOOLS[0];self.put(name,b"different compiler")
        self.runtime["trusted_files_sha256"][name]=m.sha(self.root/name)
        with self.assertRaises(m.Reject):self.admit()
    def test_wrong_trace_field_or_boolean_index_rejected_even_if_capture_rebound(self):
        original=copy.deepcopy(self.config_provenance["slots"]["5"])
        for key,value in [("name","arbitrary"),("idx",4),("idx",True),("configHash","0"*16),("leanHash","0"*40),("options",{})]:
            row=copy.deepcopy(original);row["trace"][key]=value
            p=self.put("formal/.lake/config/5/lakefile.olean.trace",json.dumps(row["trace"]).encode())
            row["artifacts_sha256"]["lakefile.olean.trace"]=m.sha(p)
            self.config_provenance["slots"]["5"]=row;self.rebind_config()
            with self.assertRaises(m.Reject):self.admit()
    def test_wrong_capture_platform_rejected(self):
        self.config_provenance["platform"]="arm64-apple-darwin";self.rebind_config()
        with self.assertRaises(m.Reject):self.admit()
    def test_boolean_index_equal_to_zero_or_one_is_rejected(self):
        for slot,value in [("0",False),("1",True)]:
            row=self.config_provenance["slots"][slot];row["trace"]["idx"]=value
            p=self.put("formal/.lake/config/"+slot+"/lakefile.olean.trace",json.dumps(row["trace"]).encode())
            row["artifacts_sha256"]["lakefile.olean.trace"]=m.sha(p);self.rebind_config()
            with self.assertRaises(m.Reject):self.admit()
    def test_unbound_configuration_provenance_file_sha_rejected(self):
        self.runtime["lake_configuration_provenance_binding"]["sha256"]="0"*64
        with self.assertRaises(m.Reject):self.admit()
    def test_changed_observed_trace_with_original_capture_rejected(self):
        p=self.root/"formal/.lake/config/5/lakefile.olean.trace";x=json.loads(p.read_text());x["options"]={};p.write_text(json.dumps(x))
        with self.assertRaises(m.Reject):self.admit()
    def test_changed_configuration_byte_after_admission_rejected(self):
        _,guard,_,_=self.admit();self.put("formal/.lake/config/5/lakefile.olean",b"changed")
        with self.assertRaises(m.Reject):guard.check()
    def test_wrong_source_or_package_revision_capture_rejected(self):
        self.config_provenance["source_sha256"]=dict(m.CONFIG_SOURCES)
        self.config_provenance["source_sha256"]["formal/lakefile.lean"]="0"*64;self.rebind_config()
        with self.assertRaises(m.Reject):self.admit()
        self.config_provenance["source_sha256"]=dict(m.CONFIG_SOURCES)
        self.config_provenance["package_revisions"]=dict(FREEZE["package_revisions"])
        self.config_provenance["package_revisions"]["proofwidgets"]="0"*40;self.rebind_config()
        with self.assertRaises(m.Reject):self.admit()
    def test_nonempty_lock_rejected_even_if_capture_rebound(self):
        p=self.put("formal/.lake/config/5/lakefile.olean.lock",b"arbitrary proof/data")
        self.config_provenance["slots"]["5"]["artifacts_sha256"]["lakefile.olean.lock"]=m.sha(p);self.rebind_config()
        with self.assertRaises(m.Reject):self.admit()
    def test_byteidentical_configuration_rewrite_after_admission_rejected(self):
        _,guard,_,_=self.admit();p=self.root/"formal/.lake/config/5/lakefile.olean"
        original=p.read_bytes();p.write_bytes(original)
        with self.assertRaises(m.Reject):guard.check()
    def test_added_configuration_file_after_admission_rejected(self):
        _,guard,_,_=self.admit();self.put("formal/.lake/config/5/Proof.olean",b"arbitrary")
        with self.assertRaises(m.Reject):guard.check()
    def test_changed_configuration_capture_after_admission_rejected(self):
        _,guard,_,_=self.admit();self.config_file.write_bytes(self.config_file.read_bytes()+b"\n")
        with self.assertRaises(m.Reject):guard.check()
    def test_optional_absent_empty_locks_are_explicitly_bound(self):
        for slot,row in self.config_provenance["slots"].items():
            (self.root/"formal/.lake/config"/slot/"lakefile.olean.lock").unlink();row["artifacts_sha256"].pop("lakefile.olean.lock")
        self.rebind_config();files=m.indexed_configuration_inventory(self.root,self.config_provenance)
        self.runtime["lake_configuration_artifacts_sha256"]=files
        self.runtime["lake_configuration_artifacts_stat"]=m.configuration_stats(self.root,files)
        _,guard,_,_=self.admit();guard.check()
        self.put("formal/.lake/config/5/lakefile.olean.lock",b"")
        with self.assertRaises(m.Reject):guard.check()

if __name__ == "__main__": unittest.main()
