#!/usr/bin/env python3
"""Separate strict sampler runner. Plan/execute need out-of-band frozen hashes.

This version is an unreviewed preparation artifact, not a launch authorization.
The tested runtime modules below are loaded only after their exact hash checks.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
SOURCE_SHA = "2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd"
ASSETS = {"strict_serial_check.py": "05df96db18964f76a109d72d876ba7c72f799782e1c54bad9f587cd213110e7e",
          "no_rebuild_landrun.py": "a296bcbdcbb313b0d43cc7237103fbd231df8dd3b5bfc7ffd9d7e289422be5a7",
          "build_lean_serial.py": "5dd644d68305af37343963e283e4b25efb95420896add41f8aa8fd6e2737a66c"}
ROOTS = ("Math115.StrictSamplerStatement", "Math115.StrictSamplerSolution")
TARGETS = ("Math115.StrictSampler.boundedSampling", "Math115.StrictSampler.fixedMachineBoundedSampling")
PREFIX = ".tools/elan/toolchains/leanprover--lean4---v4.34.1"
PROVENANCE = ".tools/linux-verification/checker-provenance.json"
OVERRIDES = ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN", "PYTHONPATH", "PYTHONHOME", "PYTHONOPTIMIZE", "BASH_ENV", "ENV", "LD_PRELOAD", "LD_LIBRARY_PATH")
SYSTEM_COMMANDS = ("bash", "git", "systemctl", "systemd-run", "python3", "uname", "id", "mkdir", "cat", "dirname")
FACETS = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir", ".o", ".bc", ".so", ".dll", ".dylib")
SHA = re.compile(r"[0-9a-f]{64}\Z")
TOOL_ALIASES = {
    ".tools/verification-bin/comparator": ".tools/comparator/.lake/build/bin/comparator",
    ".tools/verification-bin/lean4export": ".tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export",
}

class Reject(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise Reject(message)

def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def read(path):
    return json.loads(path.read_text())

def relative(root, name):
    require(isinstance(name, str) and "\\" not in name and "\x00" not in name, "Invalid relative path")
    p = PurePosixPath(name)
    require(not p.is_absolute() and ".." not in p.parts and name not in ("", "."), "Escaping input path")
    result = root.joinpath(*p.parts)
    require(result.resolve().is_relative_to(root.resolve()), "Input escapes checking checkout")
    require(not any(x.is_symlink() for x in (result, *result.parents) if x == root or x.is_relative_to(root)), "Symlinked input path refused")
    return result

def trusted_runtime_path(root, name):
    """Only bootstrap's two absolute executable aliases bypass relative()."""
    if name not in TOOL_ALIASES:
        return relative(root, name)
    parent = relative(root, str(PurePosixPath(name).parent))
    alias = parent / PurePosixPath(name).name
    target = relative(root, TOOL_ALIASES[name])
    require(alias.is_symlink() and os.readlink(alias) == str(target), "Changed bootstrap tool alias: " + name)
    require(target.is_file(), "Missing regular bootstrap tool target: " + name)
    return target

def file_identity(value):
    return {k: getattr(value, "st_" + k) for k in ("dev", "ino", "mode", "size", "mtime_ns", "ctime_ns")}

def tool_alias_inventory(root):
    result = {}
    for name, target_name in TOOL_ALIASES.items():
        target = trusted_runtime_path(root, name)
        alias = root / name
        link_before, target_before = file_identity(alias.lstat()), file_identity(target.stat())
        digest = sha(target)
        require(trusted_runtime_path(root, name) == target and
                file_identity(alias.lstat()) == link_before and file_identity(target.stat()) == target_before,
                "Bootstrap alias/target changed during authentication: " + name)
        result[name] = {"readlink": str(target), "target": target_name,
                        "link_identity": link_before, "target_identity": target_before, "sha256": digest}
    return result

def freeze_runtime_tools(root, names):
    aliases = tool_alias_inventory(root)
    tools = {name: sha(trusted_runtime_path(root, name)) for name in names}
    require(aliases == tool_alias_inventory(root) and
            all(tools.get(name) == item["sha256"] for name, item in aliases.items()),
            "Bootstrap aliases changed while freezing tools")
    return tools, aliases

def load_assets():
    loaded = {}
    for name, digest in ASSETS.items():
        path = HERE / "tested-runtime" / name
        require(sha(path) == digest, "Measured runtime/parser body changed: " + name)
        if name == "no_rebuild_landrun.py":
            continue
        spec = importlib.util.spec_from_file_location("sampler_v1_" + name[:-3], path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        loaded[name] = module
    return loaded["strict_serial_check.py"], loaded["build_lean_serial.py"]

def git(root, *args):
    r = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True, timeout=30)
    require(r.returncode == 0, "Git pin/clean check failed")
    return r.stdout.strip()

def validate_descriptor(d):
    require(set(d) == {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms", "enable_nanoda"}, "Unexpected descriptor fields")
    require((d["challenge_module"], d["solution_module"]) == ROOTS, "Old or changed descriptor roots")
    require(tuple(d["theorem_names"]) == TARGETS and d["definition_names"] == [], "Changed goals or replaceable definitions")
    require(d["permitted_axioms"] == ["propext", "Quot.sound", "Classical.choice"] and d["enable_nanoda"] is False, "Changed axiom/kernel contract")

def source_path(name):
    namespace = name.split(".")[0]
    require(namespace in {"Math115", "OAI", "ComparatorChallenges"}, "Non-submitted source namespace")
    prefix = "formal" if namespace == "Math115" else ".upstream/openai-math/lean"
    return prefix + "/" + name.replace(".", "/") + ".lean"

def validate_sources(root, freeze, parser):
    require(tuple(freeze["roots"]) == ROOTS and tuple(freeze["targets"]) == TARGETS, "Old-bound source freeze")
    require(freeze["base_commit"] == "fe72b20170e7f85e399368e56baf65b8782b4b50", "Wrong revised source base")
    rows = freeze["modules"]
    require(len(rows) == 679 and len({x["name"] for x in rows}) == len(rows), "Incomplete or duplicated source graph")
    indexed = {x["name"]: x for x in rows}
    external = set()
    def resolve(name):
        if name not in indexed:
            require(name.split(".")[0] not in {"Math115", "OAI", "ComparatorChallenges"}, "Submitted import omitted from freeze: " + name)
            external.add(name)
            return None
        x = indexed[name]
        require(x["source"] == source_path(name), "Changed source resolution: " + name)
        path = relative(root, x["source"])
        require(path.is_file() and sha(path) == x["sha256"], "Source hash mismatch: " + name)
        imports = parser.lean_imports(path.read_text())
        require(list(imports) == x["imports"], "Import/header mismatch: " + name)
        return parser.Module(name, path, imports)
    ordered = parser.dependency_order(ROOTS, resolve)
    require([m.name for m in ordered] == [x["name"] for x in rows], "Graph/order is not exact descriptor closure")
    require(sorted(external) == freeze["external_imports"], "External import boundary changed")
    def reachable(name):
        result, pending = set(), [name]
        while pending:
            name = pending.pop()
            if name in result:
                continue
            result.add(name)
            pending.extend(indexed.get(name, {}).get("imports", []))
        return result
    challenge, solution = reachable(ROOTS[0]), reachable(ROOTS[1])
    require(ROOTS[1] not in challenge and ROOTS[0] not in solution, "Statement/solution roots import each other")
    require("Math115.LatticeBoundedSampling" not in challenge, "Statement imports final theorem")
    require("Math115.LatticeBoundedSampling" in solution and "Math115.PublicLatticeSampler" in challenge & solution, "Machine/theorem binding missing")
    require(not ({"OAI.Combinatorics.ContingencyTables.UnconditionalMain", "ComparatorChallenges.ContingencyTables"} & (challenge | solution)), "Original public theorem collision")
    return ordered

def cache_inventory(root, roots):
    result = {}
    for name in roots:
        base = relative(root, name)
        require(base.is_dir(), "Missing trusted import-cache directory")
        for path in sorted(base.rglob("*")):
            require(not path.is_symlink(), "Symlinked trusted cache entry")
            if path.is_file():
                result[str(path.relative_to(root))] = sha(path)
    return result

def no_hidden_objects(root, cache_roots, allow_own_build=False):
    build = root / "formal/.lake/build"
    bases = [root / "formal", root / ".upstream/openai-math/lean", root / ".upstream/openai-math/.lake/build"]
    packages = root / "formal/.lake/packages"
    for base in bases:
        if not base.exists():
            continue
        for path in base.rglob("*"):
            if path.is_relative_to(packages):
                continue
            require(not path.is_symlink(), "Symlinked submitted tree")
            if not path.is_file() or not path.name.endswith((*FACETS, ".c")):
                continue
            if path.parent == root / "formal/.lake" and path.name.startswith("lakefile."):
                continue  # separately hash-bound trusted Lake configuration artifact
            if allow_own_build and path.is_relative_to(build):
                continue
            raise Reject("Submitted proof artifact outside owned fresh build: " + str(path.relative_to(root)))
    for name in cache_roots:
        base = relative(root, name)
        for namespace in ("Math115", "OAI", "ComparatorChallenges"):
            require(not (base / namespace).exists(), "Submitted namespace hidden in trusted cache")

class Guard:
    def __init__(self, root, sources, tools, caches, serial, config_roots=(), config_files=None, system_executables=None, tool_aliases=None):
        self.root, self.sources, self.tools, self.caches = root, sources, tools, caches
        self.serial = serial
        self.config_roots, self.config_files = config_roots, config_files or {}
        self.system_executables = system_executables or {}
        self.tool_aliases = tool_aliases
        require(not (set(tools) & set(TOOL_ALIASES)) or tool_aliases is not None, "Unbound bootstrap alias guard")
    def add(self, path):
        self.tools[str(path.relative_to(self.root))] = sha(path)
    def check(self, rehash=False):
        require(configuration_inventory(self.root, self.config_roots) == self.config_files, "Lake configuration artifact inventory changed")
        for name, item in self.system_executables.items():
            actual = shutil.which(name)
            require(actual is not None and str(Path(actual).resolve()) == item["path"] and sha(Path(item["path"])) == item["sha256"], "System command resolution/bytes changed: " + name)
        if self.tool_aliases is not None:
            require(tool_alias_inventory(self.root) == self.tool_aliases, "Bootstrap alias identity/target bytes changed")
        for name, digest in self.sources.items():
            path = relative(self.root, name)
            require(path.is_file() and sha(path) == digest, "Frozen source changed: " + name)
        for name, digest in self.tools.items():
            path = trusted_runtime_path(self.root, name)
            require(path.is_file() and sha(path) == digest, "Frozen tool changed: " + name)
        # Complete cache set is checked at admission and before/after Comparator.
        # At every serial stage all frozen cache entries retain their stat identity.
        for name, (digest, stat) in self.caches.items():
            path = relative(self.root, name)
            require(path.is_file(), "Trusted cache file vanished")
            current = path.stat()
            require((current.st_size, current.st_mtime_ns, current.st_ctime_ns, current.st_ino) == stat,
                    "Trusted cache metadata changed: " + name)
            if rehash:
                require(sha(path) == digest, "Trusted cache bytes changed")

def configuration_inventory(root, roots):
    result = {}
    for name in roots:
        base = relative(root, name)
        for path in sorted(base.glob("lakefile.*")):
            require(not path.is_symlink(), "Symlinked Lake configuration artifact")
            if path.is_file():
                result[str(path.relative_to(root))] = sha(path)
    return result

def validate_entrypoint_audit(freeze, audit):
    require(audit.get("status") == "compiled_and_standard_axiom_audited", "New entrypoint compilation/audit binding missing")
    require(set(audit["sources_sha256"]) == set(ROOTS), "Native entrypoint source binding incomplete")
    indexed = {x["name"]: x["sha256"] for x in freeze["modules"]}
    require(audit["sources_sha256"] == {name: indexed[name] for name in ROOTS}, "Native audit covers different source entrypoints")
    require(set(audit["target_axioms"]) == set(TARGETS), "Named target axiom evidence incomplete")
    require(all(set(axioms) <= {"propext", "Quot.sound", "Classical.choice"} for axioms in audit["target_axioms"].values()), "Native audit has forbidden solution axiom")
    require(bool(SHA.fullmatch(audit["evidence_manifest_sha256"])), "Native audit evidence manifest hash missing")

def admit(root, freeze, runtime, serial, parser, git_read=git, ambient=None):
    ambient = os.environ if ambient is None else ambient
    require(not any(ambient.get(k) for k in OVERRIDES), "Ambient import/Python/toolchain override")
    require(runtime.get("status") == "authenticated_linux_runtime_for_strict_sampler", "Runtime template is not authenticated")
    require(runtime["source_freeze_sha256"] == SOURCE_SHA, "Runtime bound to another source freeze")
    require(git_read(root, "rev-parse", "HEAD") == freeze["base_commit"], "Wrong checking base commit")
    allowed = set(freeze["overlay_sha256"]) | {source_path(x) for x in ROOTS}
    for options in (("diff", "--name-only"), ("diff", "--cached", "--name-only"), ("ls-files", "--others", "--exclude-standard")):
        require(set(git_read(root, *options).splitlines()) <= allowed, "Unapproved checking source changes")
    require(git_read(root / ".upstream/openai-math", "rev-parse", "HEAD") == freeze["upstream_revision"], "Upstream pin mismatch")
    for options in (("diff", "--name-only"), ("diff", "--cached", "--name-only"), ("ls-files", "--others", "--exclude-standard")):
        require(not git_read(root / ".upstream/openai-math", *options), "Upstream source dirty")
    modules = validate_sources(root, freeze, parser)
    sources = {x["source"]: x["sha256"] for x in freeze["modules"]}
    sources.update(freeze["overlay_sha256"])
    sources.update(freeze["config_sha256"])
    descriptor = relative(root, freeze["descriptor_path"])
    require(sha(descriptor) == freeze["descriptor_sha256"], "Descriptor hash changed")
    validate_descriptor(read(descriptor))
    sources[freeze["descriptor_path"]] = freeze["descriptor_sha256"]
    manifest = read(root / "formal/lake-manifest.json")
    require(manifest["packagesDir"] == ".lake/packages", "Unexpected package resolution")
    actual_pins = {x["name"]: x["rev"] for x in manifest["packages"]}
    require(actual_pins == freeze["package_revisions"], "Package pins changed")
    packages = {}
    for entry in manifest["packages"]:
        require(entry["type"] == "git" and entry.get("subDir") is None, "Unsupported package source")
        package = relative(root, "formal/.lake/packages/" + entry["name"])
        require(git_read(package, "rev-parse", "HEAD") == entry["rev"], "Package revision mismatch")
        require(not git_read(package, "status", "--porcelain", "--untracked-files=all"), "Package source dirty")
        packages[entry["name"]] = (package, set(git_read(package, "ls-files").splitlines()))
    for folder, pin in serial.PINS.items():
        require(git_read(root / folder, "rev-parse", "HEAD") == pin, "Checker source pin mismatch")
        require(not git_read(root / folder, "status", "--porcelain", "--untracked-files=all"), "Checker source dirty")
    provenance = read(relative(root, PROVENANCE))
    serial.validate_provenance(provenance, parser.TOOLCHAIN)
    tools = dict(runtime["trusted_files_sha256"])
    aliases = tool_alias_inventory(root)
    require(runtime.get("trusted_tool_aliases") == aliases, "Unbound or changed bootstrap alias identity")
    require(all(tools.get(name) == item["sha256"] for name, item in aliases.items()), "Alias target/runtime digest mismatch")
    require(PROVENANCE in tools, "Unbound checker provenance")
    for name, digest in provenance["binary_sha256"].items():
        path = ".tools/verification-bin/" + name
        require(tools.get(path) == digest, "Executable provenance/runtime hash mismatch")
    require(all(PREFIX + "/bin/" + n in tools for n in ("lean", "leanir", "lake")) and all(".tools/elan/bin/" + n in tools for n in ("elan", "lake")), "Missing actual compiler/Lake/Elan hashes")
    require(set(runtime["system_executables"]) == set(SYSTEM_COMMANDS), "Unbound system command inventory")
    config_roots = ["formal/.lake", *["formal/.lake/packages/" + n + "/.lake" for n in sorted(packages)]]
    configuration = configuration_inventory(root, config_roots)
    require(configuration == runtime["lake_configuration_artifacts_sha256"], "Trusted Lake configuration artifact set differs")
    require(any(name.startswith("formal/.lake/lakefile.") and name.endswith(".olean") for name in configuration), "Precompiled hash-bound Lake configuration required")
    tools.update(configuration)
    expected_cache_roots = sorted([PREFIX + "/lib/lean", *["formal/.lake/packages/" + n + "/.lake/build/lib/lean" for n in packages]])
    require(runtime["trusted_cache_roots"] == expected_cache_roots, "Unapproved cache roots")
    no_hidden_objects(root, expected_cache_roots)
    actual_cache = cache_inventory(root, expected_cache_roots)
    require(actual_cache == runtime["trusted_cache_files_sha256"], "Complete trusted cache inventory differs")
    external = {}
    for name in freeze["external_imports"]:
        rel = name.replace(".", "/")
        candidates = []
        builtin = relative(root, PREFIX + "/lib/lean/" + rel + ".olean")
        if builtin.is_file():
            candidates.append((str(builtin.relative_to(root)), None))
        for package, tracked in packages.values():
            if rel + ".lean" in tracked:
                obj = package / ".lake/build/lib/lean" / (rel + ".olean")
                require(obj.is_file(), "Direct trusted import object missing: " + name)
                source = package / (rel + ".lean")
                candidates.append((str(obj.relative_to(root)), str(source.relative_to(root))))
                tools[str(source.relative_to(root))] = sha(source)
        require(len(candidates) == 1, "Missing or ambiguous direct external import: " + name)
        external[name] = {"olean": candidates[0][0], "source": candidates[0][1]}
    require(external == runtime["external_import_resolution"], "External source/object resolution changed")
    caches = {}
    for name, digest in actual_cache.items():
        stat = relative(root, name).stat()
        caches[name] = (digest, (stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_ino))
    guard = Guard(root, sources, tools, caches, serial, config_roots, configuration, runtime["system_executables"], aliases)
    guard.check(rehash=True)
    require(not serial.inventory(root), "Whole-run start has submitted build files")
    return modules, guard, descriptor, expected_cache_roots

def run(root, out, freeze, runtime, modules, guard, descriptor, caches, serial, wall, runner=None):
    plan = {"schema_version": 1, "status": "prepared_revised_sampler", "scope": "separate revised sampler only",
            "source_freeze_sha256": SOURCE_SHA, "roots": list(ROOTS), "descriptor_sha256": sha(descriptor),
            "wall_seconds": wall, "commands": [], "fresh_start": serial.fresh_start(root), "started_unix": time.time()}
    lake = relative(root, PREFIX + "/bin/lake")
    path = os.pathsep.join([str(root / ".tools/verification-bin"), str(lake.parent), str(root / ".tools/elan/bin"), os.environ.get("PATH", "")])
    git_path = Path(shutil.which("git", path=path) or "/usr/bin/git").resolve()
    adapter = out / "no_rebuild_landrun.py"
    shutil.copyfile(HERE / "tested-runtime/no_rebuild_landrun.py", adapter)
    adapter.chmod(0o755)
    serial.save(out / "no-rebuild-config.json", {"strict_adapter": str(root / ".tools/verification-bin/landrun"), "lake": str(lake), "roots": list(ROOTS), "exporter": str(root / ".tools/verification-bin/lean4export")})
    guard.add(adapter); guard.add(out / "no-rebuild-config.json")
    runner = serial.MeasuredRunner(root, out, plan, wall) if runner is None else runner(plan)
    previous = serial.inventory(root)
    deadline = time.monotonic() + wall
    def step(label, argv, unchanged=False):
        nonlocal previous
        require(time.monotonic() < deadline, "Whole-run deadline exhausted")
        guard.check()
        no_hidden_objects(root, caches, allow_own_build=True)
        require(serial.inventory(root) == previous, "Submitted build drift outside owned stage")
        entry = {"stage": label, "argv": argv, "status": "running", "started_unix": time.time()}
        plan["commands"].append(entry); serial.save(out / "receipt.json", plan)
        try:
            result = runner(argv, label)
            entry.update(returncode=result.returncode, elapsed_seconds=time.time()-entry["started_unix"])
            guard.check()
            after = serial.inventory(root)
            require(result.returncode == 0, label + " failed; no later stage")
            require(not unchanged or after == previous, "No-build/probe/export stage modified submitted artifacts")
            entry.update(status="passed", output_sha256={n:h for n,h in after.items() if previous.get(n) != h},
                         project_build_inventory_sha256=hashlib.sha256(json.dumps(after, sort_keys=True).encode()).hexdigest())
            previous = after
            return result
        except BaseException as error:
            entry.update(status="failed", error=str(error).replace(str(root), "<CHECKOUT>"))
            raise
        finally:
            serial.save(out / "receipt.json", plan)
    try:
        step("original_linux_and_landrun_preflight", serial.original_probe_command(root), True)
        for index, module in enumerate(modules):
            name = module.name
            step(f"{index:04d}_dependencies_current", serial.sandbox_command(root, lake, git_path, path, ["--no-cache", "--no-build", "build", f"+{name}:deps"]), True)
            before = dict(previous)
            step(f"{index:04d}_module_build", serial.sandbox_command(root, lake, git_path, path, ["--no-cache", "build", f"+{name}:olean"]))
            changed = {n: h for n, h in previous.items() if before.get(n) != h}
            require(all(n in previous for n in before), "Compiler deleted earlier artifact")
            require(all(serial.object_owner(n) in {None, name} for n in changed), "Compiler changed another proof object")
            require(any(serial.object_owner(n) == name for n in changed), "No selected proof object produced")
        step("comparator_targets_no_rebuild", serial.sandbox_command(root, lake, git_path, path, ["--no-cache", "--no-build", "build", *ROOTS]), True)
        step("original_precomparison_landrun_preflight", serial.original_probe_command(root), True)
        require(cache_inventory(root, caches) == runtime["trusted_cache_files_sha256"], "Cache inventory drift before comparison")
        env = {"PATH": path, "ELAN_HOME": str(root / ".tools/elan"), "MATHLIB_CACHE_DIR": str(root / ".tools/mathlib-cache"), "COMPARATOR_LANDRUN": str(adapter), "COMPARATOR_LEAN4EXPORT": str(root / ".tools/verification-bin/lean4export")}
        result = step("unchanged_comparator", [*serial.service_prefix(root, env), str(lake), "env", str(root / ".tools/verification-bin/comparator"), str(descriptor)], True)
        require(all(x in (result.stdout or "") for x in ("Running Lean default kernel on solution.", "Lean default kernel accepts the solution", "Your solution is okay!")), "Missing actual kernel/comparison acceptance")
        guard.check(rehash=True)
        require(cache_inventory(root, caches) == runtime["trusted_cache_files_sha256"], "Cache inventory drift after comparison")
        plan.update(status="revised_sampler_comparison_passed", final_project_output_sha256=previous, completed_unix=time.time())
    except BaseException as error:
        plan.update(status="interrupted" if isinstance(error, (KeyboardInterrupt, SystemExit)) else "failed", error=str(error).replace(str(root), "<CHECKOUT>"), stopped_unix=time.time())
        raise
    finally:
        serial.save(out / "receipt.json", plan)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, required=True)
    p.add_argument("--runtime-freeze", type=Path, required=True)
    p.add_argument("--runtime-freeze-sha256", required=True)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--plan", action="store_true"); mode.add_argument("--execute", action="store_true")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--wall-seconds", type=int, default=39600)
    a = p.parse_args()
    require(1 <= a.wall_seconds <= 39600, "Unsupported guest cap")
    require(SHA.fullmatch(a.runtime_freeze_sha256) and sha(a.runtime_freeze) == a.runtime_freeze_sha256, "Caller runtime freeze SHA mismatch")
    require(sha(HERE / "source-freeze.json") == SOURCE_SHA, "Frozen sampler source manifest changed")
    root = a.root.resolve(); out = relative(root, str(a.output.resolve().relative_to(root)))
    require(out.is_relative_to(root / ".tools/linux-verification") and not out.exists(), "Need fresh trusted output directory")
    serial, parser = load_assets()
    require(serial.fcntl is not None, "POSIX lock required")
    with (root / ".tools/linux-verification/serial-comparator.lock").open("a") as lock:
        serial.fcntl.flock(lock, serial.fcntl.LOCK_EX | serial.fcntl.LOCK_NB)
        freeze, runtime = read(HERE / "source-freeze.json"), read(a.runtime_freeze)
        modules, guard, descriptor, caches = admit(root, freeze, runtime, serial, parser)
        # Keep all runtime controls and these helpers immutable during the run.
        for name in ("strict_sampler.py", "source-freeze.json"):
            guard.add(HERE / name)
        for name in ASSETS:
            guard.add(HERE / "tested-runtime" / name)
        guard.add(a.runtime_freeze.resolve())
        out.mkdir(parents=True)
        serial.save(out / "plan.json", {"status": "admitted_plan_only", "source_freeze_sha256": SOURCE_SHA, "runtime_freeze_sha256": a.runtime_freeze_sha256, "module_count": len(modules), "roots": list(ROOTS)})
        if a.execute:
            require(platform.system() == "Linux" and platform.machine() == "x86_64" and os.getuid() != 0, "Execution requires non-root Linux x86_64")
            validate_entrypoint_audit(freeze, runtime.get("entrypoint_native_audit", {}))
            run(root, out, freeze, runtime, modules, guard, descriptor, caches, serial, a.wall_seconds)
        else:
            print(f"Admitted {len(modules)} source modules; no Lean/Lake/checker run.")
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Reject, OSError, KeyError, ValueError, RuntimeError) as error:
        print("Strict sampler stopped: " + str(error), file=sys.stderr)
        raise SystemExit(1)
