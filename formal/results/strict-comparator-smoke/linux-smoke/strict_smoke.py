#!/usr/bin/env python3
"""Separate tiny strict fixture; never evidence of the original challenge.

Requires the already bootstrapped exact original checking checkout and its
normal PAM user session. No network downloads or project-baseline builds.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("checkpoint10_serial", HERE / "strict_serial_check.py")
serial = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = serial
spec.loader.exec_module(serial)
ROOTS = ("SmokeChallenge", "SmokeSolution")
MODULES = ("SmokeChallenge", "SmokeBase", "SmokeSolution")
FIXTURE_FILES = {
    "lean-toolchain": "leanprover/lean4:v4.34.1\n",
    "lakefile.toml": 'name = "comparatorSmoke"\nversion = "0.1.0"\n'
                     '[[lean_lib]]\nname = "SmokeChallenge"\n'
                     '[[lean_lib]]\nname = "SmokeBase"\n'
                     '[[lean_lib]]\nname = "SmokeSolution"\n',
    "lake-manifest.json": json.dumps({"version": "1.1.0", "packagesDir": ".lake/packages",
                                     "packages": [], "name": "comparatorSmoke", "lakeDir": ".lake"}) + "\n",
    "SmokeChallenge.lean": "theorem ComparatorSmoke.accepts : True := True.intro\n",
    "SmokeBase.lean": "def ComparatorSmoke.witness : True := True.intro\n",
    "SmokeSolution.lean": "import SmokeBase\ntheorem ComparatorSmoke.accepts : True := ComparatorSmoke.witness\n",
}
DESCRIPTOR = {"challenge_module": ROOTS[0], "solution_module": ROOTS[1],
              "theorem_names": ["ComparatorSmoke.accepts"], "definition_names": [],
              "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": False}

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--wall-seconds", type=int, default=1800)
    args = parser.parse_args()
    if not 1 <= args.wall_seconds <= 1800:
        parser.error("smoke cap must be 1..1800 seconds")
    if platform.system() != "Linux" or platform.machine() != "x86_64" or os.getuid() == 0:
        raise serial.CheckError("Requires non-root Linux x86_64")
    root = args.root.resolve()
    out = serial.contained(root, args.output)
    if not out.is_relative_to(root / ".tools/linux-verification") or out.exists():
        raise serial.CheckError("Requires new output under trusted .tools/linux-verification")
    with (root / ".tools/linux-verification/serial-comparator.lock").open("a") as lock:
        serial.fcntl.flock(lock, serial.fcntl.LOCK_EX | serial.fcntl.LOCK_NB)
        return run_fixture(root, out, args.wall_seconds)

def run_fixture(root: Path, out: Path, wall_seconds: int) -> int:
    # Planning validates all original source/checker/toolchain/dependency pins,
    # without invoking Lean/Lake or compiling any original submitted module.
    original_plan, snapshot, _, _ = serial.make_plan(root, serial.PROJECT_REV)
    initial_original = serial.fresh_start(root)
    out.mkdir(parents=True)
    fixture = out / "fixture"
    formal = fixture / "formal"
    formal.mkdir(parents=True)
    (formal / ".lake").mkdir()
    # Trusted tools stay outside every sandbox-writable fixture path. This
    # link is solely for unchanged command constructors; no tool is copied.
    (fixture / ".tools").symlink_to(root / ".tools", target_is_directory=True)
    for relative, content in FIXTURE_FILES.items():
        path = formal / relative
        path.write_text(content)
        snapshot.add(path)
    descriptor = out / "Smoke.json"
    serial.save(descriptor, DESCRIPTOR)
    snapshot.add(descriptor)
    snapshot.add(Path(__file__).resolve())
    adapter = out / "no_rebuild_landrun.py"
    shutil.copyfile(HERE / adapter.name, adapter)
    adapter.chmod(0o755)
    lake = root / ".tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake"
    config = out / "no-rebuild-config.json"
    serial.save(config, {"strict_adapter": str(root / ".tools/verification-bin/landrun"),
                        "lake": str(lake), "roots": list(ROOTS),
                        "exporter": str(root / ".tools/verification-bin/lean4export")})
    snapshot.add(adapter)
    snapshot.add(config)
    plan = {"schema_version": 1, "status": "prepared_fixture_only", "commands": [],
            "scope": "separate tiny fixture; no original challenge success claim",
            "original_project_revision": serial.PROJECT_REV,
            "original_descriptor_sha256": original_plan["descriptor_sha256"],
            "original_zero_project_files": initial_original,
            "fixture_fresh_start": serial.fresh_start(fixture),
            "fixture_roots": list(ROOTS), "fixture_modules": list(MODULES),
            "input_sha256": snapshot.record(), "wall_seconds": wall_seconds,
            "started_unix": time.time()}
    runner = serial.MeasuredRunner(fixture, out, plan, wall_seconds)
    runner.executables = {(lake.parent / name).resolve() for name in ("lean", "leanir")}
    path = os.pathsep.join([str(root / ".tools/verification-bin"), str(lake.parent),
                           str(root / ".tools/elan/bin"), os.environ.get("PATH", "")])
    git = Path(shutil.which("git", path=path) or "/usr/bin/git").resolve()
    previous = serial.inventory(fixture)
    def step(label, command, unchanged=False):
        nonlocal previous
        snapshot.check(rehash=True)
        if serial.inventory(root):
            raise serial.CheckError("Original project unexpectedly gained build artifacts")
        before = serial.inventory(fixture)
        if before != previous:
            raise serial.CheckError("Fixture build changed outside recorded stage")
        entry = {"stage": label, "argv": command, "status": "running", "started_unix": time.time()}
        plan["commands"].append(entry)
        serial.save(out / "receipt.json", plan)
        result = runner(command, label)
        entry.update(returncode=result.returncode, elapsed_seconds=time.time()-entry["started_unix"])
        snapshot.check(rehash=True)
        after = serial.inventory(fixture)
        if result.returncode != 0:
            raise serial.CheckError(f"{label} failed; no later stage authorized")
        if unchanged and after != before:
            raise serial.CheckError(f"{label} changed fixture build files")
        if serial.inventory(root):
            raise serial.CheckError("Original project unexpectedly gained build artifacts")
        entry.update(status="passed", fixture_inventory_sha256=after)
        previous = after
        serial.save(out / "receipt.json", plan)
        return result
    try:
        plan["status"] = "running_fixture"
        step("original_linux_and_landrun_preflight", serial.original_probe_command(root), unchanged=True)
        for index, name in enumerate(MODULES):
            step(f"{index:04d}_dependencies_current", serial.sandbox_command(fixture, lake, git, path,
                 ["--no-cache", "--no-build", "build", f"+{name}:deps"]), unchanged=True)
            before = dict(previous)
            step(f"{index:04d}_module_build", serial.sandbox_command(fixture, lake, git, path,
                 ["--no-cache", "build", f"+{name}:olean"]))
            changed = {n: h for n, h in previous.items() if before.get(n) != h}
            if any(n not in previous for n in before) or any(serial.object_owner(n) not in {None, name} for n in changed):
                raise serial.CheckError("Fixture compiler deleted/changed another module's proof object")
            if not any(serial.object_owner(n) == name for n in changed):
                raise serial.CheckError("Fixture compiler produced no selected proof object")
        step("fixture_targets_no_rebuild", serial.sandbox_command(fixture, lake, git, path,
             ["--no-cache", "--no-build", "build", *ROOTS]), unchanged=True)
        step("original_precomparison_landrun_preflight", serial.original_probe_command(root), unchanged=True)
        env = {"PATH": path, "COMPARATOR_LANDRUN": str(adapter),
               "COMPARATOR_LEAN4EXPORT": str(root / ".tools/verification-bin/lean4export")}
        result = step("unchanged_comparator", [*serial.service_prefix(fixture, env), str(lake), "env",
                      str(root / ".tools/verification-bin/comparator"), str(descriptor)], unchanged=True)
        required = ("Running Lean default kernel on solution.", "Lean default kernel accepts the solution", "Your solution is okay!")
        if not all(marker in result.stdout for marker in required):
            raise serial.CheckError("No complete fixture kernel/comparison acceptance evidence")
        plan.update(status="fixture_comparison_passed", completed_unix=time.time(),
                    original_project_files_after=serial.inventory(root))
    except BaseException as error:
        plan.update(status="fixture_failed", error=str(error).replace(str(root), "<CHECKOUT>"), stopped_unix=time.time())
        raise
    finally:
        serial.save(out / "receipt.json", plan)
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (serial.CheckError, OSError, ValueError, KeyError) as error:
        print(f"Strict fixture stopped: {error}", file=sys.stderr)
        raise SystemExit(1)
