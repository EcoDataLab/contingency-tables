#!/usr/bin/env python3
"""Proposal: fresh-start serial sandbox builds, then unchanged pinned Comparator.

--plan uses the reviewed repository planner; no Lean/Lake/compiler is invoked.
--execute is Linux-only and requires an exclusive, already bootstrapped checking
checkout. This candidate is NOT yet approved for an actual VM/checking launch.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import signal
import shutil
import subprocess
import sys
import time
import uuid
from typing import Callable

try:
    import fcntl
except ImportError:
    fcntl = None

PLANNER_SHA = "5dd644d68305af37343963e283e4b25efb95420896add41f8aa8fd6e2737a66c"
PROJECT_REV = "895b45c8bcb0ca7f60e7a6b0b91af89b2ac7c566"
BOOTSTRAP_SHA = "f7be322a8c6e166bedc4c9997562746ae6ec2c5ccf4f97b75eb3b7fe72ae9859"
DESCRIPTOR = ".upstream/openai-math/lean/ComparatorChallenges/ContingencyTables.json"
DESCRIPTOR_SHA = "4baaa8be9da6f2c3b8664c94cad82b8f2c549b69315374584d6d01e381719a57"
ROOTS = ("ComparatorChallenges.ContingencyTables", "OAI.Combinatorics.ContingencyTables.UnconditionalMain")
PINS = {
    ".tools/comparator": "d03acab154d269c06e60e4de7e4cc85deebff94b",
    ".tools/comparator/.lake/packages/lean4export": "076e8e57707e813375e8f9da8bf989799ace9680",
    ".tools/landrun": "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4",
}

class CheckError(RuntimeError):
    pass

def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def save(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)

def reviewed_planner(root: Path):
    path = root / "scripts/build_lean_serial.py"
    if digest(path) != PLANNER_SHA:
        raise CheckError("Reviewed dependency planner bytes changed")
    spec = importlib.util.spec_from_file_location("reviewed_math115_serial_planner", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module

def contained(root: Path, path: Path) -> Path:
    resolved = path.resolve()
    if not resolved.is_relative_to(root.resolve()):
        raise CheckError("Checking path escapes its private checkout")
    return resolved

def inventory(root: Path) -> dict[str, str]:
    build = root / "formal/.lake/build"
    contained(root, build)
    if any(path.is_symlink() for path in (root / "formal", root / "formal/.lake", build)):
        raise CheckError("Project build directory or parent may not be a symlink")
    if build.exists() and not build.is_dir():
        raise CheckError("Project build path must be a directory")
    result = {}
    if build.exists():
        for path in build.rglob("*"):
            if path.is_symlink():
                raise CheckError("Project build tree contains a symlink")
            if path.is_file():
                result[str(path.relative_to(root))] = digest(path)
    return result

def fresh_start(root: Path) -> dict:
    existing = inventory(root)
    if existing:
        raise CheckError("Total serial checking run must start with an empty project build tree")
    return {"project_build_files": 0, "project_proof_objects": 0,
            "time_unix": time.time(), "boundary": "start of total serial-build-plus-comparison run"}

def validate_provenance(provenance: dict, toolchain: str) -> None:
    expected_fields = {"comparator_revision": PINS[".tools/comparator"],
                       "lean4export_revision": PINS[".tools/comparator/.lake/packages/lean4export"],
                       "landrun_revision": PINS[".tools/landrun"], "go_version": "go1.27.2",
                       "actual_build_toolchain": toolchain,
                       "checker_declared_toolchain": "leanprover/lean4:v4.34.0"}
    for key, expected in expected_fields.items():
        if provenance.get(key) != expected:
            raise CheckError(f"Checker provenance pin mismatch: {key}")
    if set(provenance["binary_sha256"]) != {"comparator", "lean4export", "landrun", "landrun-real"}:
        raise CheckError("Checker provenance must cover all four executable bodies")

def descriptor_closure(plan: dict, modules: list, planner) -> list:
    # The reviewed header extractor includes implicit Init for the audit file.
    # Init is already a trusted toolchain import, not an additional project root.
    actual_roots = set(plan["roots"])
    if not set(ROOTS) <= actual_roots or actual_roots - set(ROOTS) - {"Init"}:
        raise CheckError("Reviewed full planner added roots outside the original descriptor")
    indexed = {module.name: module for module in modules}
    proof_closure = planner.dependency_order(ROOTS, indexed.get)
    if {module.name for module in proof_closure} != set(indexed):
        raise CheckError("Planner includes modules outside the descriptor's closure")
    return proof_closure

def make_plan(root: Path, project_revision: str) -> tuple[dict, object, list, object]:
    if not re.fullmatch(r"[0-9a-f]{40}", project_revision):
        raise CheckError("Project revision must be an immutable 40-digit Git object ID")
    if project_revision != PROJECT_REV:
        raise CheckError("This candidate is scoped to the original project revision")
    planner = reviewed_planner(root)
    planner.clean_checkout(root, project_revision)
    if digest(root / "scripts/bootstrap_comparator.sh") != BOOTSTRAP_SHA:
        raise CheckError("Original strict bootstrap script bytes changed")
    if digest(root / DESCRIPTOR) != DESCRIPTOR_SHA:
        raise CheckError("Original three-theorem descriptor changed")
    descriptor = json.loads((root / DESCRIPTOR).read_text())
    if (descriptor["challenge_module"], descriptor["solution_module"]) != ROOTS:
        raise CheckError("Descriptor roots differ from the original challenge")
    for folder, pin in PINS.items():
        planner.clean_checkout(root / folder, pin)
    plan, snapshot, modules = planner.make_plan(root, "full")
    # The reviewed full-scope audit imports only the original solution root.
    # Fail if that future audit changes scope; it is not executed here.
    proof_closure = descriptor_closure(plan, modules, planner)
    snapshot.add(root / DESCRIPTOR)
    snapshot.add(root / "scripts/bootstrap_comparator.sh")
    snapshot.add(Path(__file__).resolve())
    snapshot.add(Path(__file__).with_name("no_rebuild_landrun.py").resolve())
    for boundary in plan["trusted_external_imports"].values():
        olean = contained(root, root / boundary["olean"])
        snapshot.add(olean)
        # Record any matching companions already present in the trusted cache.
        for suffix in (".server", ".private"):
            companion = olean.with_name(olean.name + suffix)
            if companion.is_file():
                snapshot.add(contained(root, companion))
    provenance_path = root / ".tools/linux-verification/checker-provenance.json"
    provenance = json.loads(provenance_path.read_text())
    snapshot.add(provenance_path)
    validate_provenance(provenance, planner.TOOLCHAIN)
    for name, expected in provenance["binary_sha256"].items():
        binary = root / ".tools/verification-bin" / name
        contained(root, binary)
        if digest(binary) != expected:
            raise CheckError(f"Checker executable changed: {name}")
        snapshot.add(binary)
    snapshot.check(rehash=True)
    plan.update(schema_version=2, status="planned_only", descriptor=DESCRIPTOR,
                descriptor_sha256=DESCRIPTOR_SHA, project_revision=project_revision,
                roots=list(ROOTS), modules=[{"name": m.name, "source": str(m.source.relative_to(root)),
                                            "imports": list(m.imports)} for m in proof_closure],
                input_sha256=snapshot.record(), checker_provenance=provenance,
                trust_boundary="zero project files at total run start; only own serial sandbox objects subsequently reused",
                comparison="unchanged pinned Comparator; Lake calls fail closed with --no-build",
                commands=[], axiom_audit="not separately executed; pinned Comparator performs its checks")
    return plan, snapshot, proof_closure, planner

def service_prefix(root: Path, environment: dict[str, str]) -> list[str]:
    return ["systemd-run", "--user", "--wait", "--pipe", "--collect", "--quiet",
            "--property=RestrictAddressFamilies=~AF_UNIX", "--property=NoNewPrivileges=yes",
            "--working-directory", str(root / "formal"),
            *[part for key, value in environment.items() for part in ("-E", f"{key}={value}")], "--"]

def sandbox_command(root: Path, lake: Path, git: Path, path: str, options: list[str]) -> list[str]:
    # Exact pinned safeLakeBuild filesystem/executable/env rules. --best-effort
    # is removed only by the unchanged recorded strict adapter.
    return [*service_prefix(root, {"PATH": path, "LEAN_ABORT_ON_PANIC": "1"}),
            str(root / ".tools/verification-bin/landrun"), "--best-effort", "--ro", "/",
            "--rw", "/dev", "-ldd", "-add-exec", "--env", "PATH", "--env", "HOME",
            "--env", "LEAN_ABORT_ON_PANIC", "--ro", str(root / "formal"),
            "--rwx", str(root / "formal/.lake"), "--rox", str(lake.parent.parent),
            "--rox", str(git), "--", str(lake), *options]

def compare_command(root: Path, lake: Path, path: str, adapter: Path) -> list[str]:
    env = {"PATH": path, "ELAN_HOME": str(root / ".tools/elan"),
           "MATHLIB_CACHE_DIR": str(root / ".tools/mathlib-cache"),
           "COMPARATOR_LANDRUN": str(adapter),
           "COMPARATOR_LEAN4EXPORT": str(root / ".tools/verification-bin/lean4export")}
    return [*service_prefix(root, env), str(lake), "env",
            str(root / ".tools/verification-bin/comparator"), "../" + DESCRIPTOR]

def object_owner(relative: str) -> str | None:
    prefix = "formal/.lake/build/lib/lean/"
    if relative.startswith(prefix):
        suffix = relative[len(prefix):]
        for ending in (".olean.private", ".olean.server", ".olean"):
            if suffix.endswith(ending):
                return suffix[:-len(ending)].replace("/", ".")
    return None

def original_probe_command(root: Path) -> list[str]:
    # Sourcing with the supported preflight argument runs the original case
    # arm, then calls its original real-Landrun probe body without bootstrap,
    # download, compilation, or any changed script bytes.
    return ["bash", "-c", 'source "$1" preflight; configure_paths; strict_landrun_probe',
            "strict-serial-probe", str(root / "scripts/bootstrap_comparator.sh")]

def compiler_pids(cgroup: Path, executables: set[Path], proc: Path = Path("/proc")) -> list[int]:
    """Observed processes only: sampling is telemetry, not the serial guarantee."""
    try:
        pids = (cgroup / "cgroup.procs").read_text().split()
    except FileNotFoundError:
        return []
    matches = []
    for value in pids:
        try:
            executable = (proc / value / "exe").resolve(strict=True)
        except FileNotFoundError:
            continue  # Process exited between the cgroup and procfs reads.
        if executable in executables:
            matches.append(int(value))
    return matches

class MeasuredRunner:
    """Durable stage logs, owned service deadline, sampled compiler telemetry.

    No other service/process is stopped. The mathematical dispatch bound comes
    from the pinned Lake dependency gate and exclusive immutable checkout;
    procfs sampling independently catches sustained violations, not every exec.
    """
    def __init__(self, root: Path, out: Path, plan: dict, wall_seconds: int):
        self.root, self.out, self.plan = root, out, plan
        self.deadline = time.monotonic() + wall_seconds
        self.token = uuid.uuid4().hex
        prefix = root / ".tools/elan/toolchains/leanprover--lean4---v4.34.1/bin"
        self.executables = {(prefix / name).resolve() for name in ("lean", "leanir")}

    def __call__(self, argv: list[str], label: str):
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise CheckError("Total checking wall-clock limit exhausted")
        entry = self.plan["commands"][-1]
        unit = None
        effective = list(argv)
        if argv[0] == "systemd-run":
            unit = f"math115-serial-{self.token}-{len(self.plan['commands']):04d}.service"
            effective[1:1] = [f"--unit={unit}", f"--property=RuntimeMaxSec={remaining:.3f}s"]
        entry.update(effective_argv=effective, owned_unit=unit,
                     sampled_heavy_compiler_peak=0, compiler_sampling_interval_seconds=0.25)
        stdout_path, stderr_path = (self.out / f"{label}.{stream}.log" for stream in ("stdout", "stderr"))
        cgroup = None
        next_query = 0.0
        process = None
        try:
            with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                process = subprocess.Popen(effective, cwd=self.root / "formal", stdout=stdout,
                                           stderr=stderr, start_new_session=True)
                entry["launcher_pid"] = process.pid
                save(self.out / "receipt.json", self.plan)
                while process.poll() is None:
                    if time.monotonic() >= self.deadline:
                        raise CheckError("Total checking wall-clock limit exhausted")
                    if unit and cgroup is None and time.monotonic() >= next_query:
                        query = subprocess.run(["systemctl", "--user", "show", unit,
                                                "--property=ControlGroup", "--value"],
                                               text=True, capture_output=True, timeout=5)
                        relative = query.stdout.strip()
                        if query.returncode == 0 and relative.startswith("/") and ".." not in Path(relative).parts:
                            cgroup = Path("/sys/fs/cgroup") / relative.lstrip("/")
                            entry["observed_cgroup"] = relative
                        next_query = time.monotonic() + 1
                    if cgroup is not None:
                        observed = compiler_pids(cgroup, self.executables)
                        entry["sampled_heavy_compiler_peak"] = max(entry["sampled_heavy_compiler_peak"], len(observed))
                        if len(observed) > 1:
                            entry["overlap_pids"] = observed
                            raise CheckError("Observed overlapping heavy compilers in this run's own service")
                    time.sleep(min(0.25, max(0.001, self.deadline - time.monotonic())))
                code = process.wait()
        except BaseException:
            if unit:
                # Stop only our exact randomly named unit, whose RuntimeMaxSec
                # also enforces the deadline if this launcher is interrupted.
                try:
                    cleanup = subprocess.run(["systemctl", "--user", "stop", unit], capture_output=True, timeout=15)
                    entry["owned_unit_stop_returncode"] = cleanup.returncode
                except (OSError, subprocess.TimeoutExpired) as cleanup_error:
                    entry["owned_unit_stop_error"] = str(cleanup_error)
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait(timeout=5)
            raise
        finally:
            for stream, file in (("stdout", stdout_path), ("stderr", stderr_path)):
                if file.is_file():
                    entry[f"{stream}_sha256"] = digest(file)
            save(self.out / "receipt.json", self.plan)
        # Comparator's small status log contains the required acceptance
        # markers; other stages need no in-memory copies of compiler output.
        output = stdout_path.read_text(errors="replace") if label == "unchanged_comparator" else ""
        return subprocess.CompletedProcess(effective, code, output, "")

def run_check(root: Path, plan: dict, snapshot, modules: list, out: Path,
              runner: Callable[[list[str], str], subprocess.CompletedProcess],
              wall_seconds: int = 43200) -> None:
    # The trusted operator must keep all non-cooperating compilers out of this
    # dedicated checkout. The CLI's lock sits outside sandbox-writable .lake.
    plan.update(wall_seconds=wall_seconds, started_unix=time.time())
    deadline = time.monotonic() + wall_seconds
    lake = root / ".tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake"
    path = os.pathsep.join([str(root / ".tools/verification-bin"), str(lake.parent),
                           str(root / ".tools/elan/bin"), os.environ.get("PATH", "")])
    git = Path(shutil.which("git", path=path) or "/usr/bin/git").resolve()
    previous = inventory(root)
    def step(label: str, argv: list[str], module: str | None = None):
        if time.monotonic() >= deadline:
            raise CheckError("Total checking wall-clock limit exhausted")
        snapshot.check(rehash=True)
        entry = {"stage": label, "module": module, "argv": argv,
                 "started_unix": time.time(), "status": "running"}
        plan["commands"].append(entry); save(out / "receipt.json", plan)
        try:
            result = runner(argv, label)
            entry.update(returncode=result.returncode, status="passed" if result.returncode == 0 else "failed",
                         elapsed_seconds=time.time()-entry["started_unix"])
            snapshot.check(rehash=True)
            if result.returncode:
                raise CheckError(f"{label} failed; no later compile/comparison authorized")
            return result
        finally:
            save(out / "receipt.json", plan)
    try:
        plan["fresh_start"] = fresh_start(root)
        snapshot.check(rehash=True)
        plan.update(status="running")
        save(out / "receipt.json", plan)
        step("original_linux_and_landrun_preflight", original_probe_command(root))
        if inventory(root):
            raise CheckError("Preflight unexpectedly produced project build files")
        for index, module in enumerate(modules):
            name = module.name
            step(f"{index:04d}_dependencies_current", sandbox_command(root, lake, git, path,
                 ["--no-cache", "--no-build", "build", f"+{name}:deps"]), name)
            before = inventory(root)
            if before != previous:
                raise CheckError("Project build files changed outside the recorded serial compiler")
            step(f"{index:04d}_module_build", sandbox_command(root, lake, git, path,
                 ["--no-cache", "--fail-fast", "build", f"+{name}:olean"]), name)
            after = inventory(root)
            if any(n not in after for n in before):
                raise CheckError("Serial compiler removed an earlier project's artifact")
            changed = {n: h for n, h in after.items() if before.get(n) != h}
            if any(object_owner(n) not in {None, name} for n in changed):
                raise CheckError("Selected module compiler changed another project's proof object")
            if not any(object_owner(n) == name for n in changed):
                raise CheckError("Selected serial compiler produced no recorded project proof object")
            plan["commands"][-1]["output_sha256"] = changed
            plan["commands"][-1]["project_build_inventory_sha256"] = hashlib.sha256(
                json.dumps(after, sort_keys=True).encode()).hexdigest()
            previous = after; save(out / "receipt.json", plan)
        # Check the exact default targets that pinned Comparator will request,
        # not merely the helper's olean facet. Lake decides trace compatibility.
        step("comparator_targets_no_rebuild", sandbox_command(root, lake, git, path,
             ["--no-cache", "--no-build", "build", *ROOTS]))
        if inventory(root) != previous:
            raise CheckError("Final trace check modified project artifacts")
        step("original_precomparison_landrun_preflight", original_probe_command(root))
        if inventory(root) != previous:
            raise CheckError("Precomparison probe modified project artifacts")
        adapter = out / "no_rebuild_landrun.py"
        shutil.copyfile(Path(__file__).with_name("no_rebuild_landrun.py"), adapter)
        adapter.chmod(0o755)
        save(out / "no-rebuild-config.json", {"strict_adapter": str(root / ".tools/verification-bin/landrun"),
             "lake": str(lake), "roots": list(ROOTS),
             "exporter": str(root / ".tools/verification-bin/lean4export")})
        plan["resource_adapter_sha256"] = digest(adapter)
        plan["resource_adapter_config_sha256"] = digest(out / "no-rebuild-config.json")
        # Pinned Comparator executes this trusted adapter directly under the
        # same user-service restrictions. It delegates the real strict sandbox
        # and uses --no-build on every exact Comparator Lake build invocation.
        result = step("unchanged_comparator", compare_command(root, lake, path, adapter))
        required = ("Running Lean default kernel on solution.",
                    "Lean default kernel accepts the solution", "Your solution is okay!")
        if not all(message in (result.stdout or "") for message in required):
            raise CheckError("Comparator exited zero without kernel and comparison acceptance evidence")
        if inventory(root) != previous:
            raise CheckError("Comparator changed project build artifacts despite no-build enforcement")
        snapshot.check(rehash=True)
        plan.update(status="comparison_passed", completed_unix=time.time(),
                    final_project_output_sha256=inventory(root))
    except BaseException as error:
        plan.update(status="interrupted" if isinstance(error, (KeyboardInterrupt, SystemExit)) else "failed",
                    stopped_unix=time.time(), error=str(error).replace(str(root), "<CHECKOUT>"))
        raise
    finally:
        save(out / "receipt.json", plan)

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--project-revision", required=True)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--wall-seconds", type=int, default=43200,
                        help="total run cap, including serial build and comparison (maximum 12h)")
    args = parser.parse_args()
    if args.plan == args.execute:
        parser.error("choose exactly --plan or --execute")
    if not 1 <= args.wall_seconds <= 43200:
        parser.error("wall-seconds must be between 1 and 43200")
    if fcntl is None:
        raise CheckError("This orchestration CLI requires a POSIX file lock")
    root = args.root.resolve(); out = contained(root, args.output.resolve())
    # Reports/adapters remain beyond every sandbox-writable project path.
    if not out.is_relative_to(root / ".tools/linux-verification"):
        raise CheckError("Output must be under trusted .tools/linux-verification")
    if out.exists():
        raise CheckError("Output exists; no duplicate or resume with partial objects")
    out.mkdir(parents=True)
    lock_path = root / ".tools/linux-verification/serial-comparator.lock"
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        plan, snapshot, modules, _ = make_plan(root, args.project_revision)
        save(out / "plan.json", plan)
        if args.plan:
            print(f"Planned {len(modules)} modules only; no Lean/Lake/checker invocation.")
            return 0
        if platform.system() != "Linux" or platform.machine() != "x86_64" or os.getuid() == 0:
            raise CheckError("Execution requires non-root Linux x86_64")
        runner = MeasuredRunner(root, out, plan, args.wall_seconds)
        run_check(root, plan, snapshot, modules, out, runner, args.wall_seconds)
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CheckError, OSError, ValueError, KeyError) as error:
        print(f"Strict serial check stopped: {error}", file=sys.stderr)
        raise SystemExit(1)
