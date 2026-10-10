#!/usr/bin/env python3
"""Build this repository's selected Lean import closure one module at a time.

The planner reads source files; --plan never invokes Lake or Lean.  At execution
time Lake, not this script, decides whether artifacts and dependency traces are
current.  Cached external packages remain an explicit trust boundary.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Callable

try:
    import fcntl
except ImportError:  # Native Windows can still import the parser and mock tests.
    fcntl = None

UPSTREAM_REV = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
MATHLIB_REV = "d13f23b723b8a846827a245b89c10fc7d3f11612"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
ROOTS = {
    "standalone": (
        "Math115.QuadraticCoefficient",
        "Math115.GlobalDisplayOwnership",
        "Math115.RepairCoefficient",
    ),
    "focused": (
        "OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafEnergy",
        "OAI.Combinatorics.ContingencyTables.Transport.IntegerRootTransport",
        "Math115",
    ),
    "full": (
        "OAI.Combinatorics.ContingencyTables.UnconditionalMain",
        "ComparatorChallenges.ContingencyTables",
    ),
}
AUDITS = {
    "standalone": "Math115/StandaloneAxiomAudit.lean",
    "focused": "Math115/AxiomAudit.lean",
    "full": "Math115/UpstreamAxiomAudit.lean",
}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


class BuildError(RuntimeError):
    """A failed precondition, source change, or nonzero Lake result."""


def now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_imports(source: str) -> tuple[str, ...]:
    """Read the pinned Lean header grammar, rejecting unsupported import names.

    Handles nested comments and the `module`, `prelude`, `public`, `meta`, and
    `all` modifiers from Lean 4.34.1's Parser/Module/Syntax.lean.  This deliberately
    supports the ASCII module names used by our pinned inputs; quoted or Unicode
    import identifiers fail clearly instead of being silently omitted.  Only the
    header is scanned, so strings, quotations, and comments in proof bodies are
    irrelevant.  Compilation remains Lean's job.
    """
    pos = 0

    def token() -> str:
        nonlocal pos
        while pos < len(source):
            if source[pos].isspace() or (pos == 0 and source[pos] == "\ufeff"):
                pos += 1
            elif source.startswith("--", pos):
                end = source.find("\n", pos)
                pos = len(source) if end < 0 else end + 1
            elif source.startswith("/-", pos):
                pos += 2
                depth = 1
                while depth and pos < len(source):
                    if source.startswith("/-", pos):
                        depth += 1
                        pos += 2
                    elif source.startswith("-/", pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
                if depth:
                    raise BuildError("Unterminated comment in Lean module header")
            else:
                start = pos
                while pos < len(source) and not source[pos].isspace():
                    if source.startswith(("--", "/-"), pos):
                        break
                    pos += 1
                return source[start:pos]
        return ""

    word = token()
    is_module = word == "module"
    if is_module:
        word = token()
    prelude = word == "prelude"
    if prelude:
        word = token()
    imports = [] if prelude else ["Init"]
    while word in {"public", "meta", "import"}:
        public = word == "public"
        if public:
            word = token()
        meta = word == "meta"
        if meta:
            word = token()
        if word != "import":
            # `public section`, `meta def`, etc. begin the command body.
            break
        word = token()
        all_import = word == "all"
        if all_import:
            word = token()
        if (public or meta or all_import) and not is_module:
            raise BuildError("Import modifiers require the Lean `module` header")
        if public and all_import:
            raise BuildError("Lean does not permit `public import all`")
        if not MODULE_NAME.fullmatch(word):
            raise BuildError(f"Unsupported or missing import module name: {word!r}")
        imports.append(word)
        word = token()
    return tuple(dict.fromkeys(imports))


@dataclass(frozen=True)
class Module:
    name: str
    source: Path
    imports: tuple[str, ...]


def dependency_order(roots: tuple[str, ...], resolve: Callable[[str], Module | None]) -> list[Module]:
    """Iterative DFS; None denotes a validated trusted external boundary."""
    order: list[Module] = []
    colors: dict[str, int] = {}
    modules: dict[str, Module] = {}
    for root in roots:
        stack = [(root, False)]
        while stack:
            name, leaving = stack.pop()
            if leaving:
                colors[name] = 2
                order.append(modules[name])
                continue
            if colors.get(name) == 2:
                continue
            if colors.get(name) == 1:
                raise BuildError(f"Import cycle reaches {name}")
            mod = resolve(name)
            if mod is None:
                colors[name] = 2
                continue
            colors[name] = 1
            modules[name] = mod
            stack.append((name, True))
            stack.extend((dep, False) for dep in reversed(mod.imports))
    return order


class Snapshot:
    def __init__(self, root: Path):
        self.root = root
        self.hashes: dict[Path, str] = {}
        self.stats: dict[Path, tuple[int, int]] = {}

    def add(self, path: Path) -> str:
        digest = sha256(path)
        if path in self.hashes and self.hashes[path] != digest:
            raise BuildError(f"Input changed during planning: {path.relative_to(self.root)}")
        stat = path.stat()
        self.hashes[path] = digest
        self.stats[path] = (stat.st_size, stat.st_mtime_ns)
        return digest

    def check(self, *, rehash: bool = False) -> None:
        for path, digest in self.hashes.items():
            try:
                stat = path.stat()
                current = (stat.st_size, stat.st_mtime_ns)
                if rehash or current != self.stats[path]:
                    if sha256(path) != digest:
                        raise BuildError(f"Source/configuration changed: {path.relative_to(self.root)}")
                    self.stats[path] = current
            except FileNotFoundError as exc:
                raise BuildError(f"Input disappeared: {path.relative_to(self.root)}") from exc

    def record(self) -> dict[str, str]:
        return {str(p.relative_to(self.root)): self.hashes[p] for p in sorted(self.hashes)}


def git(checkout: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(checkout), *args], text=True, capture_output=True)
    if result.returncode:
        raise BuildError(f"Git check failed: {checkout.name}: {' '.join(args)}")
    return result.stdout.strip()


def clean_checkout(checkout: Path, revision: str) -> set[str]:
    if git(checkout, "rev-parse", "HEAD") != revision:
        raise BuildError(f"Wrong pinned revision: {checkout.name}")
    git(checkout, "diff", "--quiet")
    git(checkout, "diff", "--cached", "--quiet")
    return set(git(checkout, "ls-files", "-z").split("\0"))


def make_plan(root: Path, scope: str) -> tuple[dict, Snapshot, list[Module]]:
    formal = root / "formal"
    upstream = root / ".upstream/openai-math"
    snapshot = Snapshot(root)
    upstream_files = clean_checkout(upstream, UPSTREAM_REV)
    for path in (formal / "lean-toolchain", upstream / "lean/lean-toolchain"):
        snapshot.add(path)
        if path.read_text().strip() != TOOLCHAIN:
            raise BuildError("The serial builder requires the unchanged pinned Lean toolchain")
    for path in (formal / "lakefile.lean", formal / "lake-manifest.json",
                 root / "scripts/verify_lean.sh", Path(__file__).resolve()):
        snapshot.add(path)
    manifest = json.loads((formal / "lake-manifest.json").read_text())
    if manifest.get("packagesDir") != ".lake/packages":
        raise BuildError("Unsupported packagesDir; review the serial builder's module mapping")
    packages = []
    pins = {}
    for entry in manifest["packages"]:
        name, revision = entry["name"], entry["rev"]
        if (entry["type"] != "git" or entry.get("subDir") is not None
                or not re.fullmatch(r"[A-Za-z0-9_-]+", name)
                or not re.fullmatch(r"[0-9a-f]{40}", revision)):
            raise BuildError("Unsupported manifest entry; review dependency resolution")
        path = formal / ".lake/packages" / name
        tracked = clean_checkout(path, revision)
        for config in (entry.get("configFile"), entry.get("manifestFile")):
            if config and (path / config).is_file():
                snapshot.add(path / config)
        packages.append((name, path, tracked))
        pins[name] = revision
    if pins.get("mathlib") != MATHLIB_REV:
        raise BuildError("Mathlib revision differs from the reviewed pin")
    toolchain_dir = root / ".tools/elan/toolchains/leanprover--lean4---v4.34.1"
    for name in ("lean", "lake"):
        binary = toolchain_dir / "bin" / name
        if not binary.is_file():
            raise BuildError("Pinned toolchain is absent; run scripts/bootstrap_lean.sh first")
        snapshot.add(binary)
    boundaries: dict[str, dict] = {}

    def resolve(name: str) -> Module | None:
        if not MODULE_NAME.fullmatch(name):
            raise BuildError(f"Unsupported module name: {name!r}")
        relative = Path(*name.split(".")).with_suffix(".lean")
        namespace = name.split(".", 1)[0]
        if namespace == "Math115":
            path = formal / relative
        elif namespace in {"OAI", "ComparatorChallenges"}:
            path = upstream / "lean" / relative
            if str(Path("lean") / relative) not in upstream_files:
                raise BuildError(f"Import is absent from the pinned upstream tree: {name}")
        else:
            if name in boundaries:
                return None
            olean_rel = relative.with_suffix(".olean")
            candidates = []
            for package_name, package, tracked in packages:
                if str(relative) in tracked:
                    candidates.append((package_name, package / relative,
                                       package / ".lake/build/lib/lean" / olean_rel))
            built_in = toolchain_dir / "lib/lean" / olean_rel
            if built_in.is_file():
                candidates.append(("Lean toolchain", None, built_in))
            if len(candidates) != 1:
                raise BuildError(f"Missing or ambiguous external import {name}; bootstrap the pinned dependencies")
            owner, source, olean = candidates[0]
            if not olean.is_file():
                raise BuildError(f"Trusted cache is missing {name}; run scripts/bootstrap_lean.sh first")
            if source is not None:
                snapshot.add(source)
            boundaries[name] = {
                "owner": owner, "olean": str(olean.relative_to(root)),
                "trust": "existing toolchain/package artifact; checked by Lake --no-build at execution",
            }
            return None
        if not path.is_file():
            raise BuildError(f"Missing local module {name}: {path.relative_to(root)}")
        snapshot.add(path)
        return Module(name, path, lean_imports(path.read_text()))

    audit = formal / AUDITS[scope]
    snapshot.add(audit)
    roots = tuple(dict.fromkeys((*ROOTS[scope], *lean_imports(audit.read_text()))))
    modules = dependency_order(roots, resolve)
    snapshot.check(rehash=True)
    plan = {
        "schema_version": 1, "created_at": now(), "scope": scope,
        "status": "planned_only", "axiom_audit": "not_run_by_this_helper",
        "trust_boundary": "Official Mathlib/dependency cache and Lean bootstrap binaries remain trusted; not Comparator replay",
        "upstream_revision": UPSTREAM_REV, "lean_toolchain": TOOLCHAIN,
        "package_revisions": pins, "roots": list(roots),
        "audit_source": str(audit.relative_to(root)),
        "modules": [{"name": m.name, "source": str(m.source.relative_to(root)),
                     "imports": list(m.imports)} for m in modules],
        "trusted_external_imports": dict(sorted(boundaries.items())),
        "input_sha256": snapshot.record(), "commands": [],
    }
    return plan, snapshot, modules


def write_report(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def run_serial(root: Path, plan: dict, snapshot: Snapshot, modules: list[Module],
               report_path: Path, *, runner: Callable = subprocess.run) -> None:
    lake = root / ".tools/elan/bin/lake"
    env = os.environ.copy()
    env.update(ELAN_HOME=str(root / ".tools/elan"), ELAN_TOOLCHAIN=TOOLCHAIN,
               MATHLIB_CACHE_DIR=str(root / ".tools/mathlib-cache"))
    # Let the pinned Lake workspace construct its module path.
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    plan.update(status="running", started_at=now())
    write_report(report_path, plan)
    try:
        for index, mod in enumerate(modules, 1):
            print(f"Serial module {index}/{len(modules)}: {mod.name}", flush=True)
            for stage, options in (
                ("dependencies_current", ["--no-cache", "--no-build", "build", f"+{mod.name}:deps"]),
                ("module_build", ["--no-cache", "build", f"+{mod.name}:olean"]),
            ):
                snapshot.check()
                command = {"module": mod.name, "stage": stage, "argv": ["lake", *options],
                           "started_at": now(), "status": "running"}
                plan["commands"].append(command)
                write_report(report_path, plan)
                started = time.monotonic()
                result = runner([str(lake), *options], cwd=root / "formal", env=env)
                command.update(returncode=result.returncode, elapsed_seconds=round(time.monotonic() - started, 3),
                               status="passed" if result.returncode == 0 else "failed")
                write_report(report_path, plan)
                if result.returncode:
                    if stage == "dependencies_current":
                        raise BuildError(f"Dependency preflight failed for {mod.name}; no compile was authorized. "
                                         "Restore the pinned cache or rebuild changed imports serially in an exclusive checkout.")
                    raise BuildError(f"Lake compilation failed for {mod.name} (exit {result.returncode})")
                snapshot.check()
        snapshot.check(rehash=True)
        plan.update(status="build_completed", completed_at=now())
        print("Serial module builds completed. The calling verification script must still run its axiom audit.", flush=True)
    except BaseException as exc:
        plan.update(status="interrupted" if isinstance(exc, (KeyboardInterrupt, SystemExit)) else "failed",
                    stopped_at=now(), error=str(exc).replace(str(root), "<workspace>"))
        raise
    finally:
        write_report(report_path, plan)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scope", choices=tuple(ROOTS))
    parser.add_argument("--plan", action="store_true", help="Write the import plan without invoking Lake or Lean")
    parser.add_argument("--report", type=Path, help="JSON provenance output (default formal/results/<scope>-serial[-plan].json)")
    args = parser.parse_args()
    if fcntl is None:
        print("Serial CLI execution requires Linux or macOS; parsing and mock tests remain portable.", file=sys.stderr)
        return 2
    root = Path(__file__).resolve().parent.parent
    suffix = "-serial-plan.json" if args.plan else "-serial.json"
    report_path = args.report or root / "formal/results" / (args.scope + suffix)
    # This lock prevents two instances of this helper. Other compiler invocations
    # must also be kept out of this checkout by the operator.
    lock_path = root / "formal/.lake/math115-serial.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with lock_path.open("a") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise BuildError("Another serial verifier is using this checkout") from exc
            plan, snapshot, modules = make_plan(root, args.scope)
            write_report(report_path, plan)
            print(f"Planned {len(modules)} local modules; {len(plan['trusted_external_imports'])} trusted external imports.", flush=True)
            if args.plan:
                print("Planning only: no Lake/Lean process or axiom audit was run.", flush=True)
            else:
                run_serial(root, plan, snapshot, modules, report_path)
    except (BuildError, OSError, ValueError, KeyError) as exc:
        print(f"Serial verification stopped: {str(exc).replace(str(root), '<workspace>')}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
