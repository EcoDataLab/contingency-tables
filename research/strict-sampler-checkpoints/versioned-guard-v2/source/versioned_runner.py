#!/usr/bin/env python3
"""Separate strict sampler runner. Plan/execute need out-of-band frozen hashes.

Private version2 candidate: not installed or launch-authorized.
Trusted supervisor maintains an exclusive quiet checking/cache context. The
selected-cache traversal is anchored and preserves three leaf observations;
it does not claim arbitrary transient race/error trace equivalence.
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
import stat
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
METADATA_SHA = '6eb447ff60a09d13bc134252e490bd99e7a15b92c7436a0db5a677269b91a3a5'
GUARD_VERSION = "anchored-selected-cache-v2"

def load_metadata():
    helper = HERE / "anchored_metadata.py"
    require(sha(helper) == METADATA_SHA, "Anchored metadata implementation changed")
    spec = importlib.util.spec_from_file_location("pinned_anchored_metadata_v2", helper)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

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
LEAN_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
CONFIG_SOURCES = {
    "formal/lakefile.lean": "3583edf9de94982194b653696fb502624efe2f73836f8f07b227d8fd4a0794af",
    "formal/.lake/packages/mathlib/lakefile.lean": "274e720ccc7dbabeb9fbf362290dc7e5ed2c5175fbade0ef20cc19b1331affaf",
    "formal/.lake/packages/proofwidgets/lakefile.lean": "0a319fffbf511dab4c3307dc105f8e8fdb4f6160020995cef5f442061cc0abca",
    "formal/.lake/packages/plausible/lakefile.toml": "4147957012320a3afe8f041662202b7a3453c8a0df4311c1698da029a3b4834f",
    "formal/.lake/packages/LeanSearchClient/lakefile.toml": "cb5d6c80c4ffd4b3be99294a911ebf2f6a2fee4eb9f840d96f0f813bd484c05d",
    "formal/.lake/packages/importGraph/lakefile.toml": "a48a5617c553b9fb528d6da7d4e15b1a61fff3326d6eab6399176d9e22e2bb53",
    "formal/.lake/packages/aesop/lakefile.toml": "054f79cdcc1a5e15d1856aac6bf3375cbe12de657926218962401efed2a08119",
    "formal/.lake/packages/Qq/lakefile.toml": "42826e4e06221f41fcd863e19d937a0a68be7d54df90abd7800a3c09f4557a15",
    "formal/.lake/packages/batteries/lakefile.toml": "acadcd8beb13a53a4ac9399e6706c829309d2380f338d13b037886666f978015",
    "formal/.lake/packages/Cli/lakefile.toml": "188aaec6ddb57f411c11b95c3ece85ff26ab9ae8085371fee47e1dc855c4e186",
}
# Source-derived pinned Lake reverse-direct-dependency traversal gives these
# Lean configuration slots; TOML configurations do not emit compiled OLeans.
CONFIG_SLOTS = {
    "0": ("[anonymous]", "formal/lakefile.lean", "a946bf7374de28d2", {}),
    "1": ("mathlib", "formal/.lake/packages/mathlib/lakefile.lean", "5fae05c6298a8b59", {}),
    "5": ("proofwidgets", "formal/.lake/packages/proofwidgets/lakefile.lean", "a4f8a6ba6807ecfe",
          {"errorOnBuild": "ProofWidgets failed to reuse pre-built JS code. Please report this issue on the Lean Zulip."}),
}
CONFIG_TOOLS = tuple(PREFIX + "/bin/" + n for n in ("lean", "leanir", "lake"))
CLI_CACHE = "formal/.lake/packages/Cli/.lake/build/lib/lean"
CLI_ABSENT = "formal/.lake/packages/Cli/.lake"
CACHE_IDENTITY_FIELDS = ("dev", "ino", "mode", "uid", "gid", "mtime_ns", "ctime_ns")
RUNTIME_FIELDS = {"schema_version", "status", "source_freeze_sha256", "trusted_files_sha256",
    "trusted_tool_aliases", "system_executables", "trusted_cache_roots", "trusted_cache_files_sha256",
    "external_import_resolution", "entrypoint_native_audit", "lake_configuration_provenance",
    "lake_configuration_provenance_binding", "lake_configuration_artifacts_sha256",
    "lake_configuration_artifacts_stat", "trusted_cache_states", "external_import_owners",
    "unused_cache_policy", "unused_cache_policy_binding"}
DIAGNOSTICS = False
_diag_started = 0.0
_diag_last = {}

def enable_diagnostics(enabled=False):
    global DIAGNOSTICS, _diag_started, _diag_last
    DIAGNOSTICS = bool(enabled)
    _diag_started, _diag_last = time.monotonic(), {}

def progress(stage, event, **fields):
    if DIAGNOSTICS:
        print("STRICT_AUTH_PROGRESS=" + json.dumps({"stage": stage, "event": event,
              "elapsed_seconds": round(time.monotonic() - _diag_started, 3), **fields}, sort_keys=True),
              file=sys.stderr, flush=True)

def progress_tick(stage, files, byte_count=0, **fields):
    if DIAGNOSTICS:
        now = time.monotonic()
        if now - _diag_last.get(stage, now) >= 5 or files % 1024 == 0:
            progress(stage, "heartbeat", files=files, bytes=byte_count, **fields)
            _diag_last[stage] = now
        else:
            _diag_last.setdefault(stage, now)

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
    progress("git", "begin", worktree=root.name, argv=list(args))
    r = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True, timeout=30)
    progress("git", "end", worktree=root.name, returncode=r.returncode)
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

def validate_unused_cache_policy(policy):
    require(set(policy) == {"schema_version", "source_freeze_sha256", "origin", "allowed_absence"}
            and type(policy["schema_version"]) is int and policy["schema_version"] == 1
            and policy["source_freeze_sha256"] == SOURCE_SHA, "Wrong unused-cache policy schema/source")
    require(set(policy["origin"]) == {"review_manifest_sha256", "stopped_checking_child_sha256"}
            and all(isinstance(v, str) and SHA.fullmatch(v) for v in policy["origin"].values()),
            "Unbound unused-cache policy origin")
    require(policy["allowed_absence"] == {CLI_CACHE: {"first_missing": CLI_ABSENT, "required_owner": "Cli"}},
            "Unused-cache policy exceeds exact Cli .lake absence")

def cache_identity(value):
    return {name: getattr(value, "st_" + name) for name in CACHE_IDENTITY_FIELDS}

def cache_root_states(root, roots, owners, policy):
    """Only ENOENT at the nominated ancestor represents an allowed absence.

    Every existing component is inspected without following links. Files,
    dangling links and any other filesystem errors are never absence evidence.
    Parent identity binds even creation/removal that ends absent again.
    """
    validate_unused_cache_policy(policy)
    require(isinstance(owners, list) and owners == sorted(set(owners))
            and all(isinstance(x, str) for x in owners), "Invalid required owner set")
    require("Cli" not in owners, "Unused Cli cache has a required source owner")
    require(len(roots) == len(set(roots)) and CLI_CACHE in roots, "Incomplete/duplicate cache root state request")
    return {name: cache_root_state(root, name) for name in roots}

def cache_root_state(root, name):
    relative(root, name)  # Preserve original lexical/containment/link guard.
    current = root
    parent_stat = root.lstat()
    require(stat.S_ISDIR(parent_stat.st_mode), "Cache checkout root is not a regular directory")
    for part in PurePosixPath(name).parts:
        current = current / part
        component = str(current.relative_to(root))
        try:
            observed = current.lstat()
        except FileNotFoundError:
            require(name == CLI_CACHE and component == CLI_ABSENT,
                    "Unexpected missing trusted cache component: " + component)
            return {"state": "absent", "first_missing": component,
                    "parent": str(current.parent.relative_to(root)),
                    "parent_identity": cache_identity(parent_stat)}
        require(stat.S_ISDIR(observed.st_mode), "Nondirectory/symlink trusted cache component: " + component)
        parent_stat = observed
    require(name != CLI_CACHE, "Nominated Cli .lake absence became present")
    return {"state": "directory", "identity": cache_identity(observed)}

def validate_cache_state_shapes(states, roots):
    require(isinstance(states, dict) and set(states) == set(roots), "Cache state keyset differs")
    for name, row in states.items():
        required = {"state", "first_missing", "parent", "parent_identity"} if name == CLI_CACHE else {"state", "identity"}
        require(isinstance(row, dict) and set(row) == required, "Mixed/unexpected cache state fields")
        if name == CLI_CACHE:
            require(row["state"] == "absent" and row["first_missing"] == CLI_ABSENT
                    and row["parent"] == "formal/.lake/packages/Cli", "Wrong Cli absence state")
            identity = row["parent_identity"]
        else:
            require(row["state"] == "directory", "Other cache root may not be absent")
            identity = row["identity"]
        require(isinstance(identity, dict) and set(identity) == set(CACHE_IDENTITY_FIELDS)
                and all(type(x) is int for x in identity.values()), "Wrong cache directory identity types")

def cache_inventory(root, roots, states=None):
    progress("cache_inventory", "begin", roots=len(roots))
    result = {}
    if states is not None:
        validate_cache_state_shapes(states, roots)
        require(cache_root_state(root, CLI_CACHE) == states[CLI_CACHE], "Cli absence identity differs before cache inventory")
    for name in roots:
        if states is not None and name == CLI_CACHE:
            progress("cache_inventory", "nominated_absence", root=name)
            continue  # Exact caller-bound state is rederived at every boundary.
        progress("cache_inventory", "root_begin", root=name)
        _diag_files, _diag_bytes = 0, 0
        base = relative(root, name)
        require(stat.S_ISDIR(base.lstat().st_mode), "Missing trusted import-cache directory")
        pending = [base]
        while pending:
            directory = pending.pop()
            before = directory.lstat()
            require(stat.S_ISDIR(before.st_mode), "Nonregular/symlink cache directory")
            # scandir/stat errors propagate; rglob would suppress some errors.
            with os.scandir(directory) as entries:
                children = sorted(entries, key=lambda entry: entry.name)
            require(cache_identity(directory.lstat()) == cache_identity(before), "Cache directory changed during enumeration")
            for entry in children:
                path = directory / entry.name
                observed = entry.stat(follow_symlinks=False)
                if stat.S_ISDIR(observed.st_mode):
                    pending.append(path)
                else:
                    require(stat.S_ISREG(observed.st_mode), "Nonregular/symlink trusted cache entry")
                    if observed.st_size >= 64 * 1024 * 1024:
                        progress("cache_inventory", "large_file_begin", root=name, file=str(path.relative_to(root)), bytes=observed.st_size)
                    result[str(path.relative_to(root))] = sha(path)
                    require(cache_identity(path.lstat()) == cache_identity(observed), "Cache entry changed during hashing")
                    _diag_files += 1; _diag_bytes += observed.st_size
                    progress_tick("cache_inventory", _diag_files, _diag_bytes, root=name)
                    if observed.st_size >= 64 * 1024 * 1024:
                        progress("cache_inventory", "large_file_end", root=name, file=str(path.relative_to(root)), bytes=observed.st_size)
        progress("cache_inventory", "root_end", root=name, files=_diag_files, bytes=_diag_bytes)
    if states is not None:
        require(cache_root_state(root, CLI_CACHE) == states[CLI_CACHE], "Cli absence identity drift during cache inventory")
    progress("cache_inventory", "end", files=len(result))
    return result

def resolve_external_imports(root, freeze, packages):
    """Same exactly-one source/object rules, rederived from tracked sources."""
    external, source_hashes, owners = {}, {}, set()
    progress("external_resolution", "begin", imports=len(freeze["external_imports"]))
    for name in freeze["external_imports"]:
        rel = name.replace(".", "/")
        candidates = []
        builtin = relative(root, PREFIX + "/lib/lean/" + rel + ".olean")
        if builtin.is_file():
            candidates.append((str(builtin.relative_to(root)), None, "<toolchain>"))
        for owner, (package, tracked) in packages.items():
            if rel + ".lean" in tracked:
                obj = relative(root, str((package / ".lake/build/lib/lean" / (rel + ".olean")).relative_to(root)))
                require(obj.is_file(), "Direct trusted import object missing: " + name)
                source = relative(root, str((package / (rel + ".lean")).relative_to(root)))
                candidates.append((str(obj.relative_to(root)), str(source.relative_to(root)), owner))
                source_hashes[str(source.relative_to(root))] = sha(source)
        require(len(candidates) == 1, "Missing or ambiguous direct external import: " + name)
        external[name] = {"olean": candidates[0][0], "source": candidates[0][1]}
        owners.add(candidates[0][2])
    progress("external_resolution", "end", imports=len(external), owners=sorted(owners))
    return external, source_hashes, sorted(owners)

def no_hidden_objects(root, cache_roots, allow_own_build=False, configuration_files=None):
    progress("hidden_objects", "begin")
    _diag_visited, _diag_skipped = 0, 0
    build = root / "formal/.lake/build"
    bases = [root / "formal", root / ".upstream/openai-math/lean", root / ".upstream/openai-math/.lake/build"]
    packages = root / "formal/.lake/packages"
    for base in bases:
        if not base.exists():
            continue
        progress("hidden_objects", "tree_begin", tree=str(base.relative_to(root)))
        for path in base.rglob("*"):
            _diag_visited += 1
            progress_tick("hidden_objects", _diag_visited, package_entries_skipped=_diag_skipped)
            if path.is_relative_to(packages):
                _diag_skipped += 1
                continue
            require(not path.is_symlink(), "Symlinked submitted tree")
            if not path.is_file() or not path.name.endswith((*FACETS, ".c")):
                continue
            name = str(path.relative_to(root))
            if name in {"formal/.lake/config/" + slot + "/lakefile.olean" for slot in CONFIG_SLOTS}:
                require((configuration_files or {}).get(name) == sha(path), "Unbound indexed Lake configuration")
                continue
            if allow_own_build and path.is_relative_to(build):
                continue
            raise Reject("Submitted proof artifact outside owned fresh build: " + str(path.relative_to(root)))
    for name in cache_roots:
        base = relative(root, name)
        for namespace in ("Math115", "OAI", "ComparatorChallenges"):
            require(not (base / namespace).exists(), "Submitted namespace hidden in trusted cache")
    progress("hidden_objects", "end", visited=_diag_visited, package_entries_skipped=_diag_skipped)

class Guard:
    def __init__(self, root, sources, tools, caches, serial, config_roots=(), config_files=None, system_executables=None, tool_aliases=None, config_provenance=None, config_stats=None, cache_roots=(), cache_states=None, external_owners=None, unused_cache_policy=None):
        self.root, self.sources, self.tools, self.caches = root, sources, tools, caches
        self._metadata_index = load_metadata().FrozenMetadataIndex(caches, require)
        self.serial = serial
        self.config_roots, self.config_files = config_roots, config_files or {}
        self.system_executables = system_executables or {}
        self.tool_aliases = tool_aliases
        self.config_provenance = config_provenance
        self.config_stats = config_stats
        self.cache_roots, self.cache_states = cache_roots, cache_states
        self.external_owners, self.unused_cache_policy = external_owners, unused_cache_policy
        require(not cache_roots or cache_states is not None, "Unbound cache state guard")
        require(not (set(tools) & set(TOOL_ALIASES)) or tool_aliases is not None, "Unbound bootstrap alias guard")
    def add(self, path):
        self.tools[str(path.relative_to(self.root))] = sha(path)
    def check(self, rehash=False):
        progress("guard", "begin", rehash=rehash)
        if self.cache_states is not None:
            validate_cache_state_shapes(self.cache_states, self.cache_roots)
            require(cache_root_states(self.root, self.cache_roots, self.external_owners, self.unused_cache_policy)
                    == self.cache_states, "Trusted cache directory/absence identity drift")
        configuration = indexed_configuration_inventory(self.root, self.config_provenance) if self.config_provenance is not None else configuration_inventory(self.root, self.config_roots)
        require(configuration == self.config_files, "Lake configuration artifact inventory changed")
        if self.config_stats is not None:
            require(configuration_stats(self.root, configuration) == self.config_stats, "Lake configuration identity changed")
        for name, item in self.system_executables.items():
            actual = shutil.which(name)
            require(actual is not None and str(Path(actual).resolve()) == item["path"] and sha(Path(item["path"])) == item["sha256"], "System command resolution/bytes changed: " + name)
        if self.tool_aliases is not None:
            require(tool_alias_inventory(self.root) == self.tool_aliases, "Bootstrap alias identity/target bytes changed")
        progress("guard", "sources_begin", files=len(self.sources))
        for name, digest in self.sources.items():
            path = relative(self.root, name)
            require(path.is_file() and sha(path) == digest, "Frozen source changed: " + name)
        progress("guard", "tools_begin", files=len(self.tools))
        for name, digest in self.tools.items():
            path = trusted_runtime_path(self.root, name)
            require(path.is_file() and sha(path) == digest, "Frozen tool changed: " + name)
        # Complete cache set is checked at admission and before/after Comparator.
        # At every serial stage all frozen cache entries retain their stat identity.
        progress("guard_cache", "begin", rehash=rehash, files=len(self.caches))
        observations = None if rehash else self._metadata_index.snapshot(
            self.root, {name: item[1] for name, item in self.caches.items()})
        _diag_files, _diag_bytes, _diag_root = 0, 0, None
        _diag_root_files, _diag_root_bytes = 0, 0
        for name, (digest, stat) in self.caches.items():
            if DIAGNOSTICS:
                _diag_current_root = next((x for x in self.cache_roots if name.startswith(x + "/")), "unlabelled-cache")
                if _diag_current_root != _diag_root:
                    if _diag_root is not None:
                        progress("guard_cache", "root_end", root=_diag_root, files=_diag_root_files, bytes=_diag_root_bytes)
                    progress("guard_cache", "root_begin", root=_diag_current_root)
                    _diag_root = _diag_current_root
                    _diag_root_files, _diag_root_bytes = 0, 0
            if rehash:
                path = relative(self.root, name)
                require(path.is_file(), "Trusted cache file vanished")
                current = path.stat()
            else:
                current = observations[name]
            require((current.st_size, current.st_mtime_ns, current.st_ctime_ns, current.st_ino) == stat,
                    "Trusted cache metadata changed: " + name)
            if rehash:
                if current.st_size >= 64 * 1024 * 1024:
                    progress("guard_cache", "large_file_begin", root=_diag_root, file=name, bytes=current.st_size)
                require(sha(path) == digest, "Trusted cache bytes changed")
                if current.st_size >= 64 * 1024 * 1024:
                    progress("guard_cache", "large_file_end", root=_diag_root, file=name, bytes=current.st_size)
            _diag_files += 1; _diag_bytes += current.st_size
            _diag_root_files += 1; _diag_root_bytes += current.st_size
            progress_tick("guard_cache", _diag_files, _diag_bytes, root=_diag_root, rehash=rehash)
        if _diag_root is not None:
            progress("guard_cache", "root_end", root=_diag_root, files=_diag_root_files, bytes=_diag_root_bytes)
        progress("guard_cache", "end", rehash=rehash, files=_diag_files, bytes=_diag_bytes)
        progress("guard", "end", rehash=rehash)

def configuration_inventory(root, roots):
    result = {}
    for name in roots:
        base = relative(root, name)
        for path in sorted(base.glob("lakefile.*")):
            require(not path.is_symlink(), "Symlinked Lake configuration artifact")
            if path.is_file():
                result[str(path.relative_to(root))] = sha(path)
    return result

def indexed_configuration_inventory(root, provenance):
    """No artifact may authenticate itself: hashes come from a separate capture.

    The caller freezes this provenance by an out-of-band SHA before collection.
    Its object digests must be independently authenticated from sealed inputs,
    not inferred from an object name, trace, or current observed object bytes.
    """
    require(provenance.get("status") == "authenticated_readonly_retained_configuration_capture", "Missing independent Lake configuration provenance")
    require(set(provenance) == {"schema_version", "status", "source_freeze_sha256", "origin", "platform", "package_revisions", "source_sha256", "tool_sha256", "slots"}, "Unexpected Lake provenance fields")
    require(provenance["schema_version"] == 1 and provenance["source_freeze_sha256"] == SOURCE_SHA, "Wrong Lake provenance schema/source binding")
    origin = provenance["origin"]
    require(set(origin) == {"retained_bootstrap_sha256", "readonly_capture_manifest_sha256"} and origin["retained_bootstrap_sha256"] == "da762be8cf147ef834961359511d3cf7cf5d47e04da2ed440f2c898befca9a91" and SHA.fullmatch(origin["readonly_capture_manifest_sha256"]), "Missing authenticated retained-image/capture binding")
    require(provenance["platform"] in {"x86_64-unknown-linux-gnu", "x86_64-linux-gnu"}, "Configuration provenance is not the pinned Linux target")
    freeze = read(HERE / "source-freeze.json")
    require(provenance["package_revisions"] == freeze["package_revisions"], "Configuration package pins differ")
    require(provenance["source_sha256"] == CONFIG_SOURCES, "Configuration source keyset/hashes differ")
    for name, digest in CONFIG_SOURCES.items():
        path = relative(root, name)
        require(path.is_file() and sha(path) == digest, "Configuration source bytes differ: " + name)
    tools = provenance["tool_sha256"]
    require(set(tools) == set(CONFIG_TOOLS), "Configuration compiler/Lake binding incomplete")
    for name, digest in tools.items():
        path = relative(root, name)
        require(SHA.fullmatch(digest) and path.is_file() and sha(path) == digest, "Configuration compiler/Lake bytes differ")
    slots = provenance["slots"]
    require(set(slots) == set(CONFIG_SLOTS), "Missing/extra configuration slot")
    base = relative(root, "formal/.lake/config")
    require(base.is_dir() and {p.name for p in base.iterdir()} == set(CONFIG_SLOTS), "Configuration directory slot keyset differs")
    result = {}
    for slot, (name, source, config_hash, options) in CONFIG_SLOTS.items():
        row = slots[slot]
        require(set(row) == {"source", "source_sha256", "trace", "artifacts_sha256"} and row["source"] == source and row["source_sha256"] == CONFIG_SOURCES[source], "Configuration slot source binding differs")
        expected_trace = {"idx": int(slot), "name": name, "platform": provenance["platform"], "leanHash": LEAN_COMMIT, "configHash": config_hash, "options": options}
        require(type(row["trace"].get("idx")) is int and row["trace"] == expected_trace, "Configuration trace/source/tool/options differ")
        hashes = row["artifacts_sha256"]
        required = {"lakefile.olean", "lakefile.olean.trace"}
        require(set(hashes) in (required, required | {"lakefile.olean.lock"}), "Unexpected configuration artifact names")
        folder = relative(root, "formal/.lake/config/" + slot)
        require(folder.is_dir() and {p.name for p in folder.iterdir()} == set(hashes), "Configuration artifact keyset differs")
        for filename, digest in hashes.items():
            path = relative(root, "formal/.lake/config/" + slot + "/" + filename)
            require(SHA.fullmatch(digest) and path.is_file() and sha(path) == digest, "Configuration artifact bytes differ: " + filename)
            if filename.endswith(".lock"):
                require(path.stat().st_size == 0, "Nonempty configuration lock")
            result[str(path.relative_to(root))] = digest
        observed = read(folder / "lakefile.olean.trace")
        require(type(observed.get("idx")) is int and observed == expected_trace, "Observed trace differs from independent capture")
    return result

def configuration_stats(root, configuration):
    fields = ("st_dev", "st_ino", "st_size", "st_mode", "st_uid", "st_gid", "st_mtime_ns", "st_ctime_ns")
    result = {}
    for name in configuration:
        value = relative(root, name).stat()
        result[name] = [getattr(value, field) for field in fields]
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
    progress("admission", "begin")
    ambient = os.environ if ambient is None else ambient
    require(not any(ambient.get(k) for k in OVERRIDES), "Ambient import/Python/toolchain override")
    require(runtime.get("status") == "authenticated_linux_runtime_for_strict_sampler", "Runtime template is not authenticated")
    require(set(runtime) == RUNTIME_FIELDS and type(runtime["schema_version"]) is int
            and runtime["schema_version"] == 2, "Mixed/old runtime cache-state schema")
    require(runtime["source_freeze_sha256"] == SOURCE_SHA, "Runtime bound to another source freeze")
    require(git_read(root, "rev-parse", "HEAD") == freeze["base_commit"], "Wrong checking base commit")
    allowed = set(freeze["overlay_sha256"]) | {source_path(x) for x in ROOTS}
    for options in (("diff", "--name-only"), ("diff", "--cached", "--name-only"), ("ls-files", "--others", "--exclude-standard")):
        require(set(git_read(root, *options).splitlines()) <= allowed, "Unapproved checking source changes")
    require(git_read(root / ".upstream/openai-math", "rev-parse", "HEAD") == freeze["upstream_revision"], "Upstream pin mismatch")
    for options in (("diff", "--name-only"), ("diff", "--cached", "--name-only"), ("ls-files", "--others", "--exclude-standard")):
        require(not git_read(root / ".upstream/openai-math", *options), "Upstream source dirty")
    progress("admission", "source_graph_begin")
    modules = validate_sources(root, freeze, parser)
    progress("admission", "source_graph_end", modules=len(modules))
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
    progress("admission", "package_and_checker_git_begin")
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
    progress("admission", "package_and_checker_git_end")
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
    config_provenance = runtime.get("lake_configuration_provenance", {})
    binding = runtime.get("lake_configuration_provenance_binding", {})
    require(set(binding) == {"path", "sha256"}, "Configuration provenance file binding missing")
    provenance_file = relative(root, binding["path"])
    require(provenance_file.is_relative_to(root / ".tools/linux-verification") and SHA.fullmatch(binding["sha256"]) and sha(provenance_file) == binding["sha256"] and read(provenance_file) == config_provenance, "Independent configuration provenance file differs")
    progress("admission", "configuration_begin")
    configuration = indexed_configuration_inventory(root, config_provenance)
    require(configuration == runtime["lake_configuration_artifacts_sha256"], "Trusted Lake configuration artifact set differs")
    require(set(config_provenance["tool_sha256"]) <= set(tools) and all(tools[n] == h for n,h in config_provenance["tool_sha256"].items()), "Configuration and runtime tool provenance differ")
    tools.update(configuration)
    tools.update(CONFIG_SOURCES)
    tools[binding["path"]] = binding["sha256"]
    config_stats = configuration_stats(root, configuration)
    require(runtime.get("lake_configuration_artifacts_stat") == config_stats, "Configuration runtime identity differs")
    expected_cache_roots = sorted([PREFIX + "/lib/lean", *["formal/.lake/packages/" + n + "/.lake/build/lib/lean" for n in packages]])
    require(runtime["trusted_cache_roots"] == expected_cache_roots, "Unapproved cache roots")
    policy_binding = runtime["unused_cache_policy_binding"]
    require(set(policy_binding) == {"path", "sha256"}, "Missing caller-bound unused-cache policy")
    policy_file = relative(root, policy_binding["path"])
    require(policy_file.is_relative_to(root / ".tools/linux-verification")
            and SHA.fullmatch(policy_binding["sha256"]) and sha(policy_file) == policy_binding["sha256"]
            and read(policy_file) == runtime["unused_cache_policy"], "Unused-cache policy file/SHA differs")
    validate_unused_cache_policy(runtime["unused_cache_policy"])
    tools[policy_binding["path"]] = policy_binding["sha256"]
    progress("admission", "configuration_and_policy_end")
    external, external_sources, owners = resolve_external_imports(root, freeze, packages)
    require(external == runtime["external_import_resolution"], "External source/object resolution changed")
    require(owners == runtime["external_import_owners"], "Required external source-owner set changed")
    tools.update(external_sources)
    validate_cache_state_shapes(runtime["trusted_cache_states"], expected_cache_roots)
    progress("admission", "cache_states_begin")
    states = cache_root_states(root, expected_cache_roots, owners, runtime["unused_cache_policy"])
    require(states == runtime["trusted_cache_states"], "Cache directory/absence state differs")
    progress("admission", "cache_states_end")
    no_hidden_objects(root, expected_cache_roots, configuration_files=configuration)
    progress("admission", "independent_cache_inventory_begin")
    actual_cache = cache_inventory(root, expected_cache_roots, states)
    require(actual_cache == runtime["trusted_cache_files_sha256"], "Complete trusted cache inventory differs")
    progress("admission", "independent_cache_inventory_end", files=len(actual_cache))
    caches = {}
    for name, digest in actual_cache.items():
        stat = relative(root, name).stat()
        caches[name] = (digest, (stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_ino))
    guard = Guard(root, sources, tools, caches, serial, config_roots, configuration, runtime["system_executables"], aliases, config_provenance, config_stats,
                  expected_cache_roots, states, owners, runtime["unused_cache_policy"])
    progress("admission", "guard_full_rehash_begin")
    guard.check(rehash=True)
    progress("admission", "guard_full_rehash_end")
    require(not serial.inventory(root), "Whole-run start has submitted build files")
    progress("admission", "end")
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
        no_hidden_objects(root, caches, allow_own_build=True, configuration_files=guard.config_files)
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
        require(cache_inventory(root, caches, guard.cache_states) == runtime["trusted_cache_files_sha256"], "Cache inventory drift before comparison")
        env = {"PATH": path, "ELAN_HOME": str(root / ".tools/elan"), "MATHLIB_CACHE_DIR": str(root / ".tools/mathlib-cache"), "COMPARATOR_LANDRUN": str(adapter), "COMPARATOR_LEAN4EXPORT": str(root / ".tools/verification-bin/lean4export")}
        result = step("unchanged_comparator", [*serial.service_prefix(root, env), str(lake), "env", str(root / ".tools/verification-bin/comparator"), str(descriptor)], True)
        require(all(x in (result.stdout or "") for x in ("Running Lean default kernel on solution.", "Lean default kernel accepts the solution", "Your solution is okay!")), "Missing actual kernel/comparison acceptance")
        guard.check(rehash=True)
        require(cache_inventory(root, caches, guard.cache_states) == runtime["trusted_cache_files_sha256"], "Cache inventory drift after comparison")
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
    p.add_argument("--diagnostics", action="store_true", help="Flushed progress on existing stderr; no verification change")
    a = p.parse_args()
    enable_diagnostics(a.diagnostics)
    progress("runner", "begin", plan_only=a.plan)
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
        for name in ("strict_sampler.py", "source-freeze.json", "anchored_metadata.py"):
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
    progress("runner", "end", plan_only=a.plan)
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Reject, OSError, KeyError, ValueError, RuntimeError) as error:
        print("Strict sampler stopped: " + str(error), file=sys.stderr)
        raise SystemExit(1)
