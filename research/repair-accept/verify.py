#!/usr/bin/env python3
"""Compile this additive research scope and audit its actual Lean environment.

Requires the repository's pinned compiler and an existing baseline dependency
build. No downloads, default-target changes, or cache writes are performed.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
SCOPES = {
    "repair-accept": (
        ["RepairAcceptanceCoin", "RepairAcceptanceThreshold", "RepairAcceptanceLaw",
         "Math115.AllSmallRepairFiber", "RepairAcceptancePhysical", "Math115.FiniteStarTrace"],
        ["Math115.AllSmallRepairFiber.reduced_repairTable_fiber_card",
         "Math115.RepairAcceptancePhysical.physical_finiteBit_retry_variation",
         "Math115.FiniteStarTrace.poincare_transfer"],
        ["OAI.Combinatorics.ContingencyTables.Machines.FairBits",
         "OAI.Combinatorics.ContingencyTables.Transport.FiniteRationalThreshold"]),
    "rectangular-defect": (
        ["VariableWidthLimit"],
        ["OAI.ContingencyTables.IntegerWeightedTransport.integer_box_root_leaf_transport_widths_limit"],
        []),
    "effective-width": (
        ["Math115.EffectiveWidthBound"],
        ["Math115.EffectiveWidthBound.refinedConstant_le_actual_width"],
        []),
}


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="a new attempt directory; existing results are never overwritten")
    parser.add_argument("--lean", type=Path,
                        default=ROOT / ".tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
    parser.add_argument("--scope", choices=SCOPES, default="repair-accept")
    args = parser.parse_args()
    modules, headlines, upstream_modules = SCOPES[args.scope]
    packet = ROOT / "research" / args.scope
    lean = args.lean.resolve()
    baseline = ROOT / "formal/.lake/build/lib/lean"
    actual_pin = subprocess.check_output(
        ["git", "-C", str(ROOT / ".upstream/openai-math"), "rev-parse", "HEAD"], text=True).strip()
    if actual_pin != PIN:
        raise SystemExit("Pinned upstream checkout differs; bootstrap the reviewed source first.")
    if not lean.is_file() or not baseline.is_dir():
        raise SystemExit("Pinned Lean and baseline dependencies must be built first; see README.md.")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    objects = output / "objects"
    objects.mkdir()
    # Lean resolves a namespace at one search root. Mirror the baseline as links
    # so a new Math115/OAI module does not hide other modules in that namespace.
    for path in baseline.rglob("*"):
        if path.is_file():
            target = objects / path.relative_to(baseline)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(path.resolve())
    search = [objects, *sorted((ROOT / "formal/.lake/packages").glob("*/.lake/build/lib/lean"))]
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(map(str, search)), "LEAN_NUM_THREADS": "2"}
    records = []

    def compile_one(module, source, source_root):
        target = objects / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.is_symlink():
            target.unlink()  # Remove only this attempt's link, never its target.
        cmd = [str(lean), "-j2", "-DautoImplicit=false", "--root=" + str(source_root),
               "-o", str(target), str(source)]
        started = time.monotonic()
        result = subprocess.run(cmd, env=env, cwd=ROOT, capture_output=True, text=True, timeout=600)
        stem = module.replace(".", "_")
        (output / (stem + ".stdout.txt")).write_text(result.stdout.replace(str(ROOT), "<repo>"))
        (output / (stem + ".stderr.txt")).write_text(result.stderr.replace(str(ROOT), "<repo>"))
        record = {"module": module, "source": str(source.relative_to(ROOT)),
                  "source_sha256": sha(source), "returncode": result.returncode,
                  "seconds": round(time.monotonic() - started, 3)}
        if result.returncode == 0:
            record["olean_sha256"] = sha(target)
        records.append(record)
        (output / "compilation.json").write_text(json.dumps(records, indent=2) + "\n")
        print(module, result.returncode, record["seconds"], flush=True)
        if result.returncode:
            raise SystemExit("Compilation failed; complete output retained in " + str(output))

    upstream = ROOT / ".upstream/openai-math/lean"
    # These small pinned modules are not required by the old default target.
    for module in upstream_modules:
        compile_one(module, upstream / (module.replace(".", "/") + ".lean"), upstream)
    for module in modules:
        compile_one(module, packet / "formal" / (module.replace(".", "/") + ".lean"), packet / "formal")
    compile_one("ResearchAudit.EnvironmentAudit", ROOT / "formal/ResearchAudit/EnvironmentAudit.lean",
                ROOT / "formal")
    driver = output / "ResearchScopeAudit.lean"
    driver.write_text("\n".join("import " + m for m in modules) +
                      "\nimport ResearchAudit.EnvironmentAudit\n" +
                      "#environment_audit prefixes [] modules [" + ", ".join(modules) +
                      "] headlines [" + ", ".join(headlines) + "]\n")
    started = time.monotonic()
    result = subprocess.run([str(lean), "-j2", "-DautoImplicit=false", str(driver)],
                            env=env, cwd=ROOT, capture_output=True, text=True, timeout=600)
    (output / "audit.stderr.txt").write_text(result.stderr.replace(str(ROOT), "<repo>"))
    (output / "audit.stdout.json.gz").write_bytes(gzip.compress(result.stdout.encode(), mtime=0))
    if result.returncode:
        raise SystemExit("Environment audit failed; complete output retained.")
    audit = json.loads(result.stdout)
    if any(d["nonstandard_axioms"] for d in audit["declarations"]):
        raise SystemExit("Unexpected axiom in the compiled research scope.")
    # Only imported objects are inventoried; unrelated cache contents are outside
    # this ordinary compiler check. Compiler/bootstrap and caches remain trusted.
    builtin = lean.parent.parent / "lib/lean"
    imported = {}
    for module in audit["imported_modules"]:
        relative = Path(module.replace(".", "/") + ".olean")
        candidates = [p / relative for p in [*search, builtin]]
        found = next((p for p in candidates if p.is_file()), None)
        if found is None:
            raise SystemExit("Could not inventory imported object: " + module)
        imported[module] = sha(found)
    (output / "imported-objects.json.gz").write_bytes(gzip.compress(
        (json.dumps(imported, indent=2) + "\n").encode(), mtime=0))
    summary = {"schema_version": 1, "status": "passed", "upstream_commit": PIN,
               "compiler_version": subprocess.check_output([str(lean), "--version"], text=True).strip(),
               "compiler_sha256": sha(lean), "modules": modules, "compilation": records,
               "audit_seconds": round(time.monotonic() - started, 3),
               "audit_sha256": sha(output / "audit.stdout.json.gz"),
               "imported_objects_file": "imported-objects.json.gz",
               "imported_objects_sha256": sha(output / "imported-objects.json.gz"),
               "declaration_count": audit["declaration_count"], "theorem_count": audit["theorem_count"],
               "headlines": [{"name": h["name"], "closure_size": len(h["closure"]),
                              "statement": next(d["statement"] for d in h["declarations"]
                                                if d["name"] == h["name"])} for h in audit["headlines"]],
               "scope": "Fresh research-module compilation and compiled-environment audit with trusted pinned compiler and reused baseline imports; not default-target rebuild or Comparator replay."}
    (output / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "passed", "theorems": audit["theorem_count"],
                      "headlines": len(audit["headlines"])}))


if __name__ == "__main__":
    main()
