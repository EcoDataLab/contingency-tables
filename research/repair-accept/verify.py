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
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
sys.path.insert(0, str(ROOT / "scripts"))
from build_lean_serial import BuildError, Module, dependency_order, lean_imports

INTEGRATION_SCOPE = "integration-sampler"
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
    "spaced-attempts": (
        ["Marked.Survivor", "Marked.L2"],
        ["Marked.Survivor.hybrid_bound", "Marked.Survivor.refresh_output_law",
         "Marked.Survivor.burn_once_bound", "Marked.Survivor.dominated_centered_energy",
         "Marked.Survivor.survivor_mixing_of_centered_l2",
         "Marked.Survivor.burn_once_l2_bound", "Marked.Survivor.spaced_terminal_bound"],
        []),
    "killed-survivor": (
        ["Marked.Survivor", "Marked.L2", "Marked.Killed"],
        ["Marked.Survivor.quadratic_comparison",
         "Marked.Survivor.killed_quadratic_bound", "Marked.Survivor.killed_energy_bound",
         "Marked.Survivor.killed_survivor_mass",
         "Marked.Survivor.terminal_exhaustion_bound",
         "Marked.Survivor.terminal_exhaustion_bound_positive_marks"],
        []),
    "shape-refinement": (
        ["Math115.EffectiveWidthBound", "Math115.ShapeDegreeBound", "Math115.ShapeScalarScales",
         "Math115.ReferenceEdgeAcceptance", "Research.AcceptancePadding"],
        ["Math115.ShapeDegreeBound.available_bound_le", "Math115.ShapeDegreeBound.degreeEnvelope_le",
         "Math115.ShapeScalarScales.proposal_rational_coefficient_le",
         "Math115.ShapeScalarScales.proposal_dyadic_coefficient_le",
         "Math115.ShapeScalarScales.guarded_padded_count_le_twice",
         "Math115.ShapeScalarScales.localDimension_conditions",
         "Research.AcceptancePadding.reference_edge_acceptance_block_floor",
         "Research.AcceptancePadding.reference_edge_acceptance_floorPadding",
         "Research.AcceptancePadding.floorPadding_budget",
         "Research.AcceptancePadding.cutoff_budget",
         "Research.AcceptancePadding.bounded_aspect_gap",
         "Research.AcceptancePadding.outerCutoff_budget"],
        []),
    "retained-root": (
        ["Math115.ShapeDegreeBound", "Math115.RetainedRoot", "Research.RetainedRootTransport",
         "Research.RetainedRootPhysical", "Research.RetainedRootShifts", "Research.RetainedRootNonnegative",
         "Research.ModeAnchor", "Research.RetainedStencilSum", "Research.ModeAnchorStencil",
         "Research.RetainedPhysicalCap", "Research.RetainedPhysicalSupport",
         "Math115.RetainedRootSquare", "ResearchComparison.ResidualCap", "Research.GrowthScalar",
         "Research.PositiveSupport", "Research.SpectralPath", "Research.SpectralPrefix",
         "Research.SpectralRetained"],
        ["Math115.RetainedRootPhysical.adjacent_physical_box_leaf_transport_retained",
         "Math115.RetainedRootPhysical.retainedRootCoefficient_shift",
         "OAI.ContingencyTables.IntegerWeightedTransport.retainedRootCoefficient_nonnegative_limit",
         "Math115.RetainedPhysicalCap.physical_correction_le_adjacent",
         "Math115.RetainedPhysicalSupport.positive_physical_support_diameter",
         "Research.PositiveSupport.positive_support_restriction",
         "Research.SpectralPath.exists_path_rayleigh_minimizer",
         "Research.SpectralRetained.retained_spectral_variance_bound",
         "Math115.RetainedRootSquare.tight_fullCoefficient_bound",
         "Research.GrowthRefinement.doubled_growth_twice",
         "Research.GrowthRefinement.shape_gap_width_square",
         "Research.GrowthRefinement.bounded_aspect_gap_width_square",
         "Research.GrowthRefinement.arbitrary_aspect_width_square_integer",
         "Math115.LegacyResidualCap.all_state_l7_cap"],
        []),
    "constant-padding": (
        ["Math115.ReferenceEdgeAcceptance", "Research.AcceptancePadding",
         "Research.WeightedIncidence", "Research.SurvivalConvolution", "Research.CompositionSurvival",
         "Research.ReciprocalZero", "Research.ReciprocalZeroPhysical"],
        ["Research.WeightedIncidence.product_weighted_incidence",
         "Research.WeightedIncidence.weighted_level_recurrence",
         "Research.SurvivalConvolution.finite_nbu_convolution",
         "Research.SurvivalConvolution.finite_nbu_reciprocal",
         "Research.CompositionSurvival.tail_nbu", "Research.CompositionSurvival.tail_sum",
         "Research.CompositionSurvival.composition_reciprocal_bound",
         "Research.ReciprocalZero.zero_count_times_convolution",
         "Research.ReciprocalZero.zero_entry_probability_reciprocal",
         "Research.ReciprocalZeroPhysical.accepted_half_seven",
         "Research.ConstantPaddingAcceptance.reference_edge_acceptance_seven"],
        []),
}

# The physical assembly freshly compiles its existing research dependencies,
# without copying their source files or changing the earlier receipt scopes.
SCOPES["physical-spectral"] = (
    [*SCOPES["retained-root"][0], *SCOPES["constant-padding"][0],
     "Research.ReciprocalCount", "Research.RetainedContextVariance",
     "Research.RetainedTransversalVariance", "Research.RetainedRepairSquare",
     "Research.RetainedChainSquare", "Research.RetainedChainSquareTotal"],
    ["Research.ReciprocalCount.one_unit_count_growth",
     "Research.ReciprocalCount.shape_padding_count_le_twice",
     "Research.SpectralRetained.retained_spectral_variance_bound",
     "Math115.RetainedContextVariance.paperCapacity_context_variance_spectral_bound",
     "Math115.RetainedTransversalVariance.paperCapacity_transversal_variance_spectral",
     "Math115.RetainedRepairSquare.state_variance_square",
     "Math115.RetainedChainSquare.chain_poincare_square",
     "Math115.RetainedChainSquare.unitChain_poincare_square",
     "Math115.RetainedChainSquare.selectedChain_poincare_shape_square",
     "Math115.RetainedChainSquare.selectedChain_poincare_d9",
     "Math115.RetainedChainSquareTotal.feasibleSquareChain_poincare_d9",
     "Math115.RetainedChainSquareTotal.feasibleSquareChain_pi"],
    [],
)

SCOPES["physical-defect-trace"] = (
    [*SCOPES["physical-spectral"][0], "Math115.FiniteStarTrace",
     "Research.WeightedHarmonicTrace", "Research.PhysicalTraceMargins",
     "Research.PhysicalTraceGeometry", "Research.PhysicalAcceptedConductance",
     "Research.PhysicalTraceIrreflexive", "Research.DefectCoordinateGeometry",
     "Research.PhysicalDefectDegree", "Research.PhysicalDefectTrace",
     "Research.PhysicalDefectTraceFinal"],
    ["Math115.PhysicalDefectDegree.physical_nonbalanced_degree_le",
     "Research.WeightedHarmonicTrace.harmonic_energy_eq_trace",
     "Research.WeightedHarmonicTrace.normalized_poincare_transfer",
     "Math115.PhysicalDefectTrace.rationalPhysicalTrace_move",
     "Math115.PhysicalDefectTrace.actualRationalTrace_pi",
     "Math115.PhysicalDefectTrace.actualRationalTrace_lazy",
     "Math115.PhysicalDefectTrace.actualRationalTrace_poincare_square",
     "Math115.PhysicalDefectTrace.actualRationalTrace_poincare_shape_square",
     "Math115.PhysicalDefectTrace.actualRationalTrace_poincare_d8"],
    ["OAI.Combinatorics.ContingencyTables.Sampling.SmallPatternArithmetic"],
)

# The aggregate packet preserves the same rational physical defect trace and
# adds an original-margin correction budget with eight new source modules.
SCOPES["aggregate-defect-trace"] = (
    [*SCOPES["physical-defect-trace"][0], "Research.ResidualSelectedBudget",
     "Research.CompletedRepairInjection", "Research.CompletedRepairMoment",
     "Research.AggregateCorrectionCap", "Research.UniformContextVariance",
     "Research.AggregateDefectTrace", "Research.AggregateShapeTrace", "Research.AggregateAspectTrace"],
    ["Math115.CompletedRepairInjection.repairToChild_large_crossing",
     "Math115.AggregateCorrectionCap.physical_correction_le_aggregate_adjacent",
     "Math115.AggregateDefectTrace.uniformCorrectionCap_aggregate",
     "Math115.AggregateDefectTrace.state_variance_aggregate",
     "Math115.AggregateDefectTrace.actualRationalTrace_poincare_aggregate",
     "Math115.AggregateDefectTrace.actualRationalTrace_poincare_aggregate_shape",
     "Math115.AggregateDefectTrace.actualRationalTrace_poincare_aggregate_aspect_sq",
     "Math115.PhysicalDefectTrace.actualRationalTrace_poincare_d8"],
    [*SCOPES["physical-defect-trace"][2]],
)

# Reuse source files shared with earlier packets instead of copying them.
SOURCE_ROOTS = {
    **{module: ROOT / "research/physical-defect-trace/formal"
       for module in SCOPES["physical-defect-trace"][0]
       if module not in SCOPES["physical-spectral"][0]},
    **{module: ROOT / "research/physical-spectral/formal"
       for module in SCOPES["physical-spectral"][0]},
    **{module: ROOT / "research/retained-root/formal"
       for module in SCOPES["retained-root"][0]},
    **{module: ROOT / "research/constant-padding/formal"
       for module in SCOPES["constant-padding"][0]},
    "Math115.EffectiveWidthBound": ROOT / "research/effective-width/formal",
    "Math115.ReferenceEdgeAcceptance": ROOT / "formal",
    "Research.AcceptancePadding": ROOT / "research/shape-refinement/formal",
    "Math115.ShapeDegreeBound": ROOT / "research/shape-refinement/formal",
    "Math115.FiniteStarTrace": ROOT / "research/repair-accept/formal",
    **{f"Marked.{name}": ROOT / "research/spaced-attempts/formal"
       for name in ("Survivor", "L2", "Killed")},
}


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def partial_text(value):
    # TimeoutExpired may carry bytes even when subprocess.run used text=True.
    return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value or ""


def integration_plan(root=ROOT):
    """Resolve public source imports without invoking Lean, Lake or Git.

    The manifest names additive sources explicitly. Baseline source imports
    come from the ordinary project and pinned upstream roots; package/toolchain
    objects remain the same prepared external boundary as the existing runner.
    """
    root = Path(root).resolve()
    manifest_path = root / "research/repair-accept/integration-sampler.json"
    manifest = json.loads(manifest_path.read_text())
    if manifest["schema_version"] != 1:
        raise BuildError("Unsupported integration manifest schema")
    sources = {}
    for name, relative in manifest["sources"].items():
        path = (root / relative).resolve()
        if not path.is_relative_to(root):
            raise BuildError("Integration source escapes repository: " + relative)
        suffix = Path(*name.split(".")).with_suffix(".lean")
        if path.parts[-len(suffix.parts):] != suffix.parts:
            raise BuildError("Source path does not match module: " + name)
        if not path.is_file():
            raise BuildError("Missing public integration source: " + relative)
        sources[name] = path
    packages = root / "formal/.lake/packages"
    toolchain = root / ".tools/elan/toolchains/leanprover--lean4---v4.34.1"
    external = set()

    def resolve(name):
        path = sources.get(name)
        if path is None:
            relative = Path(*name.split(".")).with_suffix(".lean")
            namespace = name.split(".", 1)[0]
            if namespace in {"Math115", "ResearchAudit"}:
                path = root / "formal" / relative
            elif namespace in {"OAI", "ComparatorChallenges"}:
                path = root / ".upstream/openai-math/lean" / relative
            elif namespace.startswith("Research") or namespace == "Marked":
                raise BuildError("Public research import has no manifest binding: " + name)
            else:
                candidates = [p for package in packages.glob("*")
                              if (p := package / relative).is_file()]
                builtin = toolchain / "lib/lean" / relative.with_suffix(".olean")
                if builtin.is_file():
                    candidates.append(builtin)
                if len(candidates) != 1:
                    raise BuildError("Missing or ambiguous external import " + name +
                                     "; run the normal pinned bootstrap first")
                external.add(name)
                return None
        if not path.is_file():
            raise BuildError("Missing source " + str(path.relative_to(root)) +
                             "; run the normal pinned bootstrap first")
        return Module(name, path, lean_imports(path.read_text()))

    baseline = dependency_order(tuple(manifest["baseline_roots"]), resolve)
    baseline_names = {module.name for module in baseline}
    ordered = dependency_order(tuple(manifest["audit_modules"]), resolve)
    additions = [module for module in ordered if module.name not in baseline_names]
    if {module.name for module in additions} != set(sources):
        raise BuildError("Integration manifest must contain exactly the additive source closure")
    # Include the public auditor's imports in source-resolution validation.
    dependency_order(("ResearchAudit.EnvironmentAudit",), resolve)

    def record(module):
        source_root = module.source.parents[len(module.name.split(".")) - 1]
        return {"module": module.name, "source": str(module.source.relative_to(root)),
                "source_root": str(source_root.relative_to(root)),
                "imports": list(module.imports)}

    return {"schema_version": 1, "status": "planned_only", "scope": INTEGRATION_SCOPE,
            "manifest": str(manifest_path.relative_to(root)),
            "baseline_roots": manifest["baseline_roots"],
            "baseline_modules": [module.name for module in baseline],
            "audit_modules": manifest["audit_modules"], "headlines": manifest["headlines"],
            "compilation": [record(module) for module in additions],
            "auditor_source": "formal/ResearchAudit/EnvironmentAudit.lean",
            "trusted_external_imports": sorted(external),
            "execution": "not_run; prepared pinned packages and baseline build required"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="a new attempt directory; existing results are never overwritten")
    parser.add_argument("--lean", type=Path,
                        default=ROOT / ".tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
    parser.add_argument("--scope", choices=[*SCOPES, INTEGRATION_SCOPE], default="repair-accept")
    parser.add_argument("--plan", action="store_true",
                        help="resolve integration-sampler source order only; no compiler or output writes")
    args = parser.parse_args()
    if args.plan and args.scope != INTEGRATION_SCOPE:
        parser.error("--plan is available only for --scope integration-sampler")
    if not args.plan and args.output is None:
        parser.error("--output is required unless --plan is used")
    plan = None
    if args.scope == INTEGRATION_SCOPE:
        try:
            plan = integration_plan()
        except (BuildError, OSError, ValueError) as error:
            raise SystemExit(str(error)) from error
        if args.plan:
            print(json.dumps(plan, indent=2))
            return
        modules, headlines, upstream_modules = plan["audit_modules"], plan["headlines"], []
    else:
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
    if plan is not None:
        (output / "source-plan.json").write_text(json.dumps(plan, indent=2) + "\n")
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
        timed_out = False
        try:
            result = subprocess.run(cmd, env=env, cwd=ROOT, capture_output=True, text=True, timeout=600)
        except subprocess.TimeoutExpired as error:
            timed_out = True
            result = subprocess.CompletedProcess(cmd, None, partial_text(error.stdout), partial_text(error.stderr))
        stem = module.replace(".", "_")
        (output / (stem + ".stdout.txt")).write_text(result.stdout.replace(str(ROOT), "<repo>"))
        (output / (stem + ".stderr.txt")).write_text(result.stderr.replace(str(ROOT), "<repo>"))
        record = {"module": module, "source": str(source.relative_to(ROOT)),
                  "source_sha256": sha(source), "returncode": result.returncode,
                  "seconds": round(time.monotonic() - started, 3)}
        if timed_out:
            record.update(timeout=True, timeout_seconds=600)
        if result.returncode == 0:
            record["olean_sha256"] = sha(target)
        records.append(record)
        (output / "compilation.json").write_text(json.dumps(records, indent=2) + "\n")
        print(module, result.returncode, record["seconds"], flush=True)
        if timed_out:
            raise SystemExit("Compilation timed out; partial output and stage result retained in " + str(output))
        if result.returncode:
            raise SystemExit("Compilation failed; complete output retained in " + str(output))

    upstream = ROOT / ".upstream/openai-math/lean"
    # These small pinned modules are not required by the old default target.
    for module in upstream_modules:
        compile_one(module, upstream / (module.replace(".", "/") + ".lean"), upstream)
    if plan is not None:
        for entry in plan["compilation"]:
            compile_one(entry["module"], ROOT / entry["source"], ROOT / entry["source_root"])
    else:
        for module in modules:
            source_root = SOURCE_ROOTS.get(module, packet / "formal")
            compile_one(module, source_root / (module.replace(".", "/") + ".lean"), source_root)
    compile_one("ResearchAudit.EnvironmentAudit", ROOT / "formal/ResearchAudit/EnvironmentAudit.lean",
                ROOT / "formal")
    driver = output / "ResearchScopeAudit.lean"
    driver.write_text("\n".join("import " + m for m in modules) +
                      "\nimport ResearchAudit.EnvironmentAudit\n" +
                      "#environment_audit prefixes [] modules [" + ", ".join(modules) +
                      "] headlines [" + ", ".join(headlines) + "]\n")
    started = time.monotonic()
    audit_timeout = 1800 if plan is not None else 600
    timed_out = False
    try:
        result = subprocess.run([str(lean), "-j2", "-DautoImplicit=false", str(driver)],
                                env=env, cwd=ROOT, capture_output=True, text=True, timeout=audit_timeout)
    except subprocess.TimeoutExpired as error:
        timed_out = True
        result = subprocess.CompletedProcess(error.cmd, None, partial_text(error.stdout), partial_text(error.stderr))
    (output / "audit.stderr.txt").write_text(result.stderr.replace(str(ROOT), "<repo>"))
    (output / "audit.stdout.json.gz").write_bytes(gzip.compress(result.stdout.encode(), mtime=0))
    if timed_out:
        (output / "audit-result.json").write_text(json.dumps({
            "stage": "audit", "returncode": None, "timeout": True,
            "timeout_seconds": audit_timeout, "seconds": round(time.monotonic() - started, 3),
        }, indent=2) + "\n")
        raise SystemExit("Environment audit timed out; partial output and stage result retained.")
    if result.returncode:
        raise SystemExit("Environment audit failed; complete output retained.")
    audit = json.loads(result.stdout)
    if any(d["nonstandard_axioms"] for d in audit["declarations"]):
        raise SystemExit("Unexpected axiom in the compiled research scope.")
    if plan is not None:
        if audit["modules"] != modules or [h["name"] for h in audit["headlines"]] != headlines:
            raise SystemExit("Compiled integration audit differs from the selected endpoint scope.")
        for headline in audit["headlines"]:
            names = set(headline["closure"])
            if names != {d["name"] for d in headline["declarations"]}:
                raise SystemExit("Integration headline closure inventory is incomplete.")
            for declaration in headline["declarations"]:
                if declaration["nonstandard_axioms"] or not set(declaration["dependencies"]) <= names:
                    raise SystemExit("Integration headline closure contains an unsupported dependency or axiom.")
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
    if plan is not None:
        summary["source_plan_file"] = "source-plan.json"
        summary["scope"] = (
            "Fresh public integration-source closure compilation and compiled-environment audit of "
            "the selected endpoint modules and their headline closures; trusted pinned compiler "
            "and reused baseline/package imports; not an audit of every rebuilt dependency "
            "declaration, default-target rebuild, or Comparator replay.")
    (output / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "passed", "theorems": audit["theorem_count"],
                      "headlines": len(audit["headlines"])}))


if __name__ == "__main__":
    main()
