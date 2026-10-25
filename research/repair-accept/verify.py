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
