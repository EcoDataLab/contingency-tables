# Finite junction/star energy bridge

This supporting Lean helper proves an energy comparison for a finite repair
map and actual supplied incidence conductances. For every defect observable g,
it derives `E_J(F_g) ≤ 12 E_star(g)`, where F_g is the completion-weighted mean
in each repair fiber. It proves the joint bound
`repairNoise + centerError ≤ 2 E_star`; that bound and the desired energy
conclusion are not premises.

The structural inputs are explicit: finite center, defect and junction sets;
nonnegative defect weights and incidence conductances; designated repair
conductance at least half the defect weight; injective shared junction defects;
their exact source-repair correspondence; junction weight bounded by the shared
defect weight; destination incidence at least half the junction weight; and
incoming junction mass bounded by the full repair-fiber mass. Parallel junctions
with distinct shared defects are allowed. Empty sets and zero-mass fibers are
included. This theorem concerns the induced F_g, rather than arbitrary center
observables.

All sums are raw. Junction indices count each supplied edge once. `starEnergy`
is identified with the existing `Research.WeightedHarmonicTrace` Schur-star
energy, with the existing ordered-energy factor one half and zero-star behavior.
No new clock, variance normalizer, center Poincare premise or physical gap
coefficient is supplied.

Actual contingency-table labels, original-margin feasibility, capacity
conditions, all-label repair fibers, directed acceptance, the incoming
family-4 injection and `N4≤N0` remain a separate mathematical instantiation.
They are not compiled by this helper. The growing-row applications and their
exponent bounds remain reviewed mathematics; this finite helper alone does
not formalize them. No sampler runtime or outside human review is claimed.

The saved targeted Lean 4.34.1 build passed, using authenticated prior public
objects without rebuilding dependencies. The actual compiled-environment
audit enumerated 23 declarations, including 15 theorems, and checked five
headline closures with only standard axioms. The final junction theorem's
closure has 12,177 declarations; the joint bound's has 11,231. These are
overlapping closure counts, not additional independent theorem totals.

Exact owned declaration types are in `results/declarations.json`. The compact
deduplicated `results/closure-axioms.json.gz` retains every headline closure
name and each dependency's module, kind, dependencies and axiom reports;
it omits repeated type text for imported declarations. The receipt binds
that projection and the original audit digest. Compiler, imported objects
and prior audit infrastructure remain trusted. No cache or binary is shipped.

`required-imports.json` records the pinned compiler/upstream/mathlib identities,
three directly required prior source/object identities, and the prior public
aggregate receipt. The two failed preparation attempts are summarized in
`results/failures.json`; identical proof bytes subsequently compiled. One
unused finite-instance helper warning is preserved in the successful stream.

For a targeted replay, prepare the same already-built authenticated import
root and the pinned dependency paths used by the existing public research
verification workflow. Set `LEAN_PATH` to those existing upstream/mathlib
object paths, then run:

```sh
bash REPRODUCE.sh /absolute/path/to/authenticated/import-root \
  /absolute/path/to/new-output-directory
```

The small script checks the helper and three prior source/object pins,
creates a private import overlay, compiles only this module, invokes the
existing compiled-environment auditor and checks exact types plus five
complete axiom closures. It rejects an existing output directory. It does
not install prerequisites, fetch a cache, rebuild the baseline, modify prior
objects, or run a sampler. The saved run used Apple arm64; no new Linux,
default-target or strict Comparator replay claim is made. The prepared replay
script has received syntax and saved-audit checks; a second compiler replay
has not been run.
