# Native round-one compilation evidence

This historical round ended **failed** on 2026-10-10 at 14:52:52 UTC. It recorded
two new successful full-module compilations: `LatticeSamplerPreparation` and
`LatticeEmptyOutput`. `LatticeProfileWalk` and `LatticeUnitStep` failed; eight
dependent modules were blocked. The 685-module plan recorded 675 completed
modules, including 673 validated normal dependency reuses. This is a fixed
round-one subset, not a report of the latest research round.

[verification.json](verification.json) binds the attempted sources, compiler
results, dependency hashes and diagnostic transformations.
[review.json](review.json) records an independent AI-agent review of downloaded
artifacts and saved metadata. Neither is a new axiom audit or independent Lean
execution. The review replayed 35 downloaded artifact hashes, 685 locally available
source hashes, 84 frozen overlay sources and 675 successful receipt dependency maps.
Live remote runtime and dependency-object bytes were not reauthenticated by that
review. The saved operator receipts record their earlier checks.

## Included attempts

| Module | Result | Source | Diagnostic |
| --- | --- | --- | --- |
| Preparation | Exit 0; 224.38 seconds | [Exact candidate](formal/Math115/LatticeSamplerPreparation.lean) | [Deprecation warning](logs/Math115.LatticeSamplerPreparation.log) |
| EmptyOutput | Exit 0; 58.33 seconds | [Exact archived source](formal/Math115/LatticeEmptyOutput.lean) | [Empty log](logs/Math115.LatticeEmptyOutput.log) |
| ProfileWalk | Exit 1 | [Exact candidate](formal/Math115/LatticeProfileWalk.lean) | [Universe/type errors](logs/Math115.LatticeProfileWalk.log) |
| UnitStep | Exit 1 | [Exact candidate](formal/Math115/LatticeUnitStep.lean) | [Heartbeat errors](logs/Math115.LatticeUnitStep.log) |

All four source files retain their exact attempted bytes. Three are candidate
overlays over the [preserved research archive](../../../research/outer-sampler/README.md);
EmptyOutput equals its archived source. That archive remains unchanged. The
downloaded attempted and published objects for both successes were byte-identical
and matched their compiler receipts. Compiled objects are not distributed here.
The ordinary normal compiler used Lean 4.34.1, `-j2` and
`-DautoImplicit=false`. Its object hashes are evidence of these native attempts,
not a promise of identical binaries on another platform.

Compiler logs replace only the personal absolute checkout prefix through
`formal\` with `formal\`. Diagnostics, line endings and other bytes are preserved.
The receipt lists both raw and sanitized SHA256 values and replacement counts.
Command arrays use role-token path projections rather than private absolute
paths. Original raw receipt and command digests remain recorded; the raw private
metadata is not distributed.

## Reproducing the source attempts

Use a separate checkout at commit
`4143769696d63005efd9ea5257ea4069b145e16d`. Set up the repository's pinned
Lean 4.34.1, upstream checkout and package dependencies as described in
[formal verification](../../../docs/formal-verification.md). Copy the thirteen
archived draft modules into that checkout's `formal/Math115/`, then overlay the
four exact sources from this directory. This operates on the separate replay
checkout; it does not alter the preserved archive.

With the repository-local pinned tools available, these ordinary commands first
build each attempt's dependencies and then invoke the compiler on that module:

```bash
export ELAN_HOME="$PWD/.tools/elan"
cd formal
mkdir -p ../round1-replay-output
for module in LatticeSamplerPreparation LatticeEmptyOutput LatticeProfileWalk LatticeUnitStep; do
  ../.tools/elan/bin/lake --no-cache build "+Math115.${module}:deps" || break
  ../.tools/elan/bin/lake env lean -j2 -DautoImplicit=false --root=. \
    -o "../round1-replay-output/${module}.olean" "Math115/${module}.lean" \
    > "../round1-replay-output/${module}.log" 2>&1
  result=$?
  printf '%s exit=%s\n' "$module" "$result"
done
```

These commands are a source-replay recipe, not the original orchestration or a
strict sandbox verification command. The original native receipts used fresh
attempt output paths and the frozen plan's dependency objects. A new run needs
its own environment, source and result receipts; the historical timings and
Windows object hashes are not reproduced by copying this package.

No new named axiom audit was run for the two successful modules in this round.
Normal compilation alone does not establish a no-`sorry` audit. No complete
encoded sampler, runtime theorem, numeric full runtime exponent, Linux sandbox,
exporter, kernel or Comparator acceptance is claimed by this package.
