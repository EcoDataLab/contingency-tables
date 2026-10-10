# Outer-sampler research handoff

These thirteen Lean sources are preserved research drafts, outside the default
source tree. The separately validated normal base covers 1,236 focused
declarations and six standalone declarations; those results are independent of
this archive. This archive does not establish a verified public outer sampler.

The final native Windows x86_64 attempt reused 673 validated modules, produced
no fresh successful compilations, failed on three modules, and blocked nine
dependents. `LatticeProfileStep` had passed normal compilation in the preceding
attempt and was reused unchanged. The standard 22-name axiom audit has **not**
been run on that production object. Compilation and axiom verification are
separate obligations.

[status.json](status.json) records all thirteen source hashes and individual
states. [manifest.json](manifest.json) binds the packaged bytes and sanitized
diagnostics to their source hashes. Only absolute checkout prefixes and path
separators were sanitized in the logs; their diagnostic text and line numbers
are retained. No compiled objects or private execution metadata are included.

## Reproduction

Use an isolated checkout with the repository's pinned
[toolchain](../../formal/lean-toolchain),
[Lake configuration](../../formal/lakefile.lean), and
[dependency manifest](../../formal/lake-manifest.json). The toolchain is
`leanprover/lean4:v4.34.1`; `status.json` also records the upstream and Mathlib
revisions. From the isolated repository root on a platform supported by the
bootstrap script, install the pinned tools before materializing the archived
hierarchy under `formal/Math115/`. Build each module explicitly with its
dependency closure:

```sh
export ELAN_HOME="$PWD/.tools/elan"
export ELAN_TOOLCHAIN="$(cat formal/lean-toolchain)"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
bash scripts/bootstrap_lean.sh
cp research/outer-sampler/formal/Math115/*.lean formal/Math115/
cd formal
../.tools/elan/bin/lake build Math115.LatticeProfileStep
../.tools/elan/bin/lake build Math115.LatticeProfileWalk
../.tools/elan/bin/lake build Math115.LatticeSamplerPreparation
../.tools/elan/bin/lake build Math115.LatticeUnitStep
```

These are reproduction instructions, not a report of a new run. The last three
builds are expected to expose the recorded unresolved errors. Once their
prerequisites pass, build the remaining modules individually in import order
using the imports recorded in `status.json`. Keeping these files under
`research/outer-sampler/` excludes the archive from the default build; explicitly
copying them into `formal/Math115/` is a research operation.

## Remaining work

| Module | Last compiler result | Next obligation |
| --- | --- | --- |
| `LatticeProfileWalk` | `whnf` heartbeat limit at line 189 | Resolve elaboration of the final encoded step without changing the intended statement. |
| `LatticeSamplerPreparation` | Composition carrier mismatches at lines 79–80; `whnf` limit at line 82; unknown `«e₀».symm` at line 377 | Pin the correct composition functions and carriers, resolve the equivalence name, and compile the complete module. |
| `LatticeUnitStep` | `whnf` heartbeat limits at lines 116 and 144 | Resolve the two proof elaboration bottlenecks while preserving the executable definitions and statements. |
| `LatticeProfileStep` | Prior normal compilation pass, reused unchanged | Run the strict standard 22-name audit on the production object. |
| Nine dependent modules | Dependency blocked; no direct result in the final attempt | Compile after prerequisites pass, then perform declaration-level axiom audits. |

After compilation and strict axiom audits, recheck the actual outer-sampler
program, distribution statements, termination and cost claims, and public
integration before promoting any archived draft into a verified default target.
The current status is a handoff for that work, not evidence that it is complete.
