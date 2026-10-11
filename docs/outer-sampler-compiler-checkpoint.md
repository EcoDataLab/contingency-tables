# Outer-sampler compiler checkpoint

One fixed fair-bit machine now has a verified polynomial-time bounded-sampling guarantee for ordinary integer tables. For every finite pair of dimensions, natural row and column margins with equal totals, and precision `h≥1`, it halts with a feasible original table on every tape at one globally polynomial time, and its output law at that same time has normalized total variation at most `2^-h` from uniform. Empty dimensions and zero margins are included. The size measure is `S=m+n+clog₂(sum(r)+1)+h+1`, with numeric precision `h`.

The [theorem source](../formal/results/native-sampler-checkpoint/sources/Math115/LatticeBoundedSampling.lean), [actual statement index](../formal/results/native-sampler-checkpoint/semantic/headline-index.json), and [claim table with hypotheses](../formal/results/native-sampler-checkpoint/semantic/claim-table.md) bind this result to the compiled machine and its proof.

All thirteen latest research source modules pass ordinary Lean compilation. The final normal run has **685 completed records = 684 authenticated reuses + one fresh Cost compilation**, with no failed or blocked modules. The full environment audit, independent artifact review, and semantic readback pass. Inventory totals include upstream/generated declarations and are not new-result counts.

| Module | Accepted normal compiler evidence | Audit coverage |
| --- | --- | --- |
| `LatticeBoundedSampling` | Normal compilation passed for `adc3ed0d…` | Full R10 environment audit |
| `LatticeEmptyOutput` | Normal compilation passed for `5af2b648…` | Full R10 environment audit |
| `LatticeOuterProgram` | Normal compilation passed for `e761386d…` | Full R10 environment audit |
| `LatticeOuterSemantics` | Normal compilation passed for `cd22fe44…` | Full R10 environment audit |
| `LatticeProfileStep` | Normal compilation passed for `f5a8b460…` | Full R10 environment audit |
| `LatticeProfileWalk` | Normal compilation passed for `d1786e79…` | Full R10 environment audit |
| `LatticeSampler` | Normal compilation passed for `3e2d55e1…` | Full R10 environment audit |
| `LatticeSamplerCost` | Normal compilation passed for `bd78d5a5…` | Full R10 environment audit |
| `LatticeSamplerPreparation` | Normal compilation passed for `e5d33b3c…` | Full R10 environment audit |
| `LatticeUnitOuter` | Normal compilation passed for `2c8e44d0…` | Full R10 environment audit |
| `LatticeUnitStep` | Normal compilation passed for `4cb0745b…` | Full R10 environment audit |
| `LatticeUnitWalk` | Normal compilation passed for `b0fc16f7…` | Full R10 environment audit |
| `PublicLatticeSampler` | Normal compilation passed for `b7cc9fea…` | Full R10 environment audit |

The [structured evidence bundle](../formal/results/native-sampler-checkpoint/checkpoint.json) records exact source/object hashes, compiler durations, complete sanitized failed attempts, and current/historical audit bindings. The [full audit report](../formal/results/native-sampler-checkpoint/audit/summary.json) and [actual semantic readback](../formal/results/native-sampler-checkpoint/semantic/semantic-readback.json) confirm the final theorem reaches the `80,000d¹⁷` ideal-chain route, `U=5d³`, `L=3d`, the computed schedule, both completion branches, greedy fallback, fresh bits, and literal output. No caller-supplied oracle or stationary-start premise remains.

A polynomial machine-time degree is proved to exist, but its numeric value has not been extracted. The inverse-gap power 17 and reserved-bit power 170 are different quantities. No exact sampling/counting theorem, empirical speedup, standalone binary, fresh Linux rebuild for this overlay, or strict sampler Comparator result is claimed. The checked default target and original archive remain unchanged.

The [original first-round note at its published commit](https://github.com/EcoDataLab/contingency-tables/blob/cf39b6929abf080f3c2e319092eb2506c375d121/docs/outer-sampler-compiler-checkpoint.md) preserves the complete historical table and status. Its [published first-round evidence package](../formal/results/native-round1-evidence/README.md) remains unchanged. Every resumed-session failed attempt is preserved in the additive bundle. The recovered Walk receipt shows compilation finished before the earlier pause; authentication after resumption corrects the incomplete pause interpretation while preserving the original interrupted driver metadata.

The [separate strict-checking package](../formal/results/strict-comparator-smoke/README.md) records authenticated acceptance of a tiny fixture, including fresh fixture builds, exporter, default kernel, and comparison. That scope does not cover the original challenge exports or this sampler. Its tested Linux entrypoint and evidence belong to the separate fixture package; normal compiler records do not inherit that acceptance.

Retained source headers describing a source-only or uncompiled state record the files’ creation-time status. Current exact-hash compiler and audit receipts determine this checkpoint’s status; the verified source bytes and comments are preserved.

## Reproduce

Run the checked-base bootstrap and focused verification **inside an isolated validation checkout** at the recorded base commit:

```sh
cd /absolute/path/to/isolated-base-validation
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh focused --serial
```

For the research overlay, prepare a separate clean isolated replay checkout at that same commit and bootstrap its pinned dependencies there. Then invoke the replay from the evidence checkout, passing the replay checkout's absolute path:

```sh
cd /absolute/path/to/isolated-replay
bash scripts/bootstrap_lean.sh
cd /absolute/path/to/evidence-checkout
bash formal/results/native-sampler-checkpoint/reproduce.sh /absolute/path/to/isolated-replay
```

The helper requires the recorded base commit and a clean worktree, resolves symlinks, refuses the checkout containing the evidence bundle, and validates all thirteen hashes before writing any overlay. Keep validation logs outside the clean replay worktree and run no other editor or compiler in it during replay. It stops on the first dependency or target failure and returns that exact nonzero exit code.

The explicit Lean invocation retains recorded `-j2`, `-DautoImplicit=false`, `--root`, `-o`, and `-i` options, and applies the source-attempt memory option from the ledger (including `-M8192` where the per-source ledger records it, such as later Cost and BoundedSampling attempts). Older authenticated reused objects are not claimed to have used that cap. Fresh `.olean`/`.ilean` outputs are saved outside Lake's build cache; later Lake dependency builds can rebuild earlier research modules using its supported dependency workflow. This is a source-replay recipe, not exact replay of the native serial driver or reuse schedule. It neither invokes Comparator nor promotes the overlay into the checked target; new attempts need their own receipts.
Ordinary Lean compilation trusts pinned compiler/bootstrap and imported cache objects. AI-agent evidence review checks artifacts and recorded provenance; it is separate from outside human review and independent kernel verification. The bundle omits binary objects and most runtime/dependency objects, binds private raw metadata by digest, and preserves only sanitized paths. The [handoff](handoff.md) keeps the remaining reproduction and default-build integration, numerical cost analysis, strict sampler verification, and application-validation obligations separate.

The retained environment-audit driver, helper, actual report and unchanged inventory snapshots preserve native audit evidence. The ordinary source-replay script is a separate procedure; no fully portable audit replay has been tested or claimed.
