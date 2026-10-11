# Strict tiny Comparator fixture: tested Linux entrypoint

The recorded separate True-only fixture passed real strict sandbox probes, three
serial module builds, the exact-root no-build handoff, exporter execution, built-in
Lean kernel replay and Comparator statement/axiom acceptance. All ten recorded
stages returned zero. The original project build tree remained empty. This result
verifies this small checking pipeline; the original three-theorem challenge still
requires its own run.

The measured environment used four virtual CPUs, 6,144 MiB guest RAM, zero swap,
about 60.6 GiB free disk, Linux `7.3.0-8-generic`, Landlock ABI 11, a normal PAM login
as a non-root user with zero effective capabilities, and existing systemd user bus.
Actual AF_UNIX/NoNewPrivileges enforcement and real Landrun allowed-write,
outside-write and TCP-bind denial probes passed before and after compilation.
The outer owned VM supervisor completed in about five minutes 41 seconds and
closed its VM. This is a measured fixture duration, not a runtime estimate for
the original challenge or a memory sufficiency bound for larger proofs.

`linux-smoke/` contains exact tested bytes, copied without code changes:

| File | SHA256 |
| --- | --- |
| `strict_smoke.py` | `a68fc81971f0ccfbd6808dd20161a0b2fd839b5abbd1e44b9e9875ab2b8716ff` |
| `strict_serial_check.py` | `05df96db18964f76a109d72d876ba7c72f799782e1c54bad9f587cd213110e7e` |
| `no_rebuild_landrun.py` | `a296bcbdcbb313b0d43cc7237103fbd231df8dd3b5bfc7ffd9d7e289422be5a7` |

The fixture source, descriptor and topological order are embedded in
`strict_smoke.py`: `SmokeChallenge`, `SmokeBase`, then `SmokeSolution`. Both roots
declare `ComparatorSmoke.accepts : True`; the solution uses the dependency's
concrete witness. The shared serial runner is imported as a library. Its separate
original-baseline CLI was not executed in this fixture and remains experimental.

These exact checking inputs are required:

| Input | Pin |
| --- | --- |
| Checking project | `895b45c8bcb0ca7f60e7a6b0b91af89b2ac7c566` |
| Upstream source | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Lean | `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` |
| Comparator | `d03acab154d269c06e60e4de7e4cc85deebff94b` |
| Exporter | `076e8e57707e813375e8f9da8bf989799ace9680` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| Go | `go1.27.2` |
| Original descriptor SHA256 | `4baaa8be9da6f2c3b8664c94cad82b8f2c549b69315374584d6d01e381719a57` |
| Strict bootstrap SHA256 | `f7be322a8c6e166bedc4c9997562746ae6ec2c5ccf4f97b75eb3b7fe72ae9859` |
| Dependency planner SHA256 | `5dd644d68305af37343963e283e4b25efb95420896add41f8aa8fd6e2737a66c` |

Use a dedicated Linux x86_64 checking checkout from the public
`EcoDataLab/contingency-tables` repository at the exact project revision above.
Keep its tracked files clean. Python 3.11 or newer, Git and the bootstrapped native
tools are required. The real prerequisite probes must succeed; a container's root
shell, synthetic user bus or best-effort sandbox is not an equivalent environment.
Keep unrelated compilers and source/cache writers out of this checkout.

Set `CHECKOUT` to the absolute path of that dedicated checkout. From the normal
checking-user session, bootstrap it:

```bash
cd "$CHECKOUT"
bash scripts/bootstrap_comparator.sh preflight
bash scripts/bootstrap_lean.sh
bash scripts/bootstrap_comparator.sh bootstrap
```

Verify the source hashes above, then copy the three exact Python files into a
trusted directory inside the checking checkout, for example
`$CHECKOUT/.tools/linux-verification/tiny-fixture-runner/`. The entire original
`formal/.lake/build` tree must contain zero files. No objects from a native build,
earlier failed run or another checking environment may be supplied. Keep official
toolchain/package caches separate and intact.

Run the fixture with a new output directory:

```bash
python3 "$CHECKOUT/.tools/linux-verification/tiny-fixture-runner/strict_smoke.py" \
  --root "$CHECKOUT" \
  --output "$CHECKOUT/.tools/linux-verification/tiny-fixture-01" \
  --wall-seconds 1800
```

The trusted fixture setup creates its empty `.lake` directory before constructing
the unchanged sandbox rules. Real pinned Lake performs deps-current and olean
facets in order, then checks both exact default roots with no-build. The original
strict adapter, exporter and checker bodies are unchanged. An unexpected child
command, stale dependency, changed source/object, failed kernel or missing
acceptance evidence fails the run.

The measured route also had a durable owned 3,600-second outer VM cap covering
boot, planning, original probe units, fixture stages and evidence collection. The
entrypoint's 1,800-second stage budget and individually owned heavy-stage services
do not replace that outer boundary. A compatible Linux-host reproduction needs
its own reviewed outer supervision and cleanup; this package has not tested a
portable replacement supervisor. It reproduces the exact tested guest checking
entrypoint, not an automatic provisioning system. A publicly retrievable dated
URL for the exact retained Canonical image bytes remains unresolved, so a different
compatible host/image is a new measured environment requiring its own receipt.

Official toolchain/package caches, their transitive closure and bootstrapped
checker provenance remain trusted inputs. The checker sources declare Lean
4.34.0 and were rebuilt unchanged with 4.34.1; retain that patch-level trust boundary.
The 250 ms cgroup samples record matching Lean executables rather than proving a
hard OS execution limit; the Comparator's Lean-prefix query can contribute to its
observed peak. Real no-build success and unchanged artifact hashes provide the
recorded no-rebuild evidence.

`evidence/` contains public renderings of the authenticated guest receipt and raw
stage logs. `raw-to-public-map.json` binds the 24 rendered evidence files to their
original hashes and lists the path/guest-name redaction categories. The remaining
archive member is the exact no-build adapter, bound by the source table and
manifest. Unchanged logs keep
their exact bytes; redacted renderings are not called original raw artifacts.
The original archive SHA256 is
`067091c21a10c9c4b39f9ff1169c188ec765d6cb6400e4ab5b18dab16ab3082c`.
The successful receipt requires `fixture_comparison_passed`, all ten stage exits
zero, empty original outputs, and the actual exporter/kernel/Comparator messages.
Preserve the small fixture's proposition-definition linter warning; it did not
change the successful comparison result.

The source/evidence package received an AI-agent consistency review; this was
not an outside human review or a second independently implemented kernel check.
The default Lean kernel is the independent proof-checking stage recorded above.
