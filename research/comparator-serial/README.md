# Experimental serial orchestration for the original strict Comparator

This is a source-derived design candidate with offline tests. It requires independent source review and an actual strict sandbox/trace smoke check before production use. It has **not run Lean, Lake, systemd, or Comparator in a Linux guest**. It is not a completed strict comparison. The earlier authenticated Linux VM passed Landlock ABI 11, zero-capability/user-session checks, and real sandbox denial probes, then failed the original solution build after about 99 minutes 30 seconds with 29 ENOMEM errors on four GiB RAM. No solution export, kernel acceptance, or comparison result was produced.

The proposal keeps the original three-theorem descriptor, upstream sources, Comparator/exporter/Landrun bodies, and strict adapter unchanged. It adds an explicit entrypoint because the old `bootstrap_comparator.sh verify` checks for zero project objects immediately before invoking Comparator; it cannot truthfully be used after prebuilding project proofs. Here the zero-project-object receipt is taken at the start of the **whole serial-build-plus-comparison run**, and only artifacts produced by this run are subsequently reused. Do not describe this as an execution of the original `verify` entrypoint.

## Inputs and boundary

The candidate accepts only project commit `895b45c8bcb0ca7f60e7a6b0b91af89b2ac7c566`, upstream `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`), Comparator `d03acab154d269c06e60e4de7e4cc85deebff94b`, exporter `076e8e57707e813375e8f9da8bf989799ace9680`, Landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, and Go 1.27.2. The checker sources declare Lean 4.34.0 and were rebuilt unchanged with 4.34.1; that patch-level rebuild remains an explicit trust boundary.

The original descriptor SHA256 is `4baaa8be9da6f2c3b8664c94cad82b8f2c549b69315374584d6d01e381719a57`. The original strict bootstrap script SHA256 is `f7be322a8c6e166bedc4c9997562746ae6ec2c5ccf4f97b75eb3b7fe72ae9859`. The reused dependency planner SHA256 is `5dd644d68305af37343963e283e4b25efb95420896add41f8aa8fd6e2737a66c`. The candidate refuses changed bodies/pins and rechecks its source/configuration, direct trusted import artifacts, checker binaries, and Lean/Lake binary snapshots between stages.

Official toolchain and package caches remain trusted, including their transitive dependency closure. This is not a from-source rebuild of Mathlib or an independent certification of downloaded cache artifacts. Bootstrapped checker provenance plus clean source pins are trusted evidence of how those binaries were built; this proposal does not prove reproducible checker binary builds.

Use a dedicated non-root Linux x86_64 checking checkout, existing PAM/systemd user session, zero effective capabilities, Landlock ABI at least 9, and actual AF_UNIX/NoNewPrivileges and real Landrun denial probes. Keep non-cooperating compilers and source/cache writers out of that checkout. Its advisory lock coordinates only this entrypoint. Do not import project objects from another environment, the failed replay, or an earlier partial run. The entire `formal/.lake/build` tree must initially be empty, a stronger guard than testing public `.olean` files alone. Symlinked build parents/files are refused. Trusted reporting/adapter files live outside sandbox-writable `.lake`.

## Dispatch and comparison

The existing reviewed parser and iterative dependency ordering select only the original descriptor's project closure. The helper's implicit `Init` audit import is a trusted toolchain boundary, not an added project target; any additional project root is refused. The audit file itself is not separately run by this entrypoint.

For each topologically ready module, under the original filesystem/executable/environment rules and user-service restrictions:

1. Real pinned Lake runs `--no-cache --no-build build +Module:deps`. A stale or missing dependency stops the run before authorizing the selected compiler.
2. Real pinned Lake runs `--no-cache --fail-fast build +Module:olean` and waits before the next dispatch. Lake produces the actual module artifacts and compatible traces; no fake trace or custom direct-Lean object is generated.
3. Source snapshots and project output hashes are rechecked. The selected build must produce a recorded proof object for its own module; any public/private/server companions are included in the inventory. It must not change another module's proof objects or remove earlier outputs. Per-module commands, logs, hashes and elapsed time are retained.

Then real Lake verifies both exact default roots with `--no-cache --no-build build <challenge-root> <solution-root>`. Trace incompatibility fails closed before Comparator. The original probes run again. Comparator executes its original descriptor unchanged. The new resource adapter delegates **every original sandbox option** to the unchanged strict adapter; only its two exact `lake build Root` calls become real pinned `lake --no-cache --no-build build Root`. Exporter argument lists are untouched. Unexpected child commands fail closed. The original descriptor has no external kernel commands; its built-in kernel still runs in Comparator itself. Both built-in kernel acceptance and final comparison acceptance messages, exit zero, unchanged project artifacts, and final source hashes are required before recording success.

The inference of one selected heavy module compiler relies on the pinned Lake facets, a successful dependency-current gate, stable trusted inputs, and exclusive checkout use. A 250 ms sample of the owned user-service cgroup records observed Lean/LeanIR process peaks and stops that exact service on observed overlap. Sampling can miss short processes; it is **telemetry, not a hard operating-system exec gate**. Compiler threads and the memory needs of one large theorem or in-process kernel replay are not bounded by setting a Lake job count. No such job flag is invented here.

The source rationale is inspectable in `source-inspection/sources.json`: [Lake module facets and dependency setup](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Build/Module.lean), [single-module compiler action](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/lake/Lake/Build/Actions.lean), and [pinned Comparator build/export/kernel sequence](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Main.lean). The proposed command shapes are source-derived; runtime compatibility remains unmeasured.

## Tests actually run

`validation.json` and its raw logs record 33 new offline tests, 16 existing dependency-planner tests, and syntax checks. All passed. New tests cover fresh-object/symlink refusal, implicit `Init` scope, stale dependencies, failed compilers, source changes, unexpected/deleted outputs, default-target trace failure, late artifact changes, missing kernel/comparison evidence, pin/provenance rejection, real no-build argument rewriting, unchanged export/sandbox arguments, a mocked owned-service deadline/overlap stop, and procfs telemetry parsing. The reviewed planner tests cover header parsing, dependency order/cycles/deep graphs, and build failure boundaries. Process launch and systemd interactions in the new tests are mocked.

For offline reruns from the repository root, using the bundled unchanged planner snapshot:

```bash
python3 -m unittest discover -s research/comparator-serial -p 'test_*.py' -v
python3 -m unittest discover -s research/comparator-serial/reviewed-helper/tests -p test_build_lean_serial.py -v
```

## Minimal next steps after independent review

Copy the reviewed candidate's two executable source files into a trusted directory **inside** an already bootstrapped, fresh, exact-commit checking checkout, for example `<CHECKOUT>/.tools/linux-verification/serial-orchestration/`. Review/preserve `manifest.json` and verify installed hashes. Do not launch a Linux VM merely to run the following offline planning command:

```bash
python3 <CHECKOUT>/.tools/linux-verification/serial-orchestration/strict_serial_check.py \
  --root <CHECKOUT> --project-revision 895b45c8bcb0ca7f60e7a6b0b91af89b2ac7c566 \
  --plan --output <CHECKOUT>/.tools/linux-verification/serial-plan-01
```

After source review and a real sandbox smoke test, execution substitutes `--execute --wall-seconds 43200` and a **new** output directory. It must use a fresh project build tree, not a resume with partial objects. The execution is Linux-only and has not been attempted in this stage. First validate real module/default-target trace compatibility, actual sandbox execution, and no-build adapter behavior on a small reviewed fixture; then start the original closure afresh. A fixture is a separate experiment, never evidence of the original three-theorem check.

Each heavy stage has a unique owned systemd service and remaining-budget [`RuntimeMaxSec`](https://github.com/systemd/systemd/blob/main/man/systemd.service.xml); the launcher logs stage output directly to files and stops only its own unit on timeout/interruption/observed overlap. A durable outer guest/supervisor with the same total 12-hour cap is still required for disconnect/laptop-sleep resilience and guest shutdown. The trusted original probe function creates its own transient child units; this draft does not make those original probe units children of the new heavy-stage cgroup. If a probe itself hangs, the outer guest supervisor must enforce ultimate cleanup. That integration has not been tested here.

Proposed future resource baseline: four vCPUs, eight GiB guest RAM, private 80 GiB sparse writable layer, no sharing/listeners/forwarding/TAP or host setting changes. The previous layer had about 60.6 GiB guest free at launch; remeasure real host backing space and guest free disk before another run. Eight GiB is a **hypothesis**, not an established sufficient bound; the earlier 3.3 GiB service peak during fan-out does not establish the peak of a serial heavy module, exporter or in-process kernel. Prefer scheduling the VM after native audits/jobs finish. If jobs overlap, use a fresh free-memory measurement and preserve their observed headroom; an earlier 16 GiB free-host gate is a coordination heuristic, not a permanent software requirement.

Public exact-environment reproduction also remains incomplete: the authenticated Canonical image bytes were from mutable `current` (build 20261006); a publicly retrievable dated URL for those exact bytes has not been established. Do not silently substitute another image. Another authenticated image requires its own receipt and measured preflight. A complete generic provisioning recipe, dependency/signature manifest and portable durable supervisor remain future packaging work. Describe the measured failed attempt and this experimental orchestration separately.

## Packaging and handoff

The executable candidate is the two top-level Python files. `reviewed-helper/scripts/build_lean_serial.py` is an exact snapshot from the pinned project commit, included for offline tests and source inspection; the runtime entrypoint loads and hash-checks the same helper in the fresh checking checkout. `reviewed-helper/tests/test_build_lean_serial.py` is the tested repository test snapshot, with its exact hash retained; it includes the native-Windows import boundary test added after the pinned project commit. The source-inspection files retain vendor copyright/license headers and exact official URLs. None is a new Lean proof or runtime dependency downloaded by this candidate.

The strict adapter remains byte-for-byte unchanged. The only child-build orchestration change is the documented real-Lake no-cache/no-build flags; exporter/theorem/kernel bodies and original sandbox/path/network rules remain unchanged. The new total-run guard and receipts belong to this explicit experimental entrypoint.

The [saved failed attempt](../../docs/strict-comparator-vm.md) and its [public raw outcome receipt](../../formal/results/strict-comparator-vm-895b45c/strict-comparator-attempt.json) remain separate evidence. This directory adds no successful Comparator result. `manifest.json` records the exact public source/test artifacts and official inspection pins. `validation.json` records actual offline test commands/results. Future contributors should start with independent review and the plan-only command above; full strict checking remains open.
