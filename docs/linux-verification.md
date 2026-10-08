# Manual Linux verification

The **Manual Linux formal verification** GitHub Actions workflow runs only on `workflow_dispatch`. Choose the repository commit and one scope in the Actions interface, then retain its run URL and uploaded evidence. It uses the standard `ubuntu-24.04` VM, read-only repository permissions, checkout without retained credentials, no proof-artifact cache, and a six-hour job ceiling. Pushes and pull requests do not trigger this expensive workflow.

| Scope | Work performed | Successful result means |
|---|---|---|
| `focused` | Existing focused harness, upstream transport baseline, new refinements, printed-axiom audit | Those modules compiled with the recorded permitted axioms |
| `full` | Original `UnconditionalMain` and original challenge dependency closure, original three-theorem axiom audit | Full original theorem closure compiled; this is not Comparator replay |
| `comparator` | Fresh environment, strict Linux sandbox, original challenge JSON, original three theorems, built-in-kernel replay | The recorded original claims passed Comparator under the recorded trusted-environment assumptions |

The original closure is approximately 1,297 modules and may exceed runner memory, disk, or the verification command's 270-minute allowance. Failure or timeout is reported as **not verified**. The command timeout leaves room to upload logs before the six-hour job limit; forced runner loss can still prevent artifact upload. GitHub documents standard public Linux VMs and their resources [here](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).

## Pinned inputs

| Input | Exact pin |
|---|---|
| OpenAI source | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| Project Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Comparator | `d03acab154d269c06e60e4de7e4cc85deebff94b` |
| lean4export | `076e8e57707e813375e8f9da8bf989799ace9680` |
| Landrun source | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| Go compiler | `go1.27.2`, Linux amd64 archive SHA-256 checked |

Comparator's current master requests Lean 4.35.0-rc4. The selected [Comparator revision](https://github.com/leanprover/comparator/tree/d03acab154d269c06e60e4de7e4cc85deebff94b) and its manifest-pinned exporter declare 4.34.0. The script explicitly rebuilds those unchanged sources with `ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1`, matching the project. Both tools compiled successfully under 4.34.1 on the local macOS development host; that is a source-compatibility check, not a Linux sandbox or proof-verification result. The workflow will repeat their build on Linux. No toolchain file is edited, and no `lake update` runs.

Tools and downloads stay under `.tools/`. `bootstrap_lean.sh` retains the original dependency pins. `verify_lean.sh` offers ordinary and serial compilation; `bootstrap_comparator.sh` supplies the additional Linux checks and uses the original challenge JSON. Nanoda is disabled by that original configuration.

## Comparator trust and isolation

Each Comparator attempt must start in a fresh job. It must not run `focused` or `full` first, restore their compiled proof artifacts, or use a workspace in which a submitted proof was already compiled. The script rejects existing project `.olean` files. Trusted tool compilation and the official Mathlib cache are separate: using that cache explicitly trusts its contents. This follows the [official Comparator trust requirements](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md). It is not an independent rebuilding of all Mathlib or Lean bootstrap binaries.

The preflight requires a non-root process without effective capabilities, an existing systemd user manager, actual AF_UNIX denial inside its service, and `NoNewPrivileges=yes`. It also queries the kernel for Landlock ABI 9 or newer. The pinned [Landrun source](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4) requests ABI 9 capabilities. If a hosted runner lacks the ABI or user manager, Comparator stops before downloading the large proof dependencies. The workflow does not start system services, alter the kernel, enable lingering, or substitute a weaker sandbox.

An important upstream detail is handled explicitly: the selected Comparator always supplies `--best-effort` to Landrun. The generated `verification-bin/landrun` adapter removes only that exact option before the command separator, refuses other weakening options, and executes the pinned **real** Landrun binary. It is not `fake-landrun`. A probe verifies an allowed write succeeds while an outside write and TCP bind fail, inside the systemd service that denies AF_UNIX. The comparison runs under the same restrictions. There is no fallback if any probe fails.

## Evidence and reproduction

Every run uploads `.tools/linux-verification/` with its source hashes, kernel/image metadata, tool provenance when reached, bootstrap and verification logs, and a scope-specific outcome. Older committed development logs are not mixed into that artifact. A green focused/full run must not be described as a secure Comparator pass.

On a fresh compatible Linux x86_64 checkout with an existing user systemd manager:

```sh
scripts/bootstrap_comparator.sh preflight
scripts/bootstrap_lean.sh
scripts/bootstrap_comparator.sh bootstrap
scripts/bootstrap_comparator.sh verify
```

## Serial ordinary compilation

On Linux or macOS, where several simultaneous Lean compilers could exceed memory, use an exclusive checkout and append `--serial` to the ordinary verification command. Native Windows can run the helper's parser and mocked orchestration tests; its CLI requires a Unix file lock and stops explicitly on Windows.

```sh
scripts/bootstrap_lean.sh
python3 scripts/build_lean_serial.py full --plan
scripts/verify_lean.sh full --serial
# The other supported scopes are focused and standalone.
```

The optional planning command reads files and Git metadata; it does not run Lake, Lean, or an axiom audit. The full plan at the pinned upstream revision contains 1,298 local modules, including `ComparatorChallenges.ContingencyTables`, with 97 direct trusted external imports. The planner follows the chosen roots and the audit file's imports, retaining every reachable original-source or project module in dependency order. Focused mode starts at the upstream transport baselines and the `Math115` root module; it does not sweep unrelated project files into the build.

For each module, the helper first runs `lake --no-cache --no-build build +Module:deps`. Lake must establish that all dependency artifacts and traces are current before the helper calls `lake --no-cache build +Module:olean`. The explicit `+` selects one module, including for the `Math115` root. Lake creates its normal artifacts and traces; no trace is synthesized and no direct `lean -o` output is assumed current. A missing or stale cache, a changed source, or a failed module stops the sequence. Restore the pinned official cache or correct the failing source before rerunning the same command. A restart lets Lake reuse valid completed artifacts.

Run no other compiler or source editor in that checkout during serial verification. The helper locks out another copy of itself and checks source/configuration hashes for drift; the lock cannot control unrelated Lake/Lean processes. This controls the number of module build invocations, not the memory consumed by a single Lean compiler. Repeated Lake startup and dependency checks add overhead, so serial mode can take longer. Source edits or external artifact changes concurrent with a build remain unsupported. The unchanged printed-axiom audit runs only after all module builds succeed. `--serial` is rejected for Comparator, which has separate freshness and sandbox requirements.

The serial log is `formal/results/<scope>-serial.log`. Its JSON companion records the ordered graph, source and tool hashes, package pins, each dependency/build exit code and duration, and whether building completed or stopped. It deliberately leaves `axiom_audit` as `not_run_by_this_helper`; the calling shell log supplies the actual audit result. A `*-serial-plan.json` file establishes planning only. The ordinary manual Actions workflow continues to use its original build command unless its workflow is explicitly updated to request serial mode.

The helper's 16 orchestration tests use temporary sources and mocked subprocesses, covering ordering, deep graphs, cycles, missing dependencies, failed compilation, source drift, interruption, and importability without Unix file locking. The pinned full graph was planned locally without a compiler invocation. These checks validate the scheduler; they do not constitute a completed serial Lean build or Comparator replay.

A subsequent real single-module smoke check passed for `Math115.QuadraticCoefficient`: the dependency guard took 5.817 seconds and the explicit module target took 2.588 seconds. The exact commands, input hashes, statuses, and stdout are retained in `formal/results/single-module-serial-smoke.json` and `.log`. This checked one module and did not run an axiom audit or the full serial scope.

## Completed original Linux build

[Full run 37847944509](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847944509) passed at repository commit `5e5d6ef9aa36f7e2a744f3fb8605448529f8be66`. The original theorem closure completed 10,221 Lake jobs, including trusted cached dependency jobs. The raw log prints `boundedSampling`, `exactSampling`, and `counting`, each with only `propext`, `Classical.choice`, and `Quot.sound`, and confirms the three-declaration allowlist. The verification step took 47 minutes 29 seconds.

The downloaded GitHub artifact archive was checked against its API-reported SHA-256, `194c35a135a1cf0d04a8779e668e09b97311c35357c3f6779f8224821cf8f797`. Its four raw files are retained under [`formal/results/linux-full-5e5d6ef/`](../formal/results/linux-full-5e5d6ef/): bootstrap log, environment record, outcome record, and verification log. [`linux-runs.json`](../formal/results/linux-runs.json) records their individual hashes, the verified archive digest, run/job metadata, and audit declarations. This establishes ordinary compiler and axiom-audit success for the original source at that commit. It does not cover later local proof additions or establish secure Comparator replay.

## Live sandbox result, 8 October 2026

[Comparator run 37847722684](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684), at repository commit `5e5d6ef9aa36f7e2a744f3fb8605448529f8be66`, stopped at its preflight on `ubuntu-24.04`. The live Landlock syscall returned **ABI 7**, below the required **ABI 9**. The [failed step](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684/job/113552675743) recorded: `Strict pinned Landrun needs Landlock ABI >= 9; found 7, errno=0. No best-effort fallback.` It exited before Lean/Mathlib downloads or any Comparator proof compilation. Outcome and provenance artifact upload succeeded. This establishes an unavailable sandbox prerequisite, not a failure of the mathematical claims.

The runner's measured ABI is the decisive evidence; a distribution label alone is insufficient. The current official [Ubuntu 26.04 image manifest](https://github.com/actions/runner-images/blob/39c421f5a8a953996a05ba4dc061900ebd939308/images/ubuntu/Ubuntu2604-Readme.md) advertises kernel `7.0.0-1012-azure`. Upstream [Linux 7.0 sets ABI 8](https://github.com/torvalds/linux/blob/v7.0/security/landlock/syscalls.c), while [Linux 7.1 sets ABI 9](https://github.com/torvalds/linux/blob/v7.1/security/landlock/syscalls.c). Thus changing only to that newer hosted label is not a verified remedy; a kernel backport would need to be established by the same runtime probe. No currently documented standard hosted label was verified to supply ABI 9 during this investigation.

A fresh guest with a pinned Linux 7.1-or-newer kernel and a real systemd user session is a possible later route using [QEMU system emulation](https://www.qemu.org/docs/master/system/target-i386.html). It would need an independently checked guest image, kernel configuration, acceleration availability, and complete sandbox probes before replay. That adds a guest-build and maintenance task, so it is deferred while the ordinary focused/full Linux builds run. A container sharing the present runner kernel cannot supply the missing ABI. No VM installation, paid host, new credentials, or weakened sandbox was introduced.
