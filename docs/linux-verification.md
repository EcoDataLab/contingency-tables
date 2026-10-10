# Linux verification

These Linux runs were initiated and assessed by the same AI-assisted project workflow. “Independent” compilation refers to a fresh hosted environment and source closure, not outside human reproduction or peer review. The native Windows checks likewise used project-owned hardware; see [their provenance and scope](windows-verification.md).

The **Linux formal verification** GitHub Actions workflow runs on explicit `workflow_dispatch` requests or a pushed `verify-*` tag. A verification tag runs the focused scope at that exact commit; manual dispatch permits all three scopes. Choose the revision and retain its run URL and uploaded evidence. It uses the standard `ubuntu-24.04` VM, read-only repository permissions, checkout without retained credentials, no proof-artifact cache, and a six-hour job ceiling. Ordinary branch pushes and pull requests do not trigger this expensive workflow. Maintainers can create a named checkpoint with `git tag verify-<checkpoint> <commit>` and push that tag; they should inspect the resulting run before reporting a pass. The tagged commit must contain this tag-trigger version of the workflow; tagging an older commit cannot add a trigger to its historical workflow.

| Scope | Work performed | Successful result means |
|---|---|---|
| `focused` | Existing focused harness, upstream transport baseline, new refinements, named-axiom replay and compiled-environment audit | Those modules compiled; every selected environment theorem and six headline dependency closures passed the recorded axiom checks |
| `full` | Original `UnconditionalMain` and original challenge dependency closure, original three-theorem axiom audit | Full original theorem closure compiled; this is not Comparator replay |
| `comparator` | Fresh environment, strict Linux sandbox, original challenge JSON, original three theorems, built-in-kernel replay | Would verify the original claims under the recorded trusted-environment assumptions; no successful replay is recorded here |

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

At setup, Comparator's master requested Lean 4.35.0-rc4. The selected [Comparator revision](https://github.com/leanprover/comparator/tree/d03acab154d269c06e60e4de7e4cc85deebff94b) and its manifest-pinned exporter declare 4.34.0. The script explicitly rebuilds those unchanged sources with `ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1`, matching the project. Both tools compiled successfully under 4.34.1 on the local macOS development host; that is a source-compatibility check, not a Linux sandbox or proof-verification result. The workflow will repeat their build on Linux. No toolchain file is edited, and no `lake update` runs.

Tools and downloads stay under `.tools/`. `bootstrap_lean.sh` retains the original dependency pins. `verify_lean.sh` offers ordinary and serial compilation; `bootstrap_comparator.sh` supplies the additional Linux checks and uses the original challenge JSON. Nanoda is disabled by that original configuration.

## Comparator trust and isolation

Each Comparator attempt must start in a fresh job. It must not run `focused` or `full` first, restore their compiled proof artifacts, or use a workspace in which a submitted proof was already compiled. The script rejects existing project `.olean` files. Trusted tool compilation and the official Mathlib cache are separate: using that cache explicitly trusts its contents. This follows the [official Comparator trust requirements](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md). It is not an independent rebuilding of all Mathlib or Lean bootstrap binaries.

The preflight requires a non-root process without effective capabilities, an existing systemd user manager, actual AF_UNIX denial inside its service, and `NoNewPrivileges=yes`. It also queries the kernel for Landlock ABI 9 or newer. The pinned [Landrun source](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4) requests ABI 9 capabilities. If a hosted runner lacks the ABI or user manager, Comparator stops before downloading the large proof dependencies. The workflow does not start system services, alter the kernel, enable lingering, or substitute a weaker sandbox.

An important upstream detail is handled explicitly: the selected Comparator always supplies `--best-effort` to Landrun. The generated `verification-bin/landrun` adapter removes only that exact option before the command separator, refuses other weakening options, and executes the pinned **real** Landrun binary. It is not `fake-landrun`. A probe verifies an allowed write succeeds while an outside write and TCP bind fail, inside the systemd service that denies AF_UNIX. The comparison runs under the same restrictions. There is no fallback if any probe fails.

## Evidence and reproduction

Every run uploads `.tools/linux-verification/` and any `.local/environment-audits/` attempt, with its source hashes, kernel/image metadata, tool provenance when reached, bootstrap and verification logs, and a scope-specific outcome. Older committed development logs are not mixed into that artifact. A green focused/full run must not be described as a secure Comparator pass.

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

## Independent checkpoint 4 replication

[Focused run 37890362781](https://github.com/EcoDataLab/contingency-tables/actions/runs/37890362781)
passed at `d2e8b0be8e65fdf94b800df60296d8dd49098b62` on 9 October 2026 UTC.
The fresh Linux job took 9 minutes 21 seconds. It compiled the focused proof
closure and audited all **226 selected focused declarations**, including the
new `d¹⁷` chain bounds and automatic feasibility/branch proofs. Every audited
declaration uses only the allowed foundational axioms or a subset. This run
did not invoke the separate six-declaration standalone audit.

The [saved receipt](../formal/results/linux-focused-d2e8b0b/verification.json)
records the run, exact declarations, and **39 environment-recorded source
hashes checked against that Git commit**. The complete verification step was
retrieved through the authenticated GitHub job-log connector and preserved
with timestamp prefixes removed. Environment and outcome records were parsed
from the same job transcript. The artifact archive digest is recorded as API
metadata; this run's archive was not downloaded or digest-verified.

The [verification log](../formal/results/linux-focused-d2e8b0b/verification.log)
records two successful Lake invocations ending at 8,948 and 9,124 jobs; these
counts include trusted dependency-cache jobs and are not counts of newly
proved theorems. Official Mathlib cache artifacts remain trusted. This
replication covers the stated checkpoint, not later source additions, an
outer finite-bit sampler, or strict Comparator replay.

## Independent checkpoint 5 replication

[Focused run 37924611391](https://github.com/EcoDataLab/contingency-tables/actions/runs/37924611391)
passed at `7ad5c81117bbaa869da751b1f92a9213ddefdd22` on 9 October 2026 UTC.
The job took 11 minutes 52 seconds and audited all **279 selected focused
declarations**, including the three new stationary-output modules. The
[saved receipt](../formal/results/linux-focused-7ad5c81/verification.json)
records **45 environment-recorded source hashes matched to that commit**.
All audits passed the same foundational-axiom allowlist.

The complete [verification log](../formal/results/linux-focused-7ad5c81/verification.log)
was retrieved through the authenticated GitHub job-log connector, with
timestamp prefixes removed. Environment and outcome JSON were parsed from
that transcript. The artifact archive digest is API metadata only: this
archive was not downloaded or digest-verified. The log records successful
Lake invocations ending at 8,948 and 9,131 jobs, including trusted dependency
cache jobs. This run excludes the separate standalone audit, subsequent
finite-walk additions, and strict Comparator replay.

## Independent checkpoint 6 replication

[Focused run 37927276465](https://github.com/EcoDataLab/contingency-tables/actions/runs/37927276465)
passed at `e5d5dd3e81b5eac0e3f42841530286b56bcb96e5` on 9 October 2026 UTC.
The job took 14 minutes 39 seconds and audited all **318 selected focused
declarations**, including the actual rational kernel and finite-walk output
bound. The [saved receipt](../formal/results/linux-focused-e5d5dd3/verification.json)
matches **48 environment-recorded source hashes** to that commit.

The complete [verification log](../formal/results/linux-focused-e5d5dd3/verification.log)
was retrieved through the authenticated GitHub job-log connector; timestamp
prefixes were removed and the printed environment/outcome JSON retained.
The artifact archive digest is API metadata only, without archive download
or digest verification. All audits passed the foundational-axiom allowlist.
This run excludes the six standalone audits, later completion-oracle additions,
and strict Comparator replay; official Mathlib cache artifacts remain trusted.

## Independent checkpoint 7 replication

[Focused run 37932487805](https://github.com/EcoDataLab/contingency-tables/actions/runs/37932487805)
passed at `5b3703234e7f6cd88e6b6f6b3dab85510ba4366f` on 9 October 2026 UTC.
The fresh job took 14 minutes 59 seconds and audited all **420 selected focused
declarations**, including the actual and approximate completion laws, integer
codec core, and dilated physical margins. The
[saved receipt](../formal/results/linux-focused-5b37032/verification.json)
matches **55 environment-recorded source hashes** to that exact commit.

The complete [verification log](../formal/results/linux-focused-5b37032/verification.log)
was retrieved through the authenticated GitHub job-log connector. Timestamp
prefixes were removed; environment and outcome JSON were parsed from the same
decoded log. The artifact archive digest remains API metadata only, without
archive download or digest verification. All audits passed the foundational
axiom allowlist. This covers checkpoint 7 only: it excludes the six standalone
audits, subsequent source additions, and strict Comparator replay. Official
Mathlib cache artifacts remain trusted.

## Completed original Linux build

[Full run 37847944509](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847944509) passed at repository commit `5e5d6ef9aa36f7e2a744f3fb8605448529f8be66`. The original theorem closure completed 10,221 Lake jobs, including trusted cached dependency jobs. The raw log prints `boundedSampling`, `exactSampling`, and `counting`, each with only `propext`, `Classical.choice`, and `Quot.sound`, and confirms the three-declaration allowlist. The verification step took 47 minutes 29 seconds.

The downloaded GitHub artifact archive was checked against its API-reported SHA-256, `194c35a135a1cf0d04a8779e668e09b97311c35357c3f6779f8224821cf8f797`. Its four raw files are retained under [`formal/results/linux-full-5e5d6ef/`](../formal/results/linux-full-5e5d6ef/): bootstrap log, environment record, outcome record, and verification log. [`linux-runs.json`](../formal/results/linux-runs.json) records their individual hashes, the verified archive digest, run/job metadata, and audit declarations. This establishes ordinary compiler and axiom-audit success for the original source at that commit. It does not cover later local proof additions or establish secure Comparator replay.

## Live sandbox result, 8 October 2026

[Comparator run 37847722684](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684), at repository commit `5e5d6ef9aa36f7e2a744f3fb8605448529f8be66`, stopped at its preflight on `ubuntu-24.04`. The live Landlock syscall returned **ABI 7**, below the required **ABI 9**. The [failed step](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684/job/113552675743) recorded: `Strict pinned Landrun needs Landlock ABI >= 9; found 7, errno=0. No best-effort fallback.` It exited before Lean/Mathlib downloads or any Comparator proof compilation. Outcome and provenance artifact upload succeeded. This establishes an unavailable sandbox prerequisite, not a failure of the mathematical claims.

The runner's measured ABI is the decisive evidence; a distribution label alone is insufficient. The [Ubuntu 26.04 image manifest recorded for this investigation](https://github.com/actions/runner-images/blob/39c421f5a8a953996a05ba4dc061900ebd939308/images/ubuntu/Ubuntu2604-Readme.md) advertises kernel `7.0.0-1012-azure`. Upstream [Linux 7.0 sets ABI 8](https://github.com/torvalds/linux/blob/v7.0/security/landlock/syscalls.c), while [Linux 7.1 sets ABI 9](https://github.com/torvalds/linux/blob/v7.1/security/landlock/syscalls.c). Thus changing only to that newer hosted label is not a verified remedy; a kernel backport would need to be established by the same runtime probe. No currently documented standard hosted label was verified to supply ABI 9 during this investigation.

At this historical checkpoint, a fresh guest with a pinned Linux 7.1-or-newer kernel and a real systemd user session was a possible later route using [QEMU system emulation](https://www.qemu.org/docs/master/system/target-i386.html). It would need an independently checked guest image, kernel configuration, acceleration availability, and complete sandbox probes before replay. That guest work was deferred at this checkpoint while ordinary focused/full Linux builds ran. A container sharing the present runner kernel cannot supply the missing ABI. No VM installation, paid host, new credentials, or weakened sandbox was introduced for that hosted-runner investigation. A later strict VM attempt is distinguished below.

## Independent checkpoint 8 replication

[Focused run 37963647335](https://github.com/EcoDataLab/contingency-tables/actions/runs/37963647335)
passed at `0aa5a61140712ada44893b03d805a756e0e9823a` on 9 October 2026 UTC.
The fresh job took 14 minutes 9 seconds and audited all **632 selected focused
declarations**, including the finite-table fibers, geometric count comparison,
quarter acceptance, and conditional completion accuracy. The
[saved receipt](../formal/results/linux-focused-0aa5a61/verification.json)
matches **73 environment-recorded source hashes** to that exact commit.

The complete [verification log](../formal/results/linux-focused-0aa5a61/verification.log)
was retrieved through the authenticated GitHub job-log connector. Timestamp
prefixes were removed; environment and outcome JSON were parsed from the same
decoded log. The artifact archive digest is retained as API metadata; the
archive was not downloaded or digest-verified. All audits passed the standard
foundational-axiom allowlist. Official Mathlib cache artifacts remain trusted.
This run excludes the six standalone audits, subsequent dense-sampler and
finite-bit bridges, and strict Comparator replay. The separate
[Python CI](https://github.com/EcoDataLab/contingency-tables/actions/runs/37963605116)
passed on Python 3.10, 3.12, and 3.13.

## Completed completion-aggregate Linux build

[Focused run 37991819113](https://github.com/EcoDataLab/contingency-tables/actions/runs/37991819113)
passed at `895b45c8bcb0ca7f60e7a6b0b91af89b2ac7c566` on 9 October 2026 UTC.
The fresh job took 26 minutes 54 seconds; the recorded verification block took 24 minutes
49 seconds. All **863 selected focused declarations** passed the exact ordered
standard-axiom audit. The [saved receipt](../formal/results/linux-focused-895b45c/verification.json)
matches **111 environment-recorded source hashes** to that exact commit.
The source inventory includes saved evidence and separately audited modules;
it does not assert that every recorded file was compiled by this focused run.

The original downloaded artifact archive matches GitHub's reported SHA-256,
`a5fd4bf10ba3ef65ee26f58a6bb11c67bc7b556b2a05cc6786d4ac3824821493`.
The receipt binds the authenticated run, job, and artifact metadata to those
archive bytes. Original environment, outcome, bootstrap, and verification
files are retained alongside the exact committed audit driver and extracted
audit reports. The separate normalized bootstrap log replaces each of 69
bare carriage returns with a newline, preserving every progress segment;
the original bytes and both hashes remain recorded. The proof log requires
no such transformation.

This rebuild used a fresh project closure on Ubuntu 24.04 and trusted the
official Mathlib cache. It excludes the six standalone declarations, the
separately published 46 encoded-program and 193 physical-bridge audits, the
full original three-export audit, and strict Comparator replay. It supplies
independent compilation evidence for the expanded completion aggregate,
without adding a whole-sampler runtime or practical-performance claim.

## Later strict VM attempt

A [subsequent Linux VM](../formal/results/strict-comparator-vm-895b45c/README.md) reported Landlock ABI 11 and passed the strict sandbox preflight. The original `UnconditionalMain` theorem-closure build then failed after 99 minutes 30 seconds because the VM exhausted its 4 GiB memory allowance. This is a build resource failure after successful preflight, not a Comparator pass. No candidate theorem export or built-in-kernel replay result was obtained. The source and result scopes remain separate from the completed ordinary Linux builds above.

The [VM environment notes](strict-comparator-vm.md) preserve the exact observed configuration, source and tool pins, and outstanding public reproduction gaps. The failed log and its structured receipt remain available for comparison with later attempts.
