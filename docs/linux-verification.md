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

Tools and downloads stay under `.tools/`. The existing `bootstrap_lean.sh` and `verify_lean.sh` remain unchanged. `bootstrap_comparator.sh` supplies the additional Linux checks and uses the original challenge JSON. Nanoda is disabled by that original configuration.

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

## Live sandbox result, 8 October 2026

[Comparator run 37847722684](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684), at repository commit `5e5d6ef9aa36f7e2a744f3fb8605448529f8be66`, stopped at its preflight on `ubuntu-24.04`. The live Landlock syscall returned **ABI 7**, below the required **ABI 9**. The [failed step](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684/job/113552675743) recorded: `Strict pinned Landrun needs Landlock ABI >= 9; found 7, errno=0. No best-effort fallback.` It exited before Lean/Mathlib downloads or any Comparator proof compilation. Outcome and provenance artifact upload succeeded. This establishes an unavailable sandbox prerequisite, not a failure of the mathematical claims.

The runner's measured ABI is the decisive evidence; a distribution label alone is insufficient. The current official [Ubuntu 26.04 image manifest](https://github.com/actions/runner-images/blob/39c421f5a8a953996a05ba4dc061900ebd939308/images/ubuntu/Ubuntu2604-Readme.md) advertises kernel `7.0.0-1012-azure`. Upstream [Linux 7.0 sets ABI 8](https://github.com/torvalds/linux/blob/v7.0/security/landlock/syscalls.c), while [Linux 7.1 sets ABI 9](https://github.com/torvalds/linux/blob/v7.1/security/landlock/syscalls.c). Thus changing only to that newer hosted label is not a verified remedy; a kernel backport would need to be established by the same runtime probe. No currently documented standard hosted label was verified to supply ABI 9 during this investigation.

A fresh guest with a pinned Linux 7.1-or-newer kernel and a real systemd user session is a possible later route using [QEMU system emulation](https://www.qemu.org/docs/master/system/target-i386.html). It would need an independently checked guest image, kernel configuration, acceleration availability, and complete sandbox probes before replay. That adds a guest-build and maintenance task, so it is deferred while the ordinary focused/full Linux builds run. A container sharing the present runner kernel cannot supply the missing ABI. No VM installation, paid host, new credentials, or weakened sandbox was introduced.
