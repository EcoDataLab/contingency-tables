# Strict Comparator: Linux VM environment and failed attempt

The [recorded original-challenge attempt](../formal/results/strict-comparator-vm-895b45c/README.md) passed strict sandbox probes and then exhausted memory while building the solution. These notes document that environment and the remaining reproduction gaps. They do not describe a successful Comparator run.

## Exact observed attempt, including its negative result

The four-vCPU/four-GiB/no-swap configuration is reproducible evidence of a **pre-comparison ENOMEM build failure**, not a successful checking recipe. Its original descriptor and source pins are in the [structured receipt](../formal/results/strict-comparator-vm-895b45c/strict-comparator-attempt.json). Keep the failed run and all 29 failure diagnostics visible when describing later improvements.

The environment itself is measured usable for the strict prerequisites: Linux x86_64 kernel `7.3.0-8-generic`, Landlock ABI 11, seccomp/Landlock compiled and enabled, systemd `261.3-0ubuntu3`, real PAM console login, existing user bus, non-root UID, zero effective capabilities, and actual user-service AF_UNIX/NoNewPrivileges enforcement. The actual pinned Landrun witness/outside-write/TCP-bind probes passed. More RAM or lower build concurrency has not yet been tested in a full original replay.

## Public inputs and authentication

1. Public repository: `https://github.com/EcoDataLab/contingency-tables.git`, exact commit `895b45c8bcb0ca7f60e7a6b0b91af89b2ac7c566` for this receipt. Preserve the original upstream descriptor SHA256 `4baaa8be9da6f2c3b8664c94cad82b8f2c549b69315374584d6d01e381719a57`; future repository revisions are distinct attempts.
2. [Canonical cloud image directory](https://cloud-images.ubuntu.com/stonking/current/): `stonking-server-cloudimg-amd64.img`, observed build 20261006, SHA256 `c93d013ac1116adf585bdd84d2e8b51039fc623fb8c6d33b70da4075c4934118`. Authenticate `SHA256SUMS.gpg`/`SHA256SUMS` using the [official UEC verification procedure](https://ubuntu.com/docs/public-images/public-images-how-to/verify-image-checksum/) and fingerprint `D2EB44626FDDC30B513D5BB71A5D6C4C7DB87C81`. Authenticate its package manifest too. **Availability gap:** `current` is mutable; a dated 20261006 URL was not verified reachable. A public exact-byte recipe needs an authenticated retained vendor URL or separately reviewed lawful artifact preservation. Never silently accept a different image merely because it has the same filename. Another image requires a new manifest/hash and measured strict preflight.
3. Windows software-emulation route: [official MSYS2 UCRT64 QEMU package](https://packages.msys2.org/packages/mingw-w64-ucrt-x86_64-qemu), `11.1.2-1`, archive SHA256 `55f87e3a1448f5cf1cd7d7b9f061846a13b9571eb9b1a1df51eab3d9a9d42429`. Resolve and authenticate its full required native dependency closure (163 packages in the observed acquisition), preserve DLLs/firmware/notices, and pin each package URL/version/hash/signature. The observed keyring is the [official MSYS2 source at commit 5d249077a0cfeec9dbf51515e5e01da413d28859](https://raw.githubusercontent.com/msys2/MSYS2-keyring/5d249077a0cfeec9dbf51515e5e01da413d28859/msys2.gpg), SHA256 `1257d4ccc536c53333445a618039af4c3ea3f56b96601de9af89151ea529c19a`. All observed package signatures authenticated; no expiry/revocation/error flags were seen. Native MinGW binaries run independently of MSYS2's POSIX runtime, so an extracted private directory avoids a Windows installer. This tested bundle's `qemu-system-x86_64.exe` hash is `a812b50865ffcc7ddd43f9c33e9bb1ed7b3501c1f847ee99ede8d4b4a4a93742`. Other host platforms can use their publicly authenticated QEMU build and record it as another environment.

## Guest construction and measured gates

Use a private writable QCOW2 child of an immutable authenticated base. Provision through local `cidata` media or an equivalent documented guest-only setup: systemd/PAM/logind/D-Bus user session, Python 3, Git, curl, zstd, and native build tools. Log in normally as the checking user; do not treat `su`, synthetic user-bus setup, privileged execution, or merely printing security flags as equivalent to the script's actual probes. No host credential sharing, shared filesystem, bridge/TAP or port forwarding is needed.

The observed QEMU invocation, with publicly meaningful placeholders, was:

```text
qemu-system-x86_64 -L <QEMU_SHARE> -machine pc-q35-11.1
  -accel tcg,thread=multi -cpu max -smp 4 -m 4096
  -display none -serial stdio -monitor none
  -nic user,model=virtio-net-pci -no-reboot
  -drive if=virtio,format=qcow2,file=<RUN_DIR>/checking-overlay.qcow2
  -drive format=raw,media=cdrom,readonly=on,file=<RUN_DIR>/seed.iso
```

The tested image booted with QEMU's bundled default firmware. The [QEMU invocation reference](https://www.qemu.org/docs/master/system/invocation.html) and [Canonical QCOW guide](https://ubuntu.com/docs/public-images/public-images-how-to/launch-qcow-with-qemu/) support the mechanics; do not copy their hardware-acceleration or forwarding examples into this TCG-only recipe. Software emulation needs no Windows hypervisor/WSL feature enablement or reboot. It does not establish a full-replay runtime estimate.

In the fresh checking checkout, run the existing commands in order:

```bash
bash scripts/bootstrap_comparator.sh preflight
bash scripts/bootstrap_lean.sh
bash scripts/bootstrap_comparator.sh bootstrap
bash scripts/bootstrap_comparator.sh verify
```

Before bootstrap and replay, record zero project `.olean` objects under `formal/.lake/build`. Retain official pinned Mathlib package caches and trusted checker compilation separately; never import native project objects or the failed attempt's partial build. Preserve Comparator `d03acab...`, exporter `076e8e...`, Landrun `811cfff...`, Go 1.27.2, actual Lean 4.34.1/commit `5045d005...`, and upstream/Mathlib pins in full as recorded by the receipt. The existing strict adapter removes exactly `--best-effort`; it invokes the real pinned Landrun and rejects weakening options. No pin or sandbox check should be changed to obtain a pass.

## What still needs a tested public rerun recipe

An authenticated image/binary/dependency manifest must be publicly retrievable, with exact hashes and license/notices retained. The complete guest provisioning recipe and a generic durable supervisor should be checked in or published as reviewed artifacts; present private orchestration contains account paths and is not itself a public setup dependency. Record kernel/config hash, actual ABI/caps/user-bus/denial probes, input and binary hashes, zero-proof-object receipt, CPU/RAM/swap/disk, cap, full logs and actual comparison result.

Resource/concurrency changes must be explicitly versioned. The observed default Lake build exhausted memory despite a working sandbox. A thread-pool environment hint, a CPU allocation, or a service task limit is not automatically a hard compiler-process scheduler. A fresh layer of the preserved bootstrap state is appropriate for another attempt; the failed replay layer contains partial project objects and must not become the fresh checking input.
