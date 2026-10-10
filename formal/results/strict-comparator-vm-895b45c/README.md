# Strict Comparator: original-challenge attempt

The strict Linux VM environment passed its measured sandbox prerequisites and real pinned Landrun denial probes. The original three-theorem replay then exited **1** while building the solution module: 29 Lean process executions failed with ENOMEM (`error code: 12, not enough memory`). No candidate export, candidate kernel acceptance, or successful theorem comparison was reached.

This is an environment/resource failure before comparison. It does not establish that the candidate theorems are false or that a kernel rejected their proofs.

The attempt used an authenticated Ubuntu 26.10 amd64 cloud image dated 20261006, kernel `7.3.0-8-generic`, measured Landlock ABI 11, a non-root user with zero effective capabilities, and actual systemd `NoNewPrivileges`/AF_UNIX enforcement. QEMU 11.1.2 ran through multithreaded TCG with four virtual CPUs, four GiB RAM, no swap, and an 80-GiB sparse disk. Networking was outbound-only with no host forwarding/listeners. The repository, upstream descriptor, Mathlib, Comparator, exporter, Landrun and Go pins are recorded in the JSON receipt.

- `strict-comparator-attempt.json`: structured result, environment, source/binary pins, timing and raw/sanitized evidence hashes.
- `strict-comparator-failed-build.log`: replay-only diagnostic log. Its private checkout prefix and generated user-service identifier are replaced with documented placeholders; all module names and error/version spelling are retained.

The guest wrapper reported 5969.576 seconds (~99m30s). The systemd service reported a 3.3G memory peak with zero swap. The challenge template built and exported; its three `sorry` warnings describe the upstream specification placeholders, not accepted candidate proofs. The immutable input/backing-layer hashes recorded after the attempt match their earlier receipts.

Raw evidence is preserved privately. Its reported guest-log hash was independently reconstructed from the terminal serial log and matched exactly. These files preserve the failed attempt. The [environment and reproduction notes](../../../docs/strict-comparator-vm.md) identify the measured prerequisites and what remains necessary for a successful public rerun.
