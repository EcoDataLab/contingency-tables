# Strict observer repair and bounded sampler replay

The procfs observer now treats denied or vanished executable observations as an **incomplete whole sample**, while retaining the existing five-second watchdog and rejecting positively identified compiler overlap. The [previous full attempt](../second-proof-failure-v1/) remains frozen: it built nine of 679 historical modules, then stopped on `PermissionError(13)` reading `/proc/3555/exe`. Its failed dependency command has no completed return code. That was an observer failure; the original kernel access decision is unknown.

Fourteen deterministic observer regressions pass. A separate real Linux diagnostic observed transient denied-access recovery, persistent denial triggering the retained watchdog, and two positively identified toy processes triggering overlap cleanup. The toy executable classifier is diagnostic-only. These tests establish no proof, export, kernel replay or sampler acceptance.

A fresh full historical-sampler attempt started on 6 November 2026 with this reviewed observer and a separately versioned resource profile. Install and real sandbox preflight completed; baseline authentication completed and the explicit memo normalization/fresh authentication/frozen repeated gates were active at the saved observation. **Strict sampler acceptance remains pending.** The [current outcome](outcome.json) records the exact observation and scope. A running job, completed module count or successful setup is not acceptance.

## Repair and regression coverage

The exact [observer](source/strict_serial_check.py) SHA256 is `b5e8c0f95fdd5f6b9193c2b0537782b242d0fe0c269dae7b5a7a4c73a32cb1f0`; its [delta](source/observer.diff) is relative to the unchanged original `05df96db18964f76a109d72d876ba7c72f799782e1c54bad9f587cd213110e7e`. Only `compiler_pids` and the corresponding `MeasuredRunner.__call__` observation handling change. `PermissionError` and `ProcessLookupError` retain per-PID errno/path/error evidence and any positively identified compiler PIDs; they never return a partial or zero count. Incomplete samples do not increment valid sample counts, set a peak, or reset the watchdog. Complete observations can recover. Known overlap still aborts, including when another PID is unreadable. Other errors fail closed. The existing short-stage unobserved policy remains explicit.

The [versioned runner](source/versioned_runner.py) differs from the prior measured guard only in its observer asset pin and header. The [memo-preparation helper](source/prepare_memos.py) changes only its exact candidate-runner pin. Their function/class AST bodies are unchanged. Original admission/content/source/configuration/alias/cache checks, real sandbox, export, default kernel, comparison, hard deadlines and owned cleanup remain in force. The quiet-cache premise of the [versioned guard](../versioned-guard-v2/) remains explicit.

The normal Python suite includes 36 offline checks: 14 observer regressions, 19 supervisor/resource/cleanup checks and 3 progress checks. Run:

```bash
python3 -B -m unittest discover -s tests -p test_comparator_observer.py -v
```

The [raw toy diagnostic archive](evidence/toy-guest-evidence.tar.gz), [member authentication](evidence/toy-collection-authentication.json), [summary](evidence/toy-summary.json), exact diagnostic sources and fixture logs are retained. Recovery had 3 incomplete and 6 valid observations, peak 1, in 3.288 seconds. Persistent denial had 17 incomplete and 0 valid observations, null peak, and stopped its owned service at 5.068 seconds. Positive toy overlap had peak 2 and stopped its owned service after 1.035 seconds. All three owned services/cgroups and the VM were closed. This does not identify the cause of the historical PID 3555 denial.

The separate [AI source/evidence review](independent-review.md) passed after correcting two public documentation/reference issues. It is distinct from compiler execution and final strict acceptance.

## Exact target and resource profile

The target is the historical retained 679-module sampler: source archive `47e864e49025da1e505c32ae1c5f23428ed900b1ecc64468cb72478095824a84`, source freeze `2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd`, roots `Math115.StrictSamplerStatement` and `Math115.StrictSamplerSolution`. It excludes all newer sampler/program/runtime-degree research. It checks the original existential bounded-sampling statement and the literal original public machine, as described by the [separate challenge](../../strict-sampler-challenge/). Acceptance requires all 1362 original command stages, final inventories/rehash and actual unchanged exporter/default-kernel/Comparator acceptance messages, followed by evidence authentication.

The [versioned supervisor](source/vm_sampler_supervisor.py) retains the pinned image/backing/tool checks, fresh 80 GiB **virtual** disk, guest 10 GiB RAM/one CPU/no NIC/no swap, 12 GiB host-free-memory admission, 12,600 second outer cap and 7,200 second inner proof deadline. The [disk-profile delta](source/resource-profile.diff) requires 40 GiB initial host free disk, stops the owned VM if host free space falls below 20 GiB or its observed child-file length exceeds 16 GiB, and samples resources every second. The original 80 GiB host admission check remains unchanged in its historical source/receipt; no files were deleted to fit this attempt.

These are sampled stop guards, not an OS storage quota or a guarantee that the complete closure fits. Child file length is conservative relative to allocated disk blocks. The prior attempt's 874,774,528 byte child covered only nine modules, so it does not establish full-build growth. The [fresh pre-staging measurement](evidence/prestage-resources.json) records 56.69 GB host disk free and 16.76 GB RAM free, with no competing research processes. Resources were separately admitted through the shared workstation router before staging and launch. A resource limit produces a failed attempt with evidence and owned cleanup.

## Reproduction boundary

[Reproduction references](reproduction-references.json) bind the exact public support files and candidate layout. The observer runs from an additional owned tools directory; the original runner/authenticator remain at their unchanged original locations. No previous native or failed strict proof objects may be reused. The original sandbox prerequisites and real denied-access probes are required. Never substitute a weaker sandbox.

The supplied source/fixtures, exact toy evidence and pending-attempt controls are inspectable. A complete independently reproducible VM package is still unavailable: retained vendor image availability and private host-specific ownership/staging wrappers remain gaps documented in the [VM environment notes](../../../docs/strict-comparator-vm.md). This packet does not replace those missing inputs with an assertion of reproducibility. Public-repository commits do not alter the active guest's separately frozen historical input archive, media or configuration.
