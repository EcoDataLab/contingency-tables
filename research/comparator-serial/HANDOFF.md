# Contributor handoff

This directory is an experimental build-orchestration draft, ready for independent source review. A strict Comparator pass remains open. This stage ran 33 candidate tests, 16 existing planner tests, and Python syntax checks, all offline; Lean, Lake, systemd, and a Linux VM were not invoked. Mocked service/process tests do not establish real sandbox or trace compatibility.

Read README before trying the entrypoint. The project/upstream/tool pins and original descriptor are fixed. The existing strict adapter is unchanged. The adapter adds only documented orchestration flags to the original two Lake build calls; it preserves exporter commands and sandbox/path/network options. The fresh-project guard is at the start of this new whole serial-build-plus-comparison workflow, not an execution of the old `verify` command after prebuilding.

Next steps are independent source review, plan-only in an exact fresh bootstrapped checkout, and a separate real strict sandbox/default-trace smoke check. Resolve no-build/cache trace behavior, conservative artifact-mutation checks, sampled process telemetry, original probe child-unit cleanup, durable outer supervision, measured RAM/disk headroom, and exact public guest artifact availability before starting the original closure anew. Do not reuse partial objects or infer a working checker result from the draft.

`manifest.json` records source/helper/test hashes and official source pins. `validation.json` and `validation-*.log` record the actual offline commands/results. The root repository's existing failed-attempt archive documents the measured Linux environment and its pre-comparison memory failure; this directory adds no positive comparison evidence.
