# Bound the in-memory Comparator output summary

`MeasuredRunner` previously read the entire Comparator stdout log into a Python
string after the command exited. A local mocked-process reproduction produced
about 2.25 MB of traced peak allocations for a 1 MiB log and 8.54 MB for a 4 MiB
log. This allocation scaled with log size. It is a separate defect from the
earlier snapshot-cycle retention: long04 never reached Comparator, so this did
not cause its observed OOM.

The [observer delta](source/observer.diff) scans stdout in 64 KiB chunks for the
same three ASCII acceptance phrases used by both real consumers:
`strict_serial_check.run_check` and the historical sampler's `run`. It preserves
phrase matches across chunk boundaries and returns only the found phrases in
`CompletedProcess.stdout` for the `unchanged_comparator` label. The complete raw
stdout file and its SHA-256 remain unchanged. Other command labels retain their
existing empty `stdout` return value. Return codes and both callers' requirement
that **all three phrases** be present are unchanged; kernel and Comparator
execution checks are not replaced by a text-only acceptance claim.

Run the eight local regressions:

```bash
python3 -B -m unittest discover -s tests -p test_comparator_bounded_output.py -v
```

They prove the old runner tries a forbidden whole-file text read, exercise the
new runner with a 1 MiB log while preserving all raw bytes/hash, compare exact
substring semantics across short chunk boundaries and invalid UTF-8, verify
both consumers' phrase tuples, and assemble the new observer/runner/preparation
pin chain. A scoped fixture-only digest adapter exercises missing hashlib.file_digest on Python 3.10 and restores the original module state, including after errors. Global hashlib and frozen runtime source bytes are unchanged. All process launches in these fixtures are mocks.

The [observer recipe](source/observer-recipe.json) and [integration pins](source/integration-pins.json)
derive from the frozen observer and the `metadata-memory-v1` candidate. The
two repaired metadata helpers remain included, without duplicating them.
The small assembler checks every predecessor/result hash and materializes
fresh source files only:

```bash
python3 -B research/strict-sampler-checkpoints/runtime-output-v1/prepare_candidate.py \
  --destination /tmp/bounded-comparator-output-next
```

The assembly also includes the exactly pinned corrected supervisor at
`supervisor/vm_sampler_supervisor.py`, using the separate [tail framing and
phase-order repair](../runtime-tail-v1/). It performs no preparation, proof,
supervisor or VM run. Native validation and a full strict replay remain unrun.
Future media must bind these source pins and the intended longer
invocation/enclosing budgets; the included supervisor still carries the
historical public resource profile, rather than long04's longer profile.
No historical checkpoint or resource profile is modified here, and no retry
is authorized by this packet.

The [independent review](independent-review.md) was performed by a separate AI
agent and covers both source-only repairs and their adversarial local checks.
