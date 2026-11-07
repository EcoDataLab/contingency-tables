# Preserve physical-line context in the bounded serial tail

The VM supervisor could record a result marker that was never at the beginning
of a physical output line. It reparses its retained serial tail on each read,
including empty reads. Cropping a long line to the last 256 KiB could place a
marker at byte zero of that tail, creating a false line boundary.

A concrete old-code counterexample first parses
`prefix-not-a-line-MATH115_C11_CHECK_RESULT=0` followed by a newline and sufficient
padding. That first parse correctly records no result. Cropping leaves the tail
starting at `MATH115`; reparsing it then incorrectly records exit code zero.
This affects the supervisor's observed markers. It does **not** demonstrate
exporter, kernel, Comparator or authenticated full-challenge acceptance.

The minimal [delta](source/supervisor.diff) reserves one byte of predecessor
context whenever a tail is cropped. It preserves a real CR/LF boundary as a
newline; otherwise it prefixes the suffix with NUL, which cannot create a fresh
anchored line. The tail stays within its existing size bound. All other
supervisor logic, result checks, time/resource limits and cleanup are unchanged.
OSC terminal-control contents are also suppressed while a frame is incomplete.
If cropping would discard an OSC opener while retaining its contents, the
candidate fails closed; it does not reinterpret those contents as plain output.
Raw byte offsets and exact EOF matching preserve this rule across Unicode and
trailing newlines. This is a bounded framing guard, not a terminal emulator.

A separate phase-order defect also existed in this parser: only the final
phase in a batch was considered, so `proof` then `repair` (or `proof`, `repair`,
`proof`) could conceal a backward transition. The candidate checks the whole
newly completed phase sequence against the prior current phase before retaining
the last phase. A bounded event cursor remembers only recognized events still
present in the returned tail, so replayed events are skipped and trimmed history
cannot conceal `repair` then `proof` after a previously observed `proof`.
Valid ordered batches and repeated-tail parsing without timer reset remain
intact. No observed run failure is attributed to this.

Run the nineteen local adversarial regressions through normal discovery:

```bash
python3 -B -m unittest discover -s tests -p test_comparator_tail_boundary.py -v
```

They reproduce the old false result, cover every two-part split and empty read,
oversized lines without a newline, genuine LF/CR/CRLF markers, the real 256 KiB
tail with 64 KiB reads, other marker families, and many chunk sizes against a
full-stream physical-line oracle. Separate OSC cases cover a second old-code
counterexample, incomplete frames and split BEL/ESC-backslash closures.
Phase regressions cover same-read and trimmed-history cases, with partial phase
completion processed once. Partial result tokens require a completed physical
line: a read ending in `=0` is not accepted before later bytes determine whether
the token is `0`, `01`, or invalid text. CR alone remains the existing accepted
line terminator, alongside LF and CRLF; this is not generic terminal-redraw
interpretation.
No process, VM or proof is launched.

The [exact recipe](source/supervisor-recipe.json) pins the original public
supervisor and corrected result. To materialize a new, unused source file:

```bash
python3 -B research/strict-sampler-checkpoints/runtime-tail-v1/derive_supervisor.py \
  --output /tmp/tail-fixed-supervisor.py
```

This derives only the parser correction from the historical public profile. It
does not supply the later long04 budget/media/lease profile or authorize a
retry. Every historical checkpoint, including `metadata-memory-v1`, remains
unchanged. Native supervision with this candidate remains unrun.

The [separate AI review](../runtime-output-v1/independent-review.md) covers both
runtime repairs and their independent counterexamples; it is not native replay.
