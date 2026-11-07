# Pinned upstream dependency compilation

Three unchanged modules from the pinned OpenAI commit were absent from the
prepared object set. The initial [preflight](../preflight-01.json) stopped
before starting Lean. They were then compiled in dependency order:
`ExactIntegerChoice`, `ExactIntegerProgram`, `ExactIntegerRetry`.

[Compilation records](compilation.json) bind every source and output object
to its hash, compiler options, exit status and elapsed time. All recorded
output streams were empty; the public empty copies match those digests.
The [object inventory](imported-objects.json.gz) lists these three outputs.
No upstream source or pin changed. The proposal module's full headline
closures audit the dependencies actually used by its statements; this does
not claim an independent audit of every declaration in these upstream files.

To prepare a replay, compile these three modules from the pinned upstream
checkout with Lean 4.34.1 and the ordinary prepared dependency objects. Add
the resulting object root to `LEAN_PATH` before running the proposal
packet's `REPRODUCE.sh`. The script merges namespace roots while retaining
that search order, so a partial OAI object root does not hide other modules.
