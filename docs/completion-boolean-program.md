# Executable prefix codec and independent Boolean retries

The [CompletionBooleanRetry module](../formal/Math115/CompletionBooleanRetry.lean)
now compiles and executes in pinned Lean. Its 25 declarations passed an
isolated standard-axiom audit. This is an additional verified component after
checkpoint 8, separate from that checkpoint's 638 aggregate audits and its
632-declaration Linux run.

The module supplies executable finite-matrix encoding, signed prefix decoding,
the acceptance test, and bounded first-success retries. Negative decoded cells
are rejected before conversion to natural numbers. A decoder that silently
truncated negative cells would not implement the proved table map.

For any supplied fine-table draw consuming `q` Boolean bits, `flatRetry`
splits exactly `J*q` bits into `J` consecutive words of length `q`. The explicit
index bijection preserves their order. Uniformity of the whole bank therefore
gives the independent trial law used by the counting and accuracy proofs.

`completion_flat_law` identifies this actual computation with the normalized
retry law: return the first accepted table, or the supplied feasible original
fallback if all trials reject. A successful output equal to the fallback
remains a success. Unused suffix words after an early success do not change
the distribution. The word construction also handles `J=0` and `q=0`.

## Executed examples

The saved [native example source](../formal/results/completion-boolean-retry/NativeExamples.lean)
and [output](../formal/results/completion-boolean-retry/native-examples.log)
record six Lean evaluations:

| Computation | Output |
| --- | --- |
| Encode the 2×2 identity table with `k=3` and the supplied digit | `[[11,4],[4,11]]` |
| Decode that fine table | `some [[1,0],[0,1]]` |
| Decode a fine table with a negative decoded cell | `none` |
| First success after two rejected words | `7` |
| All trial words reject | Fallback `99` |
| Empty word bank | Fallback `99` |

These are evaluations of the actual Lean definitions. The general law
identity is a theorem; the six examples are separate execution checks.

## Reproduction and limits

The [verification receipt](../formal/results/completion-boolean-retry/verification.json)
records the frozen source, compiler result, all 25 named axiom reports,
native outputs, and artifact hashes. The [independent source review](../formal/results/completion-boolean-retry/source-review.json)
checks the signed arithmetic, word order, fallback semantics, and authored
evidence. Its `.local` paths identify the original review inputs; the public
receipt supplies the corresponding downloadable logs and drivers.

After the repository's [pinned Lean setup](formal-verification.md), a fresh
checkout can build this additional module and run its audit and examples:

```sh
cd formal
export ELAN_HOME="$PWD/../.tools/elan"
../.tools/elan/bin/lake build Math115.CompletionBooleanRetry
../.tools/elan/bin/lake env lean -j1 -DautoImplicit=false results/completion-boolean-retry/AxiomAudit.lean
../.tools/elan/bin/lake env lean -j1 -DautoImplicit=false results/completion-boolean-retry/NativeExamples.lean
```

The recorded local verification used direct Lean compilation and existing
dependency objects, not a fresh dependency-closure build. The aggregate
`Math115` target does not yet import this additional module. It has not been
independently reproduced on Linux or checked with strict Comparator.

The theorem is generic in the supplied fine-table draw. It does not establish
that an arbitrary draw is accurate or executable. Connecting the pinned
canonical dense program to this interface, assembling every physical state's
oracle, and charging binary list-machine and complete outer-sampler costs
remain separate obligations. Native execution alone is not a polynomial
machine-cost theorem or a practical sampler benchmark.
