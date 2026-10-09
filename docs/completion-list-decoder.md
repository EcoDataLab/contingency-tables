# A verified binary-list completion decoder

The rounding step now has an ordinary program over lists of binary natural
numbers, with a proved polynomial machine-cost bound. Its output is exactly
the accepted table, or rejection, used by the completion-accuracy theorem.
This closes the decoder's representation and cost bridge in the route to
the smaller `80,000d¹⁷` auxiliary-chain bound.

The program takes a dilation factor `k` and a list of rows. It sums rectangular
prefixes, divides by `k`, takes mixed differences, and removes the padding of
two. It checks the sign before natural subtraction: a negative decoded cell
causes rejection. For example, `k=3` and `[[9,12],[6,9]]` decode to
`some [[1,2],[0,1]]`, whereas `[[5]]` is rejected.

Every enumerated index is bounded by a supplied row or column list. A large
binary number cannot ask the decoder to generate that many cells. The
program is total even on ragged inputs and at `k=0`; the table-correctness
theorems apply to rectangular table encodings, including empty dimensions.

## What is proved

In [LatticeCompletionProgram.lean](../formal/Math115/LatticeCompletionProgram.lean):

- `polynomial_decode` bounds charged TreeTyped machine work and encoded
  output weight by a polynomial in the binary input weight. Arithmetic on
  the dilation factor and supplied entries is included.
- `decode_code` identifies the list program with the previously verified
  [typed Boolean decoder](completion-boolean-program.md), preserving every
  row, column, and acceptance decision.
- `decode_fineTable` identifies that output with the actual geometric
  finite-table trial used by the [completion law](completion-oracle-formalization.md).

The machine-cost theorem covers this decoder. Dense sampling, repeated
completion draws, the physical walk, and their composed costs remain
separate proof obligations. The exponent `17` still describes an inverse
spectral gap; it is not a complete sampler runtime exponent.

## Verification

The frozen module compiled with Lean 4.34.1, all **52 declarations** passed
the named standard-axiom audit, and **nine native boundary checks** passed.
An independent source and evidence review checks the same source hash.
The [receipt](../formal/results/lattice-decoder/verification.json) records
the source, drivers, clean logs, and scope.

The native cases cover empty shapes, zero dilation, rejection of a negative
cell, accepted and nonsymmetric tables, ragged inputs, and a divisor of
`2^100`. They supplement the general theorems; they are not measurements of
the complete sampler.

This local verification restored 174 missing upstream modules and reused
the remaining dependency objects and official package cache. It is an
isolated component, separate from checkpoint 8's 638 aggregate audits and
632-declaration Linux result, and from the preceding 25-declaration Boolean
module. A fresh Linux run and strict Comparator replay do not yet cover it.

With the pinned environment and dependencies available, compile and audit
the published source from `formal/`:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false -o .lake/build/lib/lean/Math115/LatticeCompletionProgram.olean \
  Math115/LatticeCompletionProgram.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false results/lattice-decoder/AxiomCheck.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false results/lattice-decoder/BoundaryCheck.lean
```
