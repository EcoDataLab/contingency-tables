# Bounded coin for a partial repair

24 October 2026. The existing integer threshold and little-endian decoder supply the success coin. A reserved k-bit bank is fresh; padding failures return `none` and ignore that bank. Successful rows use the clipped ratio `min(c0,ell)/ell`.

`finiteRow_variation` gives at most 2^-k error for the entire option-valued row when the supplied counter equals the actual fibre count. A reached successful output supplies the witness that ell>0. The bind theorem adds endpoint-law error before conditioning. The actual-counter successor discharges the generic counting premise.

[Source](formal/ResearchPhysicalTraceJoin/GeneralBoundedCoin.lean) and
[verification receipt](attempt-03/verification.json) bind the exact checked bytes.
Ordinary Lean compilation and the environment audit passed. Every declaration
in this module and every dependency in each headline closure uses only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

| Headline | Declarations in its full dependency closure |
|---|---:|
| `PartialRepairCorrection.finiteRow_variation` | 9542 |
| `PartialRepairCorrection.finiteRow_bind_variation` | 9580 |

Use `REPRODUCE.sh` with the pinned Lean compiler and prepared dependency
objects in `LEAN_PATH`, writing to a new output directory. This additive
check reuses trusted imports; it is separate from a fresh default-target
build and strict Comparator replay. Earlier failed attempts retain their
exact source and diagnostics. Compiler-generated error placeholders in a
failed attempt are not checked results.

The complete reference-branch composition is documented in
[the bridge note](../../docs/corrected-reference-sampler.md). Initialization,
other branch programs, encoded realization and charged costs remain separate.
No complete-machine exponent or practical speed result follows from this module.
