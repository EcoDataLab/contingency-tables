# Variable-capacity hard-limit bridge

This additive Lean packet proves a hard-limit transport inequality that retains
each coordinate's own capacity. It supports the reviewed
[rectangular defect-chain derivation](../../docs/rectangular-defect.md): inverse
gap at most `20000d^(31/2)`, or `40000d^(31/2)` with the dyadic proposal, for
positive ordinary margins below `U=5d^3` on both sides, at any aspect ratio.
The entire numerical physical-chain bound is not yet a Lean theorem.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| The quadratic auxiliary kernel commutes with pointwise finite-sum limits | `quadraticAuxiliaryKernel_tendsto` | Arbitrary finite list of natural capacities, pointwise convergence along a filter. |
| Variable-width transport passes to positive hard endpoints | `integer_root_leaf_transport_widths_limit` | Nontrivial filter, capacities at least two, eventual nonnegativity and the source positive/removal slice hypotheses, a valid root display, positive limiting endpoint masses. |
| The same limit retains box and degree truncation in the quadratic auxiliary coefficient | `integer_box_root_leaf_transport_widths_limit` | Same hypotheses; the coefficient uses the explicitly truncated hard weight. |

All names are in `OAI.ContingencyTables.IntegerWeightedTransport` in
[VariableWidthLimit.lean](formal/VariableWidthLimit.lean). The
[environment report](results/audit.stdout.json.gz) enumerates every declaration
defined in the module and the complete dependency closure of the boxed theorem.
Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` occur.

The [receipt](results/verification.json) records fresh ordinary compilation of
the published source with pinned Lean 4.34.1 and reused baseline dependencies.
[Imported-object hashes](results/imported-objects.json.gz) and
[compiler output](results/compiler-output.json.gz) preserve that check's inputs
and result. This is separate from the default target and its historical Linux
receipt, and is not Comparator verification.

After the ordinary baseline dependencies have been built as described in the
[main README](../../README.md), reuse the existing scoped verification runner:

```sh
python3 research/repair-accept/verify.py --scope rectangular-defect \
  --output .local/rectangular-defect-recheck
python3 experiments/variable_capacity_transport.py \
  --output .local/reports/variable-capacity-transport.json
```

The mathematical review and exact finite checks also establish the intended
capacity translation, weighted auxiliary repair argument, and physical edge
ownership. Formal assembly still needs the new capacity-dependent word/context
map, its finite variance identities, the physical specialization, and the final
gap arithmetic. No change to the encoded sampler or complete runtime degree is
claimed by this packet.
