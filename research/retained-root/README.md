# Retained-root transport components

11 October 2026. This additive packet preserves the negative diagonal terms
in the actual correction matrix. The [reviewed global derivation](../../docs/retained-root-transport.md)
then gives `32p⁴V³` rational and `64p⁴V³` dyadic inverse-gap allowances.
The local transport and scalar implications below compile; the complete
global physical gap assembly remains open.

| English claim | Lean statement | Hypotheses and scope |
|---|---|---|
| Adjacent physical means satisfy the retained correction/leaf-energy inequality. | `Math115.RetainedRootPhysical.adjacent_physical_box_leaf_transport_retained` | Actual soft-to-hard physical context, uniform width at least two, valid prefix/display, positive adjacent child masses; truncation remains inside the correction kernel. |
| The correction entries are the neighboring values of one fixed kernel. | `Math115.RetainedRootPhysical.retainedRootCoefficient_shift` | Valid adjacent display; natural-subtraction and coordinate-boundary cases are explicit. Interior support boundaries need not vanish. |
| The retained hard coefficient is nonnegative. | `OAI.ContingencyTables.IntegerWeightedTransport.retainedRootCoefficient_nonnegative_limit` | Actual soft-signature inequalities, pointwise finite limits, positive limiting child masses; no convergence of currents assumed. |
| Interior and anchor correction terms obey their scalar caps. | `Math115.RetainedRoot.interior_cap`, `endpoint_cap` | Positive ordered adjacent masses, prefix-mass and correction-mass inequalities. |
| The explicit new repair coefficient is at most `2p³V³`. | `Math115.RetainedRoot.fullCoefficient_bound` | Natural `p,V≥2`; this bounds a scalar expression, not an assumed physical gap. |
| Old scales imply `4000d¹³` rational / `8000d¹³` dyadic. | `Math115.RetainedRoot.rational_uniform_d13`, `dyadic_uniform_d13` | `p≤d`, `V≤5d³`, and the scalar premises. |
| New scales imply `42592d¹⁰` rational / `85184d¹⁰` dyadic. | `Math115.RetainedRoot.rational_uniform_d10`, `dyadic_uniform_d10` | `p≤d`, `V≤11d²`, and the scalar premises. The physical scale/gap assembly is separate. |

The [fresh receipt](results/verification.json) contains exact statements,
source/compiler hashes, imported-object hashes, and each headline's full
transitive dependency closure in the [environment audit](results/audit.stdout.json.gz).
The source inventory is generated from the actual compiled defining modules.
It overlaps other additive packets and must not be added to their counts.
Only standard Lean axioms occur. Compiler and reused baseline imports are
trusted; this is ordinary compilation, not strict Comparator replay or a
fresh default-target rebuild.

The global argument must use the boxed theorem consistently. The existing
boxed auxiliary repair cap needs `hB` and `hcap`; the local theorem does not
discharge them. Mode-anchor summation by parts, exact same-box correction cap,
conditional-variance decomposition, edge ownership and trace normalization
remain to be assembled in Lean. The reviewed proof spells out these steps.
Separate AI agents reviewed the source and mathematical interfaces; no outside
human review is claimed.

```sh
python3 research/repair-accept/verify.py --scope retained-root \
  --output .local/retained-root-fresh
PYTHONPATH=src python3 experiments/retained_root.py \
  --output .local/reports/retained-root.json
```

Use the pinned Lean compiler and already-built baseline dependencies, with a
new output directory. The [exact experiment](../../reports/retained-root.json)
checks abstract paths and actual mixed-completion contexts, including
nonzero correction terms outside the positive child support.
