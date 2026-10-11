# Finite burn-once dependent attempts

11 October 2026. This additive Lean packet proves the finite hybrid lemma
behind [spaced terminal attempts](../../docs/spaced-defect-sampling.md).
It charges the initial burn-in error once and controls dependent rejections:

`TV(output after R marks, nu) <= delta0 + (1-s)^R + (R-1)rho/4`, for `R>0`.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| A dominated survivor's centered density has energy at most one quarter. | `Marked.Survivor.dominated_centered_energy` | Finite probability pi; density in `[0,1]`. |
| One spacing block differs from complete refresh by at most `rho/4` on survivors. | `Marked.Survivor.survivor_mixing_of_centered_l2` | Positive pi, Markov block K, detailed balance, nonnegative rho and centered L2 contraction by rho. |
| Successive real blocks cost at most the number of replaced blocks times the survivor allowance. | `Marked.Survivor.hybrid_bound` | Stationary pi, Markov K, accepted-output subkernel A and the explicit survivor-mixing premise. |
| Complete-refresh attempts have the stated target/fallback mixture. | `Marked.Survivor.refresh_output_law` | Probability pi and nu; stationary accepted-output mass `pi A=s nu`. |
| Initial error is charged once to the whole bounded output kernel. | `Marked.Survivor.burn_once_bound` | The hybrid hypotheses, stationary output identity and `s<=1`. |
| The L2 premise supplies that finite bound. | `Marked.Survivor.burn_once_l2_bound` | The reversible L2 hypotheses and stationary output identity. |
| R positive marks have the headline error bound. | `Marked.Survivor.spaced_terminal_bound` | The preceding hypotheses; post-burn vector alpha has `TV(alpha,pi)<=delta0`; `R>0`. |

The [fresh receipt](results/verification.json) gives every exact Lean type
and dependency-closure size. The [compiled environment](results/audit.stdout.json.gz)
records the full closure of each headline, declaration inventory and axioms.
Both sources compiled with Lean 4.34.1 and `autoImplicit=false`; the audit
found only `propext`, `Classical.choice`, and `Quot.sound`, or subsets.
Independent AI review checked the source and saved compilation evidence.

## Definitions and scope

State and output spaces are arbitrary finite types. Vectors and kernels have
real entries, `bind mu K(y)=sum_x mu(x)K(x,y)`, and TV is half the L1 distance.
K is the spacing block itself. A is nonnegative with row sums at most one;
failure retains the current state. Its stationary successful output is `s nu`.
Detailed balance is `pi(x)K(x,z)=pi(z)K(z,x)`.

The centered L2 premise says that every g of pi-mean zero satisfies

`sum_x pi(x)(sum_z K(x,z)g(z))² <=rho² sum_x pi(x)g(x)²`.

No positive lower bound on s is needed for the finite inequality, including
`s=0`; one is needed for a useful retry schedule. The statement even allows
a signed initial vector alpha. For an actual probability input, separate
`bind_probability` and `output_markov` lemmas certify a probability output.
The recursive definition includes a transition after the last failure;
`output_one` proves it cancels because the remaining output is constant fallback.
Only the `R-1` intervening blocks contribute to the bound.

The [stronger resolvent refinement](../../docs/resolvent-rejection.md) has a
different bias and killed-chain failure bound. It is reviewed mathematics
and tested code, **not** the theorem compiled in this packet.

## Reproduce and extend

With the repository's pinned compiler and built baseline dependencies:

```sh
python3 research/repair-accept/verify.py --scope spaced-attempts \
  --output .local/spaced-attempts-fresh
```

Use a fresh output path. The shared runner does not download dependencies
or overwrite earlier results. It hashes sources, fresh objects, the compiler
and all imported objects, and audits the two actual defining modules rather
than a handwritten theorem list. Logs retain one harmless unused-simp warning.

This is ordinary Lean compilation with trusted pinned compiler and reused
dependency objects. It is not a default-target rebuild or strict Comparator
replay. The remaining physical and implementation obligations are:

- Derive the block contraction and post-burn error from the defect gap.
- Compile the uniform perturbation extension `W eta+R zeta`.
- Connect the real finite kernels to repair, completion and dyadic execution.
- Compile the integer schedules, operation/bit accounting and encoded machine.

Historical proof receipts and the default sampler are unchanged.
