# Ideal ordinary-table output after the general defect trace

24 October 2026. This result connects the actual defect/completion pairs to ordinary tables through completion-retaining repair, the actual padding test, and an inverse-fibre acceptance coin. At the ideal stationary input, every ordinary table has the same successful mass. The inverse count and the acceptance lower bound are derived from the actual map.

**Checked:** all six modules passed ordinary Lean compilation and full assumption audits. Separate AI source review found no mathematical blocker.

## Objects and hypotheses

Let r,c be the ordinary margins after removing zero rows and columns. This result concerns the nontrivial branch with m,n>=2 and positive reduced margins. An actual feasible defect start is supplied; constructing that start and selecting the other margin-shape branches remain separate obligations.

The source mask declares cell (i,j) small exactly when r_i<U or c_j<U. Write:

- N for the number of ordinary tables with margins r,c;
- Z for the number of actual pairs (positive defect state, retained completion);
- p for the number of small cells;
- a=#{i:r_i<U} and b=#{j:c_j<U};
- c0=max[a*(n*a-1), b*(m*b-1)].

For the local inverse and ideal-law results, L>=1. The success bound below specializes to the checked scales U=11*d*(m+n-2), L=7, where d is the existing dimension allowance. The nontrivial branch has p>0 and a nonempty actual defect/completion type. Equal totals and existence of an ordinary table are enforced by the table objects used in the statements.

## Exact inverse test

Fix an ordinary table X. Its successful padded target is Y=X+L on large cells, with small entries unchanged. For distinct ordered small labels s,t, put v=(row(t),col(s)). There is exactly one actual joint predecessor with these labels precisely when:

- v is small and X_v>0; or
- v is large and both ordinary residual slacks are positive:
  r_row(t)-sum_small_row(X,row(t))>0 and c_col(s)-sum_small_column(X,col(s))>0.

The explicit inverse views are x=Y-e_v+e_t and q=Y-e_v+e_s. Their feasibility, source capacities, positive completion weight, canonical labels, and literal forward repair are checked. At a large crossing the retained dense completion loses one unit. L>=1 makes that subtraction possible; positive padding alone does not replace either ordinary slack test.

Let ell(X) be the finite sum over ordered small label pairs of 1 when this test holds and 0 otherwise. The actual ordinary-output fibre has exactly ell(X) members. This count uses ordinary small entries and ordinary residual slacks; it does not require completion counts or Z. The closed factorization D0+abuv is not part of this result.

Positive original margins provide explicit injective label families of sizes a*(n*a-1) and b*(m*b-1). Hence ell(X)>=c0 for every ordinary X. With m,n>=2 and p>0, c0>0.

## Ideal correction and success

Start with a uniform actual defect/completion pair. Repair while retaining its completion, reject unless every repaired large entry is at least L, then accept with probability c0/ell(X) and unpad. The checked lower bound makes this a valid coin. Every ordinary table X has unconditional successful mass

    Pr[output=X] = c0/Z.

Consequently the total success probability is s=N*c0/Z, and successful masses have exactly the uniform ordinary-table proportions. In the stated nontrivial branch s>0, so conditioning on success is uniform.

At U=11*d*(m+n-2), L=7, the actual count bound is Z<=2*p*(p-1)*N. Therefore

    s >= c0/[2*p*(p-1)].

No claim c0>=p/4 or simplified linear-in-p success bound is made here.

| English claim | Lean statement | Main hypotheses |
|---|---|---|
| Explicit arithmetic candidates are exactly the full joint repair fibre | `inverseFibreEquiv` | An ordinary table X; the displayed arithmetic test defines the candidate type |
| That test is exactly ordinary support or ordinary row-and-column slack | `inverseLocalTest_iff_support` | L>=1; an ordinary table X |
| The actual ordinary-output multiplicity equals the finite label count | `terminalOutput_card_eq_supportCount` | L>=1; an ordinary table X |
| The documented c0 is a lower bound for every inverse count | `inverseSupportAllowance_le_count`, `terminalInverseCount_lower` | Positive reduced margins; L>=1 for the actual output count |
| c0 is positive in the nontrivial branch | `inverseSupportAllowance_positive` | m,n>=2 and p>0 |
| Every ordinary table has successful mass c0/Z | `terminalCorrected_mass` | L>=1, positive reduced margins, nonempty actual joint input type |
| Total success is N*c0/Z; successful masses have uniform proportions | `terminalCorrected_success`, `terminalCorrected_uniform_proportions` | Same ideal-law hypotheses |
| The sharper scales give Z<=2*p*(p-1)*N | `actualShape_defectJoint_card_le` | The stated U,L specialization |
| Success is at least c0/[2*p*(p-1)] | `actualShape_terminalCorrected_success_lower` | Stated scales, positive reduced margins, nonempty actual joint input type |
| Success is strictly positive | `actualShape_terminalCorrected_success_positive` | Same, with m,n>=2 |

## Delivery boundary

This is an ideal one-trial law. The earlier scheduled walk and fresh terminal completion draw approximate the uniform joint input, starting from a supplied feasible defect state. Connecting that finite-word input to this correction remains separate.

The acceptance coin here has exact rational semantics. Its finite-word rounding, precision schedule, retry amplification, initialization, zero-margin preprocessing, no-small-cell and singleton branches, and encoded execution costs are not supplied by this composition. It does not establish a complete general encoded sampler or a new runtime exponent.

## Evidence and reproduction

The [composed Lean source](formal/ResearchPhysicalTraceJoin/GeneralTerminalLaw.lean) compiled in 48.28 seconds; its [assumption audit](attempt-03/verification.json) passed in 88.28 seconds with seven complete headline dependency closures. Only `propext`, `Classical.choice` and `Quot.sound` occur. The compiler and reused input objects remain trusted. This is an additive module verification, separate from the historical default-target Linux build and Comparator scope.

The [separate AI source review](AI-SOURCE-REVIEW.md) records all six exact source hashes and the mathematical scope. It is AI review of AI work, not human review or a second kernel. [Failed attempts](attempts.json) retain the original sources and projected diagnostics.

The six packets, in dependency order, are:

1. [Exact inverse](../physical-trace-general-inverse/): construct and recover actual joint predecessors.
2. [Support/slack count](../physical-trace-general-support/): characterize and count successful predecessors.
3. [Positive lower bound](../physical-trace-general-lower/): derive the shape allowance c0.
4. [Actual denominator](../physical-trace-general-count/): reuse the smaller-scale marked-padding theorem.
5. [Ideal acceptance rule](../physical-trace-general-acceptance/): reuse `RepairAcceptanceCoin` for the rational correction.
6. This composed terminal-law packet.

Prepare the pinned Lean 4.34.1 compiler, prior dependencies (including the checked `GeneralRepair`, `Research.ReciprocalCount`, `RepairAcceptanceCoin`, and `ResearchAudit.EnvironmentAudit`) and these packets' object roots. Each packet provides the same additive replay interface:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The scripts compile the specified module and audit its environment; they download or rebuild no dependencies. Saved source and compressed audit bytes are unchanged, and the claims ledger verifies the receipts and full headline closures.
