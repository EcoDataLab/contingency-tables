# Practical uses of #115 and its refinements

Yes: uniform fixed-margin table sampling addresses useful problems beyond CBEI. The strongest current case for this project is better mathematical guarantees, exact reference calculations, and specialized algorithms. We have not demonstrated that the literal #115 sampler, or our proposed modification of its complete schedule, beats established software in an application.

## Choose the probability law first

For nonnegative integer tables with margins $r,c$, let $\Omega(r,c)$ be the feasible set and $N=\sum_i r_i$. Uniform aggregate sampling assigns each table probability $1/|\Omega|$. Randomly matching individually labeled observations instead gives

$$
\Pr(X=x\mid r,c)=\frac{\prod_i r_i!\prod_j c_j!}{N!\prod_{ij}x_{ij}!}.
$$

This second law is the conditional independence distribution implemented by SciPy's `random_table`, including its Patefield method; the factorial expression is explicit in its `logpmf` implementation. The official R `r2dtable` documentation also identifies Patefield's algorithm. These are established practical baselines for that law, not uniform-table samplers. [SciPy documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.random_table.html), [SciPy probability implementation](https://github.com/scipy/scipy/blob/main/scipy/stats/_multivariate.py), [R documentation and Patefield reference](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/r2dtable.html).

For example, with both margins `(2,2)`, the three possible tables have uniform probabilities `(1/3,1/3,1/3)`, versus `(1/6,2/3,1/6)` under individual assignment. With both margins `(1,99)`, the rare-by-rare cell equals one with probability `1/2` under uniform tables and `1/100` under individual assignment. These follow directly by enumeration and the displayed formula. Neither model becomes empirically correct merely because it is sampled exactly.

## Where the uniform problem is useful

Miller and Harrison give exact uniform counting and sampling methods for both binary and nonnegative integer matrices. Their applications include ecological co-occurrence, conditional volume tests for count tables, and bipartite graphs. Their algorithm exploits repeated column sums; bounded column sums give a polynomial regime, while general large margins can be costly. They also use exact results to assess approximate methods. This establishes practical precedent for the problem, not a new application attributable to #115. [Miller–Harrison, *Exact sampling and counting for fixed-margin matrices* (2013)](https://arxiv.org/html/1301.6635v2).

| Use | Appropriate interpretation and boundary |
| --- | --- |
| Aggregate count-table null models | Compare observed concentration or association against equally weighted aggregate arrangements with the same totals. Specify why this null answers the scientific question; it differs from the usual conditional independence test. |
| Ecological presence/absence and simple bipartite networks | Fixed degrees can control unequal species prevalence or site richness. Entries are binary, so cell caps are essential: the ordinary-table guarantee in #115 does not automatically apply. |
| Bipartite multigraphs or interaction-count matrices | A matrix records edge multiplicities and preserves vertex strengths. Uniform matrices weight multiplicity patterns equally; uniformly matching labeled edge ends instead induces factorial weights. Forbidden interactions require additional constraints. |
| Sensitivity ensembles for incomplete cross-tabs | Compare a downstream metric across feasible allocations and explicit alternative laws. This is a proposed modeling use: variation under a chosen law is not an empirically calibrated uncertainty interval. Pair it with certified feasible extrema when possible. |
| Exact test cases for larger approximate samplers | Known counts, probabilities, and metric distributions expose bias, disconnected moves, and incorrect weighting. Small exact cases are useful even when enumeration cannot handle the final application. |

The graph/matrix correspondence and ecological applications above are documented in Miller–Harrison. The sensitivity proposal is our inference, with the same input-reconciliation requirements described in the [CBEI application note](cbei-use-cases.md).

## What the theorem and refinements contribute

The pinned #115 statement covers exact uniform sampling of **ordinary** tables, with expected bit complexity polynomial in dimensions and binary margin length. Its companion bounded-table counting result is a separate guarantee. This breadth matters mathematically: it avoids requiring favorable margin sizes or a particular sparse graph. It does not supply a practical latency claim. [Pinned OpenAI statement](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md).

Our [sharp entry bounds](small-entry-formalization.md), [padding analysis](scale-formalization.md), and [localized transport](transport-localization.md) improve parts of that proof. The [ideal-oracle scale theorem](ideal-oracle-scales.md) reaches $O(d^{17})$ for an actual auxiliary chain, with automatic branch selection and state existence from equal ordinary totals. Its smaller padding falls outside the retained dense-completion interface. The separate dense-compatible $O(d^{25})$ construction remains useful for that proof path. The complete finite-bit sampler and its runtime remain open. The [padding obstruction](padding-barrier.md) also identifies where this particular construction cannot keep improving. Such results can guide algorithm design and eliminate unproductive parameter choices before implementation. Smaller sufficient worst-case budgets remain mathematical allowances; they are not measured work, and the literal universal schedule is not currently a recommended application implementation.

Several components are more immediately transferable:

- **Exploit legitimate structure.** The [block sampler](block-sampler.md) factors independent graph blocks and uses exact DP only where needed; the [cactus sampler](cactus-sampler.md) handles disjoint cycle coordinates without enumerating an enormous uniform fiber. These use classical graph structure, with explicit limits for weighted calculations and complex blocks.
- **Choose moves for the actual constraints.** Rectangle moves connect the unrestricted two-way fixed-margin problem. Additional constraints can require larger moves; a connected move set still needs a justified sampling law and convergence analysis. Markov-basis methods are established work. [Diaconis–Sturmfels (1998)](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Diaconis/Diaconis8.pdf), [Hara–Takemura–Yoshida, subtable constraints](https://arxiv.org/abs/0708.2312), [Rapallo–Yoshida, bounded tables](https://arxiv.org/abs/0905.4841).
- **Certify small cases, then test proposed hybrids.** Exact block updates and input-fixed cycle mixtures can be candidates inside a larger sampler. Their local exactness does not establish the full chain's mixing rate. A hybrid must retain the intended conditional law and include proposal-selection and preprocessing costs.

## What has actually been demonstrated here

The [cycle-mixture report](cycle-mixtures.md) certifies a gap increase exceeding 63% relative to equal rectangle selection on one 42-table synthetic fiber; it also beats every fixed rectangle-only mixture on that fiber. This is an exact finite spectral comparison, not an end-to-end speed measurement or a general theorem. Exact block/cactus tools and the [worker baseline](worker-baseline.md) supply useful reference implementations for their respective domains. The worker baseline uses the factorial law and cannot establish a speed advantage for uniform sampling. The [linear optimizer](linear-bounds.md) obtains certified metric extrema without sampling at all.

The [same-law benchmark](sampler-benchmarks.md) now compares exact DP, cycle heat baths, supplied tuned mixtures, and the worker baseline in their respective law panels. It retains preparation, cold starts, exact stationary variance where feasible, and budget failures. On tiny ordinary tables, the literal ideal chain has severe correlation: [an exact 2×2 analysis](ideal-two-by-two.md) gives variance inflation 7,679 and 15,359, while a full-line heat bath directly draws from the entire fiber. These are bounded tests of components, not a completed #115 sampler comparison.

For an application, first fix the law and permissible cells; then compare established and specialized methods on the **same** inputs and target. Report preprocessing, time per independent sample or per justified accuracy target, arithmetic limits, and failures. The next evidence needed for direct #115 superiority is such a reproducible comparison of an implemented complete sampler. Until then, practical value should be attributed to the verified components and special cases actually used.
