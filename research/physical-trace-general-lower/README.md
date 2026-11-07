# Positive lower bound on every inverse count

24 October 2026. Writing a for the number of small rows and b for the number of small columns, two injective label families prove ell(X)>=c0, where `c0=max[a*(n*a-1), b*(m*b-1)]`. The maximum avoids double-counting overlapping families.

The proof chooses a positive entry in each small row or column. Its existence follows from the actual positive margin. No inverse-fibre cardinality or probability lower bound is supplied as a premise.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| Every ordinary inverse count is at least c0 | `inverseSupportAllowance_le_count` | An ordinary table; all row and column margins positive |
| The shape allowance is positive | `inverseSupportAllowance_positive` | m,n>=2 and at least one small cell |

Ordinary compilation of the [source](formal/ResearchPhysicalTraceJoin/GeneralInverseLower.lean) passed in 36.57 seconds; the full assumption audit passed in 68.47 seconds. The [receipt](attempt-01/verification.json) records 2 complete headline dependency closures and the loaded object hashes. Only `propext`, `Classical.choice` and `Quot.sound` occur. The compiler and reused dependencies remain trusted; this is separate from default-target Linux or Comparator verification. See the [consolidated AI source review](../physical-trace-general-terminal-law/AI-SOURCE-REVIEW.md) and [composed ideal output law](../physical-trace-general-terminal-law/). No new complete sampler or runtime exponent is claimed.

Prepare the pinned Lean4.34.1 compiler and the dependency objects named by the imports, including `ResearchAudit.EnvironmentAudit`, then run:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles this module and audits its loaded environment; it downloads or rebuilds no dependencies. Saved source and compressed audit bytes are unchanged. Public diagnostic paths are projected. [Attempt history](attempts.json) preserves each actual failed compiler or audit stage and dependency preflight.
