# Total ideal inverse-fibre acceptance correction

24 October 2026. The actual partial repair returns an ordinary table only after its padding test. On a successful output X, the ideal coin uses min(c0,ell(X))/ell(X), with a total zero-fibre case. A uniform source therefore gives successful mass min(c0,ell(X))/Z.

The existing `RepairAcceptanceCoin` library supplies the rational coin law. This packet alone retains the count bound as a premise; the terminal-law composition derives it. This is an ideal rational rule, without a finite-word coin implementation.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| Generic partial-map correction has clipped constant mass | `PartialRepairCorrection.stationary_some` | Finite output and nonempty finite source |
| The actual repair has that mass formula | `terminalIdealCorrection_mass` | Nonempty actual joint; arbitrary c0 |
| Clipping disappears after a proved count bound | `terminalIdealCorrection_mass_of_le` | Additionally c0<=ell(X) |

Ordinary compilation of the [source](formal/ResearchPhysicalTraceJoin/GeneralAcceptance.lean) passed in 61.12 seconds; the full assumption audit passed in 81.88 seconds. The [receipt](attempt-02/verification.json) records 3 complete headline dependency closures and the loaded object hashes. Only `propext`, `Classical.choice` and `Quot.sound` occur. The compiler and reused dependencies remain trusted; this is separate from default-target Linux or Comparator verification. See the [consolidated AI source review](../physical-trace-general-terminal-law/AI-SOURCE-REVIEW.md) and [composed ideal output law](../physical-trace-general-terminal-law/). No new complete sampler or runtime exponent is claimed.

Prepare the pinned Lean4.34.1 compiler and the dependency objects named by the imports, including `ResearchAudit.EnvironmentAudit`, then run:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles this module and audits its loaded environment; it downloads or rebuilds no dependencies. Saved source and compressed audit bytes are unchanged. Public diagnostic paths are projected. [Attempt history](attempts.json) preserves each actual failed compiler or audit stage and dependency preflight.
