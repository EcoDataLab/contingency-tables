# Affine02 completed run: independent saved-artifact review

**Scoped PASS; no concrete blocker found.** The two exact reviewed affine sources compiled successfully, and their ordered six-plus-four named axiom audits passed against the exact allowlist `{propext, Classical.choice, Quot.sound}`. This review ran 363 local saved-artifact checks; it did not launch Lean, query a remote host, mutate Git, or edit public/prior evidence files.

Capture binding: `<original-affine02-capture-manifest>`, SHA256 `1fe47af2c4ef2ae94fb8f053d02344594073d22994c2dc335a321b63206989cf`. All 194 unique immutable members match their recorded hashes and byte sizes, and they still matched after review. Owner `final-result.json` SHA256 `d1f19e1ac9c9ca32fff60a2a32ea930db161d862059590024a9c8342078bc2c1` and `cleanup-receipt.json` SHA256 `3148b52f14821813e5bfb11bcefa657e01557b0de1f2bb088fdc315e5071d092` are at the staging root, outside the 194-member evidence manifest; both hashes match the root-provided identities.

## Actual source/object and audit results

| Module | Source SHA256 | Attempt/published object SHA256 | Compile seconds | Audit seconds |
|---|---|---|---:|---:|
| ResearchBounds.AffineFiniteWordDegreeBounds | fb84234d6c666f9f64242c99b507fc41a46fca01d413a250f455233a2c820575 | 28c827ba3689f9ba5ef143961795b4771036ddc42e1d3c500c84934321c5994c | 82.66 | 84.70 |
| ResearchBounds.AffinePublicSamplerDegree | 6187c873840d492b4559229cc362a6476a7260fbc0b1077cc3805910d5919361 | 65464f38881b228dbfe3152b1e862d85891b368f0e1683e3862e2ef4307cbc98 | 86.70 | 81.68 |

Each actual compile/audit argv equals its reviewed frozen plan and launch receipt, with `-j2 -M8192 -DautoImplicit=false`. Each stage has exit 0, null stop reason, unchanged source/input records, empty stderr, a present object and exact terminal receipt equality. Compile stdout contains only the unused-section-variable and `letI` style warnings; these do not indicate admitted proof terms or errors.

The first source uses exactly Init and the authenticated `FiniteWordDegreeBounds` object. The second uses exactly Init, the first fresh object and the authenticated accepted `PublicSamplerDegree` object. The first audit completes before the second compile starts. Both audit stages read precisely Init and their own freshly compiled object. Attempts and published private objects have identical bytes, with exact expected diagnostic paths.

Raw audit stdout was independently reparsed using the hash-authenticated reviewed parser. Requests, parsed records and receipt records match exactly, in the original ordered ten-name roster. The two degree definitions have no axiom dependencies; other declarations use only the allowed standard axioms. There is no `sorryAx` or unexpected axiom. Comment-stripped proof sources contain no `sorry`, `admit`, new `axiom` or `native_decide` token. Full records are saved in `verification.json`.

## Prior trust and immutability

The actual config matches reviewed v2 SHA256 `c79eac57586505a7c2fdf7368220b06309513084480b8efea5c78d7d031a6749`. All 14 captured execution inputs match the reviewed bytes. Prior public02 bindings equal the exact original **116-file** capture allowlist, SHA256 `8c73d0b219ec916bc932a8b7e53037b3173ccdae00437250289c34f98fdcc7d8`; the local collector manifest and pycache are excluded. All original 116 captured files still rehash, and all 116 pins appear in the actual pre-run snapshot. This uses the original capture dictionary, never a new local directory enumeration as a trust roster.

The actual authentication records bind accepted public02 source `4ac577f8...`, object `49bb4dec...`, raw compile/audit receipts and exact original three-name audit. Its copied object bytes agree with the original accepted captured bytes; its raw audit reparses into the recorded results. The accepted R10 authentication scope remains 685 success records / 676 selected internal records. The 84 authenticated external runtime input pins remain in the pre-run snapshot, and the compiler identity agrees with that snapshot and controlled environment.

The actual projection contains all eight old ResearchBounds objects and all 76 configured Math115 siblings. Each copied object's bytes, expected path, original source digest and target digest agree with the pre-run snapshot. The final private ResearchBounds prefix contains exactly those eight plus the two fresh affine objects. Controlled `LEAN_PATH` has precisely that shared prefix, the complete Math115 projection and the unchanged baseline. There is no normal-cache admission evidence or claim.

The captured pre-run snapshot has 2,389 records; all 101 records within the new root map to captured bytes and rehash. The reviewed runner checks that snapshot before and after each stage; clean terminal receipts and unchanged source/object records are consistent with those checks completing. This local review rehashes captured prior/new bytes and verifies snapshot relationships. It does not locally reconstruct or rehash every uncaptured transitive remote source/cache file; the reviewed runtime authentication and successful before/after checks supply that part of the provenance.

## Bounded execution and cleanup

The native preflight is terminal passed for the exact config/executor/harness hashes and all five required scenarios. Every actual Lean-stage admission reports at least 10 GiB free RAM and only the owned runner as a research process. The four real stages are sequential; their measured elapsed sum is 335.74 seconds. The recorded chronology is within the 1500-second compiler/audit sequence limit, and each stage stays below 300 seconds. Observed free RAM across these stages stays above 10.75 GiB; maximum observed working set is approximately 3.26 GiB.

Owned-job receipts record exact non-inheritable Job authority, kill-on-close, no breakaway and assignment before resume. All four stage identities match their corresponding receipts; each child is absent and each owned tree is empty at termination. The owner cleanup captures all four exact child identities as absent, empty research-process enumeration, empty owned tree and transport exit 0. Root separately reports both transports reaped at exit 0; this review verifies the saved cleanup receipt rather than querying those sessions live.

## Scope of the result

This supports successful native elaboration and exact named-axiom auditing of the conditional affine refinement on the same fixed public sampler. The degree remains `340 * max (max e 6) t`, conditional on global Typed certificates for the actual count/draw realizers. No numerical e or t, empirical sampler runtime, human/Comparator acceptance, or normal-cache registration is established. Source semantic review was already completed and was not repeated broadly here.

The original private saved-capture checker is identified by the raw review-manifest hash in the parent receipt; it is omitted from this compact projection. `verification.json` preserves the individual check results, full ten-name audit roster and stage observations, with process IDs omitted. Any subsequent publication or acceptance must preserve these exact source/object/receipt/config/capture bindings and these limits.
