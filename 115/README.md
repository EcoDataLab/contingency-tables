# Result #115 review and Astra handoff

Start with `115-contingency-tables-review.md`. It contains the assessment, candidate derivations, source links, mathematical obligations, experiment results, and a suggested Astra prompt.

Files in this archive:

- `115-contingency-tables-review.md`: complete review.
- `audit115.py`: independent finite mathematical and kernel checks.
- `audit115-results.json`: recorded output.
- `source-manifest.json`: pinned source paths and Git blob hashes.
- `SHA256SUMS`: hashes of the other bundle files.

Run the checks with Python 3.10+ and NumPy:

```sh
python3 audit115.py --output audit115-results-rerun.json
```

The checks are deterministic and need no network access. They are not an implementation of the full published sampler or FPRAS. Integer and Fraction checks are exact; spectral diagnostics use float64. Timing and last-digit float differences can vary by environment.

Repository snapshot: `https://github.com/openai/math`, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

Retrieve original sources from that commit using the paths in the manifest. The archive does not contain the original manuscripts or proof tree. Source hashes identify Git blobs, not the archive's files. The SHA256SUMS file identifies the review bundle's own files.

The candidate stronger bounds have not been compiled in Lean. Establish the original Comparator baseline before changing proof or program parameters. Every change to the approximate sampler must update the law tabulated by the rare exact-correction branch.
