# Contributing

Mathematical improvements, counterexamples, proof reviews, Lean proofs, exact reference implementations, and application benchmarks are welcome. Open an issue to discuss a direction or submit a pull request with a focused contribution.

## Claims and evidence

State the exact quantity improved and all assumptions. Separate:

- a conjecture or proposed parameter choice;
- a mathematical derivation conditional on specified upstream lemmas;
- an exhaustive finite check;
- a numerical experiment;
- a Lean theorem actually compiled without admissions;
- a full upstream challenge comparison.

An improved spectral-gap bound does not establish the same exponent for complete bit complexity. Exact stationarity does not establish fast mixing. An exact small-instance algorithm need not have polynomial complexity in binary input length. Reports should make those distinctions where the claim occurs.

## Reproduction

Include commands, dependency versions, seeds, source commits, and machine-readable results. Prefer integers or rational arithmetic when testing probability identities. Numerical spectral claims need tolerances and complete state sets. Test against an independent oracle where possible; avoid checks that merely repeat implementation formulas.

Run `python3 -m unittest discover -s tests -v` after installing the package, and the archived audit when changes affect its claims. Do not modify the original `115/` bundle silently. Write corrections in a new note and link them from the status ledger. Never update upstream dependencies as an incidental proof repair.

## Application data

Use public or synthetic inputs with provenance. Explain population, period, geography, rounding, zeros, and target law. Do not include private records, credentials, internal chat transcripts, or local machine paths. Missing routing evidence is not a structural zero.

## Attribution and review

Preserve source notices and credit earlier contributors. Disclose substantive AI assistance. Counterexamples and failed approaches are useful contributions when they narrow a claim or explain a limitation. Submitting a contribution means it is offered under this repository's Apache-2.0 license.

