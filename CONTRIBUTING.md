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

Run `make test` from the repository root, or `PYTHONPATH=src python3 -m unittest discover -s tests -v` without Make. These core checks require no package installation. Install `.[research]` before the NumPy-dependent archived audit when changes affect its claims. Do not modify the original `115/` bundle silently. Write corrections in a new note and link them from the status ledger. Never update upstream dependencies as an incidental proof repair.

## Application data

Use public or synthetic inputs with provenance. Explain population, period, geography, rounding, zeros, and target law. Do not include private records, credentials, internal chat transcripts, or local machine paths. Missing routing evidence is not a structural zero.

## Attribution and review

This project has been developed and reviewed with AI assistance. Existing “independent” reviews are separate AI-agent reviews of AI-produced work; they are not outside human peer review. Native Windows receipts record runs on project-owned hardware, with no outsider reproduction recorded. Human MCMC and Lean reviewers are especially welcome to check the chain hypotheses, probability laws, theorem interfaces, executable realization, and complete cost accounting.

For a reproduction, state whether you are a project contributor or an outside reviewer and distinguish a fresh project build from dependency-cache reuse, kernel replay, and human mathematical review. Preserve receipt scopes and historical source hashes.

Preserve source notices and credit earlier contributors. Disclose substantive AI assistance. Counterexamples and failed approaches are useful contributions when they narrow a claim or explain a limitation. Submitting a contribution means it is offered under this repository's Apache-2.0 license.

