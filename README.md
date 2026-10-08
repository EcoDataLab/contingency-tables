# Contingency tables: proofs and usable reference algorithms

An open EcoDataLab research project building on [OpenAI result #115](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md): sampling and counting integer tables with fixed margins and cell bounds.

We are pursuing tighter quantitative proofs and small, exact implementations useful for testing climate-accounting and commuting models. The theoretical constructions and the applied reference algorithms have different guarantees; every result records its assumptions and verification status.

## Starting points

- [Original research review](115/115-contingency-tables-review.md) and [source manifest](115/source-manifest.json): the preserved October 8, 2026 handoff, including hypotheses to test.
- [Research status](docs/status.md): current results, limitations, and next proof obligations.
- [Contributing](CONTRIBUTING.md): welcome to mathematical corrections, counterexamples, formal proofs, implementations, and reproducible benchmarks.

## Reproduce

Python 3.10 or newer is required. The core reference implementation uses the standard library.

```sh
python3 -m pip install -e '.[research]'
python3 -m unittest discover -s tests -v
python3 115/audit115.py --output /tmp/audit115-rerun.json
python3 scripts/verify_sources.py
```

The archived audit needs NumPy; exact integer and rational checks are distinguished from floating-point spectral diagnostics. Source verification downloads only files in the pinned manifest and checks their Git blob hashes. It does not execute upstream code.

## Scope

The source claim of exact expected-polynomial sampling concerns ordinary tables. Its companion FPRAS covers cell bounds and structural zeros. This project does not transfer one guarantee to the other. An exact dynamic program for a small bounded fiber does not supply a polynomial-time sampler for arbitrary binary-encoded inputs.

Uniform aggregate tables and conditional assignments of individual workers are different probability laws. Applications must specify their target law, reconcile input universes, and distinguish hard zeros from missing evidence. No private client data is included.

## Attribution

Original manuscripts and Lean library: OpenAI, pinned at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Initial review: GPT-6.1 Sol working with Ben Gould. Follow-up research, code, and review use OpenAI Codex agents under EcoDataLab's direction. AI-generated arguments are subject to the same reproducibility and review requirements as any contribution. See [NOTICE](NOTICE).

Apache-2.0. Community contributions are welcome through issues and pull requests.

