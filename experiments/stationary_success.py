#!/usr/bin/env python3
"""Exact stationary-success consequences of the independently enumerated graph.

The universal obstruction is a mathematical argument in the companion note;
this report checks only the eight bounded synthetic cases it records.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]


def report():
    geometry = runpy.run_path(str(ROOT / 'experiments/defect_transport.py'))['report']()
    cases = []
    for item in geometry['cases']:
        n, margin = item['dimension'], item['common_margin']
        p, e = n * n, (n - 1) ** 2
        tables, defects = item['transversal_states'], item['defect_states']
        success = Fraction(tables, tables + defects)
        mean_support = Fraction(defects, (p - 1) * tables)
        lower = Fraction(1, 1 + p * (p - 1))
        upper = Fraction(margin + e, margin + e + p * (p - 1) * margin)
        assert Fraction(p * margin, margin + e) <= mean_support <= p
        assert lower <= success <= upper
        assert Fraction(defects, tables) == Fraction(item['defect_to_transversal_mass_ratio'])
        cases.append({
            'dimension': n, 'common_margin': margin, 'small_cells': p,
            'original_tables': tables, 'physical_defects': defects,
            'physical_normalizer': tables + defects,
            'mean_support': str(mean_support), 'stationary_success': str(success),
            'lower_bound': str(lower), 'upper_bound': str(upper),
            'count_based_unpadding_success': '1',
        })
    sources = ['experiments/stationary_success.py', 'experiments/defect_transport.py',
               'src/contingency115/tables.py', 'formal/Math115/SmallEntrySwitching.lean']
    return {
        'schema_version': 1, 'upstream_commit': geometry['upstream_commit'],
        'scope': 'Fresh exact graph enumeration in eight synthetic all-small instances; not a Lean theorem or a runtime benchmark.',
        'reproduce': 'PYTHONPATH=src python3 experiments/stationary_success.py --output reports/stationary-success.json',
        'formula': 's = 1 / (1 + (p-1) * E_uniform[positive_cells])',
        'ideal_scale_family': {
            'parameters': 'n>=2, p=n^2, d=10+(n+1)^2, M=d^3, U=5*d^3, L=3*d',
            'claim': 'p^2 * stationary_success tends to 1 as n tends to infinity',
            'evidence': 'Reviewed mathematical squeeze argument in docs/stationary-success-obstruction.md; this family is not enumerated here.',
        },
        'cases': cases,
        'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources},
        'limits': [
            'The defect/support identity uses the unchanged physical state space and success rule, with unit completion weights and no large block.',
            'The lower success bound here uses P=N and the off-diagonal defect labels; the general stationary theorem has different hypotheses and constants.',
            'A small stationary success probability is not a mixing, physical-clock, bit-runtime, or all-samplers lower bound.',
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rendered = json.dumps(report(), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
