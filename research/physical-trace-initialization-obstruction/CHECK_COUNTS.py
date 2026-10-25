"""Exact finite illustrations of the empty-defect initialization branch.

Run this file from its public research packet. These enumerations supplement
the Lean obstruction; they are not a proof about arbitrary margins.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.tables import ExactTableSampler, TableProblem


def main():
    results = []
    for rows, columns, expected_completions, expected_tables in (
        ((0, 4), (2, 2), 1, 1),
        ((0, 4, 4), (4, 4), 19, 5),
    ):
        problem = TableProblem(rows, columns)
        chain = build_rescaled_ideal_chain(problem, U=2, L=7)
        original_count = ExactTableSampler(problem).count()
        assert len(chain.states) == 1
        assert chain.states[0].balanced
        assert chain.completion_counts == (expected_completions,)
        assert original_count == expected_tables
        results.append({
            "rows": rows, "columns": columns, "U": 2, "L": 7,
            "small_cells": sum(r < 2 or c < 2 for r in rows for c in columns),
            "large_rows": sum(r >= 2 for r in rows),
            "large_columns": sum(c >= 2 for c in columns),
            "physical_states": len(chain.states),
            "defect_states": sum(not state.balanced for state in chain.states),
            "physical_completions": expected_completions,
            "original_tables": original_count,
        })
    print(json.dumps({"evidence_class": "exact_finite_enumeration", "fixtures": results}, indent=2))


if __name__ == "__main__":
    main()
