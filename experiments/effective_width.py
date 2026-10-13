"""Exact physical graph comparisons under effective small-width reduction.

The tiny comparisons use the existing enumerating reference. The separate
degree obstruction enumerates local exchanges, never dense completions.
Neither finite check is a general proof or a performance benchmark.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.tables import TableProblem


CASES = (((2, 2), (3, 1), 9, 1), ((3, 1), (2, 2), 9, 1),
         ((5, 1), (4, 2), 7, 1), ((4, 4, 1), (4, 4, 1), 4, 1),
         ((4, 4, 1), (4, 4, 1), 4, 78), ((9, 8, 2), (9, 8, 2), 8, 1),
         ((0, 0), (0, 0), 9, 1))


def joint_fibers(chain):
    """Count successful completion-retaining repair pairs by repaired output."""
    locations = {cell: k for k, cell in enumerate(chain.small_cells)}
    row_locations = {value: k for k, value in enumerate(chain.large_rows)}
    column_locations = {value: k for k, value in enumerate(chain.large_columns)}
    counts = Counter()
    for index, state in enumerate(chain.states):
        if state.balanced:
            continue
        s, t = state.defect_labels()
        crossing = chain.small_cells[t][0], chain.small_cells[s][1]
        repaired = list(state.row_view)
        repaired[t] -= 1
        if crossing in locations:
            repaired[locations[crossing]] += 1
        for completion in chain.completions[index]:
            dense = [list(row) for row in completion]
            if crossing not in locations:
                dense[row_locations[crossing[0]]][column_locations[crossing[1]]] += 1
            if all(value >= chain.L for row in dense for value in row):
                counts[tuple(repaired), tuple(map(tuple, dense))] += 1
    return counts


def compare_width(rows, columns, cutoff, padding):
    selected = [min(r, c) for r in rows for c in columns if min(r, c) < cutoff]
    width = max(2, 1 + max(selected))
    problem = TableProblem(rows, columns)
    old = build_rescaled_ideal_chain(problem, U=cutoff, L=padding)
    new = build_rescaled_ideal_chain(problem, U=width, L=padding)
    attributes = ("states", "small_cells", "completions", "neighbors",
                  "acceptance_counts", "matrix", "stationary")
    for name in attributes:
        assert getattr(old, name) == getattr(new, name), name
    assert old.all_small == new.all_small
    if not old.all_small:
        assert old.large_rows == new.large_rows
        assert old.large_columns == new.large_columns
        assert old.residual_margins == new.residual_margins
    bounds = tuple(min(rows[i], columns[j]) + 1 for i, j in old.small_cells)
    assert all(x <= bound and q <= bound for state in old.states
               for x, q, bound in zip(state.row_view, state.column_view, bounds))
    assert old.stationary_output_law() == new.stationary_output_law()
    assert joint_fibers(old) == joint_fibers(new)
    return dict(rows=rows, columns=columns, U=cutoff, V=width, L=padding,
                V_below_2L=width < 2 * padding, p=len(old.small_cells),
                states=len(old.states), defects=sum(not z.balanced for z in old.states),
                weights=sorted(set(old.completion_counts)), cell_widths=bounds,
                capacity_equality_seen=any(x == bound or q == bound for state in old.states
                    for x, q, bound in zip(state.row_view, state.column_view, bounds)),
                graph_weights_conductances_and_output_fibers_identical=True)


def degree_obstruction(size):
    """Mixed-mask family at the original ideal scales, with effective width two."""
    small_lines = large_lines = size // 2
    d = 10 + (size + 1)**2
    cutoff, padding = 5 * d**3, 3 * d
    rows = columns = (cutoff,) * large_lines + (1,) * small_lines
    cells = tuple((i, j) for i in range(size) for j in range(size)
                  if i >= large_lines or j >= large_lines)
    locations = {cell: k for k, cell in enumerate(cells)}
    p = len(cells)
    balanced = [0] * p
    for i in range(small_lines):
        balanced[locations[large_lines + i, large_lines + i]] = 1
    crossing = locations[large_lines, large_lines]
    s, t = locations[0, large_lines], locations[large_lines, 0]
    x, q = balanced.copy(), balanced.copy()
    x[t] += 1
    x[crossing] -= 1
    q[s] += 1
    q[crossing] -= 1

    def feasible(xx, qq):
        if any(value < 0 or value > cutoff for value in xx + qq):
            return False
        delta = [v - u for u, v in zip(xx, qq)]
        if delta.count(1) != 1 or delta.count(-1) != 1 or any(v not in (-1, 0, 1) for v in delta):
            return False
        xr, qc = [0] * size, [0] * size
        for k, (i, j) in enumerate(cells):
            xr[i] += xx[k]
            qc[j] += qq[k]
        if any(xr[i] > rows[i] or (i >= large_lines and xr[i] != rows[i]) for i in range(size)):
            return False
        if any(qc[j] > columns[j] or (j >= large_lines and qc[j] != columns[j]) for j in range(size)):
            return False
        rr = [rows[i] - xr[i] + large_lines * padding for i in range(large_lines)]
        cc = [columns[j] - qc[j] + large_lines * padding for j in range(large_lines)]
        return min(rr + cc) >= 0 and sum(rr) == sum(cc)

    assert feasible(x, q)
    profile = x + [cutoff - value for value in q]
    neighbors = set()
    for donor in range(2 * p):
        for receiver in range(2 * p):
            if donor == receiver or profile[donor] == 0 or profile[receiver] == cutoff:
                continue
            candidate = profile.copy()
            candidate[donor] -= 1
            candidate[receiver] += 1
            xx, qq = candidate[:p], [cutoff - value for value in candidate[p:]]
            if feasible(xx, qq):
                neighbors.add(tuple(xx + qq))
    expected = 2 * size + 2 * small_lines * large_lines - 4
    assert len(neighbors) == expected
    return dict(m=size, n=size, small_rows=small_lines, small_columns=small_lines,
                p=p, U=cutoff, V=2, L=padding, DD_degree=len(neighbors),
                unit_branch_degree_bound=2 * (2 * size - 2),
                predicted_degree="2N + N^2/2 - 4",
                evidence="exact local exchange enumeration; no completion enumeration")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(".local/reports/effective-width.json"))
    args = parser.parse_args()
    report = {"schema_version": 1, "width_comparisons": [compare_width(*case) for case in CASES],
              "degree_obstructions": [degree_obstruction(n) for n in (4, 6, 8, 10)]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Wrote {args.output}: seven width comparisons and four degree checks passed.")
