#!/usr/bin/env python3
"""Literal finite support-count certificates; not a Lean proof or runtime claim."""
import json
import itertools
import random


def certificate(matrix, cutoff):
    m, n = len(matrix), len(matrix[0])
    rows = list(map(sum, matrix))
    columns = list(map(sum, zip(*matrix)))
    small = {(i, j) for i in range(m) for j in range(n)
             if rows[i] < cutoff or columns[j] < cutoff}
    small_row = [sum(matrix[i][j] for j in range(n) if (i, j) in small)
                 for i in range(m)]
    small_column = [sum(matrix[i][j] for i in range(m) if (i, j) in small)
                    for j in range(n)]
    labels = [(s, t) for s in sorted(small) for t in sorted(small)
              if s != t and (
                  matrix[t[0]][s[1]] > 0 if (t[0], s[1]) in small else
                  small_row[t[0]] < rows[t[0]] and
                  small_column[s[1]] < columns[s[1]])]
    a = sum(v < cutoff for v in rows)
    b = sum(v < cutoff for v in columns)
    c0 = max(a * (n * a - 1), b * (m * b - 1))
    donor = a * b * (m-a) * (n-b)
    return dict(matrix=matrix, cutoff=cutoff, rows=rows, columns=columns,
                small_rows=a, small_columns=b, small_cells=len(small),
                row_slacks=[r-s for r, s in zip(rows, small_row)],
                column_slacks=[c-s for c, s in zip(columns, small_column)],
                exact_inverse_support_count=len(labels), c0=c0,
                proposed_large_donor_family=donor, proposed_c1=c0+donor,
                labels=labels)


def main():
    examples = []
    for cutoff in (2, 3, 100, 10**6):
        x = [[0, 0, cutoff, cutoff],
             [cutoff-1, cutoff-1, 0, 0],
             [0, 0, 0, cutoff-1]]
        result = certificate(x, cutoff)
        assert result['exact_inverse_support_count'] == 17
        assert result['proposed_c1'] == 18
        assert result['small_cells'] == 8
        examples.append(result)
    print(json.dumps(dict(status='counterexample_to_c1', examples=examples), indent=2))


def spanning_check(matrix, cutoff):
    cert = certificate(matrix, cutoff)
    if min(cert['rows'] + cert['columns']) == 0:
        return False
    small_rows = [i for i, r in enumerate(cert['rows']) if r < cutoff]
    if not small_rows:
        return False
    large_rows = [i for i, r in enumerate(cert['rows']) if r >= cutoff]
    small_columns = [j for j, c in enumerate(cert['columns']) if c < cutoff]
    root = small_rows[0]
    donors = {i: next(j for j, v in enumerate(matrix[i]) if v > 0) for i in small_rows}
    labels = []
    for i in small_rows:
        for j in range(len(matrix[0])):
            if (i, j) == (root, donors[root]):
                continue
            source = root if j == donors[i] else i
            labels.append(((source, donors[i]), (i, j)))
    for j in small_columns:
        donor = next(i for i in range(len(matrix)) if matrix[i][j] > 0)
        for i in large_rows:
            source = root if i == donor else i
            labels.append(((source, j), (donor, j)))
    support = {(tuple(s), tuple(t)) for s, t in cert['labels']}
    assert len(labels) == cert['small_cells'] - 1
    assert len(set(labels)) == len(labels)
    assert set(labels) <= support
    return True


def screen():
    checked = 0
    for m, n in [(2, 2), (2, 3), (3, 2), (3, 3)]:
        for entries in itertools.product(range(2), repeat=m*n):
            matrix = [list(entries[i*n:(i+1)*n]) for i in range(m)]
            for cutoff in range(1, max(m, n)+2):
                checked += spanning_check(matrix, cutoff)
    rng = random.Random(20261106)
    for _ in range(3000):
        m, n = rng.randrange(1, 9), rng.randrange(1, 9)
        matrix = [[rng.randrange(4) for _ in range(n)] for _ in range(m)]
        checked += spanning_check(matrix, rng.randrange(1, 3*max(m, n)+2))
    print(json.dumps(dict(status='spanning_injection_screen_passed', checked=checked,
                          note='Finite screen only; Lean proof is separate.')))


if __name__ == '__main__':
    import sys
    screen() if '--screen' in sys.argv else main()
