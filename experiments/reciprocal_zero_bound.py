"""Exact finite checks of the weighted-switch zero-cell proof and L=7 geometry.

These checks validate finite instances. They are not a Lean proof, a spectral
certificate, or a cost/accuracy guarantee for a generic completion backend.
Run with Python 3 from any checkout location; --output saves the exact report.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import json
from math import comb
from pathlib import Path
import sys

ROOT = next(p for p in Path(__file__).resolve().parents if (p / "src/contingency115").is_dir())
sys.path.insert(0, str(ROOT / "src"))
from contingency115.tables import ExactTableSampler, TableProblem
from contingency115.ideal_chain import IdealChainBudget, build_rescaled_ideal_chain


def tails(margin: int, parts: int):
    denominator = comb(margin + parts - 1, parts - 1)
    return tuple(F(comb(margin - k + parts - 1, parts - 1), denominator)
                 for k in range(margin + 1))


def check_fiber(rows, columns):
    problem = TableProblem(rows, columns)
    sampler = ExactTableSampler(problem)
    tables = tuple(sampler.tables(max_tables=100_000))
    assert tables and len(tables) == sampler.count()
    R, C = len(rows), len(columns)
    records = []
    weighted_levels = 0
    worst = F(0)
    for i, a in enumerate(rows):
        for j, b in enumerate(columns):
            hist = Counter(X[i][j] for X in tables)
            pzero = F(hist[0], len(tables))
            if R == 1 or C == 1:
                # A singleton rectangle is deterministic, including zero margins.
                assert pzero == int(a == 0 or b == 0)
                records.append({"cell": [i,j], "zero_probability": str(pzero),
                                "branch": "deterministic singleton"})
                continue
            reverse = Counter()
            for Y in tables:
                level = Y[i][j]
                if not level:
                    continue
                reverse[level-1] += sum((Y[i][l]+1)*(Y[k][j]+1)
                    for k in range(R) for l in range(C)
                    if k != i and l != j and Y[k][l] > 0)
            levels = []
            for t in range(min(a,b)):
                source = (a-t)*(b-t)*hist[t]
                full_reverse = (a-t+C-2)*(b-t+R-2)*hist[t+1]
                assert source == reverse[t], (rows,columns,i,j,t,"weighted bijection")
                assert source <= full_reverse
                levels.append({"k": t, "N_k": hist[t], "N_next": hist[t+1],
                               "source_weight": source, "restricted_reverse_weight": reverse[t],
                               "full_reverse_bound": full_reverse})
                weighted_levels += 1
            f, g = tails(a,C-1), tails(b,R-1)
            for seq in (f,g):
                for u in range(len(seq)):
                    for v in range(len(seq)):
                        lhs = seq[u+v] if u+v < len(seq) else F(0)
                        assert lhs <= seq[u]*seq[v]
            A, B = sum(f), sum(g)
            S = sum(f[k]*g[k] for k in range(min(a,b)+1))
            alpha, beta = F(C-1,a+C-1), F(R-1,b+R-1)
            bound = alpha+beta-alpha*beta
            assert A == 1/alpha and B == 1/beta
            assert A*B <= S*(A+B-1)
            assert pzero <= 1/S <= bound <= alpha+beta
            for k in range(min(a,b)+1):
                assert hist[k] >= hist[0]*f[k]*g[k]
            worst = max(worst,pzero/bound)
            records.append({"cell": [i,j], "zero_probability": str(pzero),
                "alpha": str(alpha), "beta": str(beta), "sharp_bound": str(bound),
                "composition_product_sum": str(S), "levels": levels})
    return {"rows": rows, "columns": columns, "table_count": len(tables),
            "weighted_levels": weighted_levels, "worst_zero_to_bound_ratio": str(worst),
            "cells": records}


def check_physical(rows,columns):
    budget = IdealChainBudget(max_transition_work=20_000_000)
    chain = build_rescaled_ideal_chain(TableProblem(rows,columns),U=2,L=7,budget=budget)
    R,C = len(chain.large_rows),len(chain.large_columns)
    edges = 0
    worst = F(1)
    branches = Counter()
    indices = {state: k for k,state in enumerate(chain.states)}
    locations = {cell: k for k,cell in enumerate(chain.small_cells)}
    repair_edges = set()
    for i,state in enumerate(chain.states):
        labels = state.defect_labels()
        if labels is not None:
            source,positive = labels
            repaired = list(state.row_view)
            repaired[positive] -= 1
            crossing = (chain.small_cells[positive][0],chain.small_cells[source][1])
            if crossing in locations:
                repaired[locations[crossing]] += 1
            target = type(state)(tuple(repaired),tuple(repaired))
            assert target in indices
            repair_edges.add((i,indices[target]))
    for i, targets in enumerate(chain.neighbors):
        rr,cc = chain.residual_margins[i]
        if R and C:
            assert min(rr) >= C*7 and min(cc) >= R*7
        for j in targets:
            if i == j:
                continue
            edges += 1
            delta = chain.translation(i,j)
            negatives = sum(x == -1 for row in delta for x in row)
            assert all(x in (-1,0,1) for row in delta for x in row)
            assert negatives <= 2
            source_count = len(chain.completions[i])
            accepted = chain.acceptance_counts[i][j]
            probability = F(accepted,source_count)
            assert probability >= F(1,2)
            worst = min(worst,probability)
            dx = tuple(v-u for u,v in zip(chain.doubled_profile(i),chain.doubled_profile(j)))
            exchange = dx.count(1) == dx.count(-1) == 1 and all(v in (-1,0,1) for v in dx)
            repair,reverse = (i,j) in repair_edges,(j,i) in repair_edges
            assert exchange or repair or reverse
            # Memberships may overlap because the physical graph is a union.
            for name,present in [("exchange",exchange),("designated repair",repair),("reverse repair",reverse)]:
                branches[name] += int(present)
            if R <= 1 or C <= 1:
                assert probability == 1
    assert edges > 0
    return {"rows":rows,"columns":columns,"U":2,"L":7,"completion_shape":[R,C],
            "states":len(chain.states),"directed_edges":edges,"branch_memberships":dict(branches),
            "minimum_directed_acceptance":str(worst),"work_counts":dict(chain.work_counts),
            "scope":"Full finite physical graph at diagnostic U=2,L=7; no sampler cost guarantee."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    if not __debug__:
        parser.error("run without -O so the exact checks remain enabled")
    args = parser.parse_args()
    cases = [
        ((7,7),(7,7)), ((1,11),(6,6)), ((11,1),(10,2)),
        ((0,4),(1,3)), ((0,0),(0,0)),
        ((1,11),(1,1,10)), ((7,7),(2,3,9)), ((28,28),(14,21,21)),
        ((1,1,10),(1,11)), ((2,3,9),(7,7)), ((14,21,21),(28,28)),
        ((3,3,3),(3,3,3)), ((1,3,5),(2,2,5)), ((0,3,6),(0,4,5)),
        ((21,21,21),(21,21,21)),
        ((2,3,4,5),(1,3,4,6)), ((1,1,1,6),(2,3,4)),
        ((9,),(2,3,4)), ((9,),(0,4,5)), ((0,),(0,0,0)),
        ((2,3,4),(9,)), ((0,4,5),(9,)),
        ((0,0,0),(0,)), ((0,),(0,)),
    ]
    fibers = [check_fiber(*case) for case in cases]
    physical = [check_physical(*case) for case in [
        ((1,2,2),(1,2,2)), ((1,2,3),(1,3,2)),
        ((1,4),(1,2,2)), ((1,2,2),(1,4)),
        ((1,2),(1,1,1)), ((1,1,1),(1,2))]]
    report = {"status":"passed","scope":"Exact finite rational reproduction; proof derivation separate.",
        "claimed_inequality":"P0 <= alpha + beta - alpha*beta, alpha=(C-1)/(r+C-1), beta=(R-1)/(c+R-1)",
        "fiber_count":len(fibers),"checked_tables":sum(x['table_count'] for x in fibers),
        "weighted_levels":sum(x['weighted_levels'] for x in fibers),
        "physical_cases":len(physical),"fibers":fibers,"physical":physical}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:report[k] for k in ["status","fiber_count","checked_tables","weighted_levels","physical_cases"]}))


if __name__ == "__main__":
    main()
