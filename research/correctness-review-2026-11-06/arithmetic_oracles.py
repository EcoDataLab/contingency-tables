"""Fresh finite arithmetic oracles, independent of the repository test suite."""
from fractions import Fraction
from itertools import product
import json

from contingency115.budgets import ceil_log2, domination_accuracy_bits, dyadic_offset_tv
from contingency115.block_budgets import majority_failure_bound, median_block_count
from contingency115.padding import count_padded_tables, unpadding_success_upper_bound
from contingency115.padding_growth import growth_envelope

counts = {}

for p in range(1, 51):
    for q in range(1, 51):
        value = Fraction(p, q)
        answer = ceil_log2(value)
        power = Fraction(2) ** answer
        assert power / 2 < value <= power, (value, answer)
counts['ceil_log2_rationals'] = 2500

for width in range(1, 26):
    for bits in range(9):
        words = 1 << bits
        histogram = [0] * width
        for word in range(words):
            histogram[word * width // words] += 1
        actual = sum(abs(Fraction(n, words) - Fraction(1, width)) for n in histogram) / 2
        assert actual == dyadic_offset_tv(width, bits), (width, bits, actual)
counts['literal_fair_word_offset_laws'] = 225

for mass in range(1, 201):
    for gate in range(1, 16):
        target = mass * ((1 << gate) - 1)
        answer = 0
        while (1 << answer) < target:
            answer += 1
        assert answer == domination_accuracy_bits(mass, gate), (mass, gate, answer)
counts['least_domination_precisions'] = 3000

for blocks in range(1, 10, 2):
    for p in (Fraction(1, 4), Fraction(1, 8), Fraction(1, 9)):
        actual = Fraction(0)
        for outcomes in product((False, True), repeat=blocks):
            probability = Fraction(1)
            for failure in outcomes:
                probability *= p if failure else 1 - p
            if sum(outcomes) > blocks // 2:
                actual += probability
        assert actual == majority_failure_bound(blocks, p), (blocks, p)
counts['explicit_bernoulli_word_laws'] = 15

for p in (Fraction(1, 4), Fraction(1, 8), Fraction(1, 9)):
    for bits in range(1, 10):
        answer = median_block_count(bits, failure_bound=p)
        assert answer % 2 == 1
        # A separately convolved Bernoulli distribution, without binomials.
        law = [Fraction(1)]
        for n in range(1, answer + 1):
            next_law = [Fraction(0)] * (n + 1)
            for i, mass in enumerate(law):
                next_law[i] += mass * (1 - p)
                next_law[i + 1] += mass * p
            law = next_law
            if n % 2:
                passes = sum(law[n // 2 + 1:]) <= Fraction(1, 1 << bits)
                assert passes == (n == answer), (p, bits, n, answer)
counts['least_odd_majority_allowances'] = 27

padding_cases = 0
for n, u, ell in product(range(2, 6), range(1, 5), range(1, 3)):
    cap, target = u + 2 * ell, u + n * ell
    total = good = 0
    for row in product(range(cap + 1), repeat=n):
        if sum(row) == target:
            total += 1
            good += all(ell <= x <= cap - ell for x in row)
    reported = count_padded_tables(n, u, ell)
    assert (reported.good, reported.total) == (good, total), (n, u, ell)
    assert Fraction(good, total) <= unpadding_success_upper_bound(n, u, ell)
    padding_cases += 1
counts['literal_padded_table_fibers'] = padding_cases

envelope_cases = 0
for q in range(1, 21):
    for numerator in range(21):
        x = Fraction(numerator, 100)
        if q * x < 3:
            assert (1 + x) ** q <= growth_envelope(q * x), (q, x)
            envelope_cases += 1
counts['rational_growth_envelope_cases'] = envelope_cases

print(json.dumps({'status': 'passed', 'counts': counts,
                  'limits': 'Finite independent arithmetic checks; no universal proof, Lean build or full strict replay.'}, indent=2))
