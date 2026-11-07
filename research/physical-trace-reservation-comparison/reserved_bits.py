"""Independent exact-integer reservation calculations; no Lean or sampler run."""
from decimal import Decimal, localcontext
from pathlib import Path
import json


def clog2(n):
    return (n - 1).bit_length() if n > 1 else 0


COEFFICIENT = 12672000000 * 37**62


def sharper(rs, cs, target, linear=True):
    rs, cs = [x for x in rs if x > 0], [x for x in cs if x > 0]
    m, n = len(rs), len(cs)
    d = 10 + (m + 1) * (n + 1)
    U, L = 11 * d * (m + n - 2), 7
    a, b = sum(x < U for x in rs), sum(x < U for x in cs)
    p = sum(x < U or y < U for x in rs for y in cs)
    lr, lc = m - a, n - b
    assert m >= 2 and n >= 2 and p >= 2 and lr > 0 and lc > 0
    block = min(2 * p * (p - 1), 4 * p) if linear else 2 * p * (p - 1)
    R = block * (target + (1 if linear else 2))
    k = target + (2 if linear else 3) + clog2(R)
    residual_mass = sum(rs) + L * lr * lc

    def completion_bits(h):
        return COEFFICIENT * (d + clog2(residual_mass + 2) + h + 3)**85

    aggregate = U * (U - 1) + 4 * ((a + b) * U**2 + p * U)
    gap = 32 * p**3 * aggregate
    base = sum(rs) + d * L + U + 3
    T = gap * (k + 2 + 2 * d * clog2(base))
    step_target = k + 2 + clog2(T)
    N = step_target + 2
    J = 2 * 2**clog2(32 * d**2) * (step_target + 2)
    exit_precision = step_target + 2 + clog2(J)
    step_bits = (N * clog2(2 * (4 * p - 3)) + completion_bits(N)
                 + J * (clog2(32 * d**2) + completion_bits(exit_precision)))
    schedule_bits = T * step_bits + completion_bits(k + 2)
    trial_bits = schedule_bits + k
    return dict(m=m, n=n, d=d, cutoff=U, padding=L, p=p, small_rows=a, small_columns=b,
                outer_block=block, retries=R, precision=k, walk_steps=T,
                step_target=step_target, exit_attempts=J, exit_precision=exit_precision,
                uniform_step_bits=step_bits, schedule_bits=schedule_bits,
                trial_bits=trial_bits, reserved_bits=R * trial_bits)


def legacy(rs, cs, h):
    rs, cs = [x for x in rs if x > 0], [x for x in cs if x > 0]
    m, n = len(rs), len(cs)
    d = 10 + (m + 1) * (n + 1)
    U, M = 5 * d**3, sum(rs)
    p = sum(x < U or y < U for x in rs for y in cs)
    R = 2 * (1 + p**2) * (h + 3)
    base = M + 3 * d**2 + U + 3
    T = 80000 * d**17 * (h + 3 + clog2(R) + 2 * d * clog2(base))
    h_step, h_terminal = h + 3 + clog2(R) + clog2(T), h + 3 + clog2(R)

    def completion_bits(t):
        retries = 4 * (t + 2)
        fine_precision = t + 2 + clog2(retries)
        fine_binary = clog2(d**12 * (M + 3 * d**2 + 2 * d) + 2)
        return retries * 25 * (d + fine_binary + fine_precision + 1)**62

    reserved = R * (T * (clog2(32 * d**2) + completion_bits(h_step))
                    + completion_bits(h_terminal))
    branch = 'reference' if any(x >= U for x in rs) and any(y >= U for y in cs) else 'unit'
    return dict(d=d, cutoff=U, p=p, branch=branch, retries=R, walk_steps=T,
                step_precision=h_step, terminal_precision=h_terminal, reserved_bits=reserved)


def scientific(value):
    with localcontext() as ctx:
        ctx.prec = 7
        return f'{Decimal(value):.5E}'


if __name__ == '__main__':
    fixtures = [
        ('2 by 2', [1, 100000], [1, 100000]),
        ('3 by 3', [1] + [1000000]*2, [1] + [1000000]*2),
        ('8 by 8', [1] + [1000000000]*7, [1] + [1000000000]*7),
        ('16 by 16', [1] + [1000000000000]*15, [1] + [1000000000000]*15),
    ]
    records = []
    for name, rs, cs in fixtures:
        new, prior, old = sharper(rs, cs, 20), sharper(rs, cs, 20, linear=False), legacy(rs, cs, 20)
        assert new['retries'] <= prior['retries'] and new['reserved_bits'] <= prior['reserved_bits']
        assert new['trial_bits'] > 0
        records.append(dict(name=name, rows=rs, columns=cs, target=20,
                            sharper_linear=new, sharper_prior_outer=prior, legacy=old))
    out = Path(__file__).with_name('reserved-bits.json')
    out.write_text(json.dumps(dict(scope='Independent exact integer reservation calculation; no sampled run, inspected-bit expectation or runtime measurement.', records=records), indent=2) + '\n')
    for row in records:
        new, prior, old = (row[k] for k in ['sharper_linear', 'sharper_prior_outer', 'legacy'])
        print(row['name'], 'p=', new['p'], 'R=', new['retries'], 'k=', new['precision'],
              'new bits=', scientific(new['reserved_bits']),
              'prior/new=', scientific(Decimal(prior['reserved_bits'])/Decimal(new['reserved_bits'])),
              'new/legacy=', scientific(Decimal(new['reserved_bits'])/Decimal(old['reserved_bits'])))
