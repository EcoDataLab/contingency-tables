"""Exact reservations for the checked tight typed sampler; no timing or raw-program change."""
from pathlib import Path
from decimal import Decimal, localcontext
import json


def clog2(n):
    return (n-1).bit_length() if n > 1 else 0


def scalar(d, p, M, h):
    R = 2*(1+p*p)*(h+3)
    base = M+3*d*d+5*d**3+3
    T = 80000*d**17*(h+3+clog2(R)+2*d*clog2(base))
    step = h+3+clog2(R)+clog2(T)
    terminal = h+3+clog2(R)
    fine_binary = clog2(d**12*(M+3*d*d+2*d)+2)
    def C(t):
        retries = 4*(t+2)
        precision = t+2+clog2(retries)
        return retries*25*(d+fine_binary+precision+1)**62
    return R*(T*(clog2(32*d*d)+C(step))+C(terminal))


def scientific(n):
    with localcontext() as c:
        c.prec=7
        return f'{Decimal(n):.5E}'


if __name__=='__main__':
    records=json.loads(Path(__file__).with_name('reserved-bits.json').read_text())['records']
    coefficient=12672000000*37**62
    results=[]
    for record in records:
        schedule=record['sharper_linear'];m,n= schedule['m'],schedule['n']
        d,U,L=schedule['d'],schedule['cutoff'],schedule['padding']
        lr,lc=m-schedule['small_rows'],n-schedule['small_columns']
        Dr=10+(lr+1)*(lc+1)
        mass=sum(record['rows'])+L*lr*lc
        def old(h):return coefficient*(d+clog2(mass+2)+h+3)**85
        def candidate(h):return min(old(h),scalar(Dr,Dr,mass,h))
        N=schedule['step_target']+2;J=schedule['exit_attempts'];k=schedule['precision']
        step=N*clog2(2*(4*schedule['p']-3))+candidate(N)+J*(clog2(32*d*d)+candidate(schedule['exit_precision']))
        tight=schedule['retries']*(schedule['walk_steps']*step+candidate(k+2)+k)
        assert tight<=schedule['reserved_bits']
        item=dict(name=record['name'],residual_rows=lr,residual_columns=lc,request_dimension=Dr,
                  request_small_count_upper=Dr,residual_mass_upper=mass,
                  terminal_precision=k+2,old_terminal_reservation=old(k+2),
                  candidate_terminal_reservation=candidate(k+2),
                  tight_full_reservation=tight,
                  current_full_reservation=schedule['reserved_bits'],
                  legacy_full_reservation=record['legacy']['reserved_bits'])
        results.append(item)
        print(record['name'],'Dr=',Dr,'terminal improvement=',scientific(Decimal(old(k+2))/Decimal(candidate(k+2))),
              'tight bits=',scientific(tight),
              'whole reduction=',scientific(Decimal(schedule['reserved_bits'])/Decimal(tight)),
              'tight/legacy=',scientific(Decimal(tight)/Decimal(record['legacy']['reserved_bits'])))
    Path(__file__).with_name('tight-reserved-bits.json').write_text(json.dumps(dict(scope='Exact arithmetic for the checked shorter typed sampler at the current linear schedule; ordinary raw sampler unchanged. No runtime measurement.',records=results),indent=2)+'\n')
