"""Bounded local scientific-report oracles; no downloads or retained report writes."""
from fractions import Fraction
import json
from pathlib import Path
from unittest.mock import patch
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from experiments import commuting_backtest as backtest
from experiments import commuting_interval_score as scoring
from experiments import worker_library_benchmarks as benchmark
from contingency115.workers import OrdinaryWorkerSampler

case=benchmark.Case('clock_and_count','exact_small_law',(2,2),(2,2),2)
reference,probabilities=benchmark.exact_reference(case)
calls=[]
class Tracked(OrdinaryWorkerSampler):
    def sample_with_stats(self,rng=None):
        calls.append(1)
        return super().sample_with_stats(rng)
with patch.object(benchmark,'OrdinaryWorkerSampler',Tracked), patch.object(benchmark.time,'perf_counter',side_effect=range(100)):
    result=benchmark.python_method(case,'worker_urn',3,2,7,None,reference,probabilities)
assert len(calls)==10
assert result['summary']['metric']['sample_count']==4
assert [r['seed'] for r in result['runs']]==[7,8]
assert result['summary']['median_draw_seconds_per_table']==Fraction(1,2)
assert result['summary']['median_setup_plus_draw_seconds_per_table']==1
print('Clock/count:10calls;4measured outputs;seeds7,8;draw1/2 and setup+draw1 per table')
checks=0
for alpha in (Fraction(1,20),Fraction(1,5)):
    for lower in range(6):
        for upper in range(lower,9):
            for y in range(12):
                expected=upper-lower+2/alpha*max(lower-y,y-upper,0)
                assert Fraction(scoring.interval_score(lower,upper,y,alpha)['interval_score_jobs_exact'])==expected
                checks+=1
print('Interval score:',checks,'closed-distance identities')
saved=json.loads(Path('reports/commuting-backtest.json').read_text())
fresh=backtest.build_report()
changes=[]
for old,new in zip(saved['cases'],fresh['cases']):
    for law in backtest.LAWS:
        for index,(a,b) in enumerate(zip(old['laws'][law]['cells_row_major'],new['laws'][law]['cells_row_major'])):
            if tuple(a['interval'])!=tuple(b['interval']) or a['covered']!=b['covered']:
                changes.append((old['case'],law,index,a['interval'],b['interval']))
assert changes==[]
assert saved['summary']==fresh['summary']
print('Pinned panel:0interval/coverage/summary changes;minimum total',min(c['case_jobs'] for c in fresh['cases']))
