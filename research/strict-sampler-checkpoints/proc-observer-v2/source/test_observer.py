"""Narrow deterministic procfs/owned-loop fixtures; no VM/service/compiler invoked."""
from pathlib import Path
import errno,importlib.util,json,subprocess,tempfile,unittest
from unittest.mock import patch
D=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('observer_candidate',D/'strict_serial_check.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def unavailable(known=(),kind=PermissionError):
 e=m.TelemetryUnavailable('Owned executable observations incomplete: 22')
 e.observed_compiler_pids=list(known)
 e.incomplete_executables=[{'pid':22,'error_type':kind.__name__,'errno':errno.ESRCH if kind is ProcessLookupError else errno.EACCES,'filename':'/proc/22/exe','error':'injected bounded procfs error'}]
 return e

class Clock:
 def __init__(self):self.t=0.
 def now(self):return self.t
 def sleep(self,n):self.t+=n
class Process:
 def __init__(self,clock,duration):self.clock=clock;self.duration=duration;self.pid=77;self.terminated=False
 def poll(self):return 0 if self.terminated or self.clock.t>=self.duration else None
 def wait(self,timeout=None):return 0

class Observer(unittest.TestCase):
 def direct(self,decisions):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);group=root/'group';group.mkdir();(group/'cgroup.procs').write_text(' '.join(str(x) for x in decisions))
   def resolve(path,strict=False):
    decision=decisions[int(path.parent.name)]
    if isinstance(decision,BaseException):raise decision
    return decision
   with patch.object(Path,'resolve',autospec=True,side_effect=resolve):return m.compiler_pids(group,{Path('/known/lean')},root/'proc')
 def exercise(self,observe,duration=1,wall=20):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);(root/'formal').mkdir();out=root/'logs';out.mkdir();plan={'commands':[{'stage':'fixture','status':'running'}]};clock=Clock();runner=m.MeasuredRunner(root,out,plan,wall);process=Process(clock,duration);killed=[]
   def command(argv,**kwargs):return subprocess.CompletedProcess(argv,0,'/fixture\n' if 'show' in argv else '','')
   def kill(pid,sig):killed.append((pid,sig));process.terminated=True
   error=None
   with patch.object(m.time,'monotonic',side_effect=clock.now),patch.object(m.time,'time',side_effect=lambda:2000+clock.t),patch.object(m.time,'sleep',side_effect=clock.sleep),patch.object(m.subprocess,'Popen',return_value=process),patch.object(m.subprocess,'run',side_effect=command) as run,patch.object(m.os,'killpg',side_effect=kill),patch.object(m,'compiler_pids',side_effect=lambda *a:observe(clock.t)):
    runner.deadline=clock.t+wall
    try:result=runner(['systemd-run','--user','--wait','--','/bounded-stub'],'fixture')
    except BaseException as e:error=e;result=None
   saved=json.loads((out/'receipt.json').read_text())['commands'][0]
   stops=[c.args[0] for c in run.call_args_list if 'stop' in c.args[0]]
   self.assertTrue(all(a==['systemctl','--user','stop',saved['owned_unit']] for a in stops))
   return saved,error,clock.t,stops,killed,result
 def test_readable_and_missing_pid_original_behavior(self):
  self.assertEqual(self.direct({1:Path('/known/lean'),2:FileNotFoundError(errno.ENOENT,'gone')}),[1])
 def test_permission_invalidates_whole_sample(self):
  with self.assertRaises(m.TelemetryUnavailable) as c:self.direct({1:Path('/known/lean'),2:PermissionError(errno.EACCES,'denied','/proc/2/exe')})
  self.assertEqual(c.exception.observed_compiler_pids,[1]);self.assertEqual(c.exception.incomplete_executables[0]['errno'],errno.EACCES)
 def test_eperm_invalidates_whole_sample(self):
  with self.assertRaises(m.TelemetryUnavailable) as c:self.direct({1:PermissionError(errno.EPERM,'denied','/proc/1/exe')})
  self.assertEqual(c.exception.observed_compiler_pids,[]);self.assertEqual(c.exception.incomplete_executables[0]['errno'],errno.EPERM)
 def test_esrch_invalidates_whole_sample(self):
  with self.assertRaises(m.TelemetryUnavailable) as c:self.direct({1:Path('/known/lean'),2:ProcessLookupError(errno.ESRCH,'gone','/proc/2/exe')})
  self.assertEqual(c.exception.observed_compiler_pids,[1]);self.assertEqual(c.exception.incomplete_executables[0]['errno'],errno.ESRCH)
 def test_scan_after_unknown_preserves_positive_overlap(self):
  with self.assertRaises(m.TelemetryUnavailable) as c:self.direct({1:PermissionError(errno.EACCES,'denied'),2:Path('/known/lean'),3:Path('/known/lean')})
  self.assertEqual(c.exception.observed_compiler_pids,[2,3])
 def test_unrelated_errors_still_abort(self):
  with self.assertRaises(OSError) as c:self.direct({1:OSError(errno.EIO,'unexpected')})
  self.assertEqual(c.exception.errno,errno.EIO)
 def test_transient_error_then_complete_recovery(self):
  def observe(t):
   if t<.5:raise unavailable([11])
   return [11]
  row,error,_,stops,killed,result=self.exercise(observe)
  self.assertIsNone(error);self.assertEqual(result.returncode,0);self.assertEqual(row['incomplete_compiler_samples'],2);self.assertEqual(row['successful_compiler_samples'],2);self.assertEqual(row['sampled_heavy_compiler_peak'],1);self.assertEqual(row['compiler_telemetry_status'],'sampled_owned_cgroup_with_incomplete_samples');self.assertFalse(stops or killed)
 def test_short_unreadable_stage_never_reports_zero_or_partial(self):
  def observe(t):raise unavailable([11])
  row,error,_,stops,killed,result=self.exercise(observe,duration=.5)
  self.assertIsNone(error);self.assertEqual(result.returncode,0);self.assertEqual(row['successful_compiler_samples'],0);self.assertIsNone(row['sampled_heavy_compiler_peak']);self.assertEqual(row['compiler_telemetry_status'],'unavailable_short_stage');self.assertEqual(row['incomplete_sample_events'][0]['positively_observed_compiler_pids'],[11]);self.assertFalse(stops or killed)
 def test_five_second_watchdog_and_owned_cleanup(self):
  def observe(t):raise unavailable()
  row,error,t,stops,killed,_=self.exercise(observe,duration=12)
  self.assertIsInstance(error,m.CheckError);self.assertIn('five seconds',str(error));self.assertEqual(t,5);self.assertEqual(row['successful_compiler_samples'],0);self.assertIsNone(row['sampled_heavy_compiler_peak']);self.assertEqual(row['compiler_telemetry_status'],'unavailable_active_service');self.assertEqual(len(stops),1);self.assertEqual(killed[0][0],77);self.assertEqual(row['owned_unit_stop_returncode'],0);self.assertEqual(len(row['incomplete_sample_events']),16);self.assertEqual(row['omitted_incomplete_event_count'],5)
 def test_only_valid_sample_resets_watchdog(self):
  def observe(t):
   if t==.5:return [11]
   raise unavailable()
  row,error,t,_,_,_=self.exercise(observe,duration=12)
  self.assertIn('five seconds',str(error));self.assertEqual(t,5.5);self.assertEqual(row['successful_compiler_samples'],1)
 def test_partial_positive_overlap_aborts_immediately(self):
  def observe(t):raise unavailable([11,12])
  row,error,t,stops,killed,_=self.exercise(observe,duration=12)
  self.assertIsInstance(error,m.CheckError);self.assertIn('overlapping',str(error));self.assertEqual(row['overlap_pids'],[11,12]);self.assertEqual(row['successful_compiler_samples'],0);self.assertIsNone(row['sampled_heavy_compiler_peak']);self.assertEqual(t,0);self.assertEqual(len(stops),1);self.assertEqual(killed[0][0],77)
 def test_complete_positive_overlap_still_aborts(self):
  row,error,t,stops,_,_=self.exercise(lambda t:[11,12],duration=12)
  self.assertIn('overlapping',str(error));self.assertEqual(row['overlap_pids'],[11,12]);self.assertEqual(row['successful_compiler_samples'],1);self.assertEqual(row['sampled_heavy_compiler_peak'],2);self.assertEqual(t,0);self.assertEqual(len(stops),1)
 def test_hard_deadline_precedes_telemetry_grace(self):
  def observe(t):raise unavailable()
  row,error,t,stops,killed,_=self.exercise(observe,duration=12,wall=3)
  self.assertIn('wall-clock limit',str(error));self.assertEqual(t,3);self.assertEqual(len(stops),1);self.assertEqual(killed[0][0],77)
 def test_cgroup_unavailable_remains_incomplete(self):
  with tempfile.TemporaryDirectory() as tmp:
   with self.assertRaises(m.TelemetryUnavailable):m.compiler_pids(Path(tmp)/'absent',set())
if __name__=='__main__':unittest.main(verbosity=2)
