"""Original admitted --plan call, then one exact stat-only guard check.
Only the admission return object is captured; original validation code is unchanged.
"""
import argparse,hashlib,importlib.util,json,signal,sys,time
from pathlib import Path
EXPECTED_RUNNER='4ba0a3c42bee4f511909fc50ad33b00be2a5cc3cabecdd2b54ac08ec7970d1a6'
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--runner',type=Path,required=True);p.add_argument('--metrics',type=Path,required=True);p.add_argument('--root',type=Path,required=True);p.add_argument('--runtime-freeze',type=Path,required=True);p.add_argument('--runtime-freeze-sha256',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 root=a.root.resolve();metrics=a.metrics.resolve();self_path=Path(__file__).resolve()
 if sha(a.runner)!=EXPECTED_RUNNER:raise RuntimeError('Original runner changed')
 if not metrics.is_relative_to(root/'.tools/linux-verification') or metrics.exists():raise RuntimeError('Need fresh owned metrics file')
 self_pin=sha(self_path);spec=importlib.util.spec_from_file_location('unchanged_guard_benchmark_runner',a.runner);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 original=m.admit;captured=[]
 def capture_admission(*args,**kwargs):
  result=original(*args,**kwargs);captured.append(result);return result
 m.admit=capture_admission
 saved_argv=sys.argv
 sys.argv=[str(a.runner),'--root',str(root),'--runtime-freeze',str(a.runtime_freeze),'--runtime-freeze-sha256',a.runtime_freeze_sha256,'--plan','--diagnostics','--wall-seconds','3600','--output',str(a.output)]
 at=time.perf_counter()
 try:m.main()
 finally:sys.argv=saved_argv;m.admit=original
 plan_elapsed=time.perf_counter()-at
 if len(captured)!=1:raise RuntimeError('Expected exactly one original admission')
 modules,guard,descriptor,caches=captured[0]
 if len(modules)!=679 or guard.serial.inventory(root):raise RuntimeError('Wrong module count or submitted proof files')
 if sha(self_path)!=self_pin:raise RuntimeError('Timing wrapper changed')
 guard.add(self_path)
 record={'scope':'original plan admission followed by exact Guard.check(rehash=False); no proof/compiler/Comparator','plan_call_elapsed_seconds':plan_elapsed,'module_count':len(modules),'trusted_cache_files':len(guard.caches),'rehash':False,'stat_guard_cap_seconds':900,'runner_sha256':EXPECTED_RUNNER,'wrapper_sha256':self_pin,'runtime_freeze_sha256':a.runtime_freeze_sha256,'status':'stat_guard_running'}
 metrics.write_text(json.dumps(record,indent=2)+'\n');print('MATH115_STAT_GUARD_BEGIN',flush=True)
 def expired(*unused):raise TimeoutError('Stat-only guard reached900s cap')
 prior=signal.signal(signal.SIGALRM,expired);signal.alarm(900);guard_elapsed=None
 try:
  with (root/'.tools/linux-verification/serial-comparator.lock').open('a') as lock:
   guard.serial.fcntl.flock(lock,guard.serial.fcntl.LOCK_EX|guard.serial.fcntl.LOCK_NB)
   start=time.perf_counter()
   try:guard.check(rehash=False)
   finally:guard_elapsed=time.perf_counter()-start
  if guard.serial.inventory(root):raise RuntimeError('Submitted proof objects appeared')
  if sha(self_path)!=self_pin:raise RuntimeError('Timing wrapper changed')
  record['status']='exact_stat_guard_passed'
 except BaseException as e:record.update(status='exact_stat_guard_failed',error_type=type(e).__name__,error=str(e));raise
 finally:
  signal.alarm(0);signal.signal(signal.SIGALRM,prior);record['stat_guard_elapsed_seconds']=guard_elapsed;metrics.write_text(json.dumps(record,indent=2)+'\n')
 print('MATH115_STAT_GUARD_END='+json.dumps(record,sort_keys=True),flush=True)
if __name__=='__main__':main()
