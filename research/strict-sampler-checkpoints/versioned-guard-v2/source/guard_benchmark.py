"""Original-authenticated context, versioned plan, actual v2/original guards.
Trusted-supervisor quiet cache; no proof execution or universal race equivalence.
"""
import argparse,hashlib,importlib.util,inspect,json,signal,sys,time
from pathlib import Path
ORIGINAL_SHA='4ba0a3c42bee4f511909fc50ad33b00be2a5cc3cabecdd2b54ac08ec7970d1a6'
CANDIDATE_SHA='1008cc3ba5afb129c5d54c8bc030207c8e72715d9b8a1546984e956f919768ca'
HELPER_SHA='6eb447ff60a09d13bc134252e490bd99e7a15b92c7436a0db5a677269b91a3a5'
def sha(path):
 with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def main():
 p=argparse.ArgumentParser()
 for name in ('runner','candidate-runner','metrics','root','runtime-freeze','output'):p.add_argument('--'+name,type=Path,required=True)
 p.add_argument('--runtime-freeze-sha256',required=True);a=p.parse_args()
 root=a.root.resolve();metrics=a.metrics.resolve();self_path=Path(__file__).resolve();helper=a.candidate_runner.parent/'anchored_metadata.py'
 require(sys.platform.startswith('linux'),'Linux benchmark required')
 require(sha(a.runner)==ORIGINAL_SHA and sha(a.candidate_runner)==CANDIDATE_SHA and sha(helper)==HELPER_SHA,'Frozen runner/helper mismatch')
 require(metrics.is_relative_to(root/'.tools/linux-verification') and not metrics.exists(),'Fresh owned metrics required')
 self_pin=sha(self_path);original=load('pinned_original_guard_reference',a.runner);candidate=load('pinned_versioned_guard_v2',a.candidate_runner)
 captured=[];admit=candidate.admit;saved_argv=sys.argv
 def capture(*args,**kwargs):
  result=admit(*args,**kwargs);captured.append(result);return result
 candidate.admit=capture
 sys.argv=[str(a.candidate_runner),'--root',str(root),'--runtime-freeze',str(a.runtime_freeze),'--runtime-freeze-sha256',a.runtime_freeze_sha256,'--plan','--diagnostics','--wall-seconds','3600','--output',str(a.output)]
 at=time.perf_counter()
 try:candidate.main()
 finally:candidate.admit=admit;sys.argv=saved_argv
 plan_elapsed=time.perf_counter()-at
 require(len(captured)==1,'Expected one unchanged admission implementation')
 modules,guard,descriptor,caches=captured[0]
 require(len(modules)==679 and len(guard.caches)==131021 and not guard.serial.inventory(root),'Wrong full selection/cold tree')
 guard.add(self_path)
 expected={name:tuple(item[1]) for name,item in guard.caches.items()}
 reference=original.Guard(**{name:getattr(guard,name) for name in inspect.signature(original.Guard).parameters})
 original.enable_diagnostics(True)
 record=dict(status='versioned_guard_benchmark_running',scope='original authenticated context and unchanged admission/content/root checks; actual v2/original stat guards and complete dictionary validation; no execute',trusted_supervisor_quiet_cache=True,universal_race_error_equivalence=False,guard_version=candidate.GUARD_VERSION,candidate_plan_call_seconds=plan_elapsed,cache_files=len(expected),cache_bytes=sum(x[0] for x in expected.values()),module_count=len(modules),original_runner_sha256=ORIGINAL_SHA,candidate_runner_sha256=CANDIDATE_SHA,helper_sha256=HELPER_SHA,wrapper_sha256=self_pin,runtime_freeze_sha256=a.runtime_freeze_sha256,method_cap_seconds=900,aggregate_benchmark_cap_seconds=1800,measurement_order=['original_stat_guard','versioned_v2_stat_guard','separate_complete_identity_validation'],proof_compilation_executed=False)
 def save():metrics.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
 save();print('MATH115_VERSIONED_GUARD_BEGIN',flush=True)
 def expired(*unused):raise TimeoutError('Bounded versioned guard deadline')
 prior=signal.signal(signal.SIGALRM,expired);deadline=time.monotonic()+1800
 def timed(name,action):
  remaining=deadline-time.monotonic();require(remaining>0,'Aggregate benchmark deadline')
  signal.setitimer(signal.ITIMER_REAL,min(900,remaining));start=time.perf_counter()
  try:return action()
  finally:record[name+'_seconds']=time.perf_counter()-start;signal.setitimer(signal.ITIMER_REAL,0);save()
 try:
  with (root/'.tools/linux-verification/serial-comparator.lock').open('a') as lock:
   guard.serial.fcntl.flock(lock,guard.serial.fcntl.LOCK_EX|guard.serial.fcntl.LOCK_NB)
   timed('original_stat_guard',lambda:reference.check(rehash=False))
   timed('versioned_v2_stat_guard',lambda:guard.check(rehash=False))
   observed=timed('complete_identity_validation',lambda:guard._metadata_index.snapshot(root,expected))
   observed={name:(s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_ino) for name,s in observed.items()}
   require(observed==expected,'Complete actual observed identities differ from admission')
   record['exact_full_dictionary_equality']=True
   record['snapshot_dictionary_sha256']=hashlib.sha256(json.dumps(observed,sort_keys=True,separators=(',',':')).encode()).hexdigest()
  require(not guard.serial.inventory(root),'Submitted proof objects appeared')
  require(sha(self_path)==self_pin and sha(a.runner)==ORIGINAL_SHA and sha(a.candidate_runner)==CANDIDATE_SHA and sha(helper)==HELPER_SHA,'Frozen benchmark bytes drift')
  record['status']='original_and_versioned_guards_and_full_identities_passed'
 except BaseException as error:
  record.update(status='benchmark_failed',error_type=type(error).__name__,error=str(error));raise
 finally:signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,prior);save()
 print('MATH115_VERSIONED_GUARD_END='+json.dumps(record,sort_keys=True),flush=True)
if __name__=='__main__':main()
