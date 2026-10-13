"""Unchanged original plan, two standalone metadata snapshots, original guard.
No candidate installed or substituted into Guard. Stable Linux comparison only.
"""
import argparse,hashlib,importlib.util,json,signal,sys,time
from pathlib import Path
EXPECTED_RUNNER='4ba0a3c42bee4f511909fc50ad33b00be2a5cc3cabecdd2b54ac08ec7970d1a6'
EXPECTED_SNAPSHOT='c875c20375a1bf3362ac836126c7ddb249b0669ef9b2af332691f89f6278a193'
def sha(path):
 with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def main():
 p=argparse.ArgumentParser()
 for name in ('runner','snapshot','metrics','root','runtime-freeze','output'):p.add_argument('--'+name,type=Path,required=True)
 p.add_argument('--runtime-freeze-sha256',required=True);a=p.parse_args()
 root=a.root.resolve();metrics=a.metrics.resolve();self_path=Path(__file__).resolve()
 require(sys.platform.startswith('linux'),'Linux benchmark required')
 require(sha(a.runner)==EXPECTED_RUNNER and sha(a.snapshot)==EXPECTED_SNAPSHOT,'Frozen body mismatch')
 require(metrics.is_relative_to(root/'.tools/linux-verification') and not metrics.exists(),'Fresh owned metrics required')
 self_pin=sha(self_path);m=load('unchanged_snapshot_comparison_runner',a.runner);candidate=load('reviewed_standalone_snapshot',a.snapshot)
 captured=[];original=m.admit;saved_argv=sys.argv
 def capture(*args,**kwargs):
  result=original(*args,**kwargs);captured.append(result);return result
 m.admit=capture
 sys.argv=[str(a.runner),'--root',str(root),'--runtime-freeze',str(a.runtime_freeze),'--runtime-freeze-sha256',a.runtime_freeze_sha256,'--plan','--diagnostics','--wall-seconds','3600','--output',str(a.output)]
 at=time.perf_counter()
 try:m.main()
 finally:m.admit=original;sys.argv=saved_argv
 plan_elapsed=time.perf_counter()-at
 require(len(captured)==1,'Expected one unchanged admission')
 modules,guard,descriptor,caches=captured[0]
 require(len(modules)==679 and len(guard.caches)==131021 and not guard.serial.inventory(root),'Wrong admitted selection/cold tree')
 require(sha(self_path)==self_pin and sha(a.snapshot)==EXPECTED_SNAPSHOT,'Benchmark bytes changed')
 guard.add(self_path);guard.add(a.snapshot)
 expected={name:tuple(item[1]) for name,item in guard.caches.items()}
 record=dict(status='benchmark_running',scope='original full plan/admission; complete standalone metadata comparison; one unchanged stat-only guard; no execute',plan_call_elapsed_seconds=plan_elapsed,module_count=len(modules),cache_files=len(expected),cache_bytes=sum(v[0] for v in expected.values()),runner_sha256=EXPECTED_RUNNER,snapshot_sha256=EXPECTED_SNAPSHOT,wrapper_sha256=self_pin,runtime_freeze_sha256=a.runtime_freeze_sha256,method_cap_seconds=900,aggregate_benchmark_cap_seconds=1800,stable_linux_only=True,race_error_contract_equivalence=False,candidate_installed_in_checker=False)
 def save():metrics.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
 save();print('MATH115_SNAPSHOT_BENCHMARK_BEGIN',flush=True)
 def expired(*unused):raise TimeoutError('Bounded metadata benchmark deadline')
 prior=signal.signal(signal.SIGALRM,expired);deadline=time.monotonic()+1800
 def timed(name,action):
  remaining=deadline-time.monotonic();require(remaining>0,'Aggregate benchmark deadline')
  signal.setitimer(signal.ITIMER_REAL,min(900,remaining));start=time.perf_counter()
  try:return action()
  finally:record[name+'_seconds']=time.perf_counter()-start;signal.setitimer(signal.ITIMER_REAL,0);save()
 def reference():
  result={}
  for name in expected:
   path=m.relative(root,name);m.require(path.is_file(),'Trusted cache file vanished');current=path.stat()
   result[name]=(current.st_size,current.st_mtime_ns,current.st_ctime_ns,current.st_ino)
  return result
 try:
  with (root/'.tools/linux-verification/serial-comparator.lock').open('a') as lock:
   guard.serial.fcntl.flock(lock,guard.serial.fcntl.LOCK_EX|guard.serial.fcntl.LOCK_NB)
   ref=timed('reference_metadata',reference)
   require(ref==expected,'Reference differs from full frozen identity dictionary')
   trie=timed('trie_preparation',lambda:candidate.ManifestTrie(expected))
   result=timed('candidate_metadata',lambda:trie.snapshot(root))
   require(result==expected and result==ref,'Candidate differs from full frozen/reference identity dictionaries')
   encoded=json.dumps(ref,sort_keys=True,separators=(',',':')).encode();record['snapshot_dictionary_sha256']=hashlib.sha256(encoded).hexdigest()
   record['exact_full_dictionary_equality']=True
   timed('unchanged_stat_guard',lambda:guard.check(rehash=False))
  require(not guard.serial.inventory(root),'Submitted proof objects appeared')
  require(sha(self_path)==self_pin and sha(a.snapshot)==EXPECTED_SNAPSHOT,'Benchmark source drift')
  record['status']='complete_snapshot_equality_and_original_guard_passed'
 except BaseException as error:
  record.update(status='benchmark_failed',error_type=type(error).__name__,error=str(error));raise
 finally:signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,prior);save()
 print('MATH115_SNAPSHOT_BENCHMARK_END='+json.dumps(record,sort_keys=True),flush=True)
if __name__=='__main__':main()
