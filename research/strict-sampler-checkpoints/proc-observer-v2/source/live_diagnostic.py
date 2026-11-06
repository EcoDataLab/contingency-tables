"""Three fixed bounded owned toy services; no proof/cache build or observer install."""
import argparse,hashlib,importlib.util,json,os,subprocess,sys,time
from pathlib import Path
PIN='b5e8c0f95fdd5f6b9193c2b0537782b242d0fe0c269dae7b5a7a4c73a32cb1f0'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(x,message):
 if not x:raise RuntimeError(message)
def main():
 p=argparse.ArgumentParser()
 for n in ('root','observer','toy','output'):p.add_argument('--'+n,type=Path,required=True)
 p.add_argument('--toy-sha256',required=True);a=p.parse_args()
 require(os.getuid()!=0 and not a.output.exists(),'Nonroot fresh output required')
 require(sha(a.observer)==PIN and sha(a.toy)==a.toy_sha256,'Diagnostic source pin changed')
 spec=importlib.util.spec_from_file_location('private_observer_diagnostic',a.observer);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 a.output.mkdir();summary={'scope':'fixed toy process observer only; no Lean build/strict admission/kernel/Comparator','observer_sha256':PIN,'toy_sha256':sha(a.toy),'diagnostic_sha256':sha(__file__),'status':'running','scenarios':[],'started_unix':time.time()}
 try:
  lake=a.root/'.tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake';git=Path('/usr/bin/git');path=os.environ['PATH'];python=Path(sys.executable).resolve()
  require(not m.inventory(a.root),'Diagnostic starts with cold submitted build tree')
  for mode in ('recover','deny','overlap'):
   out=a.output/mode;out.mkdir();entry={'stage':'toy_'+mode,'status':'running'};plan={'commands':[entry]};runner=m.MeasuredRunner(a.root,out,plan,20)
   # Explicit toy classifier injection for this diagnostic only. Never installed as a proof checker.
   runner.executables={python}
   argv=m.sandbox_command(a.root,lake,git,path,[])
   require(argv[-1]==str(lake),'Original sandbox argv shape changed')
   argv=argv[:-1]+[str(python),'-I',str(a.toy),'--mode',mode]
   entry['argv']=argv;began=time.monotonic();error=None;result=None
   try:result=runner(argv,entry['stage'])
   except BaseException as failure:error=failure
   row={'mode':mode,'seconds':time.monotonic()-began,'result_returncode':None if result is None else result.returncode,'error_type':None if error is None else type(error).__name__,'error':None if error is None else str(error),'classifier':'explicit toy Python executable, not Lean','classified_executable':str(python),'receipt_sha256':sha(out/'receipt.json')}
   row['status']='validating';summary['scenarios'].append(row)
   unit=entry['owned_unit'];require(unit==f'math115-serial-{runner.token}-0001.service','Owned unit name mismatch')
   check=subprocess.run(['systemctl','--user','show',unit,'--property=ActiveState','--value'],capture_output=True,text=True,timeout=5)
   row['terminal_unit_query']={'returncode':check.returncode,'stdout':check.stdout,'stderr':check.stderr}
   require(check.stdout.strip() not in ('active','activating','deactivating','reloading'),'Owned service still active')
   group=entry.get('observed_cgroup')
   require(group is not None,'No actual owned cgroup observed')
   cgroup=Path('/sys/fs/cgroup')/group.lstrip('/')
   try:remaining=(cgroup/'cgroup.procs').read_text().split()
   except FileNotFoundError:remaining=[]
   require(not remaining,'Owned cgroup still has processes');row['owned_cgroup_empty_or_absent']=True
   lines=(out/('toy_'+mode+'.stdout.log')).read_text().splitlines();toy_rows=[json.loads(line) for line in lines if line.startswith('{')]
   row['toy_records']=toy_rows;require(toy_rows and all(x['uid']==os.getuid() for x in toy_rows),'Expected own nonroot toy identity missing')
   if mode=='recover':
    require(error is None and result.returncode==0,'Recovery toy service failed')
    require(entry.get('incomplete_compiler_samples',0)>0 and entry['successful_compiler_samples']>0 and entry['sampled_heavy_compiler_peak']==1,'Actual incomplete→complete recovery not observed')
    require(entry['compiler_telemetry_status']=='sampled_owned_cgroup_with_incomplete_samples','Recovery gaps not recorded')
    require([x['dumpable'] for x in toy_rows]==[0,1],'Actual dumpability transition missing')
   elif mode=='deny':
    require(isinstance(error,m.CheckError) and 'five seconds' in str(error),'Sustained denial did not trigger retained watchdog')
    require(entry.get('incomplete_compiler_samples',0)>0 and entry['compiler_telemetry_status']=='unavailable_active_service' and entry['owned_unit_stop_returncode']==0,'Denial/owned cleanup evidence missing')
    require(toy_rows[0]['dumpable']==0,'Actual nondumpable child missing')
   else:
    require(isinstance(error,m.CheckError) and 'overlapping' in str(error),'Positive toy overlap not rejected')
    require(len(entry['overlap_pids'])>1 and entry['sampled_heavy_compiler_peak']==2 and entry['owned_unit_stop_returncode']==0,'Actual two-process overlap/cleanup evidence missing')
    require(len(toy_rows)==2,'Two toy process records missing')
   row['status']='passed'
   (a.output/'result.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
  require(sha(a.observer)==PIN and sha(a.toy)==a.toy_sha256,'Diagnostic sources drifted')
  require(not m.inventory(a.root),'Toy diagnostic produced submitted build files')
  summary['status']='three_owned_toy_diagnostics_passed_no_proof'
 except BaseException as error:
  summary.update(status='failed',error_type=type(error).__name__,error=str(error));raise
 finally:
  summary['ended_unix']=time.time();(a.output/'result.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
 return 0
if __name__=='__main__':raise SystemExit(main())
