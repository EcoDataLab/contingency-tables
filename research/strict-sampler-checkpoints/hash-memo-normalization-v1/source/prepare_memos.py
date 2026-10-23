"""Explicit pre-admission bookkeeping preparation; frozen guards stay unchanged."""
import argparse,hashlib,importlib.util,json,os,shutil,stat,subprocess,sys,time
from pathlib import Path
ORIGINAL='4ba0a3c42bee4f511909fc50ad33b00be2a5cc3cabecdd2b54ac08ec7970d1a6'
V2='1008cc3ba5afb129c5d54c8bc030207c8e72715d9b8a1546984e956f919768ca'
AUTH='742ec1105d5bb44a392046ec06ca5944a20989bc0cb5a037d2997b37def2b943'
HELPER='a3bc73a5756b203788a14f848ec8d5e4362fd18cbeed9da3693fdb88ba6187cd'
SNAPSHOT='c875c20375a1bf3362ac836126c7ddb249b0669ef9b2af332691f89f6278a193'
SIDECAR='formal/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/Field/Defs.olean.server.hash'
FACETS=('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so')
def sha(path):
 with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def load(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def tuple4(s):return (s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_ino)
def leaf(path):
 s=path.lstat();require(stat.S_ISREG(s.st_mode),'Witness sidecar not regular')
 require(s.st_size<=4096,'Witness sidecar unexpectedly large')
 fields=('st_dev','st_ino','st_mode','st_uid','st_gid','st_size','st_mtime_ns','st_ctime_ns')
 raw=path.read_bytes();after=path.lstat()
 require(len(raw)==s.st_size and all(getattr(after,k)==getattr(s,k) for k in fields),'Witness changed during read')
 return dict(bytes_hex=raw.hex(),sha256=hashlib.sha256(raw).hexdigest(),stat={k:getattr(s,k) for k in fields})
def main():
 p=argparse.ArgumentParser()
 for name in ('root','runner','candidate','authenticator','baseline','output','helper','snapshot'):p.add_argument('--'+name,type=Path,required=True)
 a=p.parse_args();root=a.root.resolve();out=a.output.resolve()
 require(out.is_relative_to(root/'.tools/linux-verification') and not out.exists(),'Fresh owned output required')
 require(sha(a.runner)==ORIGINAL and sha(a.candidate)==V2 and sha(a.authenticator)==AUTH,'Frozen code mismatch')
 helper_pin,snapshot_pin,self_pin=sha(a.helper),sha(a.snapshot),sha(Path(__file__))
 require(helper_pin==HELPER and snapshot_pin==SNAPSHOT,'Preparation helper/snapshot pins changed')
 out.mkdir();m=load('memo_preparation_v2',a.candidate);snapshot=load('memo_preparation_snapshot',a.snapshot)
 serial,parser=m.load_assets();freeze=m.read(a.candidate.parent/'source-freeze.json');baseline=m.read(a.baseline)
 modules,g,descriptor,roots=m.admit(root,freeze,baseline,serial,parser)
 require(len(modules)==679 and modules[0].name=='Math115.LatticeCompletion' and not serial.inventory(root),'Wrong baseline/cold closure')
 before={n:item[0] for n,item in g.caches.items()};stats_before={n:tuple(item[1]) for n,item in g.caches.items()}
 package_roots=[r for r in roots if r.startswith('formal/.lake/packages/') and g.cache_states[r]['state']=='directory']
 allowed=lambda n:any(n.startswith(r+'/') for r in package_roots)
 result=dict(status='preparation_running',scope='trusted package .hash preparation before new admission, no frozen guard exemptions',baseline_runtime_sha256=sha(a.baseline),original_runner_sha256=ORIGINAL,candidate_sha256=V2,helper_sha256=helper_pin,snapshot_sha256=snapshot_pin,script_sha256=self_pin)
 def save(): (out/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 lake=root/m.PREFIX/'bin/lake';path=os.pathsep.join([str(root/'.tools/verification-bin'),str(lake.parent),str(root/'.tools/elan/bin'),os.environ.get('PATH','')]);git=Path(shutil.which('git',path=path)).resolve()
 plan={'commands':[]};runner=serial.MeasuredRunner(root,out,plan,1800)
 def command(label,options):
  plan['commands'].append({'stage':label,'status':'running','started_unix':time.time()})
  value=runner(serial.sandbox_command(root,lake,git,path,options),label)
  plan['commands'][-1].update(status='passed' if value.returncode==0 else 'failed',returncode=value.returncode)
  serial.save(out/'receipt.json',plan);require(value.returncode==0,label+' command failed')
 def current():
  actual=m.cache_inventory(root,roots,g.cache_states)
  stats=snapshot.ManifestTrie(actual).snapshot(root)
  return actual,stats
 def check_preparation_state(actual,stats):
  require({n:v for n,v in before.items() if not n.endswith('.hash')}=={n:v for n,v in actual.items() if not n.endswith('.hash')},'Non-memo artifact keyset/content changed')
  require(all(stats[n]==stats_before[n] for n in before if not n.endswith('.hash')),'Non-memo artifact metadata changed')
  require(set(before)<=set(actual),'Preparation deleted a cache entry')
  delta=[n for n in actual if n not in before or actual[n]!=before[n] or stats[n]!=stats_before[n]]
  require(all(n.endswith('.hash') and allowed(n) and n[:-5] in before and n[:-5] in actual and n[:-5].endswith(FACETS) for n in delta),'Changes beyond recognized associated package artifact hash memos')
  require(not serial.inventory(root),'Submitted proof objects appeared')
  for n,digest in g.sources.items():require(m.sha(m.relative(root,n))==digest,'Frozen source changed')
  for n,digest in g.tools.items():require(m.sha(m.trusted_runtime_path(root,n))==digest,'Frozen tool/config bytes changed')
  require(m.indexed_configuration_inventory(root,g.config_provenance)==g.config_files and m.configuration_stats(root,g.config_files)==g.config_stats,'Configuration state changed')
  states=m.cache_root_states(root,roots,g.external_owners,g.unused_cache_policy)
  for n,old in g.cache_states.items():
   require(states[n]['state']==old['state'],'Cache presence/absence changed')
   if old['state']=='absent':require(states[n]==old,'Nominated absence identity changed')
   else:require(all(states[n]['identity'][k]==old['identity'][k] for k in ('dev','ino','mode','uid','gid')),'Cache directory identity/ownership changed')
  return delta
 save()
 try:
  result['sidecar_before_observed_command']=leaf(root/SIDECAR)
  command('observe_first_dependencies',['--no-cache','--no-build','build','+Math115.LatticeCompletion:deps'])
  result['sidecar_after_observed_command']=leaf(root/SIDECAR)
  first,first_stats=current();result['observed_command_delta']=check_preparation_state(first,first_stats);save()
  targets={n for n in first if allowed(n) and n.endswith(FACETS)}
  require(all(n[:-5] in first and n[:-5].endswith(FACETS) for n in first if allowed(n) and n.endswith('.hash')),'Unsupported or orphaned package hash memo facet')
  targets.update(n[:-5] for n in first if allowed(n) and n.endswith('.hash'))
  require(targets and all(not any(c in n for c in ('\n','\r','\0')) for n in targets),'Invalid/empty artifact request')
  request=out/'artifact-request.txt';request.write_text(''.join(str(m.relative(root,n))+'\n' for n in sorted(targets)))
  result['normalization_targets']=len(targets);result['request_sha256']=sha(request)
  command('normalize_memos',['env',str(lake.parent/'lean'),'--run',str(a.helper),str(request)])
  after,after_stats=current();result['normalization_delta']=check_preparation_state(after,after_stats)
  result['sidecar_after_normalization']=leaf(root/SIDECAR);save()
  # Original authenticator emits a NEW actual runtime for the prepared state.
  binding=baseline['lake_configuration_provenance_binding'];policy=baseline['unused_cache_policy_binding']
  fresh=out/'runtime-freeze.json'
  args=[sys.executable,'-I',str(a.authenticator),'--root',str(root),'--runner',str(a.runner),'--output',str(fresh),'--native-audit',str(root/'.tools/linux-verification/strict-sampler-inputs/native-audit.json'),'--lake-config-provenance',str(root/binding['path']),'--lake-config-provenance-sha256',binding['sha256'],'--unused-cache-policy',str(root/policy['path']),'--unused-cache-policy-sha256',policy['sha256'],'--diagnostics']
  with (out/'fresh-auth.stdout.log').open('wb') as stdout,(out/'fresh-auth.stderr.log').open('wb') as stderr:
   authenticated=subprocess.run(args,stdout=stdout,stderr=stderr,timeout=5400)
  require(authenticated.returncode==0,'Fresh original authentication failed')
  result['fresh_runtime_sha256']=sha(fresh)
  _,frozen,_,fresh_roots=m.admit(root,freeze,m.read(fresh),serial,parser)
  stable_inventory=m.read(fresh)['trusted_cache_files_sha256']
  result['sidecars_during_stability']=[]
  for i in range(2):
   frozen.check(rehash=True)
   command('stable_dependencies_'+str(i+1),['--no-cache','--no-build','build','+Math115.LatticeCompletion:deps'])
   frozen.check(rehash=True)
   require(m.cache_inventory(root,fresh_roots,frozen.cache_states)==stable_inventory,'Complete frozen inventory drift after repeat')
   require(not serial.inventory(root),'Cold submitted objects changed')
   result['sidecars_during_stability'].append(leaf(root/SIDECAR));save()
  require(sha(a.helper)==helper_pin and sha(a.snapshot)==snapshot_pin and sha(Path(__file__))==self_pin,'Preparation source drift')
  result['status']='normalization_and_two_frozen_repeats_passed_no_proof_build'
 except BaseException as error:
  result.update(status='preparation_failed',error_type=type(error).__name__,error=str(error));raise
 finally:save()
 print('MATH115_MEMO_PREPARATION_RESULT='+json.dumps(result,sort_keys=True),flush=True)
if __name__=='__main__':main()
