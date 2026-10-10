#!/usr/bin/env python3
"""Private offline package of an authenticated final hosted artifact, after success.

No network/compiler/build/Git mutation. Run only after independent script review.
ZIP prefixes are explicit, so an ambiguous or failed attempt cannot be guessed.
"""
import argparse,datetime,gzip,hashlib,importlib.util,json,os,re,runpy,subprocess,sys,zipfile
from pathlib import Path,PurePosixPath

COMMIT='df469a50e32c652093bac17a031b5c2ae6bd8af7'
UPSTREAM='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
ALLOWED={'propext','Classical.choice','Quot.sound'}
CHECKER_SHA='f8a9de8baf9ce2d3d03877f827c72455bdfa60281da7f6e75f54b26a5786035e'
REPO='EcoDataLab/contingency-tables'
NEWCLAIM='Focused Lean compilation, named-axiom replay, and compiled-environment theorem/dependency audit; no Comparator replay.'

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def strict(data):
 def unique(pairs):
  obj={}
  for k,v in pairs:need(k not in obj,'duplicate JSON key');obj[k]=v
  return obj
 return json.loads(data.decode('utf-8-sig'),object_pairs_hook=unique)
def git(repo,*args):
 env=dict(os.environ,GIT_NO_LAZY_FETCH='1',GIT_TERMINAL_PROMPT='0')
 p=subprocess.run(['git','-C',str(repo),*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env)
 need(p.returncode==0,'required immutable Git object unavailable');return p.stdout
def blob(repo,commit,path):return git(repo,'show',commit+':'+path)
def writejson(path,data):path.write_bytes(json.dumps(data,indent=2,ensure_ascii=False).encode()+b'\n')
def gzip_data(path,data):
 with path.open('wb') as dst:
  with gzip.GzipFile(filename='',mode='wb',fileobj=dst,mtime=0,compresslevel=9) as f:f.write(data)
 need(gzip.decompress(path.read_bytes())==data,'gzip roundtrip mismatch')
def positive_integer(x):return type(x)is int and x>0

def package(a):
 root=a.repo.resolve();out=a.output.resolve()
 need(a.commit==COMMIT,'stage-close commit differs from reviewed exact commit')
 need(git(root,'rev-parse',COMMIT+'^{commit}').decode().strip()==COMMIT,'exact commit not present')
 need(out.is_relative_to((root/'.local').resolve()) and not out.exists(),'output must be NEW private .local directory')
 # Copies of supplied metadata are held privately; no auth headers/signed URL enter receipt.
 run=strict(a.run_metadata.read_bytes());job=strict(a.job_metadata.read_bytes());artifact=strict(a.artifact_metadata.read_bytes())
 rid=run.get('id');attempt=run.get('run_attempt');need(positive_integer(rid)and positive_integer(attempt),'invalid run identifiers')
 url=f'https://github.com/{REPO}/actions/runs/{rid}';api=f'https://api.github.com/repos/{REPO}/actions/runs/{rid}'
 need(run.get('repository',{}).get('full_name')==REPO and run.get('path')=='.github/workflows/formal-linux.yml','repository/workflow mismatch')
 need(run.get('head_sha')==COMMIT and run.get('html_url')==url and run.get('url')==api,'run commit/URL mismatch')
 need(run.get('event')=='workflow_dispatch' or(run.get('event')=='push' and str(run.get('head_branch','')).startswith('verify-')),'unexpected workflow trigger')
 need(run.get('status')=='completed'and run.get('conclusion')=='success','run failed/pending: no passed package')
 need(job.get('run_id')==rid and job.get('run_attempt')==attempt and job.get('head_sha')==COMMIT,'job association mismatch')
 need(positive_integer(job.get('id'))and job.get('run_url')==api and job.get('html_url')==url+'/job/'+str(job['id']),'job URL mismatch')
 need(job.get('status')=='completed'and job.get('conclusion')=='success'and'ubuntu-24.04'in job.get('labels',[]),'job did not succeed on expected runner')
 need(artifact.get('name')==f'math115-linux-focused-{rid}-{attempt}'and artifact.get('workflow_run',{}).get('id')==rid and artifact['workflow_run'].get('head_sha')==COMMIT,'artifact association mismatch')
 archive=a.artifact_zip.read_bytes();need(artifact.get('digest')=='sha256:'+sha(archive),'provider ZIP digest unavailable/mismatched')
 need(type(artifact.get('size_in_bytes'))is int and len(archive)==artifact['size_in_bytes'],'artifact ZIP byte length differs from provider metadata')
 steps=job.get('steps',[])
 for name in ['Check out the selected commit without retained credentials','Record the fresh environment and exact source inputs',
              'Install the pinned Lean toolchain and trusted Mathlib cache locally','Run the selected verification scope']:
  selected=[x for x in steps if isinstance(x,dict)and x.get('name')==name]
  need(len(selected)==1 and selected[0].get('conclusion')=='success','required scoped job step failed')
 # Validate every archive member before reading payload; no generic extraction.
 members={}
 with zipfile.ZipFile(a.artifact_zip)as z:
  infos=z.infolist();need(len(infos)<=10000 and sum(x.file_size for x in infos)<=1024**3,'archive bounds exceeded')
  for info in infos:
   p=PurePosixPath(info.filename);need(not p.is_absolute()and'..'not in p.parts and':'not in info.filename and'\\'not in info.filename and str(p)==info.filename.rstrip('/'),'unsafe/noncanonical archive member')
   need(info.filename not in members and not(info.flag_bits&1)and (info.external_attr>>16)&0o170000!=0o120000,'duplicate/encrypted/symlink member')
   if not info.is_dir():members[info.filename]=z.read(info)
 def prefix(value):
  p=PurePosixPath(value);need(not p.is_absolute()and'..'not in p.parts,'unsafe explicit member prefix');return str(p).strip('/')
 vp=prefix(a.verification_prefix);ep=prefix(a.audit_prefix)
 def member(prefix,name):
  key=prefix+'/'+name;need(key in members,'missing explicit artifact member: '+key);return members[key]
 env=strict(member(vp,'environment.json'));outcome=strict(member(vp,'outcome.json'))
 need(env.get('repository_commit')==COMMIT and env.get('scope')==outcome.get('scope')=='focused','recorded commit/scope mismatch')
 need(env.get('run_url')==outcome.get('run_url')==url and type(env.get('uid'))is int and env['uid']>0,'run URL/nonroot mismatch')
 need(env.get('runner_label')=='ubuntu-24.04'and outcome.get('passed')is True and outcome.get('claim')==NEWCLAIM,'focused outcome not passed')
 need(outcome.get('step_outcomes')=={'ENVIRONMENT_OUTCOME':'success','SANDBOX_OUTCOME':'skipped','BOOTSTRAP_OUTCOME':'success','TOOLS_OUTCOME':'skipped','VERIFICATION_OUTCOME':'success'},'scoped outcomes differ')
 expected={p for p in git(root,'ls-tree','-r','-z','--name-only',COMMIT).decode().split('\0')if p.startswith('formal/')and p.endswith('.lean')}
 expected|={'formal/lakefile.lean','formal/lake-manifest.json','formal/lean-toolchain'}
 need(set(env['source_sha256'])==expected,'owned source inventory missing/extra')
 for p,h in env['source_sha256'].items():need(sha(blob(root,COMMIT,p))==h,'immutable owned source mismatch: '+p)
 need(blob(root,COMMIT,'formal/lean-toolchain').decode().strip()=='leanprover/lean4:v4.34.1','Lean source pin mismatch')
 # Load reviewed local strict checker; require exact committed bytes/policy.
 checker_source=blob(root,COMMIT,'scripts/check_lean_axioms.py');need(sha(checker_source)==CHECKER_SHA,'reviewed checker SHA mismatch')
 need((root/'scripts/check_lean_axioms.py').read_bytes()==checker_source,'local strict checker differs')
 checker=runpy.run_path(str(root/'scripts/check_lean_axioms.py'));need(set(checker['ALLOWED'])==ALLOWED,'checker policy mismatch')
 text=member(vp,'verification.log').decode('utf-8-sig');need('\r'not in text.replace('\r\n',''),'bare CR in proof log')
 text=text.replace('\r\n','\n')
 first=re.search(r"^'[^']+' (?:depends on axioms|does not depend on any axioms)",text,re.M)
 summaries=list(re.finditer(r'^Axiom allowlist passed for (\d+) declarations\.$',text,re.M))
 need(first is not None and len(summaries)==1 and int(summaries[0].group(1))==1236,'named focused block ambiguous/count mismatch')
 audit=text[first.start():summaries[0].start()];driver=blob(root,COMMIT,'formal/Math115/AxiomAudit.lean')
 records=checker['check_audit'](driver.decode(),audit);need(len(records)==1236,'exact ordered focused audit differs')
 need(len(re.findall(r'^Verification started:',text,re.M))==len(re.findall(r'^Verification completed:',text,re.M))==1,'verification block incomplete')
 # Environment report validation is pure Python, using EXACT owned runner source.
 runner_source=blob(root,COMMIT,'scripts/run_environment_audit.py')
 need((root/'scripts/run_environment_audit.py').read_bytes()==runner_source,'local environment runner differs from exact commit')
 runner=runpy.run_path(str(root/'scripts/run_environment_audit.py'));canonical=runner['canonical_sha']
 er=strict(member(ep,'receipt.json'));cfg=strict(member(ep,'frozen-config.json'))
 need(er.get('status')=='passed_compiled_environment_audit'and er.get('runner_sha256')==sha(runner_source),'environment audit/runner mismatch')
 runner['config_check'](cfg)
 expected_heads=sorted({h['name']for c in strict(blob(root,COMMIT,'claims.json'))['claims']for h in c['headlines']})
 need(cfg['headlines']==expected_heads and cfg['imports']==['Math115'],'headline/import scope differs from immutable claims source')
 needed_named=[]
 for relative in ['formal/Math115/AxiomAudit.lean','formal/Math115/StandaloneAxiomAudit.lean']:
  needed_named+=re.findall(r'^#print axioms (\S+)\s*$',blob(root,COMMIT,relative).decode(),re.M)
 need(cfg['expected_declarations']==needed_named,'environment named inclusion differs from immutable source')
 need({k.split(':',1)[1]for k in cfg['pins']if k.startswith('source:')}==set(cfg['expected_modules']),'source pins do not cover complete expected module graph')
 reportbytes=member(ep,'environment-audit.stdout');need(len(reportbytes)<=512*1024**2,'report exceeds reviewed parser bound')
 need(sha(reportbytes)==er['environment_audit']['stdout_sha256'],'complete report digest mismatch')
 report=runner['strict_json'](reportbytes.decode('utf-8'));counts=runner['validate_report'](report,cfg)
 need(counts==er['counts'],'environment counts differ; native counts are never assumed')
 helper=blob(root,COMMIT,'formal/ResearchAudit/EnvironmentAudit.lean')
 need(cfg['helper_sha256']==sha(helper),'helper source mismatch')
 need(member(ep,'Audit.lean')==runner['driver_source'](cfg).encode()and er['driver_sha256']==sha(member(ep,'Audit.lean')),'environment driver differs')
 # Original pre-attempt config lives one directory above attempt; explicit archive binding.
 config_key=ep.rsplit('/',1)[0]+'/config.json'
 need(config_key in members and sha(members[config_key])==er['config_sha256']and strict(members[config_key])==cfg,'original/frozen configuration mismatch')
 cb=strict(member(ep,'compile-before.json'));ca=strict(member(ep,'compile-after.json'))
 ab=strict(member(ep,'audit-before.json'));aa=strict(member(ep,'audit-after.json'))
 need(cb==ca and ab==aa and canonical(ab)==er['before_after_canonical_sha256'],'input snapshot changed')
 helper_argv=er['helper_compile']['argv'];need('-o'in helper_argv,'helper compile object path missing')
 helper_object=PurePosixPath(helper_argv[helper_argv.index('-o')+1]);helper_library=helper_object.parent.parent
 need(helper_object.relative_to(helper_library)==PurePosixPath('ResearchAudit/EnvironmentAudit.olean'),'unexpected helper object identity')
 for snapshot,roots in [(cb,set(cfg['inventory_roots'])),(ab,set(cfg['inventory_roots'])|{str(helper_library)})]:
  states=snapshot.get('inventory_root_states');need(isinstance(states,dict)and set(states)==roots and set(states.values())<={'directory','absent'},'configured root-state inventory missing/extra/invalid')
 need(ab['inventory_root_states'][str(helper_library)]=='directory','audited helper library root not present')
 need(len(ab['files'])==er['input_files']and len(ab['artifact_inventory'])==er['artifact_inventory_files'],'input inventory counts differ')
 for phase,filelabel in [('helper_compile','helper-compile'),('environment_audit','environment-audit'),('compiler_version_check','compiler-version'),('compiler_prefix_check','compiler-prefix')]:
  value=er[phase];need(value['exit_code']==0 and value['timed_out']is False,'recorded compiler/helper phase failed')
  for stream in ['stdout','stderr']:need(sha(member(ep,filelabel+'.'+stream))==value[stream+'_sha256'],'phase stream digest mismatch')
 need(not member(ep,'environment-audit.stderr')and not member(ep,'helper-compile.stdout')and not member(ep,'helper-compile.stderr'),'unexpected helper/audit diagnostics')
 workspace=PurePosixPath(cfg['working_directory']).parent
 need(member(ep,'compiler-version.stdout').decode().strip()==cfg['compiler_version']==er['compiler_version'],'actual compiler version differs')
 need(str(PurePosixPath(member(ep,'compiler-prefix.stdout').decode().strip())/'lib/lean')==cfg['builtin_library'],'compiler sysroot differs')
 for label,pin in cfg['pins'].items():
  need(cb['files'].get(pin['path'])==pin['sha256'],'required pin omitted/changed in snapshots')
  if label.startswith('source:'):
   module=label.split(':',1)[1];relative=module.replace('.','/')+'.lean'
   actual=blob(root,COMMIT,'formal/'+relative)if module=='Math115'or module.startswith('Math115.')else blob(root/'.upstream/openai-math',UPSTREAM,'lean/'+relative)
   need(sha(actual)==pin['sha256'],'immutable source pin differs: '+module)
  elif label.startswith('configuration:'):need(sha(blob(root,COMMIT,label.split(':',1)[1]))==pin['sha256'],'immutable configuration pin differs')
 need(cb['files'].get(cfg['compiler'])==cfg['compiler_sha256'],'compiler object missing from required snapshot')
 need(cb['files'].get(str(workspace/'scripts/run_environment_audit.py'))==sha(runner_source),'actual runner source omitted/changed in snapshot')
 need(cb['files'].get(cfg['helper_source'])==sha(helper),'actual helper source omitted/changed in snapshot')
 audit_argv=er['environment_audit']['argv'];need(ab['files'].get(audit_argv[-1])==er['driver_sha256'],'actual driver omitted/changed in snapshot')
 # Bind every delivered helper binary to the immutable audit input map, not just metadata.
 helper_member_prefix=ep+'/helper-lib/'
 delivered_helper=False
 for key,data in members.items():
  if key.startswith(helper_member_prefix):
   original_path=str(helper_library/PurePosixPath(key[len(helper_member_prefix):]))
   need(ab['files'].get(original_path,ab['artifact_inventory'].get(original_path))==sha(data),'delivered helper library member differs from frozen snapshot')
   if original_path==str(helper_object):
    need(sha(data)==er['helper_object_sha256'],'actual EnvironmentAudit.olean bytes differ from receipt');delivered_helper=True
 need(delivered_helper,'actual helper object binary not delivered in complete workflow archive')
 closure=strict(member(ep,'imported-object-closure.json'));need(canonical(closure)==er['resolved_import_closure_sha256']and set(closure)==set(report['imported_modules']),'full imported resolution map differs')
 search=[PurePosixPath(p)for p in er['audit_lean_path'].split(':')]+[PurePosixPath(cfg['builtin_library'])]
 for module,bound in closure.items():
  obj=PurePosixPath(bound['path']);relative=PurePosixPath(module.replace('.','/')+'.olean')
  need(any(obj==p/relative for p in search),'imported module path/name outside actual search roots')
  need(ab['files'].get(str(obj),ab['artifact_inventory'].get(str(obj)))==bound['sha256'],'imported object missing/different in actual snapshot')
 # Stage publication-safe payload only after every success gate. Original bytes kept.
 out.mkdir(parents=True,exist_ok=False);(out/'environment-audit').mkdir()
 archive_map={};excluded=[];unique={}
 for key,data in members.items():
  if not(key.startswith(vp+'/')or key.startswith(ep+'/')or key==config_key):continue
  lower=key.lower()
  if lower.endswith(('.olean','.ilean','.olean.private','.olean.server','.o','.a','.so','.dll','.dylib','.exe','.ir','.ir.sig')):
   excluded.append({'archive_member':key,'sha256':sha(data),'bytes':len(data),'reason':'Binary delivery excluded; input/receipt digest binding retained.'});continue
  # All remaining files are text; refuse accidental binary projection.
  data.decode('utf-8');h=sha(data)
  target=('environment-audit/'+key[len(ep)+1:])if key.startswith(ep+'/')else('original-config.json'if key==config_key else key[len(vp)+1:])
  if key.endswith('environment-audit.stdout')or key.endswith(('.json',))and len(data)>1024*1024:target+='.gz'
  if h in unique:archive_map[key]={'public_file':unique[h],'original_sha256':h,'bytes':len(data),'deduplicated_byte_identical':True};continue
  path=out/target;path.parent.mkdir(parents=True,exist_ok=True)
  if target.endswith('.gz'):gzip_data(path,data)
  else:path.write_bytes(data)
  unique[h]=target;archive_map[key]={'public_file':target,'original_sha256':h,'bytes':len(data),'gzip':target.endswith('.gz')}
 (out/'AxiomAudit.lean').write_bytes(driver);(out/'axiom-audit.log').write_bytes(audit.encode())
 (out/'EnvironmentAudit.lean').write_bytes(helper);(out/'run_environment_audit.py').write_bytes(runner_source)
 writejson(out/'archive-member-map.json',{'members':archive_map,'excluded_binaries':excluded,'method':'Original hosted-runner bytes, gzip empty filename/mtime0/level9; identical member payloads share one public file. No redaction or truncation.'})
 result={'schema_version':1,'status':'passed','repository_commit':COMMIT,'run_url':url,'run_id':rid,'run_attempt':attempt,'job_id':job['id'],'job_url':job['html_url'],
  'scope':'Exact-commit hosted Linux focused1236 named replay and fresh compiled-environment audit. No separate standalone named audits, Comparator or new runtime result.',
  'audit_declaration_count':1236,'audited_declarations':records,'allowed_axioms':sorted(ALLOWED),'source_sha256':env['source_sha256'],
  'upstream_revision':UPSTREAM,'environment_audit_counts':counts,'headline_dependency_closure_counts':{h['name']:len(h['closure'])for h in report['headlines']},
  'artifact_provider_digest':artifact['digest'],'artifact_id':artifact['id'],'artifact_name':artifact['name'],
  'source_metadata_sha256':{k:sha(p.read_bytes())for k,p in [('run',a.run_metadata),('job',a.job_metadata),('artifact',a.artifact_metadata)]},
  'compiled_environment_receipt_original_sha256':sha(member(ep,'receipt.json')),'packager_sha256':sha(Path(__file__).read_bytes()),
  'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'binary_helper_objects_bound_but_not_published':excluded,
  'import_binding_boundary':'Complete recorded module path/name/digest bindings matched eligible ordered search roots and recorded frozen snapshots. The hosted runner performed filesystem resolution; no unavailable-filesystem reenactment is asserted.',
  'trust_boundary':er['platform_loader_boundary'],'independent_review':'Pending root and independent actual-artifact readback.'}
 result['scope']=result['scope'].replace('focused1236','focused 1236')
 result['artifacts_sha256']={p.relative_to(out).as_posix():sha(p.read_bytes())for p in sorted(out.rglob('*'))if p.is_file()}
 writejson(out/'verification.json',result)
 return{'status':'passed_private_package_pending_review','output_files':len(result['artifacts_sha256'])+1,'named_audits':1236,'environment_counts':counts}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--commit',required=True)
 for x in ['run-metadata','job-metadata','artifact-metadata','artifact-zip']:p.add_argument('--'+x,type=Path,required=True)
 p.add_argument('--verification-prefix',required=True);p.add_argument('--audit-prefix',required=True);p.add_argument('--output',type=Path,required=True)
 a=p.parse_args()
 try:result=package(a)
 except Exception as error:
  # A failed/pending or malformed artifact cannot produce passed verification.json.
  print('Final hosted packaging rejected: '+str(error),file=sys.stderr);return 1
 print(json.dumps(result,indent=2));return 0
if __name__=='__main__':raise SystemExit(main())
