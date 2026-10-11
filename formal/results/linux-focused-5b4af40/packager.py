#!/usr/bin/env python3
"""Private offline intake of the single authenticated integration-run artifact.

No network/compiler/build/Git mutation. Run only after independent script review.
ZIP prefixes are explicit, so an ambiguous or failed attempt cannot be guessed.
Completed negative runs keep their complete ZIP and no successful proof counts.
"""
import argparse,datetime,gzip,hashlib,importlib.util,json,os,re,runpy,subprocess,sys,zipfile
from pathlib import Path,PurePosixPath
import types

COMMIT='5b4af402a281a9bc02a38adb168f7b0bfde5d3aa'
RUN_ID=38101898049
EXPECTED_NAMED=1511
EXPECTED_STANDALONE=6
EXPECTED_MODULES=685
RUNNER_SHA='b0c57d1a8caa5ed464ffbff0be5d2786e665fa36df7c2bc5a962604aaed21fc7'
SERIAL_SHA='5dd644d68305af37343963e283e4b25efb95420896add41f8aa8fd6e2737a66c'
WORKFLOW_SHA='1f4321361ff97ee80c7a47a46f7316de495b494046c1f9d9ac8bae389c902a21'
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
 return json.loads(data.decode('utf-8-sig'),object_pairs_hook=unique,
  parse_constant=lambda value: (_ for _ in ()).throw(ValueError('non-finite JSON number')))
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

def frozen_python(source,path,label):
 """Load hash-checked committed helpers; call only their pure validators."""
 name='frozen_'+label+'_'+COMMIT[:8]
 module=types.ModuleType(name);module.__file__=str(path);sys.modules[name]=module
 exec(compile(source,str(path),'exec'),module.__dict__)
 return module.__dict__

def identity_records(report,contract,canonical):
 heads={h['name']:h for h in report['headlines']};result=[]
 for requirement in contract['program_identity_requirements']:
  headline=heads[requirement['headline']]
  need(set(requirement['required_reachable_names'])<=set(headline['closure']),'program identity omitted from actual closure')
  result.append(dict(requirement,actual_closure_sha256=canonical(headline),closure_size=len(headline['closure'])))
 return result

def named_block(text,driver,checker):
 need('\r'not in text.replace('\r\n',''),'bare CR in proof log')
 text=text.replace('\r\n','\n')
 first=re.search(r"^'[^']+' (?:depends on axioms|does not depend on any axioms)",text,re.M)
 summaries=list(re.finditer(r'^Axiom allowlist passed for (\d+) declarations\.$',text,re.M))
 need(first is not None and len(summaries)==1 and int(summaries[0].group(1))==EXPECTED_NAMED,'named focused block ambiguous/count mismatch')
 audit=text[first.start():summaries[0].start()]
 records=checker['check_audit'](driver.decode(),audit)
 need(len(records)==EXPECTED_NAMED,'exact ordered focused audit differs')
 need(len(re.findall(r'^Verification started:',text,re.M))==len(re.findall(r'^Verification completed:',text,re.M))==1,'verification block incomplete')
 return text,audit,records

def validate_compile_transition(before,after,helper_library):
 for field in ['files','artifact_inventory','inventory_root_states']:
  expected={p:v for p,v in after[field].items()if not PurePosixPath(p).is_relative_to(helper_library)}
  need(before[field]==expected,'compile-to-audit input changed outside fresh helper library: '+field)

def validate_serial_graph(root,text,expected_modules):
 source=blob(root,COMMIT,'scripts/build_lean_serial.py');need(sha(source)==SERIAL_SHA,'reviewed serial builder changed')
 helper=frozen_python(source,root/'scripts/build_lean_serial.py','serial')
 def resolve(name):
  path=name.replace('.','/')+'.lean'
  if name=='Math115'or name.startswith('Math115.'):
   data=blob(root,COMMIT,'formal/'+path)
  elif name.startswith(('OAI.','ComparatorChallenges.')):
   data=blob(root/'.upstream/openai-math',UPSTREAM,'lean/'+path)
  else:return None
  return helper['Module'](name,Path(path),helper['lean_imports'](data.decode('utf-8-sig')))
 audit=blob(root,COMMIT,'formal/Math115/AxiomAudit.lean').decode()
 roots=tuple(dict.fromkeys((*helper['ROOTS']['focused'],*helper['lean_imports'](audit))))
 modules=helper['dependency_order'](roots,resolve)
 need(len(modules)==EXPECTED_MODULES and set(m.name for m in modules)==set(expected_modules),'immutable source import graph differs from actual default graph')
 stages=re.findall(r'^Serial module (\d+)/(\d+): (\S+)\s*$',text,re.M)
 need(stages==[(str(i),str(len(modules)),m.name)for i,m in enumerate(modules,1)],'serial log omitted/reordered/duplicated actual source build stages')
 need(text.count('Serial module builds completed.')==1 and 'build mode: --serial'in text,'serial build completion/mode evidence absent')

def save_provider_sidecars(out,run,job,artifact):
 """Public allowlist projection; actors, runner names and download URLs omitted."""
 projected_run={k:run.get(k)for k in ['id','run_attempt','head_sha','head_branch','status','conclusion','event','path','html_url','url','created_at','updated_at','run_started_at']}
 projected_run['repository']={'full_name':run['repository']['full_name']}
 projected_job={k:job.get(k)for k in ['id','run_id','run_attempt','head_sha','status','conclusion','html_url','run_url','labels','started_at','completed_at']}
 projected_job['steps']=[{k:s.get(k)for k in ['number','name','status','conclusion','started_at','completed_at']}for s in job.get('steps',[])]
 projected_artifact={k:artifact.get(k)for k in ['id','name','digest','size_in_bytes','expired','created_at','updated_at','expires_at']}
 projected_artifact['workflow_run']={k:artifact['workflow_run'].get(k)for k in ['id','head_sha','head_branch']}
 for name,data in [('provider-run.json',projected_run),('provider-job.json',projected_job),('provider-artifact.json',projected_artifact)]:writejson(out/name,data)

def preserve_negative(a,root,out,run,job,artifact,members,reason):
 """Keep the complete authenticated ZIP privately without an upgraded result."""
 out.mkdir(parents=True,exist_ok=False)
 archive=a.artifact_zip.read_bytes();(out/'artifact.zip').write_bytes(archive)
 save_provider_sidecars(out,run,job,artifact)
 result={'schema_version':1,'status':'not_verified','repository_commit':COMMIT,'run_id':run['id'],
  'run_attempt':run['run_attempt'],'job_id':job['id'],'artifact_id':artifact['id'],
  'provider_zip_digest':artifact['digest'],'actual_zip_sha256':sha(archive),'reason':reason,
  'scope':'Failed hosted verification capture only; no successful named/environment/kernel claim.',
  'named_audits_verified':None,'environment_counts':None,
  'archive_members':{k:{'sha256':sha(v),'bytes':len(v)}for k,v in members.items()},
  'source_metadata_sha256':{k:sha(p.read_bytes())for k,p in [('run',a.run_metadata),('job',a.job_metadata),('artifact',a.artifact_metadata)]},
  'packager_sha256':sha(Path(__file__).read_bytes()),'all_archive_bytes_preserved_in':'artifact.zip'}
 writejson(out/'verification.json',result)
 return {'status':'not_verified_private_capture','named_audits':None,'environment_counts':None}

def package(a):
 root=a.repo.resolve();out=a.output.resolve()
 need(a.commit==COMMIT,'integration commit differs from reviewed exact commit')
 need(git(root,'rev-parse',COMMIT+'^{commit}').decode().strip()==COMMIT,'exact commit not present')
 need(out.is_relative_to((root/'.local').resolve()) and not out.exists(),'output must be NEW private .local directory')
 # Copies of supplied metadata are held privately; no auth headers/signed URL enter receipt.
 run=strict(a.run_metadata.read_bytes());job=strict(a.job_metadata.read_bytes());artifact=strict(a.artifact_metadata.read_bytes())
 rid=run.get('id');attempt=run.get('run_attempt');need(rid==RUN_ID and type(attempt)is int and attempt==1,'run/attempt differs from the single reviewed integration run')
 url=f'https://github.com/{REPO}/actions/runs/{rid}';api=f'https://api.github.com/repos/{REPO}/actions/runs/{rid}'
 need(run.get('repository',{}).get('full_name')==REPO and run.get('path')=='.github/workflows/formal-linux.yml','repository/workflow mismatch')
 need(run.get('head_sha')==COMMIT and run.get('html_url')==url and run.get('url')==api,'run commit/URL mismatch')
 need(run.get('event')=='workflow_dispatch' or(run.get('event')=='push' and str(run.get('head_branch','')).startswith('verify-')),'unexpected workflow trigger')
 need(run.get('status')=='completed','run is pending: no result package')
 need(job.get('run_id')==rid and type(job.get('run_attempt'))is int and job.get('run_attempt')==attempt and job.get('head_sha')==COMMIT,'job association mismatch')
 need(positive_integer(job.get('id'))and job.get('run_url')==api and job.get('html_url')==url+'/job/'+str(job['id']),'job URL mismatch')
 need(job.get('status')=='completed'and'ubuntu-24.04'in job.get('labels',[]),'job is pending or runner differs')
 need(artifact.get('name')==f'math115-linux-focused-{rid}-{attempt}'and artifact.get('workflow_run',{}).get('id')==rid and artifact['workflow_run'].get('head_sha')==COMMIT,'artifact association mismatch')
 need(positive_integer(artifact.get('id')),'invalid provider artifact identity')
 archive=a.artifact_zip.read_bytes();need(artifact.get('digest')=='sha256:'+sha(archive),'provider ZIP digest unavailable/mismatched')
 need(type(artifact.get('size_in_bytes'))is int and len(archive)==artifact['size_in_bytes'],'artifact ZIP byte length differs from provider metadata')
 steps=job.get('steps',[])
 required_steps=['Check out the selected commit without retained credentials','Record the fresh environment and exact source inputs',
                 'Install the pinned Lean toolchain and trusted Mathlib cache locally','Run the selected verification scope']
 for name in ['Check out the selected commit without retained credentials','Record the fresh environment and exact source inputs',
              'Install the pinned Lean toolchain and trusted Mathlib cache locally','Run the selected verification scope']:
  selected=[x for x in steps if isinstance(x,dict)and x.get('name')==name]
  if run.get('conclusion')==job.get('conclusion')=='success':
   need(len(selected)==1,'required scoped job step missing/ambiguous')
 # Validate every archive member before reading payload; no generic extraction.
 members={}
 with zipfile.ZipFile(a.artifact_zip)as z:
  infos=z.infolist();need(len(infos)<=10000 and sum(x.file_size for x in infos)<=1024**3,'archive bounds exceeded')
  seen=set()
  for info in infos:
   p=PurePosixPath(info.filename);need(not p.is_absolute()and'..'not in p.parts and':'not in info.filename and'\\'not in info.filename and str(p)==info.filename.rstrip('/'),'unsafe/noncanonical archive member')
   need(info.filename.casefold() not in seen and not(info.flag_bits&1)and (info.external_attr>>16)&0o170000!=0o120000,'duplicate/case-alias/encrypted/symlink member')
   seen.add(info.filename.casefold())
   if not info.is_dir():members[info.filename]=z.read(info)
 if run.get('conclusion')!='success' or job.get('conclusion')!='success':
  return preserve_negative(a,root,out,run,job,artifact,members,'Completed provider run/job did not pass.')
 def prefix(value):
  p=PurePosixPath(value);need(not p.is_absolute()and'..'not in p.parts,'unsafe explicit member prefix');return str(p).strip('/')
 need(a.audit_prefix is not None,'successful provider run requires an explicit audit prefix')
 vp=prefix(a.verification_prefix);ep=prefix(a.audit_prefix)
 attempts=[k for k in members if k.startswith('.local/environment-audits/')and k.endswith('/attempt/receipt.json')]
 if run.get('conclusion')==job.get('conclusion')=='success':
  need(attempts==[ep+'/receipt.json'],'success artifact has omitted/ambiguous environment attempts')
 def member(prefix,name):
  key=prefix+'/'+name;need(key in members,'missing explicit artifact member: '+key);return members[key]
 if vp+'/environment.json' not in members or vp+'/outcome.json' not in members:
  return preserve_negative(a,root,out,run,job,artifact,members,'Required environment/outcome artifact is absent; no successful evidence claim.')
 env=strict(member(vp,'environment.json'));outcome=strict(member(vp,'outcome.json'))
 need(env.get('repository_commit')==COMMIT and env.get('scope')==outcome.get('scope')=='focused','recorded commit/scope mismatch')
 need(env.get('run_url')==outcome.get('run_url')==url and type(env.get('uid'))is int and env['uid']>0,'run URL/nonroot mismatch')
 need(env.get('runner_label')=='ubuntu-24.04' and env.get('ordinary_build_mode')=='--serial','runner/build mode differs from reviewed serial run')
 if run.get('conclusion')!='success' or job.get('conclusion')!='success' or outcome.get('passed')is not True:
  return preserve_negative(a,root,out,run,job,artifact,members,'Completed CI run or focused outcome did not pass.')
 need(outcome.get('claim')==NEWCLAIM,'focused success claim differs')
 for name in required_steps:
  selected=[x for x in steps if isinstance(x,dict)and x.get('name')==name]
  need(selected[0].get('status')=='completed'and selected[0].get('conclusion')=='success','provider scoped step did not pass')
 need(sha(blob(root,COMMIT,'.github/workflows/formal-linux.yml'))==WORKFLOW_SHA,'reviewed workflow changed')
 need(outcome.get('step_outcomes')=={'ENVIRONMENT_OUTCOME':'success','SANDBOX_OUTCOME':'skipped','BOOTSTRAP_OUTCOME':'success','TOOLS_OUTCOME':'skipped','VERIFICATION_OUTCOME':'success'},'scoped outcomes differ')
 expected={p for p in git(root,'ls-tree','-r','-z','--name-only',COMMIT).decode().split('\0')if p.startswith('formal/')and p.endswith('.lean')}
 expected|={'formal/lakefile.lean','formal/lake-manifest.json','formal/lean-toolchain',
 'formal/default-audit-contract.json','claims.json','scripts/prepare_environment_audit.py','scripts/run_environment_audit.py'}
 need(set(env['source_sha256'])==expected,'owned source inventory missing/extra')
 for p,h in env['source_sha256'].items():need(sha(blob(root,COMMIT,p))==h,'immutable owned source mismatch: '+p)
 need(blob(root,COMMIT,'formal/lean-toolchain').decode().strip()=='leanprover/lean4:v4.34.1','Lean source pin mismatch')
 # Load reviewed local strict checker; require exact committed bytes/policy.
 checker_source=blob(root,COMMIT,'scripts/check_lean_axioms.py');need(sha(checker_source)==CHECKER_SHA,'reviewed checker SHA mismatch')
 need((root/'scripts/check_lean_axioms.py').read_bytes()==checker_source,'local strict checker differs')
 checker=frozen_python(checker_source,root/'scripts/check_lean_axioms.py','checker');need(set(checker['ALLOWED'])==ALLOWED,'checker policy mismatch')
 driver=blob(root,COMMIT,'formal/Math115/AxiomAudit.lean')
 text,audit,records=named_block(member(vp,'verification.log').decode('utf-8-sig'),driver,checker)
 # Environment report validation is pure Python, using EXACT owned runner source.
 runner_source=blob(root,COMMIT,'scripts/run_environment_audit.py')
 need(sha(runner_source)==RUNNER_SHA,'reviewed integration runner SHA differs')
 need((root/'scripts/run_environment_audit.py').read_bytes()==runner_source,'local environment runner differs from exact commit')
 runner=frozen_python(runner_source,root/'scripts/run_environment_audit.py','runner');canonical=runner['canonical_sha']
 er=strict(member(ep,'receipt.json'));cfg=strict(member(ep,'frozen-config.json'))
 need(er.get('status')=='passed_compiled_environment_audit'and er.get('runner_sha256')==sha(runner_source),'environment audit/runner mismatch')
 runner['config_check'](cfg)
 contract=strict(blob(root,COMMIT,'formal/default-audit-contract.json'))
 expected_heads=sorted(set(contract['headlines'])|{h['name']for c in strict(blob(root,COMMIT,'claims.json'))['claims']for h in c['headlines']})
 need(len(expected_heads)==22 and len(contract['private_source_helpers'])==3 and len(contract['program_identity_requirements'])==2,'integration contract scope differs')
 need(cfg.get('private_source_helpers')==contract['private_source_helpers'] and cfg.get('program_identity_requirements')==contract['program_identity_requirements'],'configured private/program seams differ from contract')
 need(cfg['headlines']==expected_heads and cfg['imports']==['Math115'],'headline/import scope differs from immutable claims source')
 needed_named=[]
 for relative in ['formal/Math115/AxiomAudit.lean','formal/Math115/StandaloneAxiomAudit.lean']:
  needed_named+=re.findall(r'^#print axioms (\S+)\s*$',blob(root,COMMIT,relative).decode(),re.M)
 need(cfg['expected_declarations']==needed_named and len(needed_named)==EXPECTED_NAMED+EXPECTED_STANDALONE,'environment named inclusion differs from immutable source')
 need(len(cfg['expected_modules'])==EXPECTED_MODULES,'default compiled module graph count differs')
 validate_serial_graph(root,text,cfg['expected_modules'])
 need({k.split(':',1)[1]for k in cfg['pins']if k.startswith('source:')}==set(cfg['expected_modules']),'source pins do not cover complete expected module graph')
 reportbytes=member(ep,'environment-audit.stdout');need(len(reportbytes)<=512*1024**2,'report exceeds reviewed parser bound')
 need(sha(reportbytes)==er['environment_audit']['stdout_sha256'],'complete report digest mismatch')
 report=runner['strict_json'](reportbytes.decode('utf-8'));counts=runner['validate_report'](report,cfg)
 need(counts==er['counts'],'environment counts differ; native counts are never assumed')
 terminal=re.findall(r'^\{"status": "passed_compiled_environment_audit", "counts": .*\}\s*$',text,re.M)
 need(len(terminal)==1 and strict(terminal[0].encode())['counts']==counts,'proof log does not bind one actual terminal audit result')
 private=runner['resolved_private_helpers'](report,cfg)
 need(len(private)==3 and private==er.get('resolved_private_source_helpers'),'actual private helper records differ from runner receipt')
 identities=identity_records(report,contract,canonical)
 need(identities==er.get('program_identity_inclusions'),'actual program identity records differ from runner receipt')
 helper=blob(root,COMMIT,'formal/ResearchAudit/EnvironmentAudit.lean')
 need(cfg['helper_sha256']==sha(helper),'helper source mismatch')
 need(member(ep,'helper-source/ResearchAudit/EnvironmentAudit.lean')==helper,'delivered staged helper source differs')
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
  need(not member(ep,filelabel+'.stderr'),'unexpected compiler/helper/audit stderr')
 need(not member(ep,'environment-audit.stderr')and not member(ep,'helper-compile.stdout')and not member(ep,'helper-compile.stderr'),'unexpected helper/audit diagnostics')
 workspace=PurePosixPath(cfg['working_directory']).parent
 need(member(ep,'compiler-version.stdout').decode().strip()==cfg['compiler_version']==er['compiler_version'],'actual compiler version differs')
 need('Lean (version 4.34.1,'in cfg['compiler_version'] and 'commit 5045d0056413266e57c625dcd7c365b10e377c52'in cfg['compiler_version'],'actual compiler is not the pinned Lean release')
 need(str(PurePosixPath(member(ep,'compiler-prefix.stdout').decode().strip())/'lib/lean')==cfg['builtin_library'],'compiler sysroot differs')
 for label,pin in cfg['pins'].items():
  need(cb['files'].get(pin['path'])==pin['sha256'],'required pin omitted/changed in snapshots')
  if label.startswith('source:'):
   module=label.split(':',1)[1];relative=module.replace('.','/')+'.lean'
   actual=blob(root,COMMIT,'formal/'+relative)if module=='Math115'or module.startswith('Math115.')else blob(root/'.upstream/openai-math',UPSTREAM,'lean/'+relative)
   need(sha(actual)==pin['sha256'],'immutable source pin differs: '+module)
  elif label.startswith(('configuration:','integration-contract:')):need(sha(blob(root,COMMIT,label.split(':',1)[1]))==pin['sha256'],'immutable configuration/contract pin differs')
  elif label.startswith('built-object:'):need(re.fullmatch('[0-9a-f]{64}',pin['sha256']) is not None,'invalid built-object digest')
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
 for module in cfg['expected_modules']:
  need(closure[module]==cfg['pins']['built-object:'+module],'actual imported project object differs from built-object pin')
 validate_compile_transition(cb,ab,helper_library)
 for field in ['published_checkpoint','published_selection','published_intake']:
  authority=contract[field];need(sha(blob(root,COMMIT,authority['path']))==authority['sha256'],'published integration authority differs')
 for module in contract['modules']:
  need(sha(blob(root,COMMIT,module['source']))==module['sha256'],'integrated proof source changed')
  need(cfg['pins']['source:'+module['module']]['sha256']==module['sha256'],'integrated source pin differs')
 for relative in ['formal/default-audit-contract.json',*[contract[f]['path'] for f in ['published_checkpoint','published_selection','published_intake']]]:
  label='integration-contract:'+relative;need(label in cfg['pins'] and cfg['pins'][label]['sha256']==sha(blob(root,COMMIT,relative)),'contract/authority not source pinned')
 # Stage publication-safe payload only after every success gate. Original bytes kept.
 out.mkdir(parents=True,exist_ok=False);(out/'environment-audit').mkdir()
 archive_map={};excluded=[];unique={};unselected={}
 for key,data in members.items():
  if not(key.startswith(vp+'/')or key.startswith(ep+'/')or key==config_key):
   unselected[key]={'sha256':sha(data),'bytes':len(data),'reason':'Outside explicitly selected prefixes; original ZIP remains authenticated private evidence.'};continue
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
 writejson(out/'archive-member-map.json',{'members':archive_map,'excluded_binaries':excluded,'unselected_members':unselected,'complete_zip_file_members':len(members),'method':'Original hosted-runner bytes, gzip empty filename/mtime0/level9; identical member payloads share one public file. Every ZIP file is mapped or excluded with exact bytes/digest. No redaction or truncation.'})
 result={'schema_version':1,'status':'passed','repository_commit':COMMIT,'run_url':url,'run_id':rid,'run_attempt':attempt,'job_id':job['id'],'job_url':job['html_url'],
  'scope':'Exact-commit hosted Linux focused1511 named replay and fresh compiled-environment audit. No separate standalone named audits, Comparator or new runtime result.',
  'audit_declaration_count':1511,'audited_declarations':records,'allowed_axioms':sorted(ALLOWED),'source_sha256':{p:h for p,h in env['source_sha256'].items()if p!='claims.json'},
  'observed_claim_ledger_sha256':env['source_sha256']['claims.json'],
  'upstream_revision':UPSTREAM,'environment_audit_counts':counts,'headline_dependency_closure_counts':{h['name']:len(h['closure'])for h in report['headlines']},
  'artifact_provider_digest':artifact['digest'],'artifact_id':artifact['id'],'artifact_name':artifact['name'],
  'source_metadata_sha256':{k:sha(p.read_bytes())for k,p in [('run',a.run_metadata),('job',a.job_metadata),('artifact',a.artifact_metadata)]},
  'compiled_environment_receipt_original_sha256':sha(member(ep,'receipt.json')),'packager_sha256':sha(Path(__file__).read_bytes()),
  'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'binary_helper_objects_bound_but_not_published':excluded,
  'import_binding_boundary':'Complete recorded module path/name/digest bindings matched eligible ordered search roots and recorded frozen snapshots. The hosted runner performed filesystem resolution; no unavailable-filesystem reenactment is asserted.',
  'trust_boundary':er['platform_loader_boundary'],'independent_review':'Pending root and independent actual-artifact readback.'}
 result['scope']=result['scope'].replace('focused1511','focused 1511')
 result['ordinary_build_mode']='--serial'
 result['known_standalone_inclusions']=EXPECTED_STANDALONE
 result['standalone_named_replay_performed']=False
 result['resolved_private_source_helpers']=private
 result['program_identity_inclusions']=identities
 result['integration_contract_sha256']=sha(blob(root,COMMIT,'formal/default-audit-contract.json'))
 result['workflow_sha256']=WORKFLOW_SHA
 result['default_source_module_count']=EXPECTED_MODULES
 save_provider_sidecars(out,run,job,artifact)
 (out/'packager.py').write_bytes(Path(__file__).read_bytes())
 result['artifacts_sha256']={p.relative_to(out).as_posix():sha(p.read_bytes())for p in sorted(out.rglob('*'))if p.is_file()}
 writejson(out/'verification.json',result)
 return{'status':'passed_private_package_pending_review','output_files':len(result['artifacts_sha256'])+1,'named_audits':1511,'environment_counts':counts}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,default=Path.cwd());p.add_argument('--commit',required=True)
 for x in ['run-metadata','job-metadata','artifact-metadata','artifact-zip']:p.add_argument('--'+x,type=Path,required=True)
 p.add_argument('--verification-prefix',required=True);p.add_argument('--audit-prefix',help='explicit completed audit attempt prefix; required for a successful provider run');p.add_argument('--output',type=Path,required=True)
 a=p.parse_args()
 try:result=package(a)
 except Exception as error:
  # A failed/pending or malformed artifact cannot produce passed verification.json.
  print('Final hosted packaging rejected: '+str(error),file=sys.stderr);return 1
 print(json.dumps(result,indent=2));return 1 if result['status'].startswith('not_verified') else 0
if __name__=='__main__':raise SystemExit(main())
