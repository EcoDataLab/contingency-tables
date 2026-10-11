"""Trusted bounded filesystem facts only; never execute or copy cache objects."""
import hashlib, json, os, stat
from pathlib import Path, PurePosixPath
ROOT='/checking'
PREFIX='.tools/elan/toolchains/leanprover--lean4---v4.34.1'
FREEZE='.tools/linux-verification/checkpoint11-runner/source-freeze.json'
FREEZE_SHA='2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd'
PACKAGES=('Cli','LeanSearchClient','Qq','aesop','batteries','importGraph','mathlib','plausible','proofwidgets')
ROOTS=(PREFIX+'/lib/lean',)+tuple('formal/.lake/packages/'+p+'/.lake/build/lib/lean' for p in PACKAGES)
MAX_KEYSET_ENTRIES=20000
MAX_SCAN_ENTRIES=30000
MAX_REPORT_BYTES=16*1024**2
MAX_HASH_BYTES=256*1024**2
FACETS=('.olean','.olean.private','.olean.server','.ilean','.ir','.o','.bc','.so','.dll','.dylib','.c')
def require(ok,message):
 if not ok:raise RuntimeError(message)
def identity(info):return (info.st_dev,info.st_ino,info.st_mode,info.st_uid,info.st_gid,info.st_size,info.st_mtime_ns,info.st_ctime_ns)
def facts(path):
 try:info=path.lstat()
 except FileNotFoundError:return {'type':'absent'}
 typ='directory' if stat.S_ISDIR(info.st_mode) else 'regular' if stat.S_ISREG(info.st_mode) else 'symlink' if stat.S_ISLNK(info.st_mode) else 'other'
 row={'type':typ,'mode':stat.S_IMODE(info.st_mode),'uid':info.st_uid,'gid':info.st_gid,'bytes':info.st_size,'device':info.st_dev,'inode':info.st_ino,'mtime_ns':info.st_mtime_ns,'ctime_ns':info.st_ctime_ns}
 if typ=='symlink':row['target']=os.readlink(path)
 return row
class Diagnostic:
 def __init__(self,mount):self.mount=Path(mount);self.key_count=0;self.scan_count=0;self.hash_bytes=0
 def path(self,name):
  p=PurePosixPath(ROOT)/name
  require(isinstance(name,str) and not PurePosixPath(name).is_absolute() and '..' not in PurePosixPath(name).parts and '\\' not in name and '\0' not in name,'Unsafe diagnostic relative name')
  return self.mount.joinpath(*p.parts[1:])
 def inspect(self,name):
  path=self.path(name);current=self.mount;components=[];parts=path.relative_to(self.mount).parts
  for i,component in enumerate(parts):
   current=current/component;row={'guest_path':'/'+current.relative_to(self.mount).as_posix(),**facts(current)};components.append(row)
   if i<len(parts)-1 and row['type']!='directory':return {'relative_name':name,'type':'blocked_parent','blocking_component':row,'components':components}
  return {'relative_name':name,**components[-1],'components':components}
 def hash(self,name):
  row=self.inspect(name);require(row['type']=='regular','Hash target not regular/no-follow: '+name);path=self.path(name);before=path.lstat()
  require(self.hash_bytes+before.st_size<=MAX_HASH_BYTES,'Selected object/source hash byte cap');self.hash_bytes+=before.st_size
  h=hashlib.sha256()
  with path.open('rb') as source:
   require(identity(os.fstat(source.fileno()))==identity(before),'Hash source changed at open')
   for block in iter(lambda:source.read(1024*1024),b''):h.update(block)
   require(identity(os.fstat(source.fileno()))==identity(before),'Hash source changed during read')
  require(identity(path.lstat())==identity(before),'Hash source changed after read');row['sha256']=h.hexdigest();return row
 def keyset(self,name,root=None):
  root=self.inspect(name) if root is None else root;root['keyset']=[];root['keyset_complete']=root['type']=='directory'
  if root['type']!='directory':return root
  pending=[self.path(name)]
  while pending:
   parent=pending.pop()
   for child in sorted(parent.iterdir(),key=lambda p:p.name):
    self.key_count+=1;require(self.key_count<=MAX_KEYSET_ENTRIES,'Cache keyset entry cap')
    rel=child.relative_to(self.path(name)).as_posix();require(len(rel.encode())<=1024,'Cache relative name cap');row={'name':rel,**facts(child)};root['keyset'].append(row)
    if row['type']=='directory':pending.append(child)
  root['keyset'].sort(key=lambda r:r['name']);root['keyset_sha256']=hashlib.sha256(json.dumps(root['keyset'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
  root['submitted_namespace_roots']={n:self.inspect(name+'/'+n) for n in ('Math115','OAI','ComparatorChallenges')};return root
 def cold_proof(self):
  report={'bases':[],'artifacts':[],'nonregular_components':[],'scan_complete':True}
  for name in ('formal','.upstream/openai-math/lean','.upstream/openai-math/.lake/build'):
   base=self.inspect(name);report['bases'].append(base)
   if base['type']=='absent' or base.get('blocking_component',{}).get('type')=='absent':continue
   if base['type']!='directory':report['nonregular_components'].append(base);continue
   pending=[self.path(name)]
   while pending:
    parent=pending.pop()
    for path in sorted(parent.iterdir(),key=lambda p:p.name):
     rel=path.relative_to(self.path('')).as_posix()
     if rel=='formal/.lake/packages' or rel.startswith('formal/.lake/packages/'):continue
     self.scan_count+=1;require(self.scan_count<=MAX_SCAN_ENTRIES,'Cold-proof scan entry cap');row={'relative_name':rel,**facts(path)}
     if row['type']=='directory':pending.append(path)
     elif row['type']!='regular':report['nonregular_components'].append(row)
     elif path.name.endswith(FACETS):report['artifacts'].append(row)
  allowed={f'formal/.lake/config/{n}/lakefile.olean' for n in ('0','1','5')}
  report['indexed_configuration_objects']=[r for r in report['artifacts'] if r['relative_name'] in allowed]
  report['submitted_proof_artifacts']=[r for r in report['artifacts'] if r['relative_name'] not in allowed]
  report['scan_complete']=not report['nonregular_components']
  report['submitted_proof_artifact_count']=len(report['submitted_proof_artifacts']);report['scanned_entries']=self.scan_count;return report
 def external(self,names):
  rows=[]
  for name in names:
   require(isinstance(name,str) and all(p and p.replace('_','').isalnum() for p in name.split('.')),'Unsafe frozen external module')
   rel=name.replace('.','/');candidates=[];selected=[]
   for owner,base in [('builtin',PREFIX+'/lib/lean')]+[(p,'formal/.lake/packages/'+p+'/.lake/build/lib/lean') for p in PACKAGES]:
    obj=base+'/'+rel+'.olean';source=None if owner=='builtin' else 'formal/.lake/packages/'+owner+'/'+rel+'.lean'
    row={'owner':owner,'object':self.inspect(obj),'source':self.inspect(source) if source else None};candidates.append(row)
    if (owner=='builtin' and row['object']['type']=='regular') or (source and row['source']['type']=='regular'):selected.append((obj,source))
   row={'module':name,'candidate_facts':candidates,'selection_basis':'raw filesystem source-file/builtin-object presence; no Git tracked-file or runtime admission claim','filesystem_candidate_count':len(selected)}
   if len(selected)==1:
    obj,source=selected[0];objfacts=self.inspect(obj);row['selected_object']=self.hash(obj) if objfacts['type']=='regular' else objfacts
    row['selected_source']=self.hash(source) if source else None
   rows.append(row)
  return rows
def classify_roots(roots):
 symlinks=[];nondirectories=[]
 for row in roots:
  links=[c for c in row['components'] if c['type']=='symlink']
  if links:symlinks.append({'relative_name':row['relative_name'],'blocking_component':links[0]})
  elif row['type']!='directory':nondirectories.append({'relative_name':row['relative_name'],'nofollow_type':row['type'],'blocking_component':row.get('blocking_component')})
 return {'first_relative_path_symlink_rejection':next(iter(symlinks),None),'first_nonsymlink_directory_predicate_failure':next(iter(nondirectories),None)}
def capture(cap):
 report={'scope':'readonly filesystem cache diagnosis; no cache object bytes copied; no Git/config/compiler execution','runtime_admission':False}
 def captured(name):
  row=cap.source(ROOT+'/'+name,'diagnostic_binding');raw=(cap.out/row['raw']).read_bytes();report.setdefault('captured_bindings',{})[name]=row;return raw
 try:
  raw=captured(FREEZE);require(hashlib.sha256(raw).hexdigest()==FREEZE_SHA,'Source-freeze binding differs');freeze=json.loads(raw);require(len(freeze['modules'])==679 and len(freeze['external_imports'])==82,'Frozen module/import counts differ')
  manifest=json.loads(captured('formal/lake-manifest.json'));require(sorted(p['name'] for p in manifest['packages'])==list(PACKAGES),'Expected nine package names differ')
  for name in ('.tools/linux-verification/strict-sampler-inputs/lake-config-provenance.json','.tools/linux-verification/strict-sampler-inputs/native-audit.json','.tools/linux-verification/checker-provenance.json','.tools/linux-verification/checkpoint11-runner/strict_sampler.py'):captured(name)
  d=Diagnostic(cap.mount);report['cache_roots']=[]
  for name in ROOTS:
   row=d.inspect(name);report['cache_roots'].append(row);d.keyset(name,row)
  report.update(classify_roots(report['cache_roots']))
  report['cold_proof']=d.cold_proof();report['external_objects']=d.external(freeze['external_imports'])
  report['submitted_sources']=[d.hash(r['source']) for r in freeze['modules']]
  report['source_hash_mismatches']=[r['source'] for r,observed in zip(freeze['modules'],report['submitted_sources']) if observed['sha256']!=r['sha256']]
  report['tools']=[d.hash(n) if d.inspect(n)['type']=='regular' else d.inspect(n) for n in [PREFIX+'/bin/'+n for n in ('lean','leanir','lake')]+['.tools/verification-bin/'+n for n in ('comparator','lean4export','landrun','landrun-real')]]
  report['cache_keyset_entries']=d.key_count;report['selected_hash_bytes']=d.hash_bytes;report['complete']=True
 except BaseException as error:report['complete']=False;report['diagnostic_error']=type(error).__name__+': '+str(error)
 report['observer_capture_bindings']=cap.rows
 raw=json.dumps(report,indent=2,sort_keys=True).encode();require(len(raw)<=MAX_REPORT_BYTES,'Cache diagnostic report byte cap');(cap.out/'cache-diagnostic.json').write_bytes(raw+b'\n')
 require(report['complete'],'Diagnostic incomplete: '+report.get('diagnostic_error','unknown'));return {'path':'cache-diagnostic.json','sha256':hashlib.sha256(raw+b'\n').hexdigest(),'bytes':len(raw)+1,'complete':True}
