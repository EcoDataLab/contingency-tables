#!/usr/bin/env python3
"""Focused replay using a pinned compiler and an existing original-import baseline.
Compiles only this endpoint's mapped/included custom proof closure. Does not
build an original dependency, default target, or strict audit. Use new output.
"""
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path
PACKET=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--base-objects',type=Path);args=ap.parse_args()
 repo=args.repo.resolve();out=args.output.resolve();base=(args.base_objects or repo/'formal/.lake/build/lib/lean').resolve();lean=repo/'.tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
 if out.exists():raise SystemExit('Use a new output directory.')
 if not base.is_dir() or not lean.is_file():raise SystemExit('Existing pinned compiler/original imports required first.')
 if (repo/'formal/lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise SystemExit('Toolchain pin differs.')
 imports=json.loads((PACKET/'imports.json').read_text());by={r['module']:r for r in imports['modules']}
 for r in by.values():
  src=PACKET/r['packet_source'] if r['role']=='new-source-included-unchanged' else repo/r['repository_source']
  if sha(src)!=r['source_sha256']:raise SystemExit('Source differs: '+r['module'])
 for r in json.loads((PACKET/'original-source-bindings.json').read_text()):
  if sha(repo/r['path'])!=r['sha256']:raise SystemExit('Original source differs: '+r['path'])
 out.mkdir(parents=True);objects=out/'objects';objects.mkdir();sources=out/'source';sources.mkdir()
 for p in base.rglob('*.olean'):
  d=objects/p.relative_to(base);d.parent.mkdir(parents=True,exist_ok=True);d.symlink_to(p.resolve())
 packages=sorted((repo/'formal/.lake/packages').glob('*/.lake/build/lib/lean'));env={**os.environ,'LEAN_PATH':os.pathsep.join(map(str,[objects,*packages])),'LEAN_NUM_THREADS':'2'};records=[]
 for module in imports['module_order']:
  r=by[module];src=PACKET/r['packet_source'] if r['role']=='new-source-included-unchanged' else repo/r['repository_source'];rel=Path(module.replace('.','/'));target=objects/rel.with_suffix('.olean');saved=sources/rel.with_suffix('.lean');saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(src.read_bytes());target.parent.mkdir(parents=True,exist_ok=True)
  if target.is_symlink():target.unlink()
  command=[str(lean),'-j2','-M8192','-DautoImplicit=false','--root='+str(sources),'-o',str(target),str(saved)];start=time.monotonic()
  try:p=subprocess.run(command,env=env,cwd=repo,capture_output=True,text=True,timeout=300)
  except subprocess.TimeoutExpired as e:
   (out/(module+'.stdout.txt')).write_bytes(e.stdout or b'');(out/(module+'.stderr.txt')).write_bytes(e.stderr or b'');raise
  (out/(module+'.stdout.txt')).write_text(p.stdout);(out/(module+'.stderr.txt')).write_text(p.stderr);record={'module':module,'source_sha256':sha(saved),'compiler_sha256':sha(lean),'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3)}
  if not p.returncode:record['olean_sha256']=sha(target)
  records.append(record);(out/'compilation.json').write_text(json.dumps(records,indent=2)+'\n')
  if p.returncode:raise SystemExit('Compile failed; full streams retained: '+module)
 audit=(out/'UnitRuntime.UnitPackedTrialAudit.stdout.txt').read_text();axes=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S);allowed={'propext','Classical.choice','Quot.sound'}
 if len(axes)!=6 or any(not set(x.strip() for x in a.split(','))<=allowed for _,a in axes):raise SystemExit('Focused axiom readback differs.')
 (out/'verification.json').write_text(json.dumps({'status':'passed-focused-replay','degree_decimal':'272019144737569436269241336269647035188617216','scope':'Custom proof closure and six focused axiom/type readbacks; existing original baseline trusted; no default build, strict audit or exhaustive environment audit.'},indent=2)+'\n')
 print('Focused exact unit endpoint replay passed.')
if __name__=='__main__':main()
