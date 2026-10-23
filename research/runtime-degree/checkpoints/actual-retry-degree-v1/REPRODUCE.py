#!/usr/bin/env python3
"""Prepared focused reproduction after the pinned ordinary baseline build.

No default-target or dependency rebuild is performed by this script. Existing
baseline/import objects are trusted. Use one new output prefix per execution.
"""
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path
PACKET=Path(__file__).resolve().parent
MODULES=['ResearchBounds.TreeDegreeBounds','ResearchBounds.TreeArithmeticDegree',
 'PrinterRuntime.LinearCollections','InitialRuntime.GreedyDegree',
 'DivisionRuntime.Degree','RetryRuntime.ListSeed','RetryRuntime.ListRepeatDegree',
 'RetryRuntime.WordChunkDegree','RetryRuntime.RangeDegree','RetryRuntime.MapWithDegree',
 'RetryRuntime.WordChunksDegree','RetryRuntime.ActualRetryWordsDegree']
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repo',type=Path,required=True)
 ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--base-objects',type=Path)
 args=ap.parse_args();repo=args.repo.resolve();output=args.output.resolve()
 if output.exists():raise SystemExit('Output directory must be new.')
 lean=repo/'.tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
 baseline=(args.base_objects or repo/'formal/.lake/build/lib/lean').resolve()
 if not lean.is_file() or not baseline.is_dir():raise SystemExit('Pinned compiler and ordinary baseline imports must exist first.')
 if (repo/'formal/lean-toolchain').read_text().strip()!='leanprover/lean4:v4.34.1':raise SystemExit('Toolchain differs from recorded pin.')
 original=json.loads((PACKET/'original-program-source-bindings.json').read_text())
 for r in original:
  rel=r['repository_source'].replace('upstream-pinned-source/','.upstream/openai-math/lean/')
  if sha(repo/rel)!=r['source_sha256']:raise SystemExit('Original program source differs: '+r['module'])
 for r in json.loads((PACKET/'manifest.json').read_text())['files']:
  if sha(PACKET/r['path'])!=r['sha256']:raise SystemExit('Packet file differs: '+r['path'])
 output.mkdir(parents=True);objects=output/'objects';objects.mkdir()
 for p in baseline.rglob('*'):
  if p.is_file():
   dest=objects/p.relative_to(baseline);dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(p.resolve())
 packages=sorted((repo/'formal/.lake/packages').glob('*/.lake/build/lib/lean'))
 env={**os.environ,'LEAN_PATH':os.pathsep.join(map(str,[objects,*packages])),'LEAN_NUM_THREADS':'2'}
 records=[]
 def run(label,source,target=None):
  source_root=PACKET/'source' if source.is_relative_to(PACKET/'source') else PACKET
  cmd=[str(lean),'-j2','-M8192','-DautoImplicit=false','--root='+str(source_root)]
  if target:cmd+=['-o',str(target)]
  cmd+=[str(source)];before=sha(source);start=time.monotonic()
  try:p=subprocess.run(cmd,env=env,cwd=repo,capture_output=True,text=True,timeout=600)
  except subprocess.TimeoutExpired as e:
   (output/(label+'.stdout.txt')).write_bytes(e.stdout or b'');(output/(label+'.stderr.txt')).write_bytes(e.stderr or b'')
   records.append({'module_or_driver':label,'source_sha256':before,'timeout':True,'seconds':round(time.monotonic()-start,3)})
   (output/'compilation.json').write_text(json.dumps(records,indent=2)+'\n');raise
  (output/(label+'.stdout.txt')).write_text(p.stdout);(output/(label+'.stderr.txt')).write_text(p.stderr)
  r={'module_or_driver':label,'source_sha256':before,'source_unchanged':sha(source)==before,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'compiler_sha256':sha(lean)}
  if not p.returncode and target:r['olean_sha256']=sha(target)
  records.append(r);(output/'compilation.json').write_text(json.dumps(records,indent=2)+'\n')
  if p.returncode or not r['source_unchanged']:raise SystemExit('Compile/check failed; complete streams retained: '+label)
  return p.stdout
 for module in MODULES:
  relative=module.replace('.','/');target=objects/(relative+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  if target.is_symlink():target.unlink()
  run(module,PACKET/'source'/(relative+'.lean'),target)
 for label,driver,count in [('RetryAudit',PACKET/'RetryAudit.lean',25),('DivisionAudit',PACKET/'source/DivisionRuntime/Audit.lean',6)]:
  stdout=run(label,driver);reports=[]
  for name,axes in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",stdout):reports.append((name,{a.strip() for a in axes.split(',') if a.strip()}))
  for name in re.findall(r"'([^']+)' does not depend on any axioms",stdout):reports.append((name,set()))
  requested=re.findall(r'^#print axioms (\S+)',driver.read_text(),re.M)
  if len(reports)!=count or len(requested)!=count or set(requested)!={n for n,_ in reports} or len({n for n,_ in reports})!=count or any(not a<=STANDARD for _,a in reports):raise SystemExit('Named axiom reports differ: '+label)
 (output/'verification.json').write_text(json.dumps({'status':'passed','modules':MODULES,'retry_reports':25,'division_reports':6,'scope':'Fresh focused candidate compilation and named transitive axiom/type checks using trusted pinned compiler and existing baseline imports; no exhaustive environment audit/default build/strict replay.'},indent=2)+'\n')
 print('Focused compilation and both named audits passed.')
if __name__=='__main__':main()
