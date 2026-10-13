"""Focused existing-auditor receipt for the final four defining modules."""
from pathlib import Path
import os, json, gzip, hashlib, subprocess, time

root=Path.cwd();work=Path(__file__).resolve().parent
packet=work.parent/'complete-draw';baseline=root/'.local/further-gap/public-aggregate-defect-trace-v1/objects'
lean=root/'.tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['CompleteDraw.Seams','CompleteDraw.PublicBridge','CompleteDraw.FinalBinding','CompleteDraw.FixedMachineTheorem']
heads=['Math115.CompleteDrawNext.explicitPublicDegree','Math115.CompleteDrawNext.typed_actual_publicDraw',
       'Math115.CompleteDrawNext.machineTime_public_explicit_degree',
       'Math115.CompleteDrawNext.fixedMachineBoundedSampling_explicit_degree']
compilation=[]
for module in modules:
    source=packet/'source'/Path(module.replace('.','/')+'.lean')
    obj=packet/'objects'/Path(module.replace('.','/')+'.olean')
    original=packet/(module.replace('.','_')+'.compilation.json')
    r=json.loads(original.read_text())
    assert r['returncode']==0 and r['source_sha256']==sha(source) and r['olean_sha256']==sha(obj)
    compilation.append({'module':module,'source':str(source.relative_to(root)),
        'source_sha256':sha(source),'returncode':0,'olean_sha256':sha(obj),
        'status':'reused_frozen_defining_compilation','fresh_build':False,
        'original_receipt':str(original.relative_to(root)),'original_receipt_sha256':sha(original)})
last=json.loads((packet/'CompleteDraw_FixedMachineTheorem.compilation.json').read_text())
search=list(dict.fromkeys([packet/'objects',baseline,*[root/p for p in last['lean_path']]]))
env={**os.environ,'LEAN_PATH':os.pathsep.join(map(str,search)),'LEAN_NUM_THREADS':'2'}
driver=work/'EnvironmentAudit.lean'
driver.write_text(''.join('import '+m+'\n' for m in modules)+
    'import ResearchAudit.EnvironmentAudit\n#environment_audit prefixes [] modules ['+
    ', '.join(modules)+'] headlines ['+', '.join(heads)+']\n')
start=time.monotonic()
p=subprocess.run([str(lean),'-j2','-M8192','-DautoImplicit=false',str(driver)],env=env,
                 text=True,capture_output=True,timeout=600)
(work/'audit.stderr.txt').write_text(p.stderr)
(work/'audit.stdout.json.gz').write_bytes(gzip.compress(p.stdout.encode(),mtime=0))
if p.returncode:raise SystemExit(p.stdout+'\n'+p.stderr)
a=json.loads(p.stdout)
assert a['modules']==modules and a['prefixes']==[]
assert all(not d['nonstandard_axioms'] for d in a['declarations'])
for h in a['headlines']:
    assert [d['name'] for d in h['declarations']]==h['closure']
    assert all(not d['nonstandard_axioms'] for d in h['declarations'])
objects={}
for module in a['imported_modules']:
    rel=Path(module.replace('.','/')+'.olean')
    found=next((prefix/rel for prefix in [*search,lean.parent.parent/'lib/lean'] if (prefix/rel).is_file()),None)
    if found is None:raise SystemExit('Missing actual imported object '+module)
    objects[module]=sha(found)
(work/'imported-objects.json.gz').write_bytes(gzip.compress((json.dumps(objects,indent=2)+'\n').encode(),mtime=0))
for r in compilation:
    assert objects[r['module']]==r['olean_sha256']
    assert sha(root/r['source'])==r['source_sha256']
summary={'schema_version':1,'status':'passed','modules':modules,'compilation':compilation,
    'upstream_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
    'compiler_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),
    'compiler_sha256':sha(lean),'audit_file':'audit.stdout.json.gz','audit_sha256':sha(work/'audit.stdout.json.gz'),
    'imported_objects_file':'imported-objects.json.gz','imported_objects_sha256':sha(work/'imported-objects.json.gz'),
    'declaration_count':a['declaration_count'],'theorem_count':a['theorem_count'],
    'headlines':[{'name':h['name'],'closure_size':len(h['closure']),
       'statement':next(d['statement'] for d in h['declarations'] if d['name']==h['name'])} for h in a['headlines']],
    'audit_seconds':round(time.monotonic()-start,3),
    'scope':'Focused compiled-environment audit of four frozen final defining modules, '
            'reusing successful exact compilations and authenticated imports; four full headline closures. '
            'No default rebuild, fresh dependency build, platform portability or strict Comparator replay.'}
(work/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='headlines'},indent=2))
print(json.dumps([{'name':h['name'],'closure_size':h['closure_size']} for h in summary['headlines']],indent=2))
