from pathlib import Path
import argparse,json,os,subprocess,hashlib,time
ap=argparse.ArgumentParser();ap.add_argument('--repo',required=True);ap.add_argument('--base-objects',required=True);ap.add_argument('--output',required=True);a=ap.parse_args()
packet=Path(__file__).resolve().parent;repo=Path(a.repo).resolve();base=Path(a.base_objects).resolve();output=Path(a.output).resolve();objects=output/'objects';objects.mkdir(parents=True,exist_ok=True)
for p in base.rglob('*.olean'):
 dst=objects/p.relative_to(base)
 if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(p.resolve())
lean=repo/'.tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
search=[objects,*sorted((repo/'formal/.lake/packages').glob('*/.lake/build/lib/lean'))]
env={**os.environ,'LEAN_PATH':os.pathsep.join(map(str,search)),'LEAN_NUM_THREADS':'2'}
records=[]
for name in ['Seams','PublicBridge','FinalBinding','FixedMachineTheorem','Audit']:
 module='CompleteDraw.'+name;source=packet/'source/CompleteDraw'/(name+'.lean');obj=objects/'CompleteDraw'/(name+'.olean');obj.parent.mkdir(exist_ok=True)
 assert not obj.is_symlink(),'Output prefix must not contain imported CompleteDraw modules'
 start=time.monotonic();p=subprocess.run([str(lean),'-j2','-M8192','-DautoImplicit=false','--root='+str(packet/'source'),'-o',str(obj),str(source)],env=env,capture_output=True,text=True,timeout=180)
 (output/(name+'.stdout.txt')).write_text(p.stdout);(output/(name+'.stderr.txt')).write_text(p.stderr)
 rec={'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'returncode':p.returncode,'seconds':time.monotonic()-start}
 if p.returncode==0:rec['olean_sha256']=hashlib.sha256(obj.read_bytes()).hexdigest()
 records.append(rec);(output/'compilation.json').write_text(json.dumps(records,indent=2)+'\n');print(module,p.returncode,flush=True)
 if p.returncode:raise SystemExit(p.returncode)
