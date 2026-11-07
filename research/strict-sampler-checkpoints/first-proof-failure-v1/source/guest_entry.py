#!/usr/bin/env python3
"""One fixed trusted guest pipeline, with bounded owned child waits and logs."""
import argparse
import base64
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import tarfile
import time

ROOT=Path('/home/verifier/checking')
INPUT=ROOT/'.tools/linux-verification/checkpoint11-inputs'
EVIDENCE=ROOT/'.tools/linux-verification/checkpoint11-evidence'
RUNNER=ROOT/'.tools/linux-verification/checkpoint11-runner/strict_sampler.py'
CAPS={'install':600,'preflight':300,'authenticate':5400,'proof':8100,'collect':600}
def sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def proof_progress(previous):
    path=EVIDENCE/'proof-output/receipt.json'
    try:
        data=json.loads(path.read_text());commands=data.get('commands',[])
        if not isinstance(commands,list) or len(commands)>1362:return previous
        last=commands[-1] if commands else {}
        row={'completed_modules':sum(x.get('status')=='passed' and str(x.get('stage','')).endswith('_module_build') for x in commands),
             'completed_stages':sum(x.get('status')=='passed' for x in commands),'last_stage':str(last.get('stage',''))[:256],
             'last_status':last.get('status','none')}
        if row==previous:return previous
        row['observed_unix']=time.time()
        with (EVIDENCE/'proof-progress.jsonl').open('a') as stream:stream.write(json.dumps(row,sort_keys=True)+'\n')
        print('MATH115_C11_PROOF_PROGRESS='+json.dumps(row,sort_keys=True),flush=True)
        return {k:v for k,v in row.items() if k!='observed_unix'}
    except (OSError,ValueError,TypeError,AttributeError):return previous
def phase(name,argv,records):
    print('MATH115_C11_STAGE='+name,flush=True)
    row={'stage':name,'argv':argv,'started_unix':time.time(),'cap_seconds':CAPS[name],'status':'running'};records.append(row)
    out,err=EVIDENCE/(name+'.stdout.log'),EVIDENCE/(name+'.stderr.log')
    with out.open('wb') as stdout,err.open('wb') as stderr:
        child=subprocess.Popen(argv,stdout=stdout,stderr=stderr,start_new_session=True)
        row['owned_child_pid']=child.pid
        try:
            if name=='proof':
                deadline=time.monotonic()+CAPS[name];previous=None
                while True:
                    remaining=deadline-time.monotonic()
                    if remaining<=0:raise subprocess.TimeoutExpired(argv,CAPS[name])
                    try:row['returncode']=child.wait(timeout=min(5,remaining));break
                    except subprocess.TimeoutExpired:previous=proof_progress(previous)
                proof_progress(previous)
            else:row['returncode']=child.wait(timeout=CAPS[name])
        except BaseException:
            if child.poll() is None:
                os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=10)
                except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=5)
            row['status']='timed_out_or_interrupted';raise
    row.update(elapsed_seconds=time.time()-row['started_unix'],stdout_sha256=sha(out),stderr_sha256=sha(err),status='passed' if row['returncode']==0 else 'failed')
    (EVIDENCE/'phases.json').write_text(json.dumps(records,indent=2,sort_keys=True)+'\n')
    require(row['returncode']==0,name+' failed')
def collect():
    print('MATH115_C11_STAGE=collect',flush=True)
    archive=EVIDENCE.parent/'checkpoint11-evidence.tar.gz'
    files=[x for x in sorted(EVIDENCE.rglob('*')) if x.is_file()]
    require(sum(x.stat().st_size for x in files)<=64*1024**2,'Raw evidence exceeds bounded collection budget')
    with tarfile.open(archive,'w:gz') as tar:
        for path in files:tar.add(path,arcname=str(path.relative_to(EVIDENCE)),recursive=False)
    print('MATH115_C11_EVIDENCE_MANIFEST='+json.dumps({'tar_gz_sha256':sha(archive),'files':{str(x.relative_to(EVIDENCE)):sha(x) for x in files}},sort_keys=True),flush=True)
    print('MATH115_C11_EVIDENCE_B64_BEGIN',flush=True)
    with archive.open('rb') as stream:
        while raw:=stream.read(57*1024):print(base64.encodebytes(raw).decode(),end='',flush=True)
    print('MATH115_C11_EVIDENCE_B64_END',flush=True)
def main():
    p=argparse.ArgumentParser();p.add_argument('--installation-manifest-sha256',required=True);p.add_argument('--lake-config-provenance-sha256',required=True);p.add_argument('--unused-cache-policy-sha256',required=True);a=p.parse_args()
    require(os.getuid()!=0 and Path('/var/lib/math115-c11-provision.ready').is_file(),'Normal non-root prepared session required')
    require(not EVIDENCE.exists(),'Existing evidence; no duplicate/resume')
    EVIDENCE.mkdir(parents=True)
    records=[];result=1;collection=1
    try:
        mem={k:int(v.split()[0])*1024 for k,v in (line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())}
        import shutil
        resource={'cpu_count':os.cpu_count(),'mem_total_bytes':mem['MemTotal'],'mem_available_bytes':mem['MemAvailable'],'swap_total_bytes':mem['SwapTotal'],'disk_free_bytes':shutil.disk_usage(ROOT).free}
        resource['kernel_release']=os.uname().release
        resource['kernel_config_sha256']=sha(Path('/boot')/('config-'+os.uname().release))
        version=subprocess.run(['systemd-run','--version'],text=True,capture_output=True,timeout=10)
        require(version.returncode==0,'Cannot measure systemd version')
        resource['systemd_version_output']=version.stdout
        (EVIDENCE/'resources.json').write_text(json.dumps(resource,indent=2,sort_keys=True)+'\n')
        require(resource['cpu_count']==1 and resource['mem_total_bytes']>=9*1024**3 and resource['mem_available_bytes']>=8*1024**3 and resource['swap_total_bytes']==0 and resource['disk_free_bytes']>=60*1024**3,'Fresh guest admission failed')
        phase('install',['/usr/bin/python3','-I','/home/verifier/checkpoint11-install.py','--root',str(ROOT),'--archive',str(INPUT/'sources.tar.gz'),'--manifest',str(INPUT/'installation-manifest.json'),'--manifest-sha256',a.installation_manifest_sha256,'--staging',str(INPUT/'installed')],records)
        phase('preflight',['bash','-c','source "$1" preflight; configure_paths; strict_landrun_probe','c11-preflight',str(ROOT/'scripts/bootstrap_comparator.sh')],records)
        native=ROOT/'.tools/linux-verification/strict-sampler-inputs/native-audit.json'
        phase('authenticate',['/usr/bin/python3','-I','/home/verifier/checkpoint11-authenticate.py','--root',str(ROOT),'--runner',str(RUNNER),'--output',str(EVIDENCE/'runtime-freeze.json'),'--native-audit',str(native),'--lake-config-provenance',str(ROOT/'.tools/linux-verification/strict-sampler-inputs/lake-config-provenance.json'),'--lake-config-provenance-sha256',a.lake_config_provenance_sha256,'--unused-cache-policy',str(ROOT/'.tools/linux-verification/strict-sampler-inputs/unused-cache-policy.json'),'--unused-cache-policy-sha256',a.unused_cache_policy_sha256,'--diagnostics'],records)
        versioned=ROOT/'.tools/linux-verification/anchored-guard-v2'
        for name in ('source-freeze.json',*[str(Path('tested-runtime')/n) for n in ('strict_serial_check.py','no_rebuild_landrun.py','build_lean_serial.py')]):
            destination=versioned/name;destination.parent.mkdir(parents=True,exist_ok=True);require(not destination.exists(),'Candidate asset already exists');shutil.copyfile(RUNNER.parent/name,destination);require(sha(destination)==sha(RUNNER.parent/name),'Candidate asset copy changed')
        runtime_sha=sha(EVIDENCE/'runtime-freeze.json')
        print('MATH115_C11_RUNTIME_FREEZE_SHA256='+runtime_sha,flush=True)
        spec=importlib.util.spec_from_file_location('c11_runner_audit_guard',RUNNER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
        m.validate_entrypoint_audit(m.read(RUNNER.parent/'source-freeze.json'),m.read(native))
        common=['/usr/bin/python3','-I',str(RUNNER),'--root',str(ROOT),'--runtime-freeze',str(EVIDENCE/'runtime-freeze.json'),'--runtime-freeze-sha256',runtime_sha]
        phase('proof',['/usr/bin/python3','-I',str(versioned/'strict_sampler.py'),'--root',str(ROOT),'--runtime-freeze',str(EVIDENCE/'runtime-freeze.json'),'--runtime-freeze-sha256',runtime_sha,'--execute','--wall-seconds','7200','--output',str(EVIDENCE/'proof-output')],records)
        proof=json.loads((EVIDENCE/'proof-output/receipt.json').read_text())
        require(proof['status']=='revised_sampler_comparison_passed' and len(proof['commands'])==1362 and all(x['status']=='passed' for x in proof['commands']),'Complete verified historical closure/comparison receipt required')
        (EVIDENCE/'proof-result.json').write_text(json.dumps({'status':'historical_retained_sampler_full_comparison_passed','module_count':679,'proof_commands':1362,'proof_deadline_seconds':7200,'proof_receipt_sha256':sha(EVIDENCE/'proof-output/receipt.json'),'runtime_freeze_sha256':runtime_sha,'historical_source_freeze_sha256':'2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd','source_scope':'historical retained679module sampler closure, excludes e40c471 new research modules','candidate_guard':'anchored-selected-cache-v2','proof_compilation_executed':True,'comparator_executed':True,'default_kernel_replay_executed':True,'guest_vcpus':1,'guest_ram_mib':10240},indent=2)+'\n')
        result=0
    except BaseException as error:
        (EVIDENCE/'failure.json').write_text(json.dumps({'error':str(error),'bounded_proof_attempt':True,'full_strict_completed':False},indent=2)+'\n')
    finally:
        (EVIDENCE/'phases.json').write_text(json.dumps(records,indent=2,sort_keys=True)+'\n')
        try:collect();collection=0
        except BaseException as error:print('MATH115_C11_COLLECTION_ERROR='+repr(error),flush=True)
        subprocess.run(['/usr/bin/sync'],timeout=30)
        print('MATH115_C11_EVIDENCE_COLLECTION_RESULT='+str(collection),flush=True)
        print('MATH115_C11_CHECK_RESULT='+str(result),flush=True)
    return result if collection==0 else 1
if __name__=='__main__':raise SystemExit(main())
