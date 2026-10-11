#!/usr/bin/env python3
"""Trusted read-only runtime freeze from the authenticated retained image.
No Lean/Lake/compiler/checker is launched here; the separately logged original
preflight is the wrapper's previous phase. SHA is emitted outside JSON parsing.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess

RUNNER_SHA = "136f13a56001c6f4f31e73a7133193cc946be32de3cc4970edc9fc06c2a65d38"
def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--runner',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--native-audit',type=Path,required=True)
    p.add_argument('--lake-config-provenance',type=Path,required=True);p.add_argument('--lake-config-provenance-sha256',required=True)
    a=p.parse_args();root=a.root.resolve()
    import hashlib
    digest=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
    if digest(a.runner)!=RUNNER_SHA:raise RuntimeError('Reviewed runner body changed')
    spec=importlib.util.spec_from_file_location('c11_trusted_runner',a.runner);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    serial,parser=m.load_assets();freeze=m.read(a.runner.parent/'source-freeze.json')
    m.require(digest(a.runner.parent/'source-freeze.json')==m.SOURCE_SHA,'Frozen sampler sources changed')
    m.require(not a.output.exists() and a.output.resolve().is_relative_to(root/'.tools/linux-verification'),'Need fresh trusted runtime output')
    m.require(not any(os.environ.get(k) for k in m.OVERRIDES),'Ambient override')
    packages={x['name']:x for x in m.read(root/'formal/lake-manifest.json')['packages']}
    cache_roots=sorted([m.PREFIX+'/lib/lean',*['formal/.lake/packages/'+n+'/.lake/build/lib/lean' for n in packages]])
    config_name=str(a.lake_config_provenance.resolve().relative_to(root));config_file=m.relative(root,config_name)
    m.require(config_file.is_relative_to(root/'.tools/linux-verification') and m.SHA.fullmatch(a.lake_config_provenance_sha256) and m.sha(config_file)==a.lake_config_provenance_sha256,'Independent configuration provenance SHA/path differs')
    config_provenance=m.read(config_file)
    configuration=m.indexed_configuration_inventory(root,config_provenance)
    config_stats=m.configuration_stats(root,configuration)
    m.no_hidden_objects(root,cache_roots,configuration_files=configuration)
    provenance=m.read(m.relative(root,m.PROVENANCE));serial.validate_provenance(provenance,parser.TOOLCHAIN)
    mandatory=[m.PROVENANCE,*(m.PREFIX+'/bin/'+n for n in ('lean','leanir','lake')),'.tools/elan/bin/elan','.tools/elan/bin/lake',*('.tools/verification-bin/'+n for n in provenance['binary_sha256'])]
    tools,aliases=m.freeze_runtime_tools(root,mandatory)
    system={}
    for name in m.SYSTEM_COMMANDS:
        path=shutil.which(name);m.require(path is not None,'Missing system command: '+name);path=Path(path).resolve()
        system[name]={'path':str(path),'sha256':m.sha(path)}
    tracked={}
    for name in packages:
        package=root/'formal/.lake/packages'/name
        r=subprocess.run(['/usr/bin/git','-C',str(package),'ls-files'],text=True,capture_output=True,timeout=30)
        m.require(r.returncode==0,'Cannot inspect pinned package source');tracked[name]=set(r.stdout.splitlines())
    resolution={}
    for name in freeze['external_imports']:
        rel=name.replace('.','/');candidates=[]
        builtin=root/m.PREFIX/'lib/lean'/(rel+'.olean')
        if builtin.is_file():candidates.append({'olean':str(builtin.relative_to(root)),'source':None})
        for owner,files in tracked.items():
            if rel+'.lean' in files:
                package='formal/.lake/packages/'+owner
                candidates.append({'olean':package+'/.lake/build/lib/lean/'+rel+'.olean','source':package+'/'+rel+'.lean'})
        m.require(len(candidates)==1,'Ambiguous/missing external import');resolution[name]=candidates[0]
    native=m.read(a.native_audit)
    runtime={'schema_version':1,'status':'authenticated_linux_runtime_for_strict_sampler','source_freeze_sha256':m.SOURCE_SHA,'trusted_files_sha256':tools,'trusted_tool_aliases':aliases,'system_executables':system,'trusted_cache_roots':cache_roots,'trusted_cache_files_sha256':m.cache_inventory(root,cache_roots),'lake_configuration_artifacts_sha256':configuration,'external_import_resolution':resolution,'entrypoint_native_audit':native}
    runtime.update(lake_configuration_provenance=config_provenance,lake_configuration_provenance_binding={'path':config_name,'sha256':a.lake_config_provenance_sha256},lake_configuration_artifacts_stat=config_stats)
    # Complete independent runner admission re-derives graph, pins, resolution,
    # full cache and configuration identities; collection alone is insufficient.
    m.admit(root,freeze,runtime,serial,parser)
    a.output.write_text(json.dumps(runtime,indent=2,sort_keys=True)+'\n')
    print('MATH115_C11_RUNTIME_FREEZE_SHA256='+m.sha(a.output),flush=True)
if __name__=='__main__':main()
