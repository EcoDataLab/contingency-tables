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
import sys

RUNNER_SHA = "4ba0a3c42bee4f511909fc50ad33b00be2a5cc3cabecdd2b54ac08ec7970d1a6"
def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--runner',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--native-audit',type=Path,required=True)
    p.add_argument('--lake-config-provenance',type=Path,required=True);p.add_argument('--lake-config-provenance-sha256',required=True)
    p.add_argument('--unused-cache-policy',type=Path,required=True);p.add_argument('--unused-cache-policy-sha256',required=True)
    p.add_argument('--diagnostics',action='store_true',help='Flushed progress on existing stderr; no verification change')
    a=p.parse_args();root=a.root.resolve()
    if a.diagnostics:print('STRICT_AUTH_PROGRESS='+json.dumps({'stage':'authentication','event':'begin'},sort_keys=True),file=sys.stderr,flush=True)
    import hashlib
    digest=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
    if digest(a.runner)!=RUNNER_SHA:raise RuntimeError('Reviewed runner body changed')
    spec=importlib.util.spec_from_file_location('c11_trusted_runner',a.runner);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    m.enable_diagnostics(a.diagnostics);m.progress('authentication','assets_begin')
    serial,parser=m.load_assets();freeze=m.read(a.runner.parent/'source-freeze.json')
    m.require(digest(a.runner.parent/'source-freeze.json')==m.SOURCE_SHA,'Frozen sampler sources changed')
    m.require(not a.output.exists() and a.output.resolve().is_relative_to(root/'.tools/linux-verification'),'Need fresh trusted runtime output')
    m.require(not any(os.environ.get(k) for k in m.OVERRIDES),'Ambient override')
    packages={x['name']:x for x in m.read(root/'formal/lake-manifest.json')['packages']}
    cache_roots=sorted([m.PREFIX+'/lib/lean',*['formal/.lake/packages/'+n+'/.lake/build/lib/lean' for n in packages]])
    config_name=str(a.lake_config_provenance.resolve().relative_to(root));config_file=m.relative(root,config_name)
    m.require(config_file.is_relative_to(root/'.tools/linux-verification') and m.SHA.fullmatch(a.lake_config_provenance_sha256) and m.sha(config_file)==a.lake_config_provenance_sha256,'Independent configuration provenance SHA/path differs')
    m.progress('authentication','configuration_begin')
    config_provenance=m.read(config_file)
    configuration=m.indexed_configuration_inventory(root,config_provenance)
    config_stats=m.configuration_stats(root,configuration)
    m.progress('authentication','configuration_end')
    m.no_hidden_objects(root,cache_roots,configuration_files=configuration)
    m.progress('authentication','tool_and_system_freeze_begin')
    provenance=m.read(m.relative(root,m.PROVENANCE));serial.validate_provenance(provenance,parser.TOOLCHAIN)
    mandatory=[m.PROVENANCE,*(m.PREFIX+'/bin/'+n for n in ('lean','leanir','lake')),'.tools/elan/bin/elan','.tools/elan/bin/lake',*('.tools/verification-bin/'+n for n in provenance['binary_sha256'])]
    tools,aliases=m.freeze_runtime_tools(root,mandatory)
    system={}
    for name in m.SYSTEM_COMMANDS:
        path=shutil.which(name);m.require(path is not None,'Missing system command: '+name);path=Path(path).resolve()
        system[name]={'path':str(path),'sha256':m.sha(path)}
    m.progress('authentication','tool_and_system_freeze_end')
    tracked={}
    for name in packages:
        m.progress('authentication','tracked_package_begin',package=name)
        package=root/'formal/.lake/packages'/name
        r=subprocess.run(['/usr/bin/git','-C',str(package),'ls-files'],text=True,capture_output=True,timeout=30)
        m.require(r.returncode==0,'Cannot inspect pinned package source');tracked[name]=set(r.stdout.splitlines())
        m.progress('authentication','tracked_package_end',package=name,tracked_files=len(tracked[name]))
    resolution,_,owners=m.resolve_external_imports(root,freeze,{n:(root/'formal/.lake/packages'/n,files) for n,files in tracked.items()})
    policy_name=str(a.unused_cache_policy.absolute().relative_to(root));policy_file=m.relative(root,policy_name)
    m.require(policy_file.is_relative_to(root/'.tools/linux-verification') and m.SHA.fullmatch(a.unused_cache_policy_sha256) and m.sha(policy_file)==a.unused_cache_policy_sha256,'Caller unused-cache policy SHA/path differs')
    policy=m.read(policy_file);m.validate_unused_cache_policy(policy)
    m.progress('authentication','cache_states_begin')
    states=m.cache_root_states(root,cache_roots,owners,policy)
    m.progress('authentication','cache_states_end',roots=len(states))
    native=m.read(a.native_audit)
    m.progress('authentication','collection_cache_inventory_begin')
    runtime={'schema_version':2,'status':'authenticated_linux_runtime_for_strict_sampler','source_freeze_sha256':m.SOURCE_SHA,'trusted_files_sha256':tools,'trusted_tool_aliases':aliases,'system_executables':system,'trusted_cache_roots':cache_roots,'trusted_cache_files_sha256':m.cache_inventory(root,cache_roots,states),'lake_configuration_artifacts_sha256':configuration,'external_import_resolution':resolution,'entrypoint_native_audit':native,
             'trusted_cache_states':states,'external_import_owners':owners,'unused_cache_policy':policy,'unused_cache_policy_binding':{'path':policy_name,'sha256':a.unused_cache_policy_sha256}}
    runtime.update(lake_configuration_provenance=config_provenance,lake_configuration_provenance_binding={'path':config_name,'sha256':a.lake_config_provenance_sha256},lake_configuration_artifacts_stat=config_stats)
    m.progress('authentication','collection_cache_inventory_end',files=len(runtime['trusted_cache_files_sha256']))
    # Complete independent runner admission re-derives graph, pins, resolution,
    # full cache and configuration identities; collection alone is insufficient.
    m.progress('authentication','independent_admission_begin')
    m.admit(root,freeze,runtime,serial,parser)
    m.progress('authentication','independent_admission_end')
    a.output.write_text(json.dumps(runtime,indent=2,sort_keys=True)+'\n')
    m.progress('authentication','runtime_emitted')
    print('MATH115_C11_RUNTIME_FREEZE_SHA256='+m.sha(a.output),flush=True)
if __name__=='__main__':main()
