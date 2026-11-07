#!/usr/bin/env python3
"""Local seed-source generator only; no download, guest or host setting change."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import shutil

HERE=Path(__file__).resolve().parent
INPUT='/home/verifier/checking/.tools/linux-verification/checkpoint11-inputs'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output.resolve()
    if out.exists():raise RuntimeError('Existing seed-source output; no overwrite')
    installation=(HERE/'payload/installation-manifest.json').read_bytes();manifest=json.loads(installation)
    wrapper=('#!/usr/bin/env bash\nset -euo pipefail\nexec /usr/bin/python3 -I /home/verifier/checkpoint11-entry.py --installation-manifest-sha256 '+sha(installation)+' --lake-config-provenance-sha256 '+manifest['lake_config_provenance_sha256']+' --unused-cache-policy-sha256 '+manifest['unused_cache_policy_sha256']+'\n').encode()
    files={INPUT+'/installation-manifest.json':(installation,'0644'),'/home/verifier/checkpoint11-start.sh':(wrapper,'0755'),'/home/verifier/checkpoint11-install.py':((HERE/'install_sources.py').read_bytes(),'0755'),'/home/verifier/checkpoint11-authenticate.py':((HERE/'authenticate_runtime.py').read_bytes(),'0755'),'/home/verifier/checkpoint11-entry.py':((HERE/'guest_entry.py').read_bytes(),'0755'),'/home/verifier/checkpoint11-seed-media.py':((HERE/'seed_media.py').read_bytes(),'0755'),'/home/verifier/checking/.tools/linux-verification/prepare-memos.py':((HERE/'prepare_memos.py').read_bytes(),'0755'),'/home/verifier/checking/.tools/linux-verification/NormalizeMemos.lean':((HERE/'NormalizeMemos.lean').read_bytes(),'0644'),'/home/verifier/checking/.tools/linux-verification/snapshots.py':((HERE/'snapshots.py').read_bytes(),'0644'),'/home/verifier/checking/.tools/linux-verification/anchored-guard-v2/strict_sampler.py':((HERE/'versioned_runner.py').read_bytes(),'0755'),'/home/verifier/checking/.tools/linux-verification/anchored-guard-v2/anchored_metadata.py':((HERE/'anchored_metadata.py').read_bytes(),'0755')}
    out.mkdir(parents=True)
    archive=HERE/'payload/sources.tar.gz'
    if archive.stat().st_size!=manifest['archive_bytes'] or sha(archive.read_bytes())!=manifest['archive_sha256']:raise RuntimeError('Frozen media archive differs')
    shutil.copyfile(archive,out/'sources.gz')
    with (out/'user-data').open('w') as f:
        f.write('#cloud-config\npackage_update: false\npackage_upgrade: false\nwrite_files:\n')
        for name,(raw,mode) in files.items():
            owner='root:root' if name.endswith('/checkpoint11-seed-media.py') else 'verifier:verifier'
            f.write(f"  - path: {name}\n    owner: {owner}\n    permissions: '{mode}'\n    defer: true\n    encoding: b64\n    content: "+base64.b64encode(raw).decode()+'\n')
        f.write('runcmd:\n  - [/usr/bin/python3, -I, /home/verifier/checkpoint11-seed-media.py, --installation-manifest-sha256, '+sha(installation)+']\n')
    (out/'meta-data').write_text('instance-id: math115-further-gap-strict-memo01\nlocal-hostname: strict-comparator-guest\n')
    record={'status':'seed_sources_prepared_not_launch_authorized','entrypoint_audit_status':manifest['entrypoint_audit_status'],'installation_manifest_sha256':sha(installation),'source_archive_sha256':manifest['archive_sha256'],'installed_sha256':{n:sha(raw) for n,(raw,_) in files.items()},'files':{x.name:sha(x.read_bytes()) for x in out.iterdir()},'guest_ram_mib':10240,'guest_vcpus':1,'guest_cap_seconds':15000,'outer_cap_seconds':12600,'pipeline_scope':'original baseline authentication then bounded pre-admission memo normalization and frozen repeated gate stability','launch_authorized':False,'requires_actual_native_audit_and_fresh_runtime_before_launch':True}
    record['installed_sha256'][INPUT+'/sources.tar.gz']=manifest['archive_sha256']
    record['inline_sha256']={n:sha(raw) for n,(raw,_) in files.items()}
    record['source_archive_transport']='separate regular read-only ISO member sources.gz; bounded guest-only media copy'
    (out/'seed-source-manifest.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print('Seed source bytes prepared; no ISO or VM launched.')
if __name__=='__main__':main()
