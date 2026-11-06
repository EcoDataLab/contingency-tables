#!/usr/bin/env python3
"""Trusted installation into one fresh retained checking child; no network."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import tarfile

BASE = "895b45c8bcb0ca7f60e7a6b0b91af89b2ac7c566"
TIP = "fe72b20170e7f85e399368e56baf65b8782b4b50"
def sha(path):
    with path.open("rb") as f: return hashlib.file_digest(f,"sha256").hexdigest()
def require(ok, message):
    if not ok: raise RuntimeError(message)
def git(root,*args):
    r=subprocess.run(["/usr/bin/git","-C",str(root),*args],text=True,capture_output=True,timeout=180)
    require(r.returncode==0,"Local Git installation step failed: "+str(args))
    return r.stdout.strip()
def run(root, archive, manifest, manifest_sha, staging):
    require(sha(manifest)==manifest_sha,"Installation manifest changed")
    data=json.loads(manifest.read_text())
    require(sha(archive)==data['archive_sha256'],"Installation archive changed")
    require(not staging.exists() and staging.is_relative_to(root/'.tools/linux-verification'),"Need fresh trusted staging")
    require(git(root,"rev-parse","HEAD")==BASE,"Retained source base differs")
    require(not git(root,"diff","--name-only") and not git(root,"diff","--cached","--name-only"),"Retained source dirty")
    build=root/'formal/.lake/build'
    require(not build.exists() or not any(x.is_file() for x in build.rglob('*')),"Submitted objects exist before source installation")
    staging.mkdir(parents=True)
    with tarfile.open(archive,"r:gz") as tar:
        seen=set()
        for member in tar:
            p=PurePosixPath(member.name)
            require(member.isfile() and not p.is_absolute() and '..' not in p.parts and member.name not in seen,"Unsafe/duplicate archive member")
            require(member.name in data['members_sha256'],"Unlisted archive member")
            require(not member.name.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.o','.bc','.so','.dll','.dylib')),"Submitted proof artifact in source packet")
            destination=staging.joinpath(*p.parts);destination.parent.mkdir(parents=True,exist_ok=True)
            with tar.extractfile(member) as source, destination.open('xb') as output:
                while chunk:=source.read(1024*1024): output.write(chunk)
            require(sha(destination)==data['members_sha256'][member.name],"Archive member hash differs")
            seen.add(member.name)
    require(seen==set(data['members_sha256']),"Missing installation member")
    bundle=staging/'project.bundle'
    git(root,'bundle','verify',str(bundle))
    git(root,'fetch',str(bundle),'refs/heads/checking')
    git(root,'checkout','--detach',TIP)
    for src,dest in data['installation'].items():
        p=PurePosixPath(dest)
        require(not p.is_absolute() and '..' not in p.parts,"Installation destination escapes root")
        require(dest.startswith(('formal/Math115/','.tools/linux-verification/checkpoint11-runner/','.tools/linux-verification/strict-sampler-inputs/')),"Unexpected installation scope")
        target=root.joinpath(*p.parts)
        require(not any(x.is_symlink() for x in (target,*target.parents) if x==root or x.is_relative_to(root)),"Symlinked installation target")
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes((staging/src).read_bytes())
    (root/'formal/.lake').mkdir(exist_ok=True)
    require(git(root,'rev-parse','HEAD')==TIP,"Final checking revision differs")
    require(not build.exists() or not any(x.is_file() for x in build.rglob('*')),"Installation supplied project artifacts")
    receipt={'status':'source_installation_passed_no_compiler','base_commit':BASE,'final_commit':TIP,'archive_sha256':data['archive_sha256'],'members_sha256':data['members_sha256'],'submitted_build_files_after':0}
    (staging/'installation-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,sort_keys=True),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--archive',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--staging',type=Path,required=True)
    a=p.parse_args();run(a.root.resolve(),a.archive.resolve(),a.manifest.resolve(),a.manifest_sha256,a.staging.resolve())
