"""Losslessly restore already authenticated guest transport; never run collected code."""
from pathlib import Path,PurePosixPath
import gzip,hashlib,json,shutil
D=Path(__file__).resolve().parent;G=D/'guest-evidence';O=D/'guest-originals'
assert G.is_dir() and not O.exists(),'Authenticated transport and fresh restore destination required'
auth=json.loads((G/'collection-authentication.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,pin in auth['files'].items():assert sha(G/name)==pin,'Authenticated transport drift: '+name
metadata=json.loads((G/'collection-transforms.json').read_text());transforms=metadata['transforms']
assert len(transforms)==5
assert set(transforms)=={'baseline-runtime-freeze.json','memo-preparation/runtime-freeze.json','memo-preparation/result.json','memo-preparation/artifact-request.txt','repair.stdout.log'}
encoded={t['transport_name'] for t in transforms.values()}
raw_size=sum(t['original_bytes'] for t in transforms.values())+sum((G/n).stat().st_size for n in auth['files'] if n not in encoded and n!='collection-transforms.json')
assert raw_size<=128*1024**2,'Expanded evidence exceeds fixed restoration budget'
O.mkdir()
for name in auth['files']:
 if name in encoded or name=='collection-transforms.json':continue
 target=O/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(G/name,target)
for name,t in transforms.items():
 assert t['encoding']=='gzip' and t['transport_name']==name+'.gz'
 source=G/t['transport_name'];assert sha(source)==t['transport_sha256']
 with gzip.open(source,'rb') as stream:raw=stream.read(t['original_bytes']+1)
 assert len(raw)==t['original_bytes'] and hashlib.sha256(raw).hexdigest()==t['original_sha256']
 target=O/name;assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
receipt=dict(status='all transported original evidence restored and hash checked; no collected code executed',source_archive_sha256=auth['tar_gz_sha256'],source_member_count=auth['members'],original_member_count=len(auth['files'])-1,restored_bytes=raw_size,files={str(p.relative_to(O)):dict(bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(O.rglob('*')) if p.is_file()})
(D/'restoration-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='files'},indent=2))
