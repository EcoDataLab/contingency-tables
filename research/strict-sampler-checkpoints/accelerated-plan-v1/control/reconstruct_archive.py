"""Validate a separately supplied retained raw serial; never execute its contents."""
import argparse,base64,hashlib,io,json,re,tarfile
from pathlib import Path,PurePosixPath
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('raw_serial',type=Path);p.add_argument('fresh_archive',type=Path);a=p.parse_args()
 packet=Path(__file__).resolve().parents[1]
 declaration=json.loads((packet/'serial-interleaving.json').read_text())
 bindings=json.loads((packet/'provenance-bindings.json').read_text())
 raw=a.raw_serial.read_bytes()
 if sha(raw)!=declaration['raw_serial_sha256']:raise ValueError('Raw serial hash mismatch')
 serial=raw.decode('utf-8',errors='strict').replace('\r\n','\n').replace('\r','\n')
 rows=re.findall(r'^MATH115_C11_EVIDENCE_MANIFEST=(.+)$',serial,re.M)
 blocks=re.findall(r'^MATH115_C11_EVIDENCE_B64_BEGIN\n(.*?)^MATH115_C11_EVIDENCE_B64_END$',serial,re.M|re.S)
 if len(rows)!=1 or len(blocks)!=1:raise ValueError('Missing or duplicate collection markers')
 manifest=json.loads(rows[0]);payload=blocks[0]
 if set(manifest)!={'tar_gz_sha256','files'}:raise ValueError('Unexpected manifest keys')
 if manifest['files']!=bindings['raw_guest_members']:raise ValueError('Member manifest mismatch')
 for item in declaration['insertions']:
  if payload.count(item['message'])!=1 or payload.find(item['message'])!=item['offset']:raise ValueError('Declared insertion mismatch')
 # Check offsets together before deleting, so later offsets remain original.
 for item in declaration['insertions']:payload=payload.replace(item['message'],'')
 archive=base64.b64decode(''.join(payload.split()),validate=True)
 if len(archive)>64*1024**2 or sha(archive)!=manifest['tar_gz_sha256'] or sha(archive)!=declaration['emitted_archive_sha256']:raise ValueError('Archive hash or size mismatch')
 seen=set();total=0
 with tarfile.open(fileobj=io.BytesIO(archive),mode='r:gz') as tf:
  for member in tf:
   name=member.name;path=PurePosixPath(name)
   if not member.isfile() or path.is_absolute() or '..' in path.parts or name in seen or name not in manifest['files']:raise ValueError('Unsafe or unexpected member')
   total+=member.size
   if total>64*1024**2:raise ValueError('Uncompressed archive too large')
   content=tf.extractfile(member).read()
   if len(content)!=member.size or sha(content)!=manifest['files'][name]:raise ValueError('Member hash mismatch')
   seen.add(name)
 if seen!=set(manifest['files']):raise ValueError('Missing members')
 with a.fresh_archive.open('xb') as f:f.write(archive)
 print(json.dumps({'archive_sha256':sha(archive),'authenticated_members':len(seen),'raw_serial_unmodified':True},sort_keys=True))
if __name__=='__main__':main()
