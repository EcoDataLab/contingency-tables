"""Authenticate supplied compressed guest evidence without extraction/execution."""
from pathlib import Path,PurePosixPath
import hashlib,json,tarfile
P=Path(__file__).resolve().parents[1]
manifest=json.loads((P/'evidence/guest-member-manifest.json').read_text())
archive=P/'evidence/guest-evidence.tar.gz'
with archive.open('rb') as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
if digest!=manifest['tar_gz_sha256']:raise ValueError('Archive hash mismatch')
seen=set();total=0
with tarfile.open(archive,'r:gz') as tf:
 for member in tf:
  name=member.name;path=PurePosixPath(name)
  if not member.isfile() or path.is_absolute() or '..' in path.parts or name in seen or name not in manifest['files']:raise ValueError('Unexpected or unsafe archive member')
  total+=member.size
  if total>64*1024**2:raise ValueError('Uncompressed size exceeds recorded collection limit')
  raw=tf.extractfile(member).read()
  if len(raw)!=member.size or hashlib.sha256(raw).hexdigest()!=manifest['files'][name]:raise ValueError('Member size/hash mismatch')
  seen.add(name)
if seen!=set(manifest['files']) or len(seen)!=manifest['members']:raise ValueError('Incomplete member set')
print(json.dumps({'archive_sha256':digest,'authenticated_members':len(seen),'uncompressed_bytes':total,'no_extraction_or_execution':True},sort_keys=True))
