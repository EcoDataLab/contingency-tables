"""Capture helpers extracted from the observed guest reader; no host/VM wrapper."""
import hashlib,os,stat
from pathlib import Path,PurePosixPath
ROOT_GUEST="/checking"
MAX_ENTRIES=256;MAX_CONFIG=16*1024**2;MAX_TOOL=64*1024**2;MAX_TOTAL=256*1024**2
class Reject(RuntimeError):pass
def require(ok,msg):
 if not ok:raise Reject(msg)
def normalize(parts):
 result=[]
 for p in parts:
  if p in ('','/','.'):continue
  if p=='..':
   require(bool(result),'Path escapes captured image');result.pop()
  else:result.append(p)
 return result
def resolve_guest(mount,guest,maxlinks=32):
 """Absolute guest links map back into captured filesystem, never boot filesystem."""
 require(PurePosixPath(guest).is_absolute(),'Guest path must be absolute')
 parts=normalize(PurePosixPath(guest).parts);resolved=[];links=[]
 while parts:
  component=parts.pop(0);path=mount.joinpath(*resolved,component);info=path.lstat()
  if stat.S_ISLNK(info.st_mode):
   require(len(links)<maxlinks,'Symlink loop/budget');target=os.readlink(path);links.append({'guest_path':'/'+('/'.join([*resolved,component])),'target':target})
   parts=normalize(([ ] if target.startswith('/') else resolved)+list(PurePosixPath(target).parts)+parts);resolved=[]
  else:
   if parts:require(stat.S_ISDIR(info.st_mode),'Non-directory path component')
   resolved.append(component)
 require(('/'+'/'.join(resolved)).startswith(ROOT_GUEST+'/') or ('/'+'/'.join(resolved))==ROOT_GUEST or ('/'+'/'.join(resolved)).startswith('/checking-user/.elan/toolchains/leanprover--lean4---v4.34.1/'),'Requested link resolves outside capture scope')
 return mount.joinpath(*resolved),links
def stable(info):return (info.st_dev,info.st_ino,info.st_mode,info.st_uid,info.st_gid,info.st_size,info.st_mtime_ns,info.st_ctime_ns)
class Capture:
 def __init__(self,mount,out):self.mount=Path(mount);self.out=Path(out);self.rows=[];self.total=0;(self.out/'raw').mkdir()
 def entry(self,guest,kind='config',allowlink=False):
  require(len(self.rows)<MAX_ENTRIES,'Entry budget exceeded')
  try:
   parent,parents=resolve_guest(self.mount,str(PurePosixPath(guest).parent));rawpath=parent/PurePosixPath(guest).name;info=rawpath.lstat()
  except FileNotFoundError:
   row={'guest_path':guest,'type':'absent','purpose':kind};self.rows.append(row);return row
  typ='regular' if stat.S_ISREG(info.st_mode) else 'directory' if stat.S_ISDIR(info.st_mode) else 'symlink' if stat.S_ISLNK(info.st_mode) else 'other'
  row={'guest_path':guest,'resolved_guest_path':'/'+rawpath.relative_to(self.mount).as_posix(),'parent_resolution_links':parents,'type':typ,'purpose':kind,'mode':stat.S_IMODE(info.st_mode),'uid':info.st_uid,'gid':info.st_gid,'size':info.st_size,'inode':info.st_ino,'device':info.st_dev,'mtime_ns':info.st_mtime_ns,'ctime_ns':info.st_ctime_ns}
  self.rows.append(row)
  if typ=='symlink':
   row['target']=os.readlink(rawpath)
   if not allowlink:return row
   path,links=resolve_guest(self.mount,guest);row['resolved_guest_path']='/'+path.relative_to(self.mount).as_posix();row['links']=links;info=path.lstat()
   require(stat.S_ISREG(info.st_mode),'Requested source/tool target not regular')
  elif typ=='regular':path=rawpath
  else:return row
  limit=MAX_TOOL if kind=='tool_binary' else MAX_CONFIG
  require(info.st_size<=limit and self.total+info.st_size<=MAX_TOTAL,'Member/aggregate byte cap')
  self.total+=info.st_size;target=self.out/'raw'/f'{len(self.rows)-1:04d}.bin';h=hashlib.sha256();before=stable(info)
  with path.open('rb') as src,target.open('xb') as dst:
   require(stable(os.fstat(src.fileno()))==before,'Source identity changed at open')
   for chunk in iter(lambda:src.read(1024*1024),b''):dst.write(chunk);h.update(chunk)
   require(stable(os.fstat(src.fileno()))==before,'Source identity changed during read')
  require(stable(path.lstat())==before,'Source identity changed after read')
  row.update(raw=target.relative_to(self.out).as_posix(),sha256=h.hexdigest(),raw_bytes=target.stat().st_size)
  return row
 def tree(self,guest):
  row=self.entry(guest);path=self.mount/row.get('resolved_guest_path',guest).lstrip('/')
  if row['type']=='directory':
   names=sorted(x.name for x in path.iterdir());row['keyset']=names
   for name in names:self.tree(guest+'/'+name)
 def source(self,guest,kind='source'):
  # Resolve parent directory links, but still map every absolute target into source mount.
  path,links=resolve_guest(self.mount,guest);canonical='/'+path.relative_to(self.mount).as_posix()
  row=self.entry(canonical,kind,True);row.update(requested_guest_path=guest,parent_resolution_links=links);require(row['type'] in {'regular','symlink'} and 'raw' in row,'Required source/tool absent or not regular');return row
