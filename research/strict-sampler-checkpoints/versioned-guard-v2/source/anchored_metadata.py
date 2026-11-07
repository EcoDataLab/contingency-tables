"""Versioned anchored selected-cache guard under a trusted quiet-cache premise.

Not a universal race-equivalence claim. Retains three leaf observations. Full
inventories/content checks and all other Guard checks stay in the original runner.
"""
from pathlib import Path,PurePosixPath
import os,stat
def identity(s):return (s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_ino)
def directory_identity(s):return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid,s.st_mtime_ns,s.st_ctime_ns)
class FrozenMetadataIndex:
 def __init__(self,names,require):
  self.require=require;self.tree={};self.names=tuple(names)
  for name in self.names:
   require(isinstance(name,str) and '\\' not in name and '\0' not in name,'Invalid relative path')
   p=PurePosixPath(name);require(not p.is_absolute() and '..' not in p.parts and name not in ('','.'),'Escaping input path')
   require(bool(p.parts),'Trusted cache file vanished')
   node=self.tree
   for part in p.parts[:-1]:
    child=node.setdefault(part,{})
    require(isinstance(child,dict),'Frozen cache file/directory conflict');node=child
   leaf=node.setdefault(p.parts[-1],[])
   require(isinstance(leaf,list),'Frozen cache directory/file conflict');leaf.append(name)
 def snapshot(self,root,expected):
  require=self.require;root=Path(root);out={};opened=[]
  require(set(expected)==set(self.names),'Frozen metadata selection changed')
  if not self.names:return out
  flags=getattr(os,'O_PATH',os.O_RDONLY)|os.O_DIRECTORY|os.O_NOFOLLOW
  try:
   before=root.lstat();require(stat.S_ISDIR(before.st_mode),'Symlinked/non-directory checking root')
   fd=os.open(root,flags);opened.append(fd)
   require(directory_identity(os.fstat(fd))==directory_identity(before),'Checking root changed during open')
   def walk(parent,node):
    before=os.fstat(parent)
    for name,child in node.items():
     if isinstance(child,list):
      # Original Path.is_symlink treats a failed lstat as false; retain that
      # predicate observation before the following regular-file observation.
      try:is_link=stat.S_ISLNK(os.stat(name,dir_fd=parent,follow_symlinks=False).st_mode)
      except (OSError,ValueError):is_link=False
      require(not is_link,'Symlinked input path refused')
      try:is_regular=stat.S_ISREG(os.stat(name,dir_fd=parent,follow_symlinks=True).st_mode)
      except (OSError,ValueError):is_regular=False
      require(is_regular,'Trusted cache file vanished')
      final=os.stat(name,dir_fd=parent,follow_symlinks=True)
      for original in child:
       require(identity(final)==tuple(expected[original]),'Trusted cache metadata changed: '+original)
       out[original]=final
     else:
      observed=os.stat(name,dir_fd=parent,follow_symlinks=False)
      require(stat.S_ISDIR(observed.st_mode),'Symlinked/non-directory cache parent')
      childfd=os.open(name,flags,dir_fd=parent);opened.append(childfd)
      try:
       require(directory_identity(os.fstat(childfd))==directory_identity(observed),'Cache parent changed during open')
       walk(childfd,child)
       after=os.stat(name,dir_fd=parent,follow_symlinks=False)
       require(directory_identity(after)==directory_identity(os.fstat(childfd)),'Cache parent namespace changed')
      finally:os.close(childfd);opened.remove(childfd)
    require(directory_identity(os.fstat(parent))==directory_identity(before),'Cache directory changed during traversal')
   walk(fd,self.tree)
   require(directory_identity(root.lstat())==directory_identity(os.fstat(fd)),'Checking root namespace changed')
   require(set(out)==set(expected),'Incomplete selected-cache observations')
   return out
  finally:
   for fd in reversed(opened):os.close(fd)
