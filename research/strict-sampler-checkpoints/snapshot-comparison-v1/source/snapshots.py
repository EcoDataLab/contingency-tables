"""Standalone metadata comparison prototype; not installed in the checker.

Selection matches frozen manifest names. Anchored traversal validates every
expected directory and leaf; unknown directory entries are not sampled or used.
"""
from pathlib import Path,PurePosixPath
import os,stat

class SnapshotReject(RuntimeError):pass

def require(ok,message):
    if not ok:raise SnapshotReject(message)

def parts(name):
    require(isinstance(name,str) and '\\' not in name and '\0' not in name,'invalid relative path')
    p=PurePosixPath(name)
    require(not p.is_absolute() and '..' not in p.parts and name not in ('','.'),'escaping relative path')
    return p.parts

def relative(root,name):
    result=root.joinpath(*parts(name))
    require(result.resolve().is_relative_to(root.resolve()),'path escapes root')
    require(not any(x.is_symlink() for x in (result,*result.parents) if x==root or x.is_relative_to(root)),'symlinked path')
    return result

def value(s):return (s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_ino)

def directory_identity(s):return (s.st_dev,s.st_ino,s.st_mode,s.st_mtime_ns,s.st_ctime_ns)

def reference(root,names):
    root=Path(root);out={}
    for name in names:
        p=relative(root,name);require(p.is_file(),'expected file missing/nonregular')
        out[name]=value(p.stat())
    return out

class ManifestTrie:
    def __init__(self,names):
        self.tree={};self.names=tuple(names)
        for name in self.names:
            node=self.tree;ps=parts(name)
            for part in ps[:-1]:
                child=node.setdefault(part,{})
                require(isinstance(child,dict),'manifest file/directory conflict')
                node=child
            leaf=node.setdefault(ps[-1],[])
            require(isinstance(leaf,list),'manifest directory/file conflict')
            leaf.append(name)

    def snapshot(self,root):
        root=Path(root);out={};opened=[]
        flags=getattr(os,'O_PATH',os.O_RDONLY)|os.O_DIRECTORY|os.O_NOFOLLOW
        try:
            root_before=root.lstat();require(stat.S_ISDIR(root_before.st_mode),'root nonregular/symlink')
            rootfd=os.open(root,flags);opened.append(rootfd)
            require(directory_identity(os.fstat(rootfd))==directory_identity(root_before),'root changed during open')
            def walk(fd,node):
                before=os.fstat(fd)
                for name,child in node.items():
                    observed=os.stat(name,dir_fd=fd,follow_symlinks=False)
                    if isinstance(child,list):
                        require(stat.S_ISREG(observed.st_mode),'expected leaf nonregular/symlink')
                        for original_name in child:out[original_name]=value(observed)
                    else:
                        require(stat.S_ISDIR(observed.st_mode),'parent nonregular/symlink')
                        childfd=os.open(name,flags,dir_fd=fd);opened.append(childfd)
                        try:
                            require(directory_identity(os.fstat(childfd))==directory_identity(observed),'parent changed during open')
                            walk(childfd,child)
                            after=os.stat(name,dir_fd=fd,follow_symlinks=False)
                            require(directory_identity(after)==directory_identity(os.fstat(childfd)),'parent namespace changed')
                        finally:
                            os.close(childfd);opened.remove(childfd)
                require(directory_identity(os.fstat(fd))==directory_identity(before),'directory changed during pass')
            walk(rootfd,self.tree)
            require(directory_identity(root.lstat())==directory_identity(os.fstat(rootfd)),'root namespace changed')
            return out
        finally:
            for fd in reversed(opened):os.close(fd)
