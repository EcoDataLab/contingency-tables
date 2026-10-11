"""Unexecuted publication adapter for a pre-authenticated readonly Linux mount.

No mounting, booting, subprocess, Git, Lean, configuration execution or cache
object copying. This adapter is not the original guest supervision/reader body.
"""
import argparse,json,os,signal
from pathlib import Path,PurePosixPath
import cache_diagnostic as diagnostic
import capture_support as support

def main():
 p=argparse.ArgumentParser();p.add_argument('--mount',type=Path,required=True);p.add_argument('--checking-root',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 root=PurePosixPath(a.checking_root)
 if not root.is_absolute() or '..' in root.parts or '\\' in a.checking_root or '\0' in a.checking_root:raise RuntimeError('Unsafe checking-root path')
 if not a.mount.is_absolute() or a.mount.is_symlink() or not a.mount.is_dir():raise RuntimeError('Need an independently authenticated readonly source mount')
 if not os.statvfs(a.mount).f_flag & os.ST_RDONLY:raise RuntimeError('Source filesystem is not readonly')
 if a.output.exists():raise RuntimeError('Need new output directory')
 a.output.mkdir(parents=True,exist_ok=False)
 diagnostic.ROOT=str(root);support.ROOT_GUEST=str(root)
 def timeout(*_):raise RuntimeError('300-second observational work deadline')
 signal.signal(signal.SIGALRM,timeout);signal.alarm(300)
 try:
  cap=support.Capture(a.mount,a.output);diagnostic.capture(cap)
 except BaseException as error:
  print(json.dumps({'status':'failed','error':type(error).__name__+': '+str(error),'scope':'readonly filesystem diagnostic, not runtime admission'}));return 1
 finally:signal.alarm(0)
 print(json.dumps({'status':'diagnostic_complete','scope':'filesystem facts only; no runtime/proof acceptance'}));return 0
if __name__=='__main__':raise SystemExit(main())
