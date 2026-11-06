"""Fixed diagnostic toy only: process-local dumpability, or a same-exe fork."""
import argparse,ctypes,json,os,time
p=argparse.ArgumentParser();p.add_argument('--mode',choices=('recover','deny','overlap'),required=True);a=p.parse_args()
assert os.getuid()!=0
libc=ctypes.CDLL(None,use_errno=True);libc.prctl.restype=ctypes.c_int
libc.prctl.argtypes=[ctypes.c_int,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong]
def dumpable(value):
 assert libc.prctl(4,value,0,0,0)==0,ctypes.get_errno()
 actual=libc.prctl(3,0,0,0,0);assert actual==value
 print(json.dumps(dict(kind='toy_dumpability',pid=os.getpid(),uid=os.getuid(),dumpable=actual,mode=a.mode)),flush=True)
if a.mode=='overlap':
 child=os.fork()
 print(json.dumps(dict(kind='toy_overlap',pid=os.getpid(),uid=os.getuid(),role='parent' if child else 'child')),flush=True)
 time.sleep(20)
else:
 dumpable(0)
 time.sleep(1.5 if a.mode=='recover' else 20)
 if a.mode=='recover':dumpable(1);time.sleep(1.5)
