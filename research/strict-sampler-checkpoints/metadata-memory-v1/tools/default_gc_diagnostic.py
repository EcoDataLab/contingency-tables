"""Bounded local reproduction with default GC left enabled; no Thor execution."""
from pathlib import Path
import gc,importlib.util,json,sys,tempfile,time,tracemalloc,weakref
D=Path(__file__).resolve().parents[1]
REPO=D.parents[2]
REFERENCES=json.loads((D/'reproduction-references.json').read_text())['files']
def source(name):
 return REPO/REFERENCES['original_metadata']['path'] if name=='original-anchored_metadata.py' else D/'source'/name
class Expected(dict):pass

def load(name):
 spec=importlib.util.spec_from_file_location('bounded_gc_'+name.replace('-','_').replace('.','_'),source(name));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
results=[];assert gc.isenabled();threshold=gc.get_threshold()
with tempfile.TemporaryDirectory() as tmp:
 root=Path(tmp);names=[f'x{i}' for i in range(100)]
 for n in names:(root/n).write_bytes(b'x')
 for name in ['original-anchored_metadata.py','anchored_metadata.py']:
  m=load(name);index=m.FrozenMetadataIndex(names,lambda ok,msg:None if ok else (_ for _ in ()).throw(RuntimeError(msg)));gc.collect();tracemalloc.start();start=tracemalloc.get_traced_memory()[0];began=time.monotonic();refs=[]
  before=gc.get_stats()
  for _ in range(80):
   expected=Expected({n:m.identity((root/n).stat()) for n in names});refs.append(weakref.ref(expected));out=index.snapshot(root,expected);del expected,out
  current,peak=tracemalloc.get_traced_memory();alive=sum(r() is not None for r in refs);after=gc.get_stats();tracemalloc.stop()
  results.append({'source':name,'snapshots':80,'files_per_snapshot':100,'live_expected_maps':alive,'traced_bytes_above_start':current-start,'traced_peak_bytes':peak,'elapsed_seconds':time.monotonic()-began,'collections_per_generation':[b['collections']-a['collections'] for a,b in zip(before,after)]});gc.collect()
assert gc.isenabled() and gc.get_threshold()==threshold
print(json.dumps({'status':'bounded local default-enabled-GC lifetime/memory comparison','python':sys.version,'gc_thresholds_unchanged':threshold,'results':results,'limits':'100files/80snapshots, the interpreter recorded above; not productionRSS or exact proof of guestOOMcausality. Traceback/lifetime checks and output equivalence are separate fixtures. No active checker or Thor changes.'},indent=2))
