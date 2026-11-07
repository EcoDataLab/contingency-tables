"""Small local lifetime/check-equivalence fixtures; no VM/compiler or global GC fix."""
from pathlib import Path
import ast,gc,hashlib,importlib.util,json,os,shutil,tempfile,unittest,weakref
from unittest.mock import patch
D=Path(__file__).resolve().parents[1]
REPO=D.parents[2]
REFERENCES=json.loads((D/'reproduction-references.json').read_text())['files']
ORIGINALS={'original-anchored_metadata.py':'original_metadata','original-snapshots.py':'original_snapshots'}
def source(file):
 return REPO/REFERENCES[ORIGINALS[file]]['path'] if file in ORIGINALS else D/'source'/file

def load(file):
 spec=importlib.util.spec_from_file_location('memory_'+file.replace('.','_').replace('-','_'),source(file));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
old=load('original-anchored_metadata.py');fixed=load('anchored_metadata.py');old_snap=load('original-snapshots.py');fixed_snap=load('snapshots.py')
class Expected(dict):pass
class Token:
 def __init__(self,value):self.value=value

def require(ok,message):
 if not ok:raise RuntimeError(message)

def call(module,root,names,expected):
 if hasattr(module,'FrozenMetadataIndex'):return module.FrozenMetadataIndex(names,require).snapshot(root,expected)
 return module.ManifestTrie(names).snapshot(root)

class MemoryFix(unittest.TestCase):
 def test_anchor_breaks_recursive_lifetime_cycle_without_gc(self):
  before_enabled=gc.isenabled();gc.collect();gc.disable()
  try:
   with tempfile.TemporaryDirectory() as tmp:
    root=Path(tmp);p=root/'x';p.write_bytes(b'x')
    counts=[]
    for module in [old,fixed]:
     refs=[];index=module.FrozenMetadataIndex(['x'],require)
     for _ in range(8):
      expected=Expected({'x':module.identity(p.stat())});refs.append(weakref.ref(expected));out=index.snapshot(root,expected);del out,expected
     counts.append(sum(r() is not None for r in refs));gc.collect()
    self.assertEqual(counts,[8,0])
  finally:
   gc.collect()
   if before_enabled:gc.enable()
 def test_preparation_snapshot_breaks_recursive_output_cycle(self):
  before_enabled=gc.isenabled();gc.collect();gc.disable()
  try:
   with tempfile.TemporaryDirectory() as tmp:
    root=Path(tmp);(root/'x').write_bytes(b'x');counts=[]
    for module in [old_snap,fixed_snap]:
     refs=[]
     def value(stat_result):
      token=Token((stat_result.st_size,stat_result.st_mtime_ns,stat_result.st_ctime_ns,stat_result.st_ino));refs.append(weakref.ref(token));return token
     with patch.object(module,'value',side_effect=value):
      for _ in range(8):out=module.ManifestTrie(['x']).snapshot(root);del out
     counts.append(sum(r() is not None for r in refs));gc.collect()
    self.assertEqual(counts,[8,0])
  finally:
   gc.collect()
   if before_enabled:gc.enable()
 def compare(self,setup,expected_change=None):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);(root/'d').mkdir();p=root/'d/x';p.write_bytes(b'value');setup(root,p);names=['d/x'];expected={'d/x':old.identity(p.stat())} if p.exists() else {'d/x':(1,2,3,4)}
   if expected_change:expected=expected_change(expected)
   rows=[]
   for module in [old,fixed,old_snap,fixed_snap]:
    opened=[];closed=[];open_real=os.open;close_real=os.close
    def track_open(*args,**kwargs):fd=open_real(*args,**kwargs);opened.append(fd);return fd
    def track_close(fd):closed.append(fd);return close_real(fd)
    result=None;error=None
    with patch.object(os,'open',side_effect=track_open),patch.object(os,'close',side_effect=track_close):
     try:result=call(module,root,names,expected)
     except Exception as e:error=(type(e).__name__,str(e))
    self.assertEqual(sorted(opened),sorted(closed));self.assertEqual(len(opened),len(set(closed)))
    if result:result={k:old.identity(v) if isinstance(v,os.stat_result) else v for k,v in result.items()}
    rows.append((result,error))
   self.assertEqual(rows[0],rows[1]);self.assertEqual(rows[2],rows[3]);return rows
 def test_success_outputs_and_fd_closure_unchanged(self):
  rows=self.compare(lambda r,p:None);self.assertEqual(rows[0][0],rows[2][0]);self.assertIsNone(rows[0][1])
 def test_leaf_symlink_rejections_unchanged(self):
  def setup(root,p):p.rename(root/'actual');p.symlink_to(root/'actual')
  rows=self.compare(setup);self.assertTrue(all(r[1] for r in rows))
 def test_parent_symlink_rejections_unchanged(self):
  def setup(root,p):(root/'d').rename(root/'real');(root/'d').symlink_to(root/'real',target_is_directory=True)
  rows=self.compare(setup);self.assertTrue(all(r[1] for r in rows))
 def test_missing_leaf_rejections_unchanged(self):
  rows=self.compare(lambda r,p:p.unlink());self.assertTrue(all(r[1] for r in rows))
 def test_expected_metadata_mismatch_rejected_unchanged(self):
  rows=self.compare(lambda r,p:None,lambda e:{'d/x':(0,0,0,0)});self.assertIsNotNone(rows[0][1]);self.assertIsNotNone(rows[1][1])
 def test_root_symlink_rejection_before_walk_definition_safe(self):
  with tempfile.TemporaryDirectory() as tmp:
   parent=Path(tmp);real=parent/'real';real.mkdir();(real/'x').write_bytes(b'x');alias=parent/'alias';alias.symlink_to(real,target_is_directory=True)
   for module in [old,fixed,old_snap,fixed_snap]:
    with self.subTest(module=module.__name__),self.assertRaises(Exception):call(module,alias,['x'],{'x':old.identity((real/'x').stat())})
 def test_child_open_failure_closes_root_and_keeps_error(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);(root/'d').mkdir();p=root/'d/x';p.write_bytes(b'x');expected={'d/x':old.identity(p.stat())}
   for module in [old,fixed,old_snap,fixed_snap]:
    opened=[];closed=[];open_real=os.open;close_real=os.close
    def checked_open(path,*args,**kwargs):
     if path=='d':raise PermissionError('injected directory open denial')
     fd=open_real(path,*args,**kwargs);opened.append(fd);return fd
    def checked_close(fd):closed.append(fd);return close_real(fd)
    with patch.object(os,'open',side_effect=checked_open),patch.object(os,'close',side_effect=checked_close),self.assertRaisesRegex(PermissionError,'injected directory open denial'):call(module,root,['d/x'],expected)
    self.assertEqual(opened,closed)
 def test_only_ast_change_is_cycle_break_in_finally(self):
  for name in ['anchored_metadata.py','snapshots.py']:
   before=ast.parse(source('original-'+name).read_text());after=ast.parse(source(name).read_text());removed=0
   for node in ast.walk(after):
    if isinstance(node,ast.Try):
     kept=[]
     for item in node.finalbody:
      if isinstance(item,ast.Assign) and len(item.targets)==1 and isinstance(item.targets[0],ast.Name) and item.targets[0].id=='walk' and isinstance(item.value,ast.Constant) and item.value.value is None:removed+=1
      else:kept.append(item)
     node.finalbody=kept
   self.assertEqual(removed,1);self.assertEqual(ast.dump(before,include_attributes=False),ast.dump(after,include_attributes=False))
 def test_path_escape_constructor_rejections_unchanged(self):
  for module in [old,fixed,old_snap,fixed_snap]:
   with self.subTest(module=module.__name__),self.assertRaises(Exception):call(module,Path('/unused'),['../x'],{})
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def constants(raw):
 return {n.targets[0].id:ast.literal_eval(n.value) for n in ast.parse(raw).body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id in {'METADATA_SHA','ASSETS','V2','SNAPSHOT','ORIGINAL','AUTH','HELPER'}}

class IntegrationPins(unittest.TestCase):
 def test_candidate_preparation_and_runtime_pin_chain(self):
  contents=self.assembly().sources();runner=constants(contents['candidate/strict_sampler.py']);prep=constants(contents['preparation/prepare_memos.py'])
  self.assertEqual(runner['METADATA_SHA'],digest(source('anchored_metadata.py')))
  self.assertEqual(prep['V2'],hashlib.sha256(contents['candidate/strict_sampler.py']).hexdigest())
  self.assertEqual(prep['SNAPSHOT'],digest(source('snapshots.py')))
  for key,reference in [('ORIGINAL','original_runner'),('AUTH','original_authenticator'),('HELPER','normalization_helper')]:self.assertEqual(prep[key],REFERENCES[reference]['sha256'])
  self.assertEqual(runner['ASSETS']['strict_serial_check.py'],REFERENCES['observer']['sha256'])
 def test_runner_and_preparation_function_bodies_unchanged(self):
  for filename,key in [('versioned_runner.py','previous_candidate'),('prepare_memos.py','previous_preparation')]:
   def bodies(raw):return [ast.dump(n,include_attributes=False) for n in ast.parse(raw).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))]
   name='candidate/strict_sampler.py' if filename=='versioned_runner.py' else 'preparation/prepare_memos.py'
   self.assertEqual(bodies(self.assembly().sources()[name]),bodies((REPO/REFERENCES[key]['path']).read_text()))
 def assembly(self):
  spec=importlib.util.spec_from_file_location('metadata_source_assembly',D/'tools/prepare_candidate.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
 def test_fresh_source_assembly_loads_fixed_helper_and_observer(self):
  m=self.assembly()
  with tempfile.TemporaryDirectory() as tmp:
   out=Path(tmp)/'fresh';receipt=m.assemble(out)
   self.assertEqual(receipt['files_sha256']['candidate/anchored_metadata.py'],digest(source('anchored_metadata.py')))
   self.assertEqual(receipt['files_sha256']['candidate/tested-runtime/strict_serial_check.py'],REFERENCES['observer']['sha256'])
   with self.assertRaises(FileExistsError):m.assemble(out)
 def test_changed_helper_rejected_before_output_creation(self):
  m=self.assembly()
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);packet=root/'packet';shutil.copytree(D,packet,ignore=shutil.ignore_patterns('__pycache__'));(packet/'source/anchored_metadata.py').write_bytes(b'changed')
   with self.assertRaisesRegex(ValueError,'Source pin mismatch'):m.assemble(root/'out',packet,REPO)
   self.assertFalse((root/'out').exists())
if __name__=='__main__':unittest.main()
