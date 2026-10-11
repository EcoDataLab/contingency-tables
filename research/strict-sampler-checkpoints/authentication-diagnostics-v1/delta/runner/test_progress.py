"""Opt-in stderr tests with real temporary files, not verification monkeypatches."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import time
import unittest
import test_strict_sampler as core
m,serial=core.m,core.serial

class FlushBuffer(io.StringIO):
    def __init__(self):super().__init__();self.flushes=0
    def flush(self):self.flushes+=1;return super().flush()

class ProgressTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve();self.path=self.root/'cache/Init.olean'
        self.path.parent.mkdir();self.path.write_bytes(b'original object')
        m.enable_diagnostics(False);self.addCleanup(m.enable_diagnostics,False)
    def records(self,output):
        return [json.loads(line.split('=',1)[1]) for line in output.splitlines() if line.startswith('STRICT_AUTH_PROGRESS=')]
    def test_default_inventory_stderr_quiet(self):
        err=io.StringIO()
        with contextlib.redirect_stderr(err):result=m.cache_inventory(self.root,['cache'])
        self.assertEqual(err.getvalue(),'');self.assertEqual(result,{'cache/Init.olean':m.sha(self.path)})
    def test_opt_in_inventory_same_result_and_flushed_root_counts(self):
        expected=m.cache_inventory(self.root,['cache']);err=FlushBuffer();out=io.StringIO();m.enable_diagnostics(True)
        with contextlib.redirect_stderr(err),contextlib.redirect_stdout(out):actual=m.cache_inventory(self.root,['cache'])
        self.assertEqual(actual,expected);self.assertEqual(out.getvalue(),'');self.assertGreater(err.flushes,0)
        records=self.records(err.getvalue());root_end=next(r for r in records if r['event']=='root_end')
        self.assertEqual((root_end['files'],root_end['bytes']),(1,len(b'original object')))
        self.assertTrue(any(r['event']=='root_begin' for r in records));self.assertEqual(records[-1]['event'],'end')
    def test_same_symlink_failure_with_diagnostics_on_or_off(self):
        (self.path.parent/'bad.olean').symlink_to(self.root/'missing')
        failures=[]
        for enabled in (False,True):
            m.enable_diagnostics(enabled);err=io.StringIO()
            with contextlib.redirect_stderr(err):
                try:m.cache_inventory(self.root,['cache'])
                except m.Reject as e:failures.append((type(e),str(e)))
                else:self.fail('symlink accepted')
            if enabled:self.assertFalse(any(r['event']=='end' for r in self.records(err.getvalue())))
        self.assertEqual(failures[0],failures[1])
    def test_guard_hash_and_identity_failure_remain_unchanged(self):
        s=self.path.stat();cache={'cache/Init.olean':(m.sha(self.path),(s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_ino))}
        guard=m.Guard(self.root,{},{},cache,serial)
        err=io.StringIO();m.enable_diagnostics(True)
        with contextlib.redirect_stderr(err):guard.check(rehash=True)
        self.assertTrue(any(r['stage']=='guard_cache' and r['event']=='end' and r['rehash'] for r in self.records(err.getvalue())))
        self.path.write_bytes(b'changed object')
        failures=[]
        for enabled in (False,True):
            m.enable_diagnostics(enabled)
            with contextlib.redirect_stderr(io.StringIO()):
                try:guard.check(rehash=True)
                except m.Reject as e:failures.append(str(e))
                else:self.fail('changed object accepted')
        self.assertEqual(failures[0],failures[1])
    def test_heartbeat_rate_limit_and_explicit_elapsed_fields(self):
        m.enable_diagnostics(True);err=io.StringIO()
        with contextlib.redirect_stderr(err):
            m.progress_tick('sample',1,10)
            m._diag_last['sample']=time.monotonic()-6
            m.progress_tick('sample',2,20)
            m.progress_tick('sample',3,30)
        records=self.records(err.getvalue());self.assertEqual(len(records),1)
        self.assertEqual((records[0]['files'],records[0]['bytes']),(2,20));self.assertGreaterEqual(records[0]['elapsed_seconds'],0)
    def test_source_walk_is_not_pruned_by_diagnostics(self):
        package=self.root/'formal/.lake/packages/pkg/deep';package.mkdir(parents=True);(package/'data').write_bytes(b'data')
        err=io.StringIO();m.enable_diagnostics(True)
        with contextlib.redirect_stderr(err):m.no_hidden_objects(self.root,[])
        end=next(r for r in self.records(err.getvalue()) if r['stage']=='hidden_objects' and r['event']=='end')
        self.assertGreater(end['package_entries_skipped'],0);self.assertGreaterEqual(end['visited'],end['package_entries_skipped'])

if __name__=='__main__':unittest.main()
