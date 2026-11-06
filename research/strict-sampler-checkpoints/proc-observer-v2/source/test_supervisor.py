"""Inherited offline supervision mocks only; no Git/VM/compiler actions."""
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
def load(name,file):
    spec=importlib.util.spec_from_file_location(name,HERE/file);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
vm=load('c11_vm_tests','vm_sampler_supervisor.py')
installer=load('c11_install_tests','install_sources.py')

class SupervisorTests(unittest.TestCase):
    def test_fixed_profile_private_drives_and_no_forwarding(self):
        a=vm.qemu_argv(Path('retained'),Path('seed'),Path('owned'))
        self.assertEqual(a[a.index('-m')+1],'10240');self.assertEqual(a[a.index('-smp')+1],'1')
        self.assertEqual(a[a.index('-nic')+1],'none')
        self.assertNotIn('hostfwd',' '.join(a))
        for flag in ['-virtfs','-fsdev','-netdev','-qmp']:self.assertNotIn(flag,a)
        self.assertEqual(a[a.index('-accel')+1],'whpx,kernel-irqchip=off');self.assertEqual(vm.CAP,12600);self.assertEqual(vm.COMMAND,b'bash /home/verifier/checkpoint11-start.sh\r\n')
    def test_real_logger_prefix_and_bounded_tail(self):
        s={};tail=vm.parse_tail(b'x'*vm.TAIL_LIMIT+b'\n[ 58.19] cloud-init[1048]: MATH115_C11_PROVISION_READY\nverifier@strict-comparator-guest:~$ ',s)
        self.assertTrue(s['guest_provisioning_ready']);self.assertTrue(s['normal_verifier_console_prompt_observed']);self.assertLessEqual(len(tail),vm.TAIL_LIMIT)
    def test_incomplete_and_unrelated_markers_refused(self):
        for raw in [b'MATH115_C11_PROVISION_READY',b'prefix MATH115_C11_PROVISION_READY\n',b'[58] other[1]: MATH115_C11_PROVISION_READY\n']:
            s={};vm.parse_tail(raw,s);self.assertNotIn('guest_provisioning_ready',s)
    def test_result_and_runtime_hash_conflicts_fail_closed(self):
        with self.assertRaises(vm.SupervisorError):vm.parse_tail(b'MATH115_C11_CHECK_RESULT=0\nMATH115_C11_CHECK_RESULT=1\n',{})
        with self.assertRaises(vm.SupervisorError):vm.parse_tail(('MATH115_C11_RUNTIME_FREEZE_SHA256='+'a'*64+'\nMATH115_C11_RUNTIME_FREEZE_SHA256='+'b'*64+'\n').encode(),{})
    def test_phase_reparse_does_not_reset_watchdog(self):
        s={};raw=b'MATH115_C11_STAGE=install\nMATH115_C11_STAGE=authenticate\n'
        with mock.patch.object(vm.time,'monotonic',return_value=10):vm.parse_tail(raw,s)
        with mock.patch.object(vm.time,'monotonic',return_value=100):vm.parse_tail(raw,s)
        self.assertEqual(s['guest_phase_observed_monotonic'],10)
        with self.assertRaises(vm.SupervisorError):vm.parse_tail(b'MATH115_C11_STAGE=install\n',s)
    def test_pending_native_audit_rejects_before_any_image_or_process_action(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);seed=root/'seed.iso';seed.write_bytes(b'iso');seed.with_suffix('.manifest.json').write_text(json.dumps({'entrypoint_audit_status':'pending','iso_sha256':vm.digest(seed)}))
            with mock.patch.object(vm,'os',SimpleNamespace(name='nt')),mock.patch.object(vm,'check_files') as check,mock.patch.object(vm.subprocess,'run') as run:
                with self.assertRaisesRegex(vm.SupervisorError,'native audit'):vm.prepare(root,root/'new',seed,12)
            check.assert_not_called();run.assert_not_called()
    def test_kill_fallback_uses_only_held_owned_handle(self):
        child,other=mock.Mock(),mock.Mock();child.poll.return_value=None;child.wait.side_effect=[subprocess.TimeoutExpired('owned',15),137];state={}
        self.assertEqual(vm.stop_owned(child,state),137);child.terminate.assert_called_once();child.kill.assert_called_once();other.assert_not_called()
    def exercise(self,mode):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);(root/'overlay').write_bytes(b'child');config=root/'supervisor-config.json';config.write_text(json.dumps({'minimum_available_host_bytes':12*vm.GIB,'minimum_free_backing_disk_bytes':40*vm.GIB,'seed_sha256':'dummy'}))
            child=mock.Mock(pid=1730);child.stdin=io.BytesIO();child.wait.return_value=0
            child.poll.side_effect=[None,None,0,0] if mode in {'dispatch','drain_error'} else None
            if mode not in {'dispatch','drain_error'}:child.poll.return_value=None
            def spawn(*args,**kwargs):
                if mode in {'dispatch','drain_error'}:kwargs['stdout'].write(b'[58] cloud-init[1]: MATH115_C11_PROVISION_READY\nverifier@guest:~$ ');kwargs['stdout'].flush()
                return child
            tick=[31.0]
            with mock.patch.object(vm,'MAX_OWNED_OVERLAY',0 if mode=='overlay_growth' else 16*vm.GIB),mock.patch.object(vm,'os',SimpleNamespace(name='nt',getpid=lambda:1729)),mock.patch.object(vm,'validate_config',return_value=(root,root,root/'seed',root/'overlay')),mock.patch.object(vm,'available_memory',side_effect=[13*vm.GIB,int(1.25*vm.GIB)] if mode=='active_memory' else None,return_value=(11 if mode=='low_memory' else 13)*vm.GIB),mock.patch.object(vm.shutil,'disk_usage',side_effect=[SimpleNamespace(free=217*vm.GIB),SimpleNamespace(free=vm.GIB)] if mode=='active_disk' else None,return_value=SimpleNamespace(free=217*vm.GIB)),mock.patch.object(vm,'research_processes',return_value=[{'pid':99,'name':'lean.exe'}] if mode=='busy' else []),mock.patch.object(vm,'owned_identity',side_effect=RuntimeError('identity observer') if mode=='identity_error' else None,return_value={'pid':1730,'creation_utc':'mock','held_popen_handle':True}),mock.patch.object(vm,'process_memory',side_effect=RuntimeError('memory observer') if mode=='observer_error' else None,return_value={}),mock.patch.object(vm,'check_files',return_value=vm.EXPECTED),mock.patch.object(vm.subprocess,'Popen',side_effect=spawn) as popen,mock.patch.object(vm.time,'monotonic',side_effect=lambda:tick[0]),mock.patch.object(vm.time,'sleep',side_effect=lambda _:tick.__setitem__(0,tick[0]+vm.CAP-vm.CLEANUP_RESERVE) if mode=='cap' else None),mock.patch('builtins.print'):
                if mode in {'low_memory','busy'}:
                    with self.assertRaises(vm.SupervisorError):vm.supervise(config)
                    popen.assert_not_called();return
                self.assertEqual(vm.supervise(config),1)
            state=json.loads((root/'status.json').read_text())
            if mode=='dispatch':self.assertEqual(child.stdin.getvalue(),vm.COMMAND);self.assertEqual(state['status'],'vm_exited_without_complete_result')
            elif mode in {'active_memory','active_disk','overlay_growth'}:self.assertEqual(state['status'],'active_host_resource_floor_reached');child.terminate.assert_called_once();child.kill.assert_not_called()
            elif mode in {'identity_error','observer_error'}:self.assertEqual(state['status'],'supervisor_error');child.terminate.assert_called_once();self.assertTrue(state['owned_qemu_reaped'])
            else:self.assertEqual(state['status'],'timed_out');child.terminate.assert_called_once()
    def test_low_memory_spawns_nothing(self):self.exercise('low_memory')
    def test_existing_compiler_spawns_nothing(self):self.exercise('busy')
    def test_fixed_crlf_dispatch_once(self):self.exercise('dispatch')
    def test_owned_outer_cap_cleanup(self):self.exercise('cap')
    def test_active_low_host_memory_stops_only_owned_vm(self):self.exercise('active_memory')
    def test_active_low_backing_disk_stops_only_owned_vm(self):self.exercise('active_disk')
    def test_owned_overlay_growth_stops_only_owned_vm(self):self.exercise('overlay_growth')
    def test_versioned_disk_limits_and_unchanged_virtual_capacity(self):
        self.assertEqual(vm.MIN_BACKING_FREE,40*vm.GIB);self.assertEqual(vm.ACTIVE_DISK_FLOOR,20*vm.GIB);self.assertEqual(vm.MAX_OWNED_OVERLAY,16*vm.GIB);self.assertEqual(vm.RESOURCE_POLL_SECONDS,1)
        source=(HERE/'vm_sampler_supervisor.py').read_text();self.assertIn('str(overlay), "80G"',source);self.assertIn('child_chain[0]["virtual-size"] != 80 * GIB',source)
    def test_disk_profile_tampering_rejected_before_runtime_access(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);run=root/'run';run.mkdir();path=run/'supervisor-config.json'
            base=dict(retained_root=str(root),run_dir=str(run),wall_clock_cap_seconds=vm.CAP,guest_vcpus=1,guest_ram_mib=10240,phase_caps_seconds=vm.PHASE_CAPS,maximum_owned_overlay_bytes=vm.MAX_OWNED_OVERLAY,resource_poll_seconds=vm.RESOURCE_POLL_SECONDS,active_host_available_floor_bytes=vm.ACTIVE_MEMORY_FLOOR,active_backing_disk_floor_bytes=vm.ACTIVE_DISK_FLOOR)
            for key,value in [('maximum_owned_overlay_bytes',17*vm.GIB),('resource_poll_seconds',2),('active_backing_disk_floor_bytes',2*vm.GIB)]:
                with self.subTest(key=key),self.assertRaisesRegex(vm.SupervisorError,'profile changed|stop floors changed'):
                    vm.validate_config(dict(base,**{key:value}),path)
    def test_identity_observer_error_still_reaps_owned_vm(self):self.exercise('identity_error')
    def test_working_set_observer_error_still_reaps_owned_vm(self):self.exercise('observer_error')
    def test_terminal_drain_conflict_persists_failure_instead_of_stale_pass(self):
        original=vm.parse_tail;calls=[0]
        def broken(tail,state):
            calls[0]+=1
            if calls[0]>1:raise vm.SupervisorError('terminal conflict')
            return original(tail,state)
        # Direct stopped-process path has no loop parse and exercises the
        # final drain, including persistence rather than an escaping error.
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);(root/'overlay').write_bytes(b'child');config=root/'supervisor-config.json';config.write_text(json.dumps({'minimum_available_host_bytes':12*vm.GIB,'minimum_free_backing_disk_bytes':40*vm.GIB,'seed_sha256':'dummy'}))
            child=mock.Mock(pid=1730);child.poll.return_value=0;child.wait.return_value=0
            def spawn(*args,**kwargs):kwargs['stdout'].write(b'MATH115_C11_CHECK_RESULT=0\nMATH115_C11_CHECK_RESULT=1\n');kwargs['stdout'].flush();return child
            with mock.patch.object(vm,'os',SimpleNamespace(name='nt',getpid=lambda:1729)),mock.patch.object(vm,'validate_config',return_value=(root,root,root/'seed',root/'overlay')),mock.patch.object(vm,'available_memory',return_value=13*vm.GIB),mock.patch.object(vm.shutil,'disk_usage',return_value=SimpleNamespace(free=217*vm.GIB)),mock.patch.object(vm,'research_processes',return_value=[]),mock.patch.object(vm,'owned_identity',return_value={'pid':1730}),mock.patch.object(vm,'check_files',return_value=vm.EXPECTED),mock.patch.object(vm.subprocess,'Popen',side_effect=spawn),mock.patch('builtins.print'):
                self.assertEqual(vm.supervise(config),1)
            state=json.loads((root/'status.json').read_text());self.assertEqual(state['status'],'terminal_serial_drain_failed');self.assertTrue(state['owned_qemu_reaped'])

if __name__=='__main__':unittest.main()
