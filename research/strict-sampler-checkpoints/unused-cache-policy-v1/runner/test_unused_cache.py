"""Focused offline absence/state cases; no actual Git/service/compiler execution."""
import copy
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
import test_strict_sampler as core
m,serial=core.m,core.serial

class CacheStateTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve()
        self.policy=m.read(core.HERE.parent/'unused-cache-policy-candidate.json')
        self.roots=[m.PREFIX+'/lib/lean',m.CLI_CACHE,'formal/.lake/packages/mathlib/.lake/build/lib/lean']
        for name in self.roots:
            if name!=m.CLI_CACHE:(self.root/name).mkdir(parents=True)
        self.parent=self.root/'formal/.lake/packages/Cli';self.parent.mkdir()
        self.owners=['<toolchain>','mathlib']
        self.states=m.cache_root_states(self.root,self.roots,self.owners,self.policy)
    def guard(self):
        return m.Guard(self.root,{},{},{},serial,cache_roots=self.roots,cache_states=self.states,external_owners=self.owners,unused_cache_policy=self.policy)
    def test_exact_unused_absent_ancestor_and_present_roots_pass(self):
        self.assertEqual(self.states[m.CLI_CACHE]['first_missing'],m.CLI_ABSENT)
        self.assertEqual(set(self.states),set(self.roots))
        self.assertEqual(m.cache_inventory(self.root,self.roots,self.states),{})
        self.guard().check()
        self.assertFalse((self.parent/'.lake').exists())
    def test_required_Cli_owner_rejects_even_valid_absence(self):
        with self.assertRaisesRegex(m.Reject,'required source owner'):
            m.cache_root_states(self.root,self.roots,['Cli'],self.policy)
    def test_another_missing_root_rejected(self):
        (self.root/self.roots[0]).rmdir()
        with self.assertRaisesRegex(m.Reject,'Unexpected missing'):
            m.cache_root_states(self.root,self.roots,self.owners,self.policy)
    def test_missing_Cli_package_parent_rejected(self):
        self.parent.rmdir()
        with self.assertRaisesRegex(m.Reject,'Unexpected missing'):
            m.cache_root_states(self.root,self.roots,self.owners,self.policy)
    def test_file_at_absent_ancestor_rejected(self):
        (self.parent/'.lake').write_bytes(b'ordinary file')
        with self.assertRaises(m.Reject):self.guard().check()
    def test_dangling_or_existing_symlink_at_absent_ancestor_rejected(self):
        link=self.parent/'.lake'
        for target in (self.root/'missing-target',self.root/self.roots[0]):
            link.symlink_to(target)
            with self.assertRaises(m.Reject):self.guard().check()
            link.unlink()
    def test_symlinked_source_parent_rejected(self):
        moved=self.parent.with_name('old-Cli');self.parent.rename(moved);self.parent.symlink_to(moved)
        with self.assertRaises(m.Reject):self.guard().check()
    def test_new_empty_lake_presence_rejected(self):
        (self.parent/'.lake').mkdir()
        with self.assertRaises(m.Reject):self.guard().check()
    def test_complete_new_Cli_cache_presence_rejected(self):
        (self.root/m.CLI_CACHE).mkdir(parents=True)
        with self.assertRaises(m.Reject):self.guard().check()
    def test_create_remove_cycle_parent_ctime_catches_drift(self):
        g=self.guard();old=self.parent.stat();(self.parent/'.lake').mkdir();(self.parent/'.lake').rmdir()
        os.utime(self.parent,ns=(old.st_atime_ns,old.st_mtime_ns))
        with self.assertRaisesRegex(m.Reject,'identity drift'):g.check()
    def test_replaced_parent_same_absence_rejected(self):
        self.parent.rename(self.parent.with_name('old-Cli'));self.parent.mkdir()
        with self.assertRaisesRegex(m.Reject,'identity drift'):self.guard().check()
    def test_parent_mode_drift_rejected(self):
        self.parent.chmod(0o700)
        with self.assertRaisesRegex(m.Reject,'identity drift'):self.guard().check()
    def test_present_empty_root_identity_drift_rejected(self):
        p=self.root/self.roots[0];p.rename(p.with_name('old-lean'));p.mkdir()
        with self.assertRaisesRegex(m.Reject,'identity drift'):self.guard().check()
    def test_wrong_extra_or_boolean_state_fields_rejected(self):
        for mutate in (lambda x:x.pop(m.CLI_CACHE),lambda x:x.update({'unknown':{}}),
                       lambda x:x[m.CLI_CACHE].update(state='directory'),
                       lambda x:x[m.CLI_CACHE].update(extra=True),
                       lambda x:x[m.CLI_CACHE]['parent_identity'].update(uid=False)):
            states=copy.deepcopy(self.states);mutate(states)
            with self.assertRaises(m.Reject):m.validate_cache_state_shapes(states,self.roots)
    def test_broadened_absence_policy_rejected(self):
        p=copy.deepcopy(self.policy);p['allowed_absence'][self.roots[0]]=p['allowed_absence'][m.CLI_CACHE]
        with self.assertRaises(m.Reject):m.cache_root_states(self.root,self.roots,self.owners,p)
    def test_cache_walk_permission_error_not_skipped(self):
        with patch.object(m.os,'scandir',side_effect=PermissionError('denied')):
            with self.assertRaises(PermissionError):m.cache_inventory(self.root,self.roots,self.states)
    def test_cache_symlink_leaf_rejected(self):
        (self.root/self.roots[0]/'bad.olean').symlink_to(self.root/'outside')
        with self.assertRaises(m.Reject):m.cache_inventory(self.root,self.roots,self.states)
    def test_direct_source_object_missing_or_ambiguous_still_rejects(self):
        package=self.root/'formal/.lake/packages/mathlib';source=package/'Mathlib/Foo.lean';source.parent.mkdir();source.write_bytes(b'-- source')
        freeze={'external_imports':['Mathlib.Foo']};packages={'mathlib':(package,{'Mathlib/Foo.lean'})}
        with self.assertRaisesRegex(m.Reject,'object missing'):m.resolve_external_imports(self.root,freeze,packages)
        obj=package/'.lake/build/lib/lean/Mathlib/Foo.olean';obj.parent.mkdir();obj.write_bytes(b'object')
        external,_,owners=m.resolve_external_imports(self.root,freeze,packages)
        self.assertEqual(owners,['mathlib']);self.assertEqual(external['Mathlib.Foo']['source'],'formal/.lake/packages/mathlib/Mathlib/Foo.lean')
        builtin=self.root/m.PREFIX/'lib/lean/Mathlib/Foo.olean';builtin.parent.mkdir();builtin.write_bytes(b'also object')
        with self.assertRaisesRegex(m.Reject,'ambiguous'):m.resolve_external_imports(self.root,freeze,packages)

class AdmissionStateTests(unittest.TestCase):
    def setUp(self):
        self.case=core.FullAdmissionTests('test_complete_admission_with_synthetic_runtime_and_real_source_graph')
        self.case.setUp()
        def cleanup():
            try:self.case.tearDown()
            finally:self.case.doCleanups()
        self.addCleanup(cleanup)
    def test_full_679_admission_exact_absence_and82_required_objects_pass(self):
        modules,g,_,roots=self.case.admit();self.assertEqual(len(modules),679);self.assertEqual(len(roots),10)
        self.assertEqual(self.case.runtime['external_import_owners'],['<toolchain>','mathlib']);g.check()
        self.assertEqual(len(self.case.runtime['external_import_resolution']),82)
    def test_old_or_mixed_runtime_schema_rejected(self):
        for change in ({'schema_version':1},{'legacy_absent_cache_roots':[]},{'schema_version':True}):
            original=copy.deepcopy(self.case.runtime);self.case.runtime.update(change)
            with self.assertRaisesRegex(m.Reject,'Mixed/old'):self.case.admit()
            self.case.runtime=original
    def test_runtime_owner_claim_cannot_override_rederived_set(self):
        self.case.runtime['external_import_owners']=[]
        with self.assertRaisesRegex(m.Reject,'owner set changed'):self.case.admit()
    def test_required_Cli_source_owner_not_masked_by_unused_claim(self):
        name='Init';rel='Init.lean';self.case.tracked['Cli'].append(rel)
        self.case.put('formal/.lake/packages/Cli/'+rel,b'-- conflicting owner')
        with self.assertRaisesRegex(m.Reject,'object missing'):self.case.admit()
    def test_missing_selected_required_object_rejected(self):
        name=next(x for x in self.case.runtime['external_import_resolution'] if x.startswith('Mathlib.'))
        (self.case.root/self.case.runtime['external_import_resolution'][name]['olean']).unlink()
        with self.assertRaisesRegex(m.Reject,'object missing'):self.case.admit()
    def test_changed_selected_object_rejected_by_guard(self):
        _,g,_,_=self.case.admit()
        name=next(x for x in self.case.runtime['external_import_resolution'] if x.startswith('Mathlib.'))
        (self.case.root/self.case.runtime['external_import_resolution'][name]['olean']).write_bytes(b'changed')
        with self.assertRaises(m.Reject):g.check(rehash=True)
    def test_policy_byte_change_rejected_before_state_use(self):
        self.case.policy_file.write_bytes(self.case.policy_file.read_bytes()+b' ')
        with self.assertRaisesRegex(m.Reject,'policy file/SHA'):self.case.admit()
    def test_policy_mutation_after_admission_rejected(self):
        _,g,_,_=self.case.admit();self.case.policy_file.write_bytes(self.case.policy_file.read_bytes()+b' ')
        with self.assertRaises(m.Reject):g.check()
    def test_absence_drift_before_or_after_owned_stage_guard_rejected(self):
        _,g,_,_=self.case.admit();g.check();(self.case.root/m.CLI_ABSENT).mkdir()
        with self.assertRaises(m.Reject):g.check()
    def test_hidden_submitted_object_still_rejected(self):
        self.case.put('formal/.lake/build/lib/lean/Math115/Bad.olean',b'untrusted proof')
        with self.assertRaises(m.Reject):self.case.admit()

if __name__=='__main__':unittest.main()
