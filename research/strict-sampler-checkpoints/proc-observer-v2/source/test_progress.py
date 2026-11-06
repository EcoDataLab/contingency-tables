"""Offline owned-progress/phase checks; no cache, compiler or VM."""
from pathlib import Path
import contextlib,importlib.util,io,json,tempfile,unittest
from unittest.mock import patch
D=Path(__file__).resolve().parent
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
guest=load('proof_guest_progress_fixture',D/'guest_entry.py');vm=load('proof_supervisor_progress_fixture',D/'vm_sampler_supervisor.py')
class Progress(unittest.TestCase):
 def test_owned_receipt_progress_is_telemetry_not_acceptance(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);out=root/'proof-output';out.mkdir();(out/'receipt.json').write_text(json.dumps({'commands':[{'stage':'0000_module_build','status':'passed'},{'stage':'0001_dependencies_current','status':'running'}]}))
   buffer=io.StringIO()
   with patch.object(guest,'EVIDENCE',root),contextlib.redirect_stdout(buffer):row=guest.proof_progress(None);self.assertEqual(guest.proof_progress(row),row)
   self.assertEqual(row['completed_modules'],1);self.assertEqual(row['completed_stages'],1)
   state={};vm.parse_tail(('MATH115_C11_STAGE=proof\n'+buffer.getvalue()).encode(),state)
   self.assertEqual(state['guest_phase'],'proof');self.assertEqual(state['proof_progress']['completed_modules'],1)
   self.assertNotIn('strict_exit_code',state);self.assertEqual(len((root/'proof-progress.jsonl').read_text().splitlines()),1)
 def test_partial_json_keeps_prior_observation(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);(root/'proof-output').mkdir();(root/'proof-output/receipt.json').write_text('{')
   prior={'completed_modules':1}
   with patch.object(guest,'EVIDENCE',root):self.assertEqual(guest.proof_progress(prior),prior)
 def test_invalid_progress_fails_closed_and_resources_consistent(self):
  with self.assertRaises(vm.SupervisorError):vm.parse_tail(b'MATH115_C11_PROOF_PROGRESS={"completed_modules":680,"completed_stages":1,"last_stage":"x","last_status":"running"}\n',{})
  self.assertEqual(vm.PHASE_CAPS,guest.CAPS);self.assertEqual(vm.PHASE_CAPS['proof'],8100)
if __name__=='__main__':unittest.main()
