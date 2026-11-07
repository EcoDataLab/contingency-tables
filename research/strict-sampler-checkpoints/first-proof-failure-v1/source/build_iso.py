"""Create/read back a local cloud-init ISO; never launches or contacts a host."""
from pathlib import Path
import hashlib,io,json,pycdlib
D=Path(__file__).resolve().parent;S=D/'seed-source';I=D/'strict-proof01.iso'
assert not I.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=json.loads((S/'seed-source-manifest.json').read_text())
for name in ('versioned_runner.py','anchored_metadata.py','guest_entry.py','authenticate_runtime.py','install_sources.py','seed_media.py'):
 remote={'guard_benchmark.py':'/home/verifier/checking/.tools/linux-verification/guard-benchmark.py','versioned_runner.py':'/home/verifier/checking/.tools/linux-verification/anchored-guard-v2/strict_sampler.py','anchored_metadata.py':'/home/verifier/checking/.tools/linux-verification/anchored-guard-v2/anchored_metadata.py','guest_entry.py':'/home/verifier/checkpoint11-entry.py','authenticate_runtime.py':'/home/verifier/checkpoint11-authenticate.py','install_sources.py':'/home/verifier/checkpoint11-install.py','seed_media.py':'/home/verifier/checkpoint11-seed-media.py'}[name]
 assert m['inline_sha256'][remote]==sha(D/name),'Stale generated seed body: '+name
iso=pycdlib.PyCdlib();iso.new(interchange_level=3,joliet=3,rock_ridge='1.09',vol_ident='cidata')
names={'meta-data':'/META_DAT.;1','user-data':'/USER_DAT.;1','sources.gz':'/SOURCES.GZ;1'}
for name,iso_name in names.items():iso.add_file(str(S/name),iso_path=iso_name,joliet_path='/'+name,rr_name=name)
iso.write(str(I));iso.close()
check=pycdlib.PyCdlib();check.open(str(I))
for name in names:
 data=io.BytesIO();check.get_file_from_iso_fp(data,joliet_path='/'+name)
 assert data.getvalue()==(S/name).read_bytes()
check.close()
m.update(iso_sha256=sha(I),iso_bytes=I.stat().st_size,supervisor_sha256=sha(D/'vm_sampler_supervisor.py'),anchored_helper_sha256=sha(D/'anchored_metadata.py'),candidate_runner_sha256=sha(D/'versioned_runner.py'),acceleration='whpx,kernel-irqchip=off',scope='install/preflight/authenticate/original authentication/versioned cold bounded execute/collect; no execute',source_controls_authorized_by_root=True,actual_iso_readback=True)
(D/'strict-proof01.manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
files=[dict(path=name,bytes=(D/name).stat().st_size,sha256=sha(D/name)) for name in ('vm_sampler_supervisor.py','strict-proof01.iso','strict-proof01.manifest.json')]
(D/'staging-manifest.json').write_text(json.dumps(dict(files=files,unchanged_archive_and_authenticator=True,actual_iso_readback=True),indent=2)+'\n')
print(json.dumps(dict(iso_sha256=sha(I),iso_bytes=I.stat().st_size,all_three_members_exact=True),indent=2))
