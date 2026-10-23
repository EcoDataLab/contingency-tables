from pathlib import Path
import hashlib,json,sys,re
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
p=Path(__file__).resolve().parent;sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((p/'manifest.json').read_text())
for row in manifest['files']:assert sha(p/row['path'])==row['sha256'],row['path']
for row in json.loads((p/'compilation.json').read_text()):assert sha(p/row['source'])==row['source_sha256'] and row['returncode']==0
v=json.loads((p/'degree-values.json').read_text());k=max(int(v['unitDegree']),int(v['referenceDegree']));t=8*(1+k*(k+1))*k**5;d=340*max(1008,t)
assert str(t)==v['drawDegreeDecimal'] and str(d)==v['publicDegreeDecimal']
audit=(p/'evidence/final-readback.stdout.txt').read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)
assert len(reports)==5
assert all({x.strip() for x in terms.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,terms in reports)
print('PASS: packet bytes, five compiled source bindings, exact arithmetic and five standard-only axiom reports')
