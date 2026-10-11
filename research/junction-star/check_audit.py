"""Check this helper's focused actual-environment audit, not a new build runner."""
import gzip, json, pathlib, sys

packet = pathlib.Path(__file__).resolve().parent
audit_path = pathlib.Path(sys.argv[1])
actual = json.loads(gzip.decompress(audit_path.read_bytes()) if audit_path.suffix == '.gz'
                    else audit_path.read_text())
expected = json.loads((packet/'results/declarations.json').read_text())
assert actual['declaration_count'] == 23 and actual['theorem_count'] == 15
assert {d['name']: d['statement'] for d in actual['declarations']} == {
    d['name']: d['statement'] for d in expected}, 'Owned exact type mismatch'
names = {h['name'] for h in actual['headlines']}
assert names == {h['name'] for h in json.loads((packet/'results/verification.json').read_text())['headlines']}
for declaration in actual['declarations']:
    assert not declaration['nonstandard_axioms'], declaration['name']
for headline in actual['headlines']:
    assert set(headline['closure']) == {d['name'] for d in headline['declarations']}
    for declaration in headline['declarations']:
        assert not declaration['nonstandard_axioms'], declaration['name']
print('Finite JunctionStarBridge exact types and five standard-axiom closures passed.')
