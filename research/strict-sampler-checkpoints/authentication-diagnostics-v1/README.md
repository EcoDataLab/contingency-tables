# Authentication diagnostics: startup03 timeout

Startup03 installed the exact diagnostic-enabled source and passed real strict sandbox preflight. Authentication then timed out at **1800 seconds during a partial third full cache rehash**. Two cache inventories completed as substeps, but no runtime freeze or plan was produced. No full submitted proof loading, export, default-kernel replay or Comparator comparison ran.

The [earlier 600-second timeout](../unused-cache-policy-v1/README.md) remains immutable. This successor adds opt-in progress logging and preserves all validation predicates, inventories, hash passes and the narrow Cli policy. It does not establish overall runtime/policy acceptance or a numerical sampler runtime degree.

## Observed progress

The complete [authentication stderr](evidence/startup/authenticate.stderr.log) contains **1050 `STRICT_AUTH_PROGRESS=` JSON records and zero other lines**. No warnings or traceback text was discarded. [Authentication stdout](evidence/startup/authenticate.stdout.log) is empty; [failure framing](evidence/startup/failure.json) preserves the 1800-second deadline. No authentication return code or measured phase-elapsed field was recorded. [Installation](evidence/startup/install.stdout.log) passed in 9.685 seconds and [preflight](evidence/startup/preflight.stdout.log) in 3.602 seconds, with non-root/zero-capability probes and Landlock ABI 11.

| Wrapper interval | Begin cumulative seconds | End cumulative seconds | Difference |
| --- | ---: | ---: | ---: |
| Collection cache inventory | 171.128 | 507.405 | 336.277 s |
| Independent cache inventory | 645.239 | 896.742 | 251.503 s |
| Independent inventory end to full guard begin | 896.742 | 1631.080 | 734.338 s |

These are cumulative timestamps; 507.405 and 896.742 are **not durations**. Wrapper markers are distinguished from slightly different inner markers. The 734.338-second interval maps to accepted runner lines 626–631, across cache metadata/stat snapshot and Guard construction. Individual call cost, CPU, physical I/O and a causal bottleneck were not measured.

Each completed inventory reported 131021 regular files and 9261675188 completed **logical file bytes** across nine present roots, with nominated Cli absence. Configuration, policy and 82 direct source/object resolution checks emitted substep-end records. Those observations do not become a complete transitive external-cache audit or overall runtime acceptance.

At cumulative 1798.730 seconds, the last heartbeat reports `guard_cache`, `rehash:true`, **27257 aggregate files and 3427131951 logical bytes**, with Mathlib current. The aggregate includes preceding roots and partial Mathlib; it is not a completed Mathlib total or physical throughput. No guard-cache/full-guard/admission end or runtime-emitted event followed. [Diagnostic interpretation](diagnostic-interpretation.json), the [original owner summary projection](evidence/owner-diagnostic-summary.json) and [independent AI readback](evidence/independent-review.md) preserve these distinctions.

[Outcome](evidence/startup/outcome.json), [cleanup](evidence/startup/cleanup.json), [verification](verification.json) and [provenance](provenance-bindings.json) bind all 30 sealed capture members, seven downloaded host files and nine regular guest archive members. Owned processes/transports closed and all five retained pins matched. The remote-only child disk is a metadata pin, not supplied or locally rehashed bytes. Full raw serial/QMP/host control data remain private. [Projection mappings](projection-map.json) bind original/public bytes and declared path substitutions; complete relevant streams remain intact.

## Exact minimal source delta

[Runner](delta/runner/strict_sampler.py) SHA `4ba0a3c42bee4f511909fc50ad33b00be2a5cc3cabecdd2b54ac08ec7970d1a6`, [authenticator](delta/runner/authenticate_runtime.py) SHA `742ec1105d5bb44a392046ec06ca5944a20989bc0cb5a037d2997b37def2b943`, [six new tests](delta/runner/test_progress.py) and [patch](delta/implementation.patch) are exact reviewed bodies. [Base references](base-reference.json) pin ten unchanged fixtures/support/policy files in the preceding packet, avoiding duplicate large source-freeze/source-plan JSON.

Both `--diagnostics` flags are opt-in; imported/default mode stays quiet. Progress uses existing stderr, while stdout success markers and runtime construction are unchanged. Heartbeats occur after completed checks; large existing files have markers around the unchanged digest. `rehash:false` counters represent stat-checked file sizes, not newly hashed bytes. Logging does not prune, memoize, skip hashes or swallow failures; a failing stderr sink remains an operational error.

Historical source tests passed 108 cases (102 unchanged plus six diagnostic cases). An additional local run exercised the exact proposed base-plus-delta layout: **108 tests passed in 33.883 seconds**, with its [receipt](evidence/proposed-layout-tests.json). That is actual local proposed-layout testing, distinct from a final public clone or live admission. Packaging did not repeat the suite; reconstructed source/test/support bytes are compared to the tested layout. The prior source/helper native evidence, full ten-root state/present-cache inventories, exact Cli absence, source-owner/cold-proof/configuration/sandbox/kernel conditions remain unchanged.

The delivered startup ceilings were auth **1800**, plan **1200**, outer **6000** seconds, retaining **4 CPU/8192 MiB/no NIC/no swap**. Plan was not executed. The earlier source recommendation of 5400 seconds remains historical, not the delivered outer cap. No automatic retry or larger profile follows from the timeout. Official caches and sealed retained context remain explicit trust inputs; the exact image and portable full-workload Linux outer environment are not supplied or exactly externally reproducible.

## Executable copy/verify/materialize recipe

Location: `research/strict-sampler-checkpoints/authentication-diagnostics-v1/`. Bootstrap pinned sources for offline fixtures as usual. Supply `DELTA_MANIFEST_SHA` from `packet_manifest_sha256` in the [publication review](../authentication-diagnostics-v1-review.json); the recipe verifies that manifest, every base/delta member, all ten pinned references and each replacement before writing a fresh tree. It preserves the already-used `.local/reproduction/auth-diagnostics` tree.

```sh
# From the repository root; DELTA_MANIFEST_SHA is the independently recorded release hash.
: "${DELTA_MANIFEST_SHA:?Set the separately verified diagnostic packet manifest SHA256}"
BASE="$PWD/research/strict-sampler-checkpoints/unused-cache-policy-v1"
DELTA="$PWD/research/strict-sampler-checkpoints/authentication-diagnostics-v1"
TEST_TREE="$PWD/.local/reproduction/auth-diagnostics-public"
python3 -B - "$BASE" "$DELTA" "$TEST_TREE" "$DELTA_MANIFEST_SHA" <<'PYCODE'
import hashlib,json,pathlib,re,shutil,sys
base,delta,out=map(pathlib.Path,sys.argv[1:4]);release=sys.argv[4]
sha=lambda b:hashlib.sha256(b).hexdigest()
def file(root,name):
    rel=pathlib.PurePosixPath(name)
    if rel.is_absolute() or '..' in rel.parts: raise RuntimeError('Unsafe member')
    p=root/name
    if p.is_symlink() or not p.is_file() or not p.resolve().is_relative_to(root.resolve()):
        raise RuntimeError('Unsafe/missing member: '+name)
    return p

def verify(root,pin):
    raw=file(root,'manifest.json').read_bytes()
    if not re.fullmatch('[0-9a-f]{64}',pin) or sha(raw)!=pin:
        raise RuntimeError('Manifest differs')
    manifest=json.loads(raw)
    entries=manifest['files']
    entries=entries if isinstance(entries,list) else [{'path':n,**v} for n,v in entries.items()]
    for row in entries:
        data=file(root,row['path']).read_bytes()
        if sha(data)!=row['sha256'] or len(data)!=row['bytes']:
            raise RuntimeError('Member differs: '+row['path'])
    return {row['path']:row['sha256'] for row in entries}

delta_files=verify(delta,release)
refs=json.loads(file(delta,'base-reference.json').read_text())
verify(base,refs['manifest_sha256'])
for name,pin in refs['unchanged_members_sha256'].items():
    if sha(file(base,name).read_bytes())!=pin: raise RuntimeError('Base reference differs')
if out.exists(): raise RuntimeError('Output already exists')
out.mkdir(parents=True)
for name in refs['unchanged_members_sha256']:
    dest=out/name;dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(file(base,name),dest)
for name in ('strict_sampler.py','authenticate_runtime.py','test_progress.py'):
    member='delta/runner/'+name;dest=out/'runner'/name
    data=file(delta,member).read_bytes()
    if sha(data)!=delta_files[member]: raise RuntimeError('Delta differs')
    dest.write_bytes(data)
print('Verified and materialized source/test/policy assets only; no runtime admission.')
PYCODE
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover \
  -s "$TEST_TREE/runner" -p 'test_*.py' -v
```

The verification/materialization code was exercised locally without rerunning tests, and all reconstructed assets match the previously tested layout. The final test command is a contributor instruction, not a new suite run in this projection. Materialization does not waive the adjacent source/support/policy freeze checks.

## Retained-context authentication and plan

Use the original dedicated cold checking source layout and independently bound configuration/policy inputs. Real non-root PAM/systemd/Landrun preflight, resource/ownership gates and durable outer supervision remain required. The actual authenticator flags included diagnostics; the prepared guest plan flags included diagnostics and `--wall-seconds 1200`:

```sh
python3 -I "$RUNNER/authenticate_runtime.py" --root "$CHECKOUT" \
  --runner "$RUNNER/strict_sampler.py" --output "$RUNTIME" \
  --native-audit "$NATIVE_AUDIT" \
  --lake-config-provenance "$CONFIG_PROVENANCE" \
  --lake-config-provenance-sha256 "$CONFIG_SHA" \
  --unused-cache-policy "$POLICY" --unused-cache-policy-sha256 "$POLICY_SHA" \
  --diagnostics
# Only after a real emitted runtime freeze; startup03 did not reach this command:
python3 -I "$RUNNER/strict_sampler.py" --root "$CHECKOUT" \
  --runtime-freeze "$RUNTIME" --runtime-freeze-sha256 "$RUNTIME_SHA" \
  --plan --wall-seconds 1200 --output "$PLAN_OUTPUT" --diagnostics
```

Complete progress is substep evidence, not permission to call an unfinished run successful. A later bounded performance diagnosis or retry must report its own source/caps/outcome, preserve this timeout and distinguish logical work from physical throughput. No subsequent result is assumed here.
