# Separate strict sampler challenge — strict acceptance pending

This corpus fixes the literal `Math115.PublicLatticeSampler.machine` while
checking the revised bounded sampler against the original input encoding,
`OutputsTable`, finite fair-bit `tableMass`, time and uniform-law definitions.
It does not replace the original upstream three-theorem descriptor.

The two selected goals deliberately cover different claims. `boundedSampling`
proves the original `Algorithms.BoundedSamplingStatement`, which existentially
chooses a machine. `fixedMachineBoundedSampling` expands the output/time/law
claim with `PublicLatticeSampler.machine` fixed. Both quantify one pair of
natural constants `C,d`, with `C>0`, before all dimensions, equal-total margins
and accuracy parameters `k>=1`. At the shared time `C*samplingSize^d`, every
finite bit tape produces a feasible table and total variation from the uniform
table law is at most `2^-k`.

This is a uniform existential polynomial theorem. Its construction uses
`d = 170 * P.natDegree` for an existential physical-compiler polynomial `P`;
neither 170 nor 17 is a complete explicit numeric degree. It does not establish
a numeric-degree comparison or practical runtime of the sampled machine.

Statement and Solution are separate modules with the same declaration names.
The Statement has exactly two intentional `sorry` theorem bodies. Solution has
none, imports the revised theorem and proves the fixed-machine goal using the
same construction. `definition_names: []` means no definitions are authorized
for replacement: Comparator's selected definitions would otherwise become
holes. All imported machine/encoding/law definitions remain fixed. Allowed
solution axioms are exactly `propext`, `Quot.sound`, `Classical.choice`.
`enable_nanoda` stays false; Lean's default kernel is still required.

The three files in `runner/tested-runtime/` are exact support bodies reused
from the measured tiny pipeline. They are imported as libraries; their older
original-baseline CLI is not used by this separate runner. The runner and
authenticator themselves have offline tests, not a full strict execution result.

Ordinary native Statement compilation, Solution compilation and a three-name
axiom audit passed. Exact source/audit bindings are in `native-audit.json` and
`evidence/`; the two included raw audit inputs are byte-identical, with their
mapping recorded in `evidence/native-checks.json`. No native compiled objects
are supplied. Creation-time source headers remain unchanged; these exact bytes
were retained through the later native and offline checks. **No strict
Linux build/export/kernel/Comparator success is claimed for this challenge.**

## Exact Linux checking inputs

Use a separate checkout at `fe72b20170e7f85e399368e56baf65b8782b4b50`
plus the thirteen public source overlays recorded by `runner/source-freeze.json`.
That freeze binds every source/import in the exact 679-module submitted closure,
the package revisions, original descriptor and configuration. Do not substitute
the moving default branch or an old descriptor. The unchanged public archive
under `formal/results/native-sampler-checkpoint/sources/Math115/` supplies the
overlay; this corpus does not duplicate the upstream or source trees.

| Input | Pin |
| --- | --- |
| Upstream | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Lean | 4.34.1, `5045d0056413266e57c625dcd7c365b10e377c52` |
| Comparator | `d03acab154d269c06e60e4de7e4cc85deebff94b` |
| Exporter | `076e8e57707e813375e8f9da8bf989799ace9680` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| Go | `go1.27.2` |

Use a normal non-root Linux x86_64 PAM session with the actual systemd user bus,
working Landlock/seccomp and Python 3.11+. Follow the existing
[Linux setup](../../docs/linux-verification.md),
[strict environment notes](../../docs/strict-comparator-vm.md) and
[measured tiny pipeline](../../formal/results/strict-comparator-smoke/README.md).
Comparator declares Lean 4.34.0 and is built unchanged with 4.34.1; this remains
an explicit patch-version trust boundary. Official toolchain/package caches
are trusted inputs, not rebuilt Mathlib proofs. Keep submitted objects absent
under every checking source/build tree; previous native or failed strict build
objects must not be reused.

Set `CHECKOUT` to that dedicated checking checkout and `HANDOFF` to this corpus
in a separate trusted source tree. Authenticate this corpus's manifest against
a separately recorded release hash first. Bootstrap commands are:

```bash
cd "$CHECKOUT"
bash scripts/bootstrap_comparator.sh preflight
bash scripts/bootstrap_lean.sh
bash scripts/bootstrap_comparator.sh bootstrap
```

Install the exact overlays and new roots with file operations only:

```bash
python3 -B - "$CHECKOUT" "$HANDOFF" <<'PY'
import hashlib,json,pathlib,shutil,sys
r,h=map(pathlib.Path,sys.argv[1:]); f=json.loads((h/'runner/source-freeze.json').read_text())
for dest,want in f['overlay_sha256'].items():
    src=r/'formal/results/native-sampler-checkpoint/sources'/pathlib.Path(dest).relative_to('formal')
    raw=src.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=want: raise RuntimeError('Overlay hash differs: '+dest)
    (r/dest).write_bytes(raw)
for name in ('StrictSamplerStatement.lean','StrictSamplerSolution.lean'):
    shutil.copyfile(h/name,r/'formal/Math115'/name)
tools=r/'.tools/linux-verification'; tools.mkdir(parents=True,exist_ok=True)
shutil.copytree(h/'runner',tools/'checkpoint11-runner')
inputs=tools/'strict-sampler-inputs'; inputs.mkdir()
for name in ('StrictSampler.json','native-audit.json'): shutil.copyfile(h/name,inputs/name)
PY
```

With unrelated writers/compilers excluded and actual strict preflight passed,
freeze the real runtime and admit the plan. The runtime template is deliberately
ineligible. Authentication records source/cache/config/tool resolution and
the two exact bootstrap executable symlinks, including link identity and target
bytes; generic symlinks and source/cache aliasing are refused.

```bash
bash -c 'source "$1" preflight; configure_paths; strict_landrun_probe' \
  strict-sampler-probe "$CHECKOUT/scripts/bootstrap_comparator.sh"
RUNNER="$CHECKOUT/.tools/linux-verification/checkpoint11-runner"
RUNTIME="$CHECKOUT/.tools/linux-verification/runtime-01.json"
python3 -I "$RUNNER/authenticate_runtime.py" --root "$CHECKOUT" \
  --runner "$RUNNER/strict_sampler.py" --output "$RUNTIME" \
  --native-audit "$CHECKOUT/.tools/linux-verification/strict-sampler-inputs/native-audit.json"
# Use the exact MATH115_C11_RUNTIME_FREEZE_SHA256 printed above as RUNTIME_SHA.
python3 -I "$RUNNER/strict_sampler.py" --root "$CHECKOUT" \
  --runtime-freeze "$RUNTIME" --runtime-freeze-sha256 "$RUNTIME_SHA" \
  --plan --output "$CHECKOUT/.tools/linux-verification/sampler-plan-01"
```

The inner execution command replaces `--plan` with
`--execute --wall-seconds 39600` and uses a new output directory. It retains
serial per-module deps/no-build and olean gates, strict sandbox checks, exact
root no-build validation, exporter, axiom/statement comparison and default
kernel acceptance. Every stage checks source/tool/configuration identity and
submitted artifact drift; caches are completely authenticated before and
after comparison. Compiler failures, incomplete telemetry, stale dependencies,
missing kernel evidence or changed inputs fail closed.

## Remaining replay gaps

The full strict workload is pending. The proposed standalone 8 GiB/four-CPU
profile is an unmeasured budget for this 679-module build; the passed 6 GiB tiny
fixture does not establish its sufficiency. The earlier original 4 GiB run
exhausted memory before comparison and remains preserved. Kernel `-M8192`
exhaustion in an earlier native proof is evidence of sensitivity, not observed
process RSS of 8 GiB. No memory widening follows automatically from a failure.

A compatible host needs reviewed durable outer supervision and owned cleanup,
covering admission, boot, preflight, guest execution and evidence collection.
The inner runner cap alone is insufficient. A portable Linux outer supervisor
has not been measured/published here; host-specific wrappers are excluded.
The exact retained vendor image's publicly retrievable dated URL also remains
unresolved; another compatible image is a new environment requiring measured
preflight and runtime authentication. Preserve raw logs, receipt, runtime hash,
resource/ownership/cleanup evidence and full acceptance messages before calling
any future run a strict success. The [first full-workload startup attempt](evidence/startup-timeout-2026-10-11.json)
reached its 600-second boot-admission deadline while cloud-init was still running.
The owned guest was stopped and reaped before any checker command was dispatched.
Its allowlisted outcome preserves the raw evidence digests; it establishes no
Lean, export, kernel or Comparator result. A smaller configuration transport is
being prepared. No completed strict-checking evidence mapping exists yet.
