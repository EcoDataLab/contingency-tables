# Native Windows verification

On 2026-10-08, a fresh native Windows checkout of public commit
[`b14082b286b99d0b1ef84efcf59e4d202493d16b`](https://github.com/EcoDataLab/contingency-tables/tree/b14082b286b99d0b1ef84efcf59e4d202493d16b)
passed all 128 Python tests, replayed the saved cycle-mixture certificates,
and compiled the complete focused Lean closure. All 68 audited declarations
passed the printed-axiom allowlist. The project-owned machine runs Windows 11
Pro on x86-64. This run was performed by the same AI-assisted project
workflow; no outsider reproduction is recorded. The numerical checks used only Python's standard library.

| Check | Result |
|---|---:|
| Unit tests | 128 passed |
| Exact gap intervals | 8 verified |
| Exact bounds for every allowed fixed mixture | 4 verified |
| Strict gap comparisons | 6 verified |
| Checkout files compared with their committed Git blob hashes | 109 verified |
| Original handoff bundle SHA256 values | 5 verified |
| Pinned public upstream Git blob hashes | 38 verified |
| Source SHA256 references in saved reports | 51 verified |
| Freshly compiled project modules | 100 passed: 86 original, 14 refinements |
| Printed-axiom audit | 68 passed: 62 focused, 6 standalone |
| Compiled source files checked against their pinned Git blobs | 100 verified |
| Canonical retained log files checked against recorded SHA256 | 125 verified |

The source references can repeat a file across reports. Certificate replay
reconstructs the finite fiber and kernels, checks source and fixture hashes,
and verifies the saved rational inequalities. It does not repeat or rely on
the floating-point optimization that proposed the certificates. See
[the certificate methodology](cycle-mixtures.md).

The initial checkout used the machine's default CRLF conversion. The fixture
hash check rejected those changed bytes. Restoring the exact Git archive bytes
and setting `core.autocrlf=false` **only in the isolated research checkout**
resolved the mismatch. The completed checks above used the restored checkout,
with every project Git blob hash verified and the index tree matching the
published commit. This is a useful distinction between equivalent text and
the exact bytes used by a reproducibility certificate.

## Portable tools and source pins

Python 3.14.8 came from the [official Windows release manifest](https://www.python.org/ftp/python/3.14.8/windows-3.14.8.json).
The portable `python-3.14.8-amd64.zip` archive's SHA256 was checked before
extraction:

```text
4873947a8afc037846b180312b83c744a4146a851cfd316a75c3125a4d8299da
```

Lean 4.34.1 came from the [official release](https://github.com/leanprover/lean4/releases/tag/v4.34.1).
The `lean-4.34.1-windows.tar.zst` archive matched the SHA256 digest in the
official release API:

```text
667394ecf6708a228221eb4919c0bdb419966b7408bcf3089a9096a6f4ae62c9
```

The native executable reports Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`; Lake reports
`5.0.0-src+5045d00`. A small `import Std` proof compiled successfully to an
`.olean` file. Both distributions were extracted into a dedicated research
directory. Command search paths and thread settings are process scoped;
no global profile, system configuration, WSL installation, administrator
action, reboot, or interruption of other user processes was required.

The original OpenAI source remains pinned at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, and Mathlib remains pinned at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The remaining dependency revisions
come directly from the committed `formal/lake-manifest.json`. All nine package
checkouts and the OpenAI checkout have been checked against those pins;
`lake update` was not run.

## Lean verification result

The native dependency bootstrap passed: 19 cache-tool source modules compiled,
and the official Mathlib cache download and extraction completed successfully.
The focused project build passed on 2026-10-08. Its dependency closure contains
86 original OpenAI modules and 14 refinement modules, including the `Math115`
aggregate module. Each module compiled freshly on Windows in dependency order,
one module at a time, with `LEAN_NUM_THREADS=2`. The final readback verified
the fresh-build records, all 100 resulting `.olean` files, all compiled source
Git blobs, the unchanged 109-file project checkout, and every dependency pin.

The 68 declarations are split between `AxiomAudit.lean` (62) and
`StandaloneAxiomAudit.lean` (6). Together they cover 66 new declarations and
two original baseline declarations. The checker matched every reported
declaration name to its unchanged audit source and permitted only `propext`,
`Classical.choice`, and `Quot.sound`. The initial receipt wrapper expected the
combined count in one audit file; the corrected wrapper checked both files.
No Lean proof or dependency source changed to resolve that bookkeeping error.

The official Mathlib artifact cache is a trusted input, as in the existing
verification workflow. This run does not include the full original theorem
closure, the strict Linux Comparator sandbox, or a separate kernel replay.

The machine-readable [verification receipt](../formal/results/thor-verification.json)
records tool checksums, source and dependency revisions, test counts,
certificate results, source and artifact hashes, and completed Lean results.
Durations in that receipt describe this verification run; they are not
cross-platform performance comparisons.

## Repeating the checks

In a checkout preserving committed LF bytes, use a verified Python interpreter
and a process-scoped import path:

```powershell
$env:PYTHONPATH = Join-Path (Get-Location) 'src'
$env:PYTHONUTF8 = '1'
python -m unittest discover -s tests -v
python experiments/cycle_mixtures.py --replay reports/cycle-mixtures.json
python scripts/verify_sources.py
```

Use an explicit portable interpreter path when `python` resolves to the
Microsoft Store alias. The exact certificate replay requires no NumPy
installation.

For the native Lean run, prepare the pinned source checkouts and official
Mathlib cache first. The receipt contains the exact dependency revisions and
an ordered module list. Save the receipt outside the checkout before selecting
the tested commit: the receipt itself was added afterward. With `$receiptPath`
set to that saved copy and `$lake` set to the verified portable Lake executable,
the project-build sequence is:

```powershell
$receipt = Get-Content $receiptPath -Raw | ConvertFrom-Json
$env:LEAN_NUM_THREADS = '2'
$env:MATHLIB_CACHE_DIR = Join-Path (Get-Location) '.tools/mathlib-cache'
$env:PATH = (Split-Path $lake) + [IO.Path]::PathSeparator + $env:PATH
Set-Location formal
foreach ($module in $receipt.lean_verification.plan.focused_compile_order) {
  & $lake --no-ansi build ('+' + $module)
  if ($LASTEXITCODE -ne 0) { throw ('Build failed: ' + $module) }
}
$auditCounts = [ordered]@{
  'Math115/AxiomAudit.lean' = 62
  'Math115/StandaloneAxiomAudit.lean' = 6
}
foreach ($auditFile in $auditCounts.Keys) {
  $audit = & $lake env lean $auditFile
  if ($LASTEXITCODE -ne 0) { throw 'Axiom audit did not compile' }
  $axiomReports = [regex]::Matches(($audit -join "`n"),
    'depends on axioms:\s*\[([^]]*)\]')
  if ($axiomReports.Count -ne $auditCounts[$auditFile]) {
    throw 'Unexpected audited declaration count'
  }
  foreach ($axiomReport in $axiomReports) {
    foreach ($axiom in ($axiomReport.Groups[1].Value -split ',')) {
      $axiomName = $axiom.Trim()
      if ($axiomName -and
          $axiomName -notin @('propext', 'Classical.choice', 'Quot.sound')) {
        throw ('Unexpected axiom: ' + $axiomName)
      }
    }
  }
}
```

This sequence applies to the stated checkpoint. Later checkpoints may have
different source closures and audit counts. The stored log digests refer to
UTF-8 text with LF line endings and research-directory paths replaced by
`<workspace>` or `<research>`.
