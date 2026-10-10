#!/usr/bin/env python3
"""Run a compiled Lean environment audit with complete before/after input binding.

The module graph defines imported scope; theorem discovery comes exclusively
from the reviewed Lean environment helper. Receipts/logs are private until
separately projected/reviewed. Every attempt gets a new output directory.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import shutil
import subprocess
import sys
import time

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
HELPER_MODULE = 'ResearchAudit.EnvironmentAudit'
ARTIFACT_ENDINGS = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig', '.ilean', '.dll', '.so', '.dylib')


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def canonical_sha(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def save(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n', encoding='utf-8')


def strict_json(text: str):
    def no_duplicate_keys(pairs):
        d = {}
        for k, v in pairs:
            if k in d:
                raise ValueError(f'duplicate JSON key: {k}')
            d[k] = v
        return d
    return json.loads(text, object_pairs_hook=no_duplicate_keys,
                      parse_constant=lambda v: (_ for _ in ()).throw(ValueError(f'invalid JSON number: {v}')))


def names(values, label, allow_empty=False):
    if not isinstance(values, list) or (not allow_empty and not values):
        raise ValueError(f'{label}: expected nonempty name array')
    if len(values) != len(set(values)) or any(not isinstance(v, str) for v in values):
        raise ValueError(f'{label}: duplicate or invalid names')
    return values


def config_check(config: dict) -> None:
    if config.get('schema_version') != 1 or not config.get('scope'):
        raise ValueError('invalid runner schema/scope')
    for field in ('imports', 'prefixes', 'source_bound_prefixes', 'expected_modules', 'headlines'):
        for n in names(config[field], field, allow_empty=field == 'headlines'):
            if not NAME.fullmatch(n):
                raise ValueError(f'invalid Lean identifier: {n}')
    if not set(config['imports']) <= set(config['expected_modules']):
        raise ValueError('every root import must be expected')
    if HELPER_MODULE in config['expected_modules'] or any(n.startswith('ResearchAudit') for n in config['prefixes']):
        raise ValueError('helper instrumentation cannot be project scope')
    if not isinstance(config.get('compiler_version'), str) or not config['compiler_version']:
        raise ValueError('missing expected compiler version')
    if not config.get('lean_path') or not config.get('pins') or not config.get('inventory_roots'):
        raise ValueError('missing search paths/input pins/inventories')
    def pure(value):
        return PureWindowsPath(value) if re.match(r'^[A-Za-z]:[\\/]', value) else PurePosixPath(value)
    path_values = [*config['inventory_roots'], *config['lean_path'], config['compiler'], config['helper_source'], config['builtin_library'], config['working_directory'], *[p['path'] for p in config['pins'].values()]]
    if any(not pure(p).is_absolute() or '..' in pure(p).parts for p in path_values):
        raise ValueError('configured paths must be absolute and contain no parent traversal')
    inventories = [pure(p) for p in config['inventory_roots']]
    compiler_path = pure(config['compiler'])
    required_roots = [pure(p) for p in config['lean_path']] + [pure(config['builtin_library']), compiler_path.parent, compiler_path.parent.parent/'lib']
    required_roots += [p.parent for p in required_roots if p.name == 'lean']
    if any(not any(p.is_relative_to(root) for root in inventories) for p in required_roots):
        raise ValueError('inventory roots do not cover every import/native runtime search directory')
    for label, pin in config['pins'].items():
        if not isinstance(pin['path'], str) or not re.fullmatch('[0-9a-f]{64}', pin['sha256']):
            raise ValueError(f'invalid pinned file: {label}')
    for field in ('compiler_sha256', 'helper_sha256'):
        if not re.fullmatch('[0-9a-f]{64}', config[field]):
            raise ValueError(f'invalid {field}')
    if not 1 <= config.get('timeout_seconds', 0) <= 7200:
        raise ValueError('timeout must be explicitly bounded to 1..7200 seconds')
    if config.get('threads') != 2:
        raise ValueError('reviewed runner uses exactly two Lean threads')


def driver_source(config: dict) -> str:
    config_check(config)
    return ('-- Environment enumeration; module scope comes from the frozen import graph.\n'
            + '\n'.join('import ' + m for m in config['imports'])
            + '\nimport ' + HELPER_MODULE + '\n'
            + '#environment_audit prefixes [' + ', '.join(config['prefixes'])
            + '] modules [' + ', '.join(config['expected_modules'])
            + '] headlines [' + ', '.join(config['headlines']) + ']\n')


def resolve_module(module: str, search_path: list[Path]) -> Path:
    """Pinned Lean SearchPath.findWithExt: first package prefix wins, no fallback."""
    parts = module.split('.')
    for root in search_path:
        if (root / parts[0]).is_dir() or (root / (parts[0] + '.olean')).exists():
            target = root.joinpath(*parts).with_suffix('.olean')
            if not target.is_file():
                raise ValueError(f'prefix shadow/missing imported object: {module} at {target}')
            return target
    raise ValueError(f'unknown imported module prefix: {module}')


def snapshot(config: dict, extra: dict[str, Path] | None = None) -> dict:
    files = {}
    for label, pin in config['pins'].items():
        p = Path(pin['path'])
        actual = sha(p)
        if actual != pin['sha256']:
            raise ValueError(f'pinned input changed: {label}')
        files[str(p.absolute())] = actual
    for label, p, expected in [('compiler', Path(config['compiler']), config['compiler_sha256']),
                                ('helper source', Path(config['helper_source']), config['helper_sha256'])]:
        actual = sha(p)
        if actual != expected:
            raise ValueError(f'{label} digest mismatch')
        files[str(p.absolute())] = actual
    inventory = {}
    for root_text in config['inventory_roots']:
        root = Path(root_text)
        if not root.is_dir():
            raise ValueError(f'missing inventory root: {root}')
        for walk_root, dirs, entries in os.walk(root, followlinks=False):
            for directory in dirs:
                if (Path(walk_root) / directory).is_symlink():
                    raise ValueError('symlinked inventory directories need an explicit real inventory root')
            for name in entries:
                if name.endswith(ARTIFACT_ENDINGS) or '.so.' in name:
                    p = Path(walk_root) / name
                    inventory[str(p.absolute())] = sha(p)
    for label, path in (extra or {}).items():
        files[str(path.absolute())] = sha(path)
    return {'files': dict(sorted(files.items())), 'artifact_inventory': dict(sorted(inventory.items()))}


def declaration_check(record: dict, imported: set[str]) -> None:
    for field in ('name', 'module', 'kind', 'statement', 'dependencies', 'axioms', 'standard_axioms', 'nonstandard_axioms'):
        if field not in record:
            raise ValueError(f'declaration missing field: {field}')
    if record['module'] not in imported or not isinstance(record['statement'], str) or not record['statement']:
        raise ValueError('declaration has unknown defining module or missing statement')
    if record['kind'] not in {'theorem', 'axiom', 'definition', 'opaque', 'quotient', 'inductive', 'constructor', 'recursor'}:
        raise ValueError('unknown declaration kind')
    deps = names(record['dependencies'], 'dependencies', True)
    axs = names(record['axioms'], 'axioms', True)
    std = names(record['standard_axioms'], 'standard axioms', True)
    bad = names(record['nonstandard_axioms'], 'nonstandard axioms', True)
    if set(axs) - ALLOWED or bad or set(std) != set(axs):
        raise ValueError(f"nonstandard/inconsistent axiom report: {record['name']}")


def validate_report(report: dict, config: dict) -> dict:
    if report.get('schema_version') != 1 or report.get('method') != 'compiled Lean environment':
        raise ValueError('unexpected environment audit schema/method')
    if report['prefixes'] != config['prefixes'] or report['modules'] != config['expected_modules']:
        raise ValueError('reported scope differs from frozen driver')
    imported = set(names(report['imported_modules'], 'imported modules'))
    if not (set(config['expected_modules']) | {HELPER_MODULE}) <= imported:
        raise ValueError('omitted expected imported module')
    source_bound_imports = {n for n in imported if any(n == p or n.startswith(p + '.') for p in config['source_bound_prefixes'])}
    if source_bound_imports != set(config['expected_modules']):
        raise ValueError('source-bound imported project graph differs from frozen normal graph')
    records = report['declarations']
    if not isinstance(records, list) or not records:
        raise ValueError('empty declaration inventory')
    record_names = names([r['name'] for r in records], 'declarations')
    if len(records) != report['declaration_count']:
        raise ValueError('declaration count mismatch')
    selected = set(config['expected_modules'])
    for record in records:
        declaration_check(record, imported)
        belongs = record['module'] in selected or any(
            record['name'] == p or record['name'].startswith(p + '.') or
            record['module'] == p or record['module'].startswith(p + '.') for p in config['prefixes'])
        if not belongs or record['module'] == HELPER_MODULE:
            raise ValueError('declaration outside configured environment scope')
    theorem_names = names(report['theorem_names'], 'theorems', True)
    expected = [r['name'] for r in records if r['kind'] == 'theorem']
    if theorem_names != expected or len(expected) != report['theorem_count']:
        raise ValueError('theorem inventory/count differs from declaration kinds')
    if not set(config.get('expected_declarations', [])) <= set(record_names):
        raise ValueError('compiled environment omitted a previously audited declaration')
    headlines = report['headlines']
    if [r['name'] for r in headlines] != config['headlines']:
        raise ValueError('omitted/duplicated/reordered headline')
    for headline in headlines:
        reachable = names(headline['closure'], 'headline closure')
        reachable_set = set(reachable)
        records = headline['declarations']
        if [r['name'] for r in records] != reachable or headline['name'] not in reachable:
            raise ValueError('headline closure records are incomplete')
        for record in records:
            declaration_check(record, imported)
            if not set(record['dependencies']) <= reachable_set:
                raise ValueError('headline closure misses a direct compiled dependency')
        by_name = {r['name']: r for r in records}
        seen, pending = set(), [headline['name']]
        while pending:
            current = pending.pop()
            if current not in seen:
                seen.add(current)
                pending.extend(by_name[current]['dependencies'])
        if seen != reachable_set:
            raise ValueError('headline closure contains unrelated declarations')
    return {'declarations': report['declaration_count'], 'theorems': report['theorem_count'],
            'headlines': len(headlines), 'imported_modules': len(imported)}


def execute(argv: list[str], cwd: Path, env: dict, output: Path, label: str, timeout: int) -> dict:
    start = time.monotonic()
    stdout, stderr = output / (label + '.stdout'), output / (label + '.stderr')
    timed_out = False
    with stdout.open('wb') as out, stderr.open('wb') as err:
        proc = subprocess.Popen(argv, cwd=cwd, env=env, stdout=out, stderr=err)
        try:
            code = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            proc.kill()
            code = proc.wait()
    return {'argv': argv, 'exit_code': code, 'timed_out': timed_out,
            'elapsed_seconds': time.monotonic() - start,
            'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr)}


def run(config_path: Path, output: Path) -> dict:
    # Existing attempts/failures are never overwritten.
    output.mkdir(parents=True, exist_ok=False)
    receipt = {'schema_version': 1, 'status': 'failed', 'started_at_utc': now(),
               'config_sha256': sha(config_path), 'runner_sha256': sha(Path(__file__)),
               'scope': 'unvalidated configuration'}
    save(output / 'receipt.json', receipt)
    try:
        config = strict_json(config_path.read_text(encoding='utf-8'))
        config_check(config)
        receipt['scope'] = config['scope']
        save(output / 'frozen-config.json', config)
        helper_source_root = output / 'helper-source'
        staged = helper_source_root / 'ResearchAudit/EnvironmentAudit.lean'
        staged.parent.mkdir(parents=True)
        shutil.copyfile(config['helper_source'], staged)
        if sha(staged) != config['helper_sha256']:
            raise ValueError('staged helper differs from reviewed helper bytes')
        helper_lib = output / 'helper-lib'
        helper_object = helper_lib / 'ResearchAudit/EnvironmentAudit.olean'
        helper_object.parent.mkdir(parents=True)
        # No directory other than ResearchAudit is created under this first
        # search path root; a partial Math115 prefix would shadow normal objects.
        driver = output / 'Audit.lean'
        driver.write_text(driver_source(config), encoding='utf-8')
        extra = {'driver': driver, 'staged helper': staged, 'config': config_path,
                 'runner': Path(__file__), 'frozen config': output / 'frozen-config.json'}
        extra['python executable'] = Path(sys.executable)
        before = snapshot(config, extra)
        save(output / 'compile-before.json', before)
        env = dict(os.environ)
        removed = []
        for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN', 'PATH',
                    'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT',
                    'DYLD_LIBRARY_PATH', 'DYLD_FALLBACK_LIBRARY_PATH', 'DYLD_INSERT_LIBRARIES',
                    'DYLD_FRAMEWORK_PATH', 'DYLD_FALLBACK_FRAMEWORK_PATH'):
            if key in env:
                removed.append(key)
                del env[key]
        env['LEAN_NUM_THREADS'] = '2'
        env['LEAN_PATH'] = os.pathsep.join(config['lean_path'])
        env['PATH'] = str(Path(config['compiler']).parent)
        receipt['controlled_environment'] = {'LEAN_PATH': env['LEAN_PATH'], 'LEAN_NUM_THREADS': '2',
                                               'removed_overrides': removed, 'PATH_prefix': str(Path(config['compiler']).parent)}
        version_run = execute([config['compiler'], '--version'], Path(config['working_directory']), env, output, 'compiler-version', 60)
        receipt['compiler_version_check'] = version_run
        banner = (output / 'compiler-version.stdout').read_text(encoding='utf-8').strip()
        if version_run['exit_code'] or (output / 'compiler-version.stderr').read_bytes() or banner != config['compiler_version']:
            raise ValueError('compiler version differs from frozen runtime')
        receipt['compiler_version'] = banner
        prefix_run = execute([config['compiler'], '--print-prefix'], Path(config['working_directory']), env, output, 'compiler-prefix', 60)
        receipt['compiler_prefix_check'] = prefix_run
        prefix = (output/'compiler-prefix.stdout').read_text(encoding='utf-8').strip()
        if prefix_run['exit_code'] or (output/'compiler-prefix.stderr').read_bytes() or (Path(prefix)/'lib/lean').resolve() != Path(config['builtin_library']).resolve():
            raise ValueError('declared builtin library differs from actual Lean sysroot')
        receipt['platform_loader_boundary'] = 'Known loader override variables cleared; PATH contains only pinned compiler directory. System loader, OS libraries, Python interpreter/stdlib and platform services remain trusted; this is an import/compiler input audit, not an OS sandbox.'
        compile_run = execute([config['compiler'], '-j2', '-DautoImplicit=false',
            '--root=' + str(helper_source_root), '-o', str(helper_object), str(staged)],
            Path(config['working_directory']), env, output, 'helper-compile', config['timeout_seconds'])
        receipt['helper_compile'] = compile_run
        after = snapshot(config, extra)
        save(output / 'compile-after.json', after)
        if before != after or compile_run['exit_code'] or compile_run['timed_out']:
            raise ValueError('helper compilation failed or changed frozen inputs')
        if (output / 'helper-compile.stdout').read_bytes() or (output / 'helper-compile.stderr').read_bytes():
            raise ValueError('unexpected helper compiler output requires review')
        extra['helper object'] = helper_object
        # Bind companion objects too; Lean 4.34 may emit private/server oleans.
        for p in helper_lib.rglob('*'):
            if p.is_file():
                extra['helper companion:' + str(p.relative_to(helper_lib))] = p
        if {p.name for p in helper_lib.iterdir()} != {'ResearchAudit'}:
            raise ValueError('helper library must contain only the ResearchAudit prefix')
        audit_config = dict(config, inventory_roots=[*config['inventory_roots'], str(helper_lib)])
        before = snapshot(audit_config, extra)
        save(output / 'audit-before.json', before)
        env['LEAN_PATH'] = str(helper_lib) + os.pathsep + os.pathsep.join(config['lean_path'])
        receipt['audit_lean_path'] = env['LEAN_PATH']
        audit_run = execute([config['compiler'], '-j2', '-DautoImplicit=false', str(driver)],
            Path(config['working_directory']), env, output, 'environment-audit', config['timeout_seconds'])
        receipt['environment_audit'] = audit_run
        after = snapshot(audit_config, extra)
        save(output / 'audit-after.json', after)
        if {p.name for p in helper_lib.iterdir()} != {'ResearchAudit'}:
            raise ValueError('audit added a foreign helper-library prefix')
        if before != after or audit_run['exit_code'] or audit_run['timed_out']:
            raise ValueError('environment audit failed or changed frozen inputs')
        if (output / 'environment-audit.stderr').read_bytes():
            raise ValueError('unexpected audit stderr requires review')
        stdout = output / 'environment-audit.stdout'
        if stdout.stat().st_size > 512 * 1024 * 1024:
            raise ValueError('audit JSON exceeds explicit 512 MiB parser bound')
        report = strict_json(stdout.read_text(encoding='utf-8'))
        receipt['counts'] = validate_report(report, config)
        search = [helper_lib, *map(Path, config['lean_path']), Path(config['builtin_library'])]
        resolved = {}
        for module in report['imported_modules']:
            p = resolve_module(module, search)
            expected_digest = before['files'].get(str(p.absolute()), before['artifact_inventory'].get(str(p.absolute())))
            if expected_digest is None or sha(p) != expected_digest:
                raise ValueError('imported module is absent from frozen artifact inventory: ' + module)
            resolved[module] = {'path': str(p), 'sha256': expected_digest}
        save(output / 'imported-object-closure.json', resolved)
        receipt['resolved_import_closure_sha256'] = canonical_sha(resolved)
        receipt['before_after_canonical_sha256'] = canonical_sha(before)
        receipt['input_files'] = len(before['files'])
        receipt['artifact_inventory_files'] = len(before['artifact_inventory'])
        receipt['helper_object_sha256'] = sha(helper_object)
        receipt['driver_sha256'] = sha(driver)
        receipt['status'] = 'passed_compiled_environment_audit'
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        receipt['error'] = str(error)
    finally:
        receipt['finished_at_utc'] = now()
        save(output / 'receipt.json', receipt)
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepare-only', action='store_true', help='validate static configuration and emit driver; do not invoke Lean')
    args = parser.parse_args()
    if args.prepare_only:
        config = strict_json(args.config.read_text(encoding='utf-8'))
        print(driver_source(config), end='')
        return 0
    receipt = run(args.config.resolve(), args.output.resolve())
    print(json.dumps({'status': receipt['status'], 'counts': receipt.get('counts'), 'error': receipt.get('error')}))
    return 0 if receipt['status'] == 'passed_compiled_environment_audit' else 1

if __name__ == '__main__':
    raise SystemExit(main())
