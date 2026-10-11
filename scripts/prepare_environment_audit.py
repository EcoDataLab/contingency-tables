#!/usr/bin/env python3
"""Prepare native saved-normal or current Lake-build environment audit inputs.

Source import parsing defines the compiled module scope and required origins.
It does not enumerate declarations/theorems; only the compiled Lean helper does.
Preparation never invokes a project compiler or downloads a cache.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path, PureWindowsPath
import re
import shutil
import subprocess

from build_lean_serial import Module, dependency_order, lean_imports
from run_environment_audit import config_check, driver_source, resolve_module, sha, strict_json

PREFIXES = ['Math115', 'OAI.ContingencyTables', 'OAI.Combinatorics.ContingencyTables']
CONTRACT = 'formal/default-audit-contract.json'
PUBLISHED = 'formal/results/native-sampler-checkpoint/'
INTEGRATED_ROOTS = {'Math115.LatticeBoundedSampling', 'Math115.LatticeSamplerCost',
                    'Math115.PublicLatticeSampler'}


def default_contract(root: Path) -> dict | None:
    """Source-bound inclusion requirements; never a theorem inventory or receipt."""
    aggregate_imports = set(lean_imports((root / 'formal/Math115.lean').read_text(encoding='utf-8')))
    path = root / CONTRACT
    if not path.is_file():
        if aggregate_imports & INTEGRATED_ROOTS:
            raise ValueError('integrated sampler root requires its source-bound audit contract')
        return None
    contract = strict_json(path.read_text(encoding='utf-8'))
    fields = {'schema_version', 'scope', 'published_checkpoint', 'published_selection',
              'published_intake', 'modules', 'headlines', 'private_source_helpers',
              'program_identity_requirements'}
    if set(contract) != fields or contract['schema_version'] != 1 or not contract['scope']:
        raise ValueError('invalid default audit contract schema')
    saved = {}
    for field, suffix in [('published_checkpoint', 'checkpoint.json'),
                          ('published_selection', 'audit/selection.json'),
                          ('published_intake', 'audit/intake-verification.json')]:
        spec = contract[field]
        if spec['path'] != PUBLISHED + suffix or sha(root / spec['path']) != spec['sha256']:
            raise ValueError('published contract authority differs: ' + field)
        saved[field] = strict_json((root / spec['path']).read_text(encoding='utf-8'))
    checkpoint, selection, intake = (saved[k] for k in
        ['published_checkpoint', 'published_selection', 'published_intake'])
    expected = []
    for source in sorted(checkpoint['latest_sources'], key=lambda r: r['module']):
        module = source['module']
        if source['state'] != 'completed' or not re.fullmatch(r'Math115\.[A-Za-z][A-Za-z0-9]*', module):
            raise ValueError('published sampler sources are not completed exact local modules')
        expected.append({'module': module,
            'source': 'formal/Math115/' + module.split('.')[-1] + '.lean',
            'sha256': source['source_sha256'],
            'public_declarations': sorted(n for n in selection['public_inclusion_names']
                                          if n.startswith(module + '.'))})
    if contract['modules'] != expected or len(expected) != 13:
        raise ValueError('integrated module/source/inclusion contract differs from published evidence')
    if not {m['module'] for m in expected} <= aggregate_imports:
        raise ValueError('default aggregate omits a required integrated module')
    for module in expected:
        if sha(root / module['source']) != module['sha256']:
            raise ValueError('integrated source bytes differ from published source: ' + module['module'])
    private = [{'defining_module': r['defining_module'], 'source_name': r['source_name'],
                'kind': 'theorem'} for r in selection['private_source_helpers']]
    identities = [{'headline': r['headline'], 'required_reachable_names': r['required_reachable_names']}
                  for r in intake['program_identity_inclusions']]
    if (contract['headlines'] != selection['exact_headlines'] or
            contract['private_source_helpers'] != private or
            contract['program_identity_requirements'] != identities):
        raise ValueError('headline/private/program obligations differ from published evidence')
    if set(previously_audited(root)) != set(selection['public_inclusion_names']):
        raise ValueError('current named audits differ from the published required inclusion set')
    return contract


def contract_pins(root: Path, native_root=None) -> dict:
    contract = default_contract(root)
    if contract is None:
        return {}
    paths = [CONTRACT, *(contract[k]['path'] for k in
             ['published_checkpoint', 'published_selection', 'published_intake'])]
    return {'integration-contract:' + p: {'path': str((native_root or root) / p),
                                         'sha256': sha(root / p)} for p in paths}


def seam_requirements(root: Path) -> dict:
    contract = default_contract(root)
    return {} if contract is None else {
        'private_source_helpers': contract['private_source_helpers'],
        'program_identity_requirements': contract['program_identity_requirements']}


def headlines(root: Path) -> list[str]:
    ledger = json.loads((root / 'claims.json').read_text(encoding='utf-8'))
    names = {h['name'] for c in ledger['claims'] for h in c['headlines']}
    contract = default_contract(root)
    if contract is not None:
        names.update(contract['headlines'])
    return sorted(names)


def previously_audited(root: Path) -> list[str]:
    # This is only an inclusion check against known named audits. It is never
    # treated as the complete theorem inventory.
    result = []
    for relative in ['formal/Math115/AxiomAudit.lean', 'formal/Math115/StandaloneAxiomAudit.lean']:
        result.extend(re.findall(r'^#print axioms (\S+)\s*$', (root / relative).read_text(encoding='utf-8'), re.MULTILINE))
    if len(result) != len(set(result)) or not result:
        raise ValueError('previous named audit inclusion list is empty or duplicated')
    return result


def native_config(root: Path, evidence: Path, helper_source: str) -> dict:
    default_contract(root)
    plan = json.loads((evidence / 'frozen-plan.json').read_text(encoding='utf-8'))
    modules = json.loads((evidence / 'modules.json').read_text(encoding='utf-8'))
    status = json.loads((evidence / 'status.json').read_text(encoding='utf-8'))
    envfiles = sorted(evidence.glob('environment-*.json'))
    if not envfiles:
        raise ValueError('normal compilation lacks compiler environment metadata')
    environments = [strict_json(p.read_text(encoding='utf-8')) for p in envfiles]
    env = environments[0]
    identity = ['lean', 'lean_sha256', 'lake_sha256', 'lean_path', 'external_objects',
                'source_commit', 'plan_sha256', 'package_pins']
    if any(any(e.get(k) != env.get(k) for k in identity) for e in environments[1:]):
        raise ValueError('normal compiler environment identities differ; select an authenticated run')
    if status['status'] != 'passed' or len(modules) != len(plan['modules']):
        raise ValueError('normal module compilation not complete')
    root_record = next(r for r in modules if r['module'] == 'Math115')
    if root_record['exit_code'] != 0 or root_record['reused']:
        raise ValueError('aggregate root must be a fresh successful normal compile')
    if (root_record.get('source') != 'formal/Math115.lean' or
            root_record.get('source_unchanged') is not True or
            root_record['source_sha256'] != sha(root / 'formal/Math115.lean')):
        raise ValueError('normal root source differs from the current aggregate')
    by_name = {r['module']: r for r in modules}
    by_plan = {r['name']: r for r in plan['modules']}
    if len(by_name) != len(modules) or len(by_plan) != len(plan['modules']) or set(by_name) != set(by_plan):
        raise ValueError('normal records differ from complete frozen module graph')
    if any(d not in by_plan for m in by_plan.values() for d in m['imports']
           if d == 'Math115' or d.startswith(('Math115.', 'OAI.', 'ComparatorChallenges.'))):
        raise ValueError('normal graph omits an internal project dependency')
    compiler = PureWindowsPath(root_record['command'][0])
    native_repo = PureWindowsPath(root_record['command'][-1]).parent.parent
    search = [PureWindowsPath(p) for p in env['lean_path'].split(';')]
    native_build = search[0].parent.parent
    pins = {}
    for relative, expected in {**plan['input_sha256'], **plan['configuration_sha256']}.items():
        pins['source/config:' + relative] = {'path': str(native_repo / relative), 'sha256': expected}
    for module, record in by_name.items():
        if (record['exit_code'] != 0 or record.get('source_unchanged') is not True or
                record['source'] != by_plan[module]['source'] or
                record['source_sha256'] != plan['input_sha256'][record['source']]):
            raise ValueError('module compile/source receipt failed: ' + module)
        if record['source'].startswith('formal/'):
            path = root / record['source']
            if (sha(path) != record['source_sha256'] or
                    list(lean_imports(path.read_text(encoding='utf-8'))) != by_plan[module]['imports']):
                raise ValueError('normal module source/imports differ from current local source: ' + module)
        p = search[0].joinpath(*module.split('.')).with_suffix('.olean')
        pins['normal-object:' + module] = {'path': str(p), 'sha256': record['olean_sha256']}
        expected = {d: by_name[d]['olean_sha256'] for d in by_plan[module]['imports'] if d in by_name}
        if record['dependency_olean_sha256'] != expected:
            raise ValueError('normal dependency object closure differs: ' + module)
    for module, external in env['external_objects'].items():
        pins['authenticated-external-object:' + module] = {'path': external['path'], 'sha256': external['sha256']}
    for name in ['frozen-plan.json', 'frozen-environment.json', 'modules.json', 'status.json']:
        pins['normal-evidence:' + name] = {'path': str(native_build / name), 'sha256': sha(evidence / name)}
    for p in envfiles:
        pins['normal-environment:' + p.name] = {'path': str(native_build / p.name), 'sha256': sha(p)}
    # The root and manual inclusion list are separately source pinned, including
    # selected declarations beyond the previous 863-focused receipt.
    for relative in ['formal/Math115/AxiomAudit.lean', 'formal/Math115/StandaloneAxiomAudit.lean']:
        pins['named-inclusion-source:' + relative] = {'path': str(native_repo / relative), 'sha256': sha(root / relative)}
    toolchain = compiler.parent.parent
    pins.update(contract_pins(root, native_repo))
    return dict(schema_version=1, scope='All compiled internal modules in the reviewed current default aggregate import closure; every selected theorem and exact headline dependency closure. Official external/toolchain artifacts are trusted inputs, fully hashed before and after.',
        imports=['Math115'], prefixes=PREFIXES, source_bound_prefixes=['Math115','OAI','ComparatorChallenges'], expected_modules=sorted(by_name),
        headlines=headlines(root), expected_declarations=previously_audited(root),
        compiler=str(compiler), compiler_sha256=env['lean_sha256'], compiler_version=env['lean'],
        helper_source=helper_source, helper_sha256=sha(root/'formal/ResearchAudit/EnvironmentAudit.lean'),
        working_directory=str(native_repo/'formal'), lean_path=list(map(str, search)),
        builtin_library=str(toolchain/'lib/lean'),
        inventory_roots=list(map(str, [p.parent if p.name == 'lean' else p for p in search]))+[str(toolchain/'lib'),str(toolchain/'bin')],
        pins=pins, threads=2, timeout_seconds=3600,
        normal_root_source_sha256=root_record['source_sha256'], normal_root_olean_sha256=root_record['olean_sha256'],
        prior_evidence_boundary='Compilation reuse is normal, authenticated, and stated in source receipts; this audit itself must run fresh. Historical receipts do not certify a changed aggregate.',
        **seam_requirements(root))


def current_config(root: Path) -> dict:
    default_contract(root)
    compiler_name = shutil.which('lean')
    if not compiler_name or not os.environ.get('LEAN_PATH'):
        raise ValueError('run current preparation under lake env with a resolved lean and LEAN_PATH')
    prefix = subprocess.check_output([compiler_name,'--print-prefix'],text=True).strip()
    compiler = Path(prefix)/'bin'/('lean.exe' if os.name == 'nt' else 'lean')
    search = [Path(p).absolute() for p in os.environ['LEAN_PATH'].split(os.pathsep) if p]
    builtin = compiler.parent.parent/'lib/lean'
    def resolve_source(name):
        relative = Path(*name.split('.')).with_suffix('.lean')
        if name == 'Math115' or name.startswith('Math115.'):
            path = root/'formal'/relative
        elif name.startswith('OAI.') or name.startswith('ComparatorChallenges.'):
            path = root/'.upstream/openai-math/lean'/relative
        else:
            return None
        if not path.is_file():
            raise ValueError('missing source in project import closure: '+name)
        return Module(name, path, lean_imports(path.read_text(encoding='utf-8')))
    modules = dependency_order(('Math115',), resolve_source)
    pins = {}
    for module in modules:
        pins['source:'+module.name] = {'path':str(module.source), 'sha256':sha(module.source)}
        obj = resolve_module(module.name, [*search,builtin])
        pins['built-object:'+module.name] = {'path':str(obj), 'sha256':sha(obj)}
    for relative in ['formal/lakefile.lean','formal/lake-manifest.json','formal/lean-toolchain',
                     'formal/Math115/AxiomAudit.lean','formal/Math115/StandaloneAxiomAudit.lean', 'claims.json']:
        pins['configuration:'+relative]={'path':str(root/relative),'sha256':sha(root/relative)}
    pins.update(contract_pins(root))
    return dict(schema_version=1,scope='Fresh current Lake-built Math115 import closure; complete compiled declaration/theorem enumeration in project origins and exact headline closure. Dependency/toolchain caches are trusted and hashed before and after.',
        imports=['Math115'],prefixes=PREFIXES,source_bound_prefixes=['Math115','OAI','ComparatorChallenges'],expected_modules=sorted(m.name for m in modules),
        headlines=headlines(root),expected_declarations=previously_audited(root),
        compiler=str(compiler),compiler_sha256=sha(compiler),
        compiler_version=subprocess.check_output([str(compiler),'--version'],text=True).strip(),
        helper_source=str(root/'formal/ResearchAudit/EnvironmentAudit.lean'),helper_sha256=sha(root/'formal/ResearchAudit/EnvironmentAudit.lean'),
        working_directory=str(root/'formal'),lean_path=list(map(str,search)),builtin_library=str(builtin),
        inventory_roots=list(map(str,[p.parent if p.name == 'lean' else p for p in search]))+[str(compiler.parent.parent/'lib'),str(compiler.parent)],
        pins=pins,threads=2,timeout_seconds=3600,**seam_requirements(root))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--normal-evidence',type=Path)
    parser.add_argument('--native-helper-source',help='exact staged native helper source path')
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--driver-output',type=Path)
    args=parser.parse_args()
    if args.normal_evidence:
        if not args.native_helper_source:parser.error('--native-helper-source required for native config')
        config=native_config(args.root.resolve(),args.normal_evidence,args.native_helper_source)
    else:
        config=current_config(args.root.resolve())
    config_check(config)
    with args.output.open('x', encoding='utf-8') as stream:json.dump(config,stream,indent=2);stream.write('\n')
    if args.driver_output:
        with args.driver_output.open('x', encoding='utf-8') as stream:stream.write(driver_source(config))
    print(json.dumps({'status':'prepared_no_project_compile','modules':len(config['expected_modules']),
                      'headlines':len(config['headlines']),'previous_named_inclusion':len(config['expected_declarations'])}))
    return 0

if __name__=='__main__':
    raise SystemExit(main())
