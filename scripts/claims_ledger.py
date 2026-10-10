#!/usr/bin/env python3
"""Validate immutable named-audit receipts and generate public claim summaries.

This replays saved named audits. It does not enumerate a Lean environment or
turn a successful old receipt into a fresh compiler run.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

from check_lean_axioms import ALLOWED, check_audit

BEGIN = '<!-- BEGIN GENERATED CLAIMS -->'
END = '<!-- END GENERATED CLAIMS -->'
CLASSES = {'lean_theorem', 'lean_component_cost', 'executable_reference', 'reviewed_mathematics', 'open_obligation'}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_path(root: Path, relative: str) -> Path:
    p = Path(relative)
    if p.is_absolute() or '..' in p.parts or not relative:
        raise ValueError(f'expected repository-relative path: {relative}')
    result = root / p
    if not result.resolve().is_relative_to(root.resolve()):
        raise ValueError(f'path escapes repository: {relative}')
    return result


def unique_names(records: list, label: str) -> list[str]:
    names = [r if isinstance(r, str) else r['name'] for r in records]
    if not names or len(names) != len(set(names)):
        raise ValueError(f'{label}: empty or duplicate declaration names')
    return names


def validate_receipt(root: Path, spec: dict) -> dict:
    path = local_path(root, spec['path'])
    if digest(path) != spec['sha256']:
        raise ValueError(f"receipt digest mismatch: {spec['id']}")
    receipt = json.loads(path.read_text(encoding='utf-8'))
    accepted_statuses = {'passed', 'passed_selected_module_compilations_and_named_audits_private_projection_pending_publication_review'}
    if receipt.get('status') not in accepted_statuses or receipt.get('status') != spec['status'] or set(receipt.get('allowed_axioms', [])) != ALLOWED:
        raise ValueError(f"receipt not passed with standard axiom policy: {spec['id']}")
    commit = receipt.get('repository_commit', receipt.get('source_checkout_base_commit'))
    if commit != spec['commit']:
        raise ValueError(f"receipt commit mismatch: {spec['id']}")
    if spec['commit_kind'] not in {'exact_repository_commit', 'base_commit_plus_source_hashes', 'source_hashes_only'}:
        raise ValueError('unknown commit binding kind')
    if spec['commit_kind'] == 'base_commit_plus_source_hashes' and (not isinstance(commit, str) or not re.fullmatch(r'[0-9a-f]{40}', commit)):
        raise ValueError('base commit binding requires a recorded full commit')
    if spec['commit_kind'] == 'source_hashes_only' and commit is not None:
        raise ValueError('source-only binding must not invent a base commit')
    if (spec['commit_kind'] == 'exact_repository_commit') != ('repository_commit' in receipt):
        raise ValueError('exact commit binding does not match receipt')
    artifacts = receipt.get('artifacts_sha256', receipt.get('file_sha256', {}))
    if not artifacts:
        raise ValueError('receipt has no hash-bound artifacts')
    for relative, expected in artifacts.items():
        if digest(local_path(path.parent, relative)) != expected:
            raise ValueError(f'artifact digest mismatch: {relative}')
    records = []
    source_hashes = dict(receipt.get('source_freeze', receipt.get('source_sha256', {})))
    module_counts = {}
    for module in receipt.get('modules', []):
        audit = module['audit']
        if audit.get('status') != 'passed' or audit.get('exit_code') != 0:
            raise ValueError(f"module audit did not pass: {module['module']}")
        if module['compile'].get('exit_code') != 0:
            raise ValueError(f"module compile/reuse did not pass: {module['module']}")
        driver = local_path(path.parent, audit['driver'])
        log = local_path(path.parent, audit['log'])
        if artifacts.get(audit['driver']) != audit['driver_sha256'] or artifacts.get(audit['log']) != audit['log_sha256']:
            raise ValueError('audit driver/log not bound to artifact hashes')
        parsed = check_audit(driver.read_text(encoding='utf-8'), log.read_text(encoding='utf-8'))
        names = unique_names(module['declarations'], module['module'])
        if names != [r['name'] for r in parsed] or len(names) != module['declaration_count']:
            raise ValueError('module declaration count/roster differs from strict replay')
        if isinstance(module['declarations'][0], dict) and module['declarations'] != parsed:
            raise ValueError('module axiom records differ from strict replay')
        records.extend(parsed)
        module_counts[module['module']] = len(parsed)
        source_hashes[module['source']] = module['source_sha256']
        for name, value in module.get('direct_dependency_source_sha256', {}).items():
            # OAI sources live in a separately pinned upstream checkout; record
            # project module source bindings here without inventing path mappings.
            if name.startswith('Math115.'):
                source_hashes['formal/' + name.replace('.', '/') + '.lean'] = value
    if not receipt.get('modules'):
        driver = local_path(path.parent, 'AxiomAudit.lean')
        log = local_path(path.parent, 'axiom-audit.log')
        if 'AxiomAudit.lean' not in artifacts or 'axiom-audit.log' not in artifacts:
            raise ValueError('focused receipt does not bind raw audit driver/log')
        records = check_audit(driver.read_text(encoding='utf-8'), log.read_text(encoding='utf-8'))
        if records != receipt['audited_declarations']:
            raise ValueError('focused receipt differs from strict replay')
    closure_path = receipt.get('source_closure')
    if isinstance(closure_path, str):
        if closure_path not in artifacts:
            raise ValueError('source closure is not bound to artifact hashes')
        closure = json.loads(local_path(path.parent, closure_path).read_text(encoding='utf-8'))
        for record in closure['records']:
            source = record['source']
            local_path(root, source)
            value = record['source_sha256']
            if source in source_hashes and source_hashes[source] != value:
                raise ValueError('conflicting source hashes in receipt closure')
            source_hashes[source] = value
    names = unique_names(records, spec['id'])
    expected = receipt.get('total_audited_declarations', receipt.get('audit_declaration_count'))
    if len(names) != expected:
        raise ValueError('receipt total differs from distinct replayed declarations')
    return {'id': spec['id'], 'path': spec['path'], 'label': spec['label'],
            'commit': commit, 'commit_kind': spec['commit_kind'],
            'scope': spec['scope'], 'count': len(names), 'module_counts': module_counts,
            'names': names, 'records': records, 'source_hashes': source_hashes,
            'current_source_mismatches': sorted(p for p, sha in source_hashes.items()
                if not local_path(root, p).is_file() or digest(local_path(root, p)) != sha)}


def validate_ledger(root: Path, ledger: dict) -> dict:
    if not ledger.get('claims'):
        raise ValueError('claims ledger must have explicit nonempty headline claims')
    if ledger.get('schema_version') != 1:
        raise ValueError('unsupported claims ledger schema')
    scopes = {}
    for spec in ledger['receipts']:
        if spec['id'] in scopes:
            raise ValueError('duplicate receipt id')
        scopes[spec['id']] = validate_receipt(root, spec)
    # A later focused run can overlap the aggregate. Only explicitly declared
    # disjoint component scopes are added; every overlap is checked by name.
    disjoint = ledger['disjoint_component_scopes']
    seen = set()
    for scope_id in disjoint:
        names = set(scopes[scope_id]['names'])
        if seen & names:
            raise ValueError('component scopes advertised as disjoint overlap')
        seen |= names
    summary_ids = ledger.get('summary_receipt_ids', list(scopes))
    if not summary_ids or len(summary_ids) != len(set(summary_ids)) or any(i not in scopes for i in summary_ids):
        raise ValueError('summary must reference distinct validated receipt scopes')
    current_id = ledger.get('current_receipt')
    if current_id is not None:
        if current_id not in summary_ids or current_id not in disjoint:
            raise ValueError('current receipt must be included in summary and current disjoint scope')
        if scopes[current_id]['current_source_mismatches']:
            raise ValueError('current receipt source bytes differ from current checkout')
    claims = []
    ids = set()
    for claim in ledger['claims']:
        if claim['id'] in ids or claim['evidence_class'] not in CLASSES:
            raise ValueError('duplicate claim id or unknown evidence class')
        ids.add(claim['id'])
        for field in ('title', 'english_claim', 'quantity', 'hypotheses', 'limitations', 'sources', 'headlines', 'evidence'):
            if field not in claim:
                raise ValueError(f'missing claim field: {field}')
        if not claim['hypotheses'] or not claim['limitations'] or not claim['sources']:
            raise ValueError('claim must describe hypotheses, limits, and sources')
        for source in claim['sources']:
            if not local_path(root, source).is_file():
                raise ValueError(f'missing claim source: {source}')
        for evidence in claim['evidence']:
            scope = scopes[evidence['receipt']]
            if evidence['scope'] != scope['scope']:
                raise ValueError('claim evidence scope differs from receipt scope')
        if claim['evidence_class'].startswith('lean_'):
            if not claim['headlines'] or not claim['evidence']:
                raise ValueError('Lean claim requires named headlines and receipts')
            for headline in claim['headlines']:
                source = headline['source']
                module = headline['module']
                # Public Math115 headline namespaces follow their defining module.
                # This explicit reviewed attribution is required until a compiled
                # environment report supplies independently authenticated origins.
                if source != 'formal/' + module.replace('.', '/') + '.lean' or headline['name'].rsplit('.', 1)[0] != module:
                    raise ValueError('headline defining module/source attribution differs from canonical namespace')
                if source not in claim['sources']:
                    raise ValueError('headline source missing from claim sources')
                bound = False
                for evidence in claim['evidence']:
                    scope = scopes[evidence['receipt']]
                    if headline['name'] in scope['names'] and source in scope['source_hashes']:
                        if digest(local_path(root, source)) != scope['source_hashes'][source]:
                            raise ValueError(f'headline source differs from verified bytes: {source}')
                        bound = True
                if not bound:
                    raise ValueError(f"headline lacks named and source-bound receipt: {headline['name']}")
        elif claim['headlines'] or claim['evidence']:
            raise ValueError('non-Lean claim must not masquerade as named Lean evidence')
        claims.append(claim)
    return {'scopes': scopes, 'claims': claims, 'disjoint_count': len(seen),
            'summary_receipt_ids': summary_ids, 'current_receipt': current_id}


def render(result: dict) -> str:
    rows = [BEGIN, '', '| Claim | Quantity and evidence | Assumptions and present limit |', '|---|---|---|']
    def cell(s):
        return str(s).replace('|', '\\|').replace('\n', ' ')
    for claim in result['claims']:
        title = f"[{claim['title']}](docs/claims-and-evidence.md#{claim['id']})"
        evidence = claim['evidence_class'].replace('_', ' ')
        rows.append('| ' + ' | '.join(map(cell, [title, claim['quantity'] + '; ' + evidence,
            ' '.join(claim['hypotheses']) + ' ' + ' '.join(claim['limitations'])])) + ' |')
    rows += ['', 'Saved receipt scopes (counts are distinct named audit requests, not exhaustive theorem totals):', '']
    for scope_id in result['summary_receipt_ids']:
        scope = result['scopes'][scope_id]
        commit = f"exact commit `{scope['commit'][:7]}`" if scope['commit_kind'] == 'exact_repository_commit' else 'source hashes bound by the receipt'
        drift = ' Selected source/configuration bytes differ in the current checkout; this receipt does not verify the new aggregate.' if scope['current_source_mismatches'] else ''
        breakdown = ''
        if 'Math115' in scope['module_counts']:
            focused = scope['module_counts']['Math115']
            breakdown = f" ({focused} focused + {scope['count'] - focused} standalone)"
        rows.append(f"- [{scope['label']}]({scope['path']}): **{scope['count']}** named declarations{breakdown}; {commit}. {scope['scope']}{drift}")
    if result['current_receipt']:
        boundary = 'Historical component receipts are preserved in the [ledger](claims.json); their named declarations overlap the current integrated aggregate and are not added to it. The historical Linux focused run is a separate reproduction scope. Compiled-environment audit status is reported separately in [formal verification](docs/formal-verification.md); these counts describe saved named audits.'
    else:
        boundary = 'Only explicitly disjoint component scopes are combined. The later Linux focused run overlaps the aggregate and is not added to it. These saved audits do not establish that every project theorem was enumerated; see the environment-audit status in [formal verification](docs/formal-verification.md).'
    rows += ['', boundary, '', END]
    return '\n'.join(rows) + '\n'


def audit_driver(result: dict, component_scope_ids: list[str]) -> str:
    """Generate imports/headline requests from validated ledger bindings.

    Environment scope uses namespace AND defining-module prefixes, so private
    names and newly added imported project theorems do not need manual rosters.
    """
    modules = sorted({name for scope_id in component_scope_ids
                      for name in result['scopes'][scope_id]['module_counts']})
    if not modules:
        raise ValueError('selected receipts do not specify audited modules')
    modules = sorted(set(modules) | {h['module'] for claim in result['claims'] for h in claim['headlines']
                      if any(e['receipt'] in component_scope_ids for e in claim['evidence'])})
    headlines = sorted({h['name'] for claim in result['claims'] for h in claim['headlines']
                        if any(e['receipt'] in component_scope_ids for e in claim['evidence'])})
    return ('-- Generated from validated claims.json; no manual theorem roster.\n'
            + '\n'.join('import ' + module for module in modules)
            + '\nimport ResearchAudit.EnvironmentAudit\n'
            + '#environment_audit prefixes [Math115, OAI.ContingencyTables, '
              'OAI.Combinatorics.ContingencyTables] modules [' + ', '.join(modules)
            + '] headlines [' + ', '.join(headlines) + ']\n')


def replace_generated(text: str, generated: str) -> str:
    if text.count(BEGIN) != 1 or text.count(END) != 1 or text.index(BEGIN) >= text.index(END):
        raise ValueError('README must contain exactly one ordered generated claims marker pair')
    start, finish = text.index(BEGIN), text.index(END) + len(END)
    return text[:start] + generated.rstrip('\n') + text[finish:]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--ledger', default='claims.json')
    parser.add_argument('--write-readme', action='store_true')
    parser.add_argument('--check-readme', action='store_true')
    parser.add_argument('--audit-driver', choices=['focused', 'all-components'], help='emit Lean driver from ledger imports/headlines; does not run Lean')
    parser.add_argument('--json', action='store_true', help='emit validated receipt-derived scope counts')
    args = parser.parse_args()
    try:
        result = validate_ledger(args.root, json.loads(local_path(args.root, args.ledger).read_text(encoding='utf-8')))
        generated = render(result)
        if args.write_readme or args.check_readme:
            path = args.root / 'README.md'
            current = path.read_text(encoding='utf-8')
            updated = replace_generated(current, generated)
            if args.check_readme and current != updated:
                raise ValueError('README generated claims are stale; run --write-readme')
            if args.write_readme:
                path.write_text(updated, encoding='utf-8')
        elif args.audit_driver:
            selected = [result['current_receipt'] or 'aggregate'] if args.audit_driver == 'focused' else list(json.loads(local_path(args.root, args.ledger).read_text(encoding='utf-8'))['disjoint_component_scopes'])
            print(audit_driver(result, selected), end='')
        elif args.json:
            print(json.dumps({'schema_version': 1, 'validation': 'saved receipt replay; no fresh Lean compile',
                              'scope_counts': {k: v['count'] for k, v in result['scopes'].items()},
                              'disjoint_component_count': result['disjoint_count'],
                              'current_receipt': result['current_receipt'],
                              'summary_receipt_ids': result['summary_receipt_ids']}, indent=2))
        else:
            print(generated, end='')
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'Claims validation failed: {error}', file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
