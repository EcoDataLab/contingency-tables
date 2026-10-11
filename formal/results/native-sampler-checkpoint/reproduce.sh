#!/usr/bin/env bash
# Ordinary source replay; this is not native orchestration or Comparator.
set -euo pipefail
BUNDLE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPLAY_INPUT="${1:?Usage: reproduce.sh /absolute/path/to/clean-isolated-checkout}"
[[ "$REPLAY_INPUT" == /* ]] || { echo 'Supply an absolute isolated-checkout path' >&2; exit 2; }
REPLAY_ROOT="$(python3 - "$BUNDLE_ROOT" "$REPLAY_INPUT" <<'CHECK'
from pathlib import Path
import hashlib,json,re,shutil,subprocess,sys

def fail(message):
    print(message,file=sys.stderr)
    raise SystemExit(2)

bundle,repo=(Path(value).resolve(strict=True) for value in sys.argv[1:])
if repo==bundle or repo in bundle.parents:
    fail('Refusing to overlay the checkout containing this evidence bundle')
if not (repo/'formal/Math115').is_dir():
    fail('Expected an isolated repository root with formal/Math115')
if not (repo/'.tools/elan/bin/lake').is_file():
    fail('Bootstrap the pinned repository toolchain in the isolated checkout first')

def git(*args):
    result=subprocess.run(['git','-C',str(repo),*args],capture_output=True,check=False)
    if result.returncode:
        fail('Could not read isolated checkout Git metadata')
    return result.stdout

data=json.loads((bundle/'checkpoint.json').read_text())
if Path(git('rev-parse','--show-toplevel').decode().strip()).resolve()!=repo:
    fail('Supply the isolated worktree root rather than a subdirectory')
if git('rev-parse','HEAD').decode().strip()!=data['base_commit']:
    fail('Isolated checkout does not match the recorded base commit')
if git('status','--porcelain=v1','--untracked-files=all'):
    fail('Replay requires a clean isolated worktree; preserve validation logs elsewhere')
if (repo/'formal/lean-toolchain').read_text().strip()!=data['lean_toolchain']:
    fail('Isolated toolchain file does not match the recorded pin')

items=data['latest_sources']
if len(items)!=13:
    fail('Expected the complete thirteen-source overlay')
target_dir=(repo/'formal/Math115').resolve(strict=True)
if repo not in target_dir.parents:
    fail('Overlay destination escapes the isolated checkout')
prepared=[]
seen=set()
for item in items:
    module=item['module']
    if not re.fullmatch(r'Math115\.[A-Za-z][A-Za-z0-9]*',module):
        fail('Unexpected overlay module name')
    name=module.split('.')[-1]+'.lean'
    if name in seen:
        fail('Duplicate overlay module')
    seen.add(name)
    src=(bundle/item['source']).resolve(strict=True)
    if bundle not in src.parents:
        fail('Overlay source escapes the evidence bundle')
    if hashlib.sha256(src.read_bytes()).hexdigest()!=item['source_sha256']:
        fail('Source hash mismatch: '+module)
    dst=target_dir/name
    if dst.is_symlink():
        fail('Refusing a symlinked overlay destination')
    prepared.append((src,dst))

# No overlay write occurs before every source and checkout check has passed.
for src,dst in prepared:
    shutil.copyfile(src,dst)
print(repo)
CHECK
)"
export ELAN_HOME="$REPLAY_ROOT/.tools/elan"
export ELAN_TOOLCHAIN="$(cat "$REPLAY_ROOT/formal/lean-toolchain")"
mkdir -p "$REPLAY_ROOT/checkpoint-replay-output"
cd "$REPLAY_ROOT/formal"
while IFS= read -r module; do
  memory_option="$(python3 - "$BUNDLE_ROOT/checkpoint.json" "$module" <<'CAP'
import json,re,sys
record=next(item for item in json.load(open(sys.argv[1]))['latest_sources'] if item['module']=='Math115.'+sys.argv[2])
option=record.get('explicit_memory_cap_option')
if option is not None:
    if not re.fullmatch(r'-M\d+',option):raise SystemExit('Invalid recorded memory cap option')
    print(option)
CAP
)"
  lean_args=(-j2)
  [[ -z "$memory_option" ]] || lean_args+=("$memory_option")
  if "$REPLAY_ROOT/.tools/elan/bin/lake" --no-cache build "+Math115.${module}:deps"; then
    :
  else
    dependency_result=$?
    printf '%s dependency exit=%s\n' "$module" "$dependency_result" >&2
    exit "$dependency_result"
  fi
  lean_args+=(-DautoImplicit=false --root=. \
    -o "$REPLAY_ROOT/checkpoint-replay-output/${module}.olean" \
    -i "$REPLAY_ROOT/checkpoint-replay-output/${module}.ilean" "Math115/${module}.lean")
  if "$REPLAY_ROOT/.tools/elan/bin/lake" env lean "${lean_args[@]}" \
    > "$REPLAY_ROOT/checkpoint-replay-output/${module}.log" 2>&1; then
    printf '%s exit=0\n' "$module"
  else
    compiler_result=$?
    printf '%s exit=%s\n' "$module" "$compiler_result" >&2
    exit "$compiler_result"
  fi
done < "$BUNDLE_ROOT/build-order.txt"
