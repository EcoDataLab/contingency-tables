#!/usr/bin/env bash
# Strict, repository-local Linux Comparator tooling. This script does not edit
# upstream sources, install global packages, or start a user systemd manager.
set -euo pipefail

TASK_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COMPARATOR_REV=d03acab154d269c06e60e4de7e4cc85deebff94b
EXPORTER_REV=076e8e57707e813375e8f9da8bf989799ace9680
LANDRUN_REV=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
GO_VERSION=go1.27.2
GO_ARCHIVE_SHA=ecbadb99091a3f46e31f5f934b068b1864eafa7995211b39eaddf76996045fe5
PROJECT_TOOLCHAIN=leanprover/lean4:v4.34.1
CHECKER_SOURCE_TOOLCHAIN=leanprover/lean4:v4.34.0
TOOLS_DIR="$TASK_ROOT/.tools"
CHECKER_DIR="$TOOLS_DIR/comparator"
LANDRUN_DIR="$TOOLS_DIR/landrun"
BIN_DIR="$TOOLS_DIR/verification-bin"
EVIDENCE_DIR="$TOOLS_DIR/linux-verification"
export ELAN_HOME="$TOOLS_DIR/elan"
export MATHLIB_CACHE_DIR="$TOOLS_DIR/mathlib-cache"

fail() { printf 'Verification prerequisite failed: %s\n' "$*" >&2; exit 2; }

linux_preflight() {
  [[ "$(uname -s)-$(uname -m)" == Linux-x86_64 ]] || fail "this strict workflow requires Linux x86_64"
  [[ "$(id -u)" -ne 0 ]] || fail "Comparator must run as a non-root user"
  command -v systemd-run >/dev/null || fail "systemd-run is unavailable"
  # A missing user manager is an unsupported runner, not permission to weaken
  # the sandbox. Do not enable lingering or create a system-wide service here.
  export XDG_RUNTIME_DIR="${XDG_RUNTIME_DIR:-/run/user/$(id -u)}"
  [[ -S "$XDG_RUNTIME_DIR/bus" ]] || fail "no existing systemd user bus at $XDG_RUNTIME_DIR/bus"
  export DBUS_SESSION_BUS_ADDRESS="${DBUS_SESSION_BUS_ADDRESS:-unix:path=$XDG_RUNTIME_DIR/bus}"
  python3 - <<'PY'
import ctypes, json, os, pathlib, platform
status = dict(line.split(":", 1) for line in pathlib.Path("/proc/self/status").read_text().splitlines() if ":" in line)
if int(status["CapEff"].strip(), 16):
    raise SystemExit("Refusing an effective-capability-bearing verification process")
libc = ctypes.CDLL(None, use_errno=True)
# __NR_landlock_create_ruleset = 444 on the required x86_64 Linux platform.
abi = libc.syscall(444, ctypes.c_void_p(), ctypes.c_size_t(0), ctypes.c_uint(1))
if abi < 9:
    raise SystemExit(f"Strict pinned Landrun needs Landlock ABI >= 9; found {abi}, errno={ctypes.get_errno()}. No best-effort fallback.")
print(json.dumps({"kernel": platform.release(), "uid": os.getuid(), "landlock_abi": abi, "effective_capabilities": 0}))
PY
  systemd-run --user --wait --pipe --collect --quiet \
    --property=RestrictAddressFamilies=~AF_UNIX --property=NoNewPrivileges=yes \
    --working-directory "$TASK_ROOT" -- /usr/bin/python3 - <<'PY'
import errno, os, pathlib, socket
assert os.getuid() != 0, "user service unexpectedly runs as root"
status = dict(line.split(":", 1) for line in pathlib.Path("/proc/self/status").read_text().splitlines() if ":" in line)
assert int(status["NoNewPrivs"].strip()) == 1, "NoNewPrivileges was not enforced"
assert int(status["CapEff"].strip(), 16) == 0, "effective capabilities remain"
try:
    connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
except OSError as error:
    assert error.errno in (errno.EAFNOSUPPORT, errno.EPERM, errno.EACCES), error
else:
    connection.close()
    raise SystemExit("systemd AF_UNIX restriction was not enforced")
print("Actual non-root systemd user service denies AF_UNIX and enforces NoNewPrivileges.")
PY
}

ensure_checkout() {
  local checkout="$1" url="$2" revision="$3"
  if [[ ! -d "$checkout/.git" ]]; then
    [[ ! -e "$checkout" ]] || fail "existing non-checkout path: $checkout"
    git clone --filter=blob:none --no-checkout --depth 1 "$url" "$checkout"
    git -C "$checkout" fetch --depth 1 origin "$revision"
    git -C "$checkout" checkout --detach "$revision"
  fi
  [[ "$(git -C "$checkout" rev-parse HEAD)" == "$revision" ]] || fail "revision mismatch: $checkout"
  git -C "$checkout" diff --quiet || fail "modified source: $checkout"
  git -C "$checkout" diff --cached --quiet || fail "staged source modifications: $checkout"
}

configure_paths() {
  [[ -x "$ELAN_HOME/bin/lake" ]] || fail "run scripts/bootstrap_lean.sh first"
  [[ "$(cat "$TASK_ROOT/formal/lean-toolchain")" == "$PROJECT_TOOLCHAIN" ]] || fail "project toolchain pin changed"
  export ELAN_TOOLCHAIN="$PROJECT_TOOLCHAIN"
  LEAN_PREFIX="$("$ELAN_HOME/bin/elan" run "$PROJECT_TOOLCHAIN" lean --print-prefix)"
  # Comparator's child sandbox forwards PATH, but does not forward ELAN_HOME.
  # Put the actual pinned Lean/Lake executables before the Elan proxy.
  export PATH="$BIN_DIR:$LEAN_PREFIX/bin:$ELAN_HOME/bin:$PATH"
}

assert_fresh_proof_environment() {
  python3 - "$TASK_ROOT/formal/.lake/build" <<'PY'
import pathlib, sys
build = pathlib.Path(sys.argv[1])
compiled = sorted(str(path) for path in build.rglob("*.olean")) if build.exists() else []
if compiled:
    raise SystemExit("Comparator needs a fresh checking environment; found precompiled project proofs: " + ", ".join(compiled[:5]))
print("No precompiled project proof artifacts; trusted Mathlib package cache is separate.")
PY
}

install_tools() {
  linux_preflight
  configure_paths
  assert_fresh_proof_environment
  mkdir -p "$BIN_DIR" "$EVIDENCE_DIR" "$TOOLS_DIR/downloads" "$TOOLS_DIR/go-runtime"
  ensure_checkout "$CHECKER_DIR" https://github.com/leanprover/comparator.git "$COMPARATOR_REV"
  ensure_checkout "$CHECKER_DIR/.lake/packages/lean4export" https://github.com/leanprover/lean4export.git "$EXPORTER_REV"
  ensure_checkout "$LANDRUN_DIR" https://github.com/Zouuup/landrun.git "$LANDRUN_REV"
  [[ "$(cat "$CHECKER_DIR/lean-toolchain")" == "$CHECKER_SOURCE_TOOLCHAIN" ]] || fail "Comparator source toolchain changed"
  [[ "$(cat "$CHECKER_DIR/.lake/packages/lean4export/lean-toolchain")" == "$CHECKER_SOURCE_TOOLCHAIN" ]] || fail "exporter source toolchain changed"
  python3 - "$CHECKER_DIR/lake-manifest.json" "$EXPORTER_REV" <<'PY'
import json, sys
packages = json.load(open(sys.argv[1]))["packages"]
assert len(packages) == 1 and packages[0]["name"] == "lean4export" and packages[0]["rev"] == sys.argv[2], "exporter dependency pin differs"
PY
  # Explicit source-compatible patch-level rebuild; no toolchain file is edited.
  (cd "$CHECKER_DIR" && "$ELAN_HOME/bin/lake" env lean --version && "$ELAN_HOME/bin/lake" build lean4export comparator)
  git -C "$CHECKER_DIR" diff --exit-code
  git -C "$CHECKER_DIR/.lake/packages/lean4export" diff --exit-code

  if [[ ! -x "$TOOLS_DIR/go-runtime/go/bin/go" ]]; then
    curl -fL --retry 3 "https://go.dev/dl/$GO_VERSION.linux-amd64.tar.gz" \
      -o "$TOOLS_DIR/downloads/$GO_VERSION.linux-amd64.tar.gz"
    python3 - "$TOOLS_DIR/downloads/$GO_VERSION.linux-amd64.tar.gz" "$GO_ARCHIVE_SHA" <<'PY'
import hashlib, pathlib, sys
assert hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest() == sys.argv[2], "Go archive checksum mismatch"
PY
    tar -xzf "$TOOLS_DIR/downloads/$GO_VERSION.linux-amd64.tar.gz" -C "$TOOLS_DIR/go-runtime"
  fi
  local go_binary="$TOOLS_DIR/go-runtime/go/bin/go"
  [[ "$("$go_binary" version)" == "go version $GO_VERSION linux/amd64" ]] || fail "Go compiler version mismatch"
  export GOTOOLCHAIN=local
  export GOCACHE="$TOOLS_DIR/go-build-cache"
  export GOMODCACHE="$TOOLS_DIR/go-module-cache"
  (
    cd "$LANDRUN_DIR"
    "$go_binary" mod download
    "$go_binary" mod verify
    "$go_binary" build -mod=readonly -trimpath -o "$BIN_DIR/landrun-real" ./cmd/landrun
    "$go_binary" version -m "$BIN_DIR/landrun-real"
  )
  git -C "$LANDRUN_DIR" diff --exit-code
  local target name
  for name in comparator lean4export; do
    if [[ "$name" == comparator ]]; then
      target="$CHECKER_DIR/.lake/build/bin/comparator"
    else
      target="$CHECKER_DIR/.lake/packages/lean4export/.lake/build/bin/lean4export"
    fi
    if [[ -L "$BIN_DIR/$name" ]]; then
      [[ "$(readlink "$BIN_DIR/$name")" == "$target" ]] || fail "unexpected $name symlink target"
    elif [[ -e "$BIN_DIR/$name" ]]; then
      fail "unexpected existing $name file"
    else
      ln -s "$target" "$BIN_DIR/$name"
    fi
  done
  # Official Comparator adds --best-effort. Remove exactly that option before
  # the command separator, and invoke the real pinned Landrun without downgrade.
  cat > "$BIN_DIR/landrun" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
strict_bin="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
arguments=()
options=true
for argument in "$@"; do
  if "$options"; then
    case "$argument" in
      --best-effort) continue ;;
      --best-effort=*|-best-effort*|--unrestricted-filesystem*|-unrestricted-filesystem*|--unrestricted-network*|-unrestricted-network*|--unrestricted-scoped*|-unrestricted-scoped*)
        echo "Strict Landrun adapter refuses a weakening option: $argument" >&2; exit 2 ;;
      --) options=false ;;
    esac
  fi
  arguments+=("$argument")
done
exec "$strict_bin/landrun-real" "${arguments[@]}"
SH
  chmod +x "$BIN_DIR/landrun"
  strict_landrun_probe
  python3 - "$TASK_ROOT" "$COMPARATOR_REV" "$EXPORTER_REV" "$LANDRUN_REV" "$GO_VERSION" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
bins = root / ".tools/verification-bin"
record = {"comparator_revision": sys.argv[2], "lean4export_revision": sys.argv[3],
          "landrun_revision": sys.argv[4], "go_version": sys.argv[5],
          "checker_declared_toolchain": "leanprover/lean4:v4.34.0",
          "actual_build_toolchain": "leanprover/lean4:v4.34.1",
          "strict_adapter": "removes exact --best-effort before command separator; invokes pinned real Landrun",
          "binary_sha256": {name: hashlib.sha256((bins / name).read_bytes()).hexdigest()
                            for name in ("comparator", "lean4export", "landrun", "landrun-real")}}
(root / ".tools/linux-verification/checker-provenance.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
PY
}

strict_landrun_probe() {
  local probe_root="$TOOLS_DIR/sandbox-probe"
  mkdir -p "$probe_root/allowed" "$probe_root/denied"
  cat > "$probe_root/probe.py" <<'PY'
import errno, pathlib, socket, sys
base = pathlib.Path(sys.argv[1])
(base / "allowed/witness").write_text("allowed\n")
try:
    (base / "denied/must-not-exist").write_text("sandbox failure\n")
except PermissionError:
    pass
else:
    raise SystemExit("Landrun permitted a write outside its allowed directory")
for family, kind in ((socket.AF_UNIX, socket.SOCK_STREAM), (socket.AF_INET, socket.SOCK_STREAM)):
    try:
        with socket.socket(family, kind) as connection:
            if family == socket.AF_INET:
                connection.bind(("127.0.0.1", 0))
    except OSError as error:
        assert error.errno in (errno.EAFNOSUPPORT, errno.EPERM, errno.EACCES), error
    else:
        raise SystemExit(f"sandbox permitted restricted socket operation for family {family}")
print("Strict real Landrun allows the witness write, denies outside writes/TCP bind; systemd denies AF_UNIX.")
PY
  systemd-run --user --wait --pipe --collect --quiet \
    --property=RestrictAddressFamilies=~AF_UNIX --property=NoNewPrivileges=yes \
    --working-directory "$TASK_ROOT" -- \
    "$BIN_DIR/landrun" --best-effort --rox / --rw /dev --rw "$probe_root/allowed" -- \
    /usr/bin/python3 "$probe_root/probe.py" "$probe_root"
  [[ ! -e "$probe_root/denied/must-not-exist" ]] || fail "Landrun denial witness exists"
}

run_comparator() {
  linux_preflight
  configure_paths
  assert_fresh_proof_environment
  [[ -f "$EVIDENCE_DIR/checker-provenance.json" ]] || fail "strict tools bootstrap has not completed"
  for binary in comparator lean4export landrun landrun-real; do
    [[ -x "$BIN_DIR/$binary" ]] || fail "missing $binary"
  done
  python3 - "$TASK_ROOT" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
record = json.loads((root / ".tools/linux-verification/checker-provenance.json").read_text())
for name, expected in record["binary_sha256"].items():
    assert hashlib.sha256((root / ".tools/verification-bin" / name).read_bytes()).hexdigest() == expected, f"checker binary changed: {name}"
PY
  [[ "$(git -C "$TASK_ROOT/.upstream/openai-math" rev-parse HEAD)" == fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb ]] || fail "upstream source pin differs"
  git -C "$TASK_ROOT/.upstream/openai-math" diff --quiet
  git -C "$TASK_ROOT/.upstream/openai-math" diff --cached --quiet
  strict_landrun_probe
  systemd-run --user --wait --pipe --collect \
    --property=RestrictAddressFamilies=~AF_UNIX --property=NoNewPrivileges=yes \
    -E "PATH=$PATH" -E "ELAN_HOME=$ELAN_HOME" -E "MATHLIB_CACHE_DIR=$MATHLIB_CACHE_DIR" \
    -E "COMPARATOR_LANDRUN=$BIN_DIR/landrun" -E "COMPARATOR_LEAN4EXPORT=$BIN_DIR/lean4export" \
    --working-directory "$TASK_ROOT/formal" -- \
    "$LEAN_PREFIX/bin/lake" env "$BIN_DIR/comparator" \
    ../.upstream/openai-math/lean/ComparatorChallenges/ContingencyTables.json
}

case "${1:-}" in
  preflight) linux_preflight ;;
  bootstrap) install_tools ;;
  verify) run_comparator ;;
  *) printf 'Usage: %s [preflight|bootstrap|verify]\n' "$0" >&2; exit 2 ;;
esac
