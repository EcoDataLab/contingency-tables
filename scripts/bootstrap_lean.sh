#!/usr/bin/env bash
# Install only into this checkout.  Do not run `lake update`: dependency pins
# are part of the reproduction record.
set -euo pipefail

TASK_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
UPSTREAM_REV=fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
MATHLIB_REV=d13f23b723b8a846827a245b89c10fc7d3f11612
ELAN_VERSION=v4.2.4
export ELAN_HOME="$TASK_ROOT/.tools/elan"
export MATHLIB_CACHE_DIR="$TASK_ROOT/.tools/mathlib-cache"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    ELAN_PLATFORM=aarch64-apple-darwin
    ELAN_SHA=7ad829861392c718dfebde3a83b5c8508df47be02af68894b094b0b3952616e5 ;;
  Darwin-x86_64)
    ELAN_PLATFORM=x86_64-apple-darwin
    ELAN_SHA=8a340b309d8ed2e96f930761fa223b3af57a38f5d253b53ac90293c9516f8cd4 ;;
  Linux-x86_64)
    ELAN_PLATFORM=x86_64-unknown-linux-gnu
    ELAN_SHA=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63 ;;
  Linux-aarch64)
    ELAN_PLATFORM=aarch64-unknown-linux-gnu
    ELAN_SHA=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9 ;;
  *) echo "Unsupported platform; install the pinned Lean toolchain locally." >&2; exit 2 ;;
esac

ensure_checkout() {
  local checkout="$1" url="$2" revision="$3"
  if [[ -d "$checkout/.git" ]]; then
    [[ "$(git -C "$checkout" rev-parse HEAD)" == "$revision" ]] || {
      echo "Existing checkout has a different revision: $checkout" >&2; exit 2;
    }
    git -C "$checkout" diff --quiet
    git -C "$checkout" diff --cached --quiet
    return
  fi
  git clone --filter=blob:none --no-checkout --depth 1 "$url" "$checkout"
  git -C "$checkout" fetch --depth 1 origin "$revision"
  if [[ "$revision" == "$UPSTREAM_REV" ]]; then
    git -C "$checkout" sparse-checkout set lean \
      preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026 \
      preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026
  fi
  git -C "$checkout" checkout --detach "$revision"
}

mkdir -p "$TASK_ROOT/.tools/downloads" "$TASK_ROOT/.tools/elan-init"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  ELAN_ARCHIVE="$TASK_ROOT/.tools/downloads/elan-$ELAN_VERSION-$ELAN_PLATFORM.tar.gz"
  curl -fL --retry 3 \
    "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$ELAN_PLATFORM.tar.gz" \
    -o "$ELAN_ARCHIVE"
  python3 - "$ELAN_ARCHIVE" "$ELAN_SHA" "$TASK_ROOT/.tools/elan-init" <<'PY'
import hashlib, pathlib, sys, tarfile
archive, expected, destination = sys.argv[1:]
assert hashlib.sha256(pathlib.Path(archive).read_bytes()).hexdigest() == expected, "Elan checksum mismatch"
with tarfile.open(archive) as bundle:
    # Official release contains one installer.  Avoid generic archive paths.
    member = bundle.getmember("elan-init")
    assert member.isfile()
    output = pathlib.Path(destination) / "elan-init"
    output.write_bytes(bundle.extractfile(member).read())
    output.chmod(0o755)
PY
  "$TASK_ROOT/.tools/elan-init/elan-init" -y --no-modify-path --default-toolchain none
fi

ensure_checkout "$TASK_ROOT/.upstream/openai-math" \
  https://github.com/openai/math.git "$UPSTREAM_REV"
cmp "$TASK_ROOT/formal/lean-toolchain" "$TASK_ROOT/.upstream/openai-math/lean/lean-toolchain"
"$ELAN_HOME/bin/elan" toolchain install "$(cat "$TASK_ROOT/formal/lean-toolchain")"
ensure_checkout "$TASK_ROOT/formal/.lake/packages/mathlib" \
  https://github.com/leanprover-community/mathlib4.git "$MATHLIB_REV"

# Lake resolves the remaining small packages from the committed manifest.
# Some unchanged upstream imports use all of Mathlib, so the complete Mathlib
# cache is required.  It remains under .tools/ and formal/.lake/.
cd "$TASK_ROOT/formal"
"$ELAN_HOME/bin/lake" env lean --version
"$ELAN_HOME/bin/lake" exe cache get
