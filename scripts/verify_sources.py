#!/usr/bin/env python3
"""Verify the unmodified handoff and pinned public source bytes; execute no source."""

import argparse
import hashlib
import json
from pathlib import Path
import urllib.request


ROOT = Path(__file__).resolve().parents[1]


def verify_bundle():
    checked = 0
    for line in (ROOT / "115/SHA256SUMS").read_text().splitlines():
        expected, name = line.split(maxsplit=1)
        path = ROOT / "115" / name
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"Bundle SHA256 mismatch: {name}")
        checked += 1
    return checked


def verify_upstream(checkout=None):
    manifest = json.loads((ROOT / "115/source-manifest.json").read_text())
    checked = 0
    for item in manifest["files"]:
        if checkout is not None:
            data = (checkout / item["path"]).read_bytes()
        else:
            url = (
                f"https://raw.githubusercontent.com/{item['repository']}/"
                f"{item['commit']}/{item['path']}"
            )
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
        digest = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if digest != item["blob_sha"]:
            raise ValueError(f"Upstream Git blob mismatch: {item['path']}")
        checked += 1
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle-only", action="store_true")
    parser.add_argument("--checkout", type=Path, help="Verify local upstream files instead of downloading")
    args = parser.parse_args()
    report = {"bundle_sha256_verified": verify_bundle()}
    if not args.bundle_only:
        report["upstream_git_blobs_verified"] = verify_upstream(args.checkout)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
