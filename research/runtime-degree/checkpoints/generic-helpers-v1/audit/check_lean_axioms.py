#!/usr/bin/env python3
"""Check every requested declaration; unexpected compiler output fails closed.

The pinned audit files contain only imports and named axiom-print commands.
Even a compiler warning requires inspection before accepting their output.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
REPORT = re.compile(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")


def check_audit(source: str, output: str) -> list[dict]:
    names = re.findall(r"^#print axioms (\S+)\s*$", source, re.MULTILINE)
    if not names or len(set(names)) != len(names):
        raise ValueError("audit must request distinct named declarations")
    if REPORT.sub("", output).strip():
        raise ValueError("unrecognized compiler output in axiom audit")
    records = [{"name": name, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]}
               for name, axioms in REPORT.findall(output)]
    if [entry["name"] for entry in records] != names:
        raise ValueError("axiom reports must match every requested declaration in order")
    for entry in records:
        extra = set(entry["axioms"]) - ALLOWED
        if extra:
            raise ValueError(f"unexpected axioms for {entry['name']}: {sorted(extra)}")
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("audit_file", type=Path)
    args = parser.parse_args()
    try:
        records = check_audit(args.audit_file.read_text(), sys.stdin.read())
    except (OSError, ValueError) as error:
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        return 1
    print(f"Axiom allowlist passed for {len(records)} declarations.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
