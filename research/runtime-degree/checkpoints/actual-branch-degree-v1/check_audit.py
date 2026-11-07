#!/usr/bin/env python3
"""Fail closed on ordered axiom reports and the exact recorded degree readback."""
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode=True

packet=Path(__file__).resolve().parent
checker_path=packet.parent/'actual-count-draw-helpers-v1/audit/check_lean_axioms.py'
spec=importlib.util.spec_from_file_location('existing_named_checker',checker_path)
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
source=(packet/'BranchAudit.lean').read_text()
output=sys.stdin.read()
readback=(packet/'audit/type-readback.txt').read_text()
try:
    if not output.endswith(readback):
        raise ValueError('unexpected theorem type/readback or compiler output')
    records=checker.check_audit(source,output[:-len(readback)])
    if len(records)!=20:
        raise ValueError('expected all 20 declarations')
    if 'bothLargeTestRealizer 1008' not in readback or '∀ (z : List ℕ × List ℕ)' not in readback:
        raise ValueError('readback does not state the actual global degree 1008 endpoint')
except (OSError,ValueError) as error:
    print('Audit failed: '+str(error),file=sys.stderr)
    raise SystemExit(1)
print('Ordered 20-name standard-axiom audit and exact actual-degree readback passed.')
