#!/usr/bin/env python3
"""Fail closed on the exact ordered axiom and actual-printer type readback."""
from pathlib import Path
import importlib.util
import sys
sys.dont_write_bytecode=True
packet=Path(__file__).resolve().parent
path=packet.parent/'actual-count-draw-helpers-v1/audit/check_lean_axioms.py'
spec=importlib.util.spec_from_file_location('existing_named_checker',path)
checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
output=sys.stdin.read();tail=(packet/'audit/type-readback.txt').read_text()
try:
    if not output.endswith(tail):raise ValueError('unexpected actual-printer type or compiler output')
    records=checker.check_audit((packet/'PrinterAudit.lean').read_text(),output[:-len(tail)])
    if len(records)!=25:raise ValueError('expected all 25 new declarations')
    if 'printMatrixRealizer 4' not in tail or '∀ (rows : List (List ℕ))' not in tail:
        raise ValueError('expected global actual printer degree 4 endpoint')
except (OSError,ValueError) as error:
    print('Audit failed: '+str(error),file=sys.stderr);raise SystemExit(1)
print('Ordered 25-name standard-axiom audit and exact actual-printer readback passed.')
