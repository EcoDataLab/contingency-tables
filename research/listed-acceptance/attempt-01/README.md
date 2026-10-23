# Preserved initial compile failure

The first source omitted the opening of `Math115.PhysicalStationarySuccess`,
which defines `Fibre`. Compilation failed on four unresolved identifiers.
The downstream `sorry` warnings are error-recovery declarations, not written
proof placeholders; this failed environment is not verification evidence.
No audit ran. The successful revision only opens that namespace.

Source bytes are unchanged. Diagnostic paths use `<packet>` and `<repo>` and
trailing whitespace is removed. The result records both original and public
diagnostic hashes. The successful source and audit are separate.
