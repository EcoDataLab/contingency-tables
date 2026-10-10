#!/usr/bin/env python3
"""Resource adapter: real pinned sandbox, fail-closed Lake trace reuse only."""
from __future__ import annotations
import json
import os
from pathlib import Path
import sys

class AdapterError(RuntimeError):
    pass

def rewrite(arguments: list[str], lake: str, roots: tuple[str, ...], exporter: str) -> list[str]:
    if "--" not in arguments:
        raise AdapterError("Missing sandbox command separator")
    split = arguments.index("--")
    command = arguments[split + 1:]
    if not command:
        raise AdapterError("Missing sandboxed command")
    if command[0] in {"lake", lake}:
        if len(command) != 3 or command[1] != "build" or command[2] not in roots:
            raise AdapterError("Only the original descriptor's exact Lake build roots are permitted")
        command = [lake, "--no-cache", "--no-build", "build", command[2]]
    elif command[0] != exporter or len(command) < 3 or command[1] not in roots or command[2] != "--":
        # The hash-pinned original descriptor has no external kernel command;
        # its built-in kernel runs in Comparator itself. Refuse any new child
        # command shape until explicitly reviewed, rather than bypass this gate.
        raise AdapterError("Only original Lake roots and exporter commands are permitted")
    # All sandbox options are preserved byte-for-byte. The unchanged strict
    # adapter removes exact --best-effort and rejects weakening options.
    return [*arguments[:split + 1], *command]

def main() -> int:
    config = json.loads(Path(__file__).with_name("no-rebuild-config.json").read_text())
    strict = config["strict_adapter"]
    adjusted = rewrite(sys.argv[1:], config["lake"], tuple(config["roots"]), config["exporter"])
    os.execv(strict, [strict, *adjusted])
    return 2

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AdapterError, KeyError, ValueError, OSError) as error:
        print(f"Serial resource adapter refused: {error}", file=sys.stderr)
        raise SystemExit(2)
