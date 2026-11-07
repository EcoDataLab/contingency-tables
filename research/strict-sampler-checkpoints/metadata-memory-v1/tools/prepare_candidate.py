"""Verify pins and assemble a fresh source-only candidate; execute no checker."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

PACKET = Path(__file__).resolve().parents[1]
REPO = PACKET.parents[2]
LAYOUT = {
    "candidate/strict_sampler.py": "source/versioned_runner.py",
    "candidate/anchored_metadata.py": "source/anchored_metadata.py",
    "preparation/prepare_memos.py": "source/prepare_memos.py",
    "preparation/snapshots.py": "source/snapshots.py",
}
REFERENCE_LAYOUT = {
    "candidate/source-freeze.json": "source_freeze",
    "candidate/tested-runtime/strict_serial_check.py": "observer",
    "candidate/tested-runtime/build_lean_serial.py": "planner",
    "candidate/tested-runtime/no_rebuild_landrun.py": "adapter",
    "preparation/NormalizeMemos.lean": "normalization_helper",
    "original/strict_sampler.py": "original_runner",
    "original/authenticate_runtime.py": "original_authenticator",
    "original/source-freeze.json": "source_freeze",
    "original/tested-runtime/strict_serial_check.py": "original_observer",
    "original/tested-runtime/build_lean_serial.py": "planner",
    "original/tested-runtime/no_rebuild_landrun.py": "adapter",
}

def sha(path):
    with path.open("rb") as stream:
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
        return digest.hexdigest()

def checked(base, name, digest):
    parts = PurePosixPath(name)
    if parts.is_absolute() or ".." in parts.parts or "\\" in name:
        raise ValueError("Escaping source path")
    path = base.joinpath(*parts.parts)
    if not path.is_file() or path.is_symlink():
        raise ValueError("Source pin mismatch: " + name)
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError("Source pin mismatch: " + name)
    return raw

def sources(packet=PACKET, repo=REPO):
    manifest = json.loads((packet / "manifest.json").read_text())
    verified = {name: checked(packet, name, digest)
                for name, digest in manifest["files_sha256"].items()}
    references = json.loads(verified["reproduction-references.json"])["files"]
    external = {name: checked(repo, row["path"], row["sha256"])
                for name, row in references.items()}
    contents = dict(verified)
    for name, recipe in json.loads(contents["derived-sources.json"]).items():
        text = external[recipe["reference"]].decode("utf-8")
        for replacement in recipe["replacements"]:
            if text.count(replacement["old"]) != 1:
                raise ValueError("Derived source replacement is not unique: " + name)
            text = text.replace(replacement["old"], replacement["new"])
        raw = text.encode()
        if hashlib.sha256(raw).hexdigest() != recipe["sha256"]:
            raise ValueError("Derived source pin mismatch: " + name)
        contents[name] = raw
    return {**{name: contents[source] for name, source in LAYOUT.items()},
            **{name: external[source] for name, source in REFERENCE_LAYOUT.items()}}

def assemble(destination, packet=PACKET, repo=REPO):
    inputs = sources(packet, repo)  # Refuse drift before creating any output.
    destination = Path(destination)
    destination.mkdir(exist_ok=False)
    output = {}
    for name, raw in inputs.items():
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        if sha(target) != hashlib.sha256(raw).hexdigest():
            raise ValueError("Source changed during assembly: " + name)
        output[name] = sha(target)
    receipt = {"status": "source_only_assembled_no_preparation_or_proof_executed",
               "files_sha256": output}
    (destination / "assembly.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return receipt

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(assemble(args.destination), indent=2, sort_keys=True))
