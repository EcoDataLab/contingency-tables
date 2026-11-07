"""Derive the bounded-output observer and updated candidate pins; execute no checks."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def inputs():
    pins = json.loads((HERE / "source/integration-pins.json").read_text())
    path = REPO / pins["base_assembler"]
    raw = path.read_bytes()
    if digest(raw) != pins["base_assembler_sha256"]:
        raise ValueError("Base source assembler changed")
    spec = importlib.util.spec_from_file_location("memory_fixed_source_assembler", path)
    base = importlib.util.module_from_spec(spec)
    # Load the bytes just authenticated, without rereading the file for execution.
    base.__file__ = str(path)
    exec(compile(raw, str(path), "exec"), base.__dict__)
    files = base.sources()
    recipe = json.loads((HERE / "source/observer-recipe.json").read_text())
    key = "candidate/tested-runtime/strict_serial_check.py"
    if digest(files[key]) != recipe["source_sha256"]:
        raise ValueError("Observer base pin mismatch")
    text = files[key].decode("utf-8")
    for row in recipe["replacements"]:
        if text.count(row["old"]) != 1:
            raise ValueError("Observer delta is not unique")
        text = text.replace(row["old"], row["new"])
    files[key] = text.encode("utf-8")
    if digest(files[key]) != recipe["result_sha256"]:
        raise ValueError("Observer result pin mismatch")
    for name, old_pin, new_pin, before, after in (
        ("candidate/strict_sampler.py", recipe["source_sha256"], recipe["result_sha256"], pins["base_runner_sha256"], pins["runner_sha256"]),
        ("preparation/prepare_memos.py", pins["base_runner_sha256"], pins["runner_sha256"], pins["base_preparation_sha256"], pins["preparation_sha256"]),
    ):
        if digest(files[name]) != before or files[name].count(old_pin.encode()) != 1:
            raise ValueError("Candidate/preparation base pin mismatch")
        files[name] = files[name].replace(old_pin.encode(), new_pin.encode())
        if digest(files[name]) != after:
            raise ValueError("Candidate/preparation result pin mismatch")
    path = REPO / pins["tail_deriver"]
    raw = path.read_bytes()
    if digest(raw) != pins["tail_deriver_sha256"]:
        raise ValueError("Tail derivation source changed")
    spec = importlib.util.spec_from_file_location("bounded_tail_derivation", path)
    tail = importlib.util.module_from_spec(spec)
    tail.__file__ = str(path)
    exec(compile(raw, str(path), "exec"), tail.__dict__)
    supervisor = tail.source()
    if digest(supervisor) != pins["supervisor_sha256"]:
        raise ValueError("Tail supervisor result pin mismatch")
    files["supervisor/vm_sampler_supervisor.py"] = supervisor
    return files

def assemble(destination):
    files = inputs()
    destination = Path(destination)
    destination.mkdir(exist_ok=False)
    hashes = {}
    for name, raw in files.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        if digest(path.read_bytes()) != digest(raw):
            raise ValueError("Assembly readback mismatch")
        hashes[name] = digest(raw)
    receipt = {"status": "source_only_assembled_no_preparation_or_proof_executed", "files_sha256": hashes}
    (destination / "assembly.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return receipt

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(assemble(args.destination), indent=2, sort_keys=True))
