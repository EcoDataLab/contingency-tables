"""Materialize the exact reviewed tail-parser repair without running a supervisor."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

def source(recipe_path=HERE / "source/supervisor-recipe.json", repo=REPO):
    recipe = json.loads(recipe_path.read_text())
    raw = (repo / recipe["source"]).read_bytes()
    if hashlib.sha256(raw).hexdigest() != recipe["source_sha256"]:
        raise ValueError("Frozen supervisor source mismatch")
    text = raw.decode("utf-8")
    for replacement in recipe["replacements"]:
        if text.count(replacement["old"]) != 1:
            raise ValueError("Supervisor delta is not unique")
        text = text.replace(replacement["old"], replacement["new"])
    result = text.encode("utf-8")
    if hashlib.sha256(result).hexdigest() != recipe["result_sha256"]:
        raise ValueError("Derived supervisor pin mismatch")
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    raw = source()
    with args.output.open("xb") as stream:
        stream.write(raw)
    print(hashlib.sha256(raw).hexdigest())
