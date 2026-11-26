#!/usr/bin/env python3
"""Verify the cutoff-five release inventory, closure, exact paper, and public receipts."""
import csv
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import tomllib

ROOT = Path(__file__).resolve().parents[1]
AUDIT = "CutoffFiveFinalAudit"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORTS = re.compile(r"^(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)", re.M)


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def file(root, name):
    relative = PurePosixPath(name)
    path = root / relative
    require(not relative.is_absolute() and ".." not in relative.parts and relative.as_posix() == name,
            f"Unsafe path {name}")
    require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root),
            f"Missing or unsafe release file {name}")
    return path


def checksum(path):
    return sha256(path.read_bytes()).hexdigest()


def inventory(root):
    files = {}
    for line in file(root, "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        require(name not in files and re.fullmatch(r"[0-9a-f]{64}", digest), f"Invalid seal {name}")
        require(checksum(file(root, name)) == digest, f"Checksum does not match for {name}")
        files[name] = digest
    return files


def tsv(root, name):
    with file(root, name).open(newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def module_path(name):
    return "/".join(name.split(".")) + ".lean"


def import_closure(formal, names):
    seen = set()
    queue = [AUDIT]
    while queue:
        name = queue.pop()
        if name in seen:
            continue
        seen.add(name)
        contents = file(formal, module_path(name)).read_text()
        for line in IMPORTS.findall(contents):
            for dependency in line.split("--", 1)[0].split():
                if module_path(dependency) in names:
                    queue.append(dependency)
                else:
                    require(dependency.split(".", 1)[0] in {"Mathlib", "Lean", "Init", "Std"},
                            f"Unrecognized external import {dependency}")
    return seen


def main():
    release = inventory(ROOT)
    formal = ROOT / "formal"
    sources = inventory(formal)
    names = {name for name in sources if name.endswith(".lean")}
    require(len(names) == 180 and set(sources) - names == {
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify_lean.py"
    }, "The formal source inventory is incomplete")
    require({name for name in release if name.startswith("formal/")} ==
            {"formal/" + name for name in set(sources) | {"SHA256SUMS"}},
            "The standalone source manifest differs from the release")
    modules = import_closure(formal, names)
    require({module_path(name) for name in modules} == names, "Unreachable formal source")
    for name in names:
        contents = file(formal, name).read_text()
        require(not re.search(r"^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b", contents, re.M),
                f"Unexpected axiom or unchecked tactic in {name}")

    lock = json.loads(file(formal, "lake-manifest.json").read_text())
    pins = {row["name"]: row for row in lock["packages"]}
    require(len(pins) == len(lock["packages"]) == 9 and all(
        item["type"] == "git" and item["url"].startswith("https://")
        and re.fullmatch(r"[0-9a-f]{40}", item["rev"]) for item in pins.values()
    ), "Expected nine unique HTTPS Git pins")
    config = tomllib.loads(file(formal, "lakefile.toml").read_text())
    require(file(formal, "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
            and pins["mathlib"]["rev"] == MATHLIB
            and config["require"] == [{"name": "mathlib", "git": pins["mathlib"]["url"], "rev": MATHLIB}]
            and config["defaultTargets"] == [AUDIT], "Formal configuration and lock disagree")

    summary = json.loads(file(ROOT, "verification/spark/summary.json").read_text())
    require(summary["machine"] == "aarch64" and summary["strict_build_exit"] == 0
            and summary["mathlib"] == MATHLIB and summary["audit"] == AUDIT
            and summary["formal_inventory_sha256"] == release["formal/SHA256SUMS"]
            and summary["replayed_modules"] == len(modules) - 1
            and summary["audited_declarations"] == 24, "Invalid independent Spark summary")
    records = tsv(ROOT, "verification/spark/module-replays.tsv")
    replayed = modules - {AUDIT}
    require(len(records) == len(replayed) and {row["module"] for row in records} == replayed,
            "Kernel receipts differ from the complete project module closure")
    require(all(row["kernel_exit"] == "0" and
                row["source_sha256"] == sources[module_path(row["module"])] for row in records),
            "Kernel receipts do not match the frozen Lean source")
    expected = re.findall(r"^#print axioms ([^\s]+)\s*$", file(formal, module_path(AUDIT)).read_text(), re.M)
    axioms = tsv(ROOT, "verification/spark/axioms.tsv")
    require(len(expected) == len(axioms) == 24 and
            {row["declaration"] for row in axioms} == set(expected) and
            all(set(filter(None, row["transitive_axioms"].split(","))) <= ALLOWED_AXIOMS for row in axioms),
            "Unexpected transitive axiom or incomplete audit")

    paper = json.loads(file(ROOT, "verification/paper.json").read_text())
    require(paper["author"] == "Bowen Zuo" and paper["edition"] == "1.1.0"
            and paper["pages"] == 12 and paper["pdf_sha256"] == release["paper/main.pdf"]
            and paper["source_files"] == sorted(name for name in release if name.endswith(".tex")),
            "The named paper metadata does not match the frozen edition")
    print(f"PASS {len(release)} files, {len(replayed)} replayed Lean modules,"
          " 24 axiom audits, nine dependency pins and the named twelve-page paper.")


if __name__ == "__main__":
    main()
