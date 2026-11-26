#!/usr/bin/env python3
"""Check the frozen source ledger, release manifest, Lean lock and audit receipts."""

import csv
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import tomllib

ROOT = Path(__file__).resolve().parents[1]
AUDITS = {
    "k3": ("FixedThreeAllAudit", 282, 27),
    "k4": ("FixedFourAllAudit", 423, 12),
    "cube": ("FixedCutoffCubeAudit", 125, 77),
}
IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import[ \t]+([^\n]+)", re.M)
HEX = re.compile(r"[0-9a-f]{64}")
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"


def require(predicate, message):
    if not predicate:
        raise SystemExit(message)


def file(name):
    parts = PurePosixPath(name)
    require(not parts.is_absolute() and ".." not in parts.parts, f"Unsafe relative path {name}")
    path = ROOT / parts
    require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(ROOT),
            f"Expected a regular release file at {name}")
    return path


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def rows(name):
    with file(name).open() as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def module_path(module):
    return Path(*module.split(".")).with_suffix(".lean").as_posix()


def closure(entry, local_sources):
    found = set()
    stack = [entry]
    while stack:
        module = stack.pop()
        if module in found:
            continue
        found.add(module)
        contents = file(module_path(module)).read_text()
        for line in IMPORT.findall(contents):
            for dependency in line.split("--", 1)[0].split():
                if module_path(dependency) in local_sources:
                    stack.append(dependency)
                else:
                    require(dependency.split(".", 1)[0] in {"Mathlib", "Lean", "Init", "Std"},
                            f"Missing local module {dependency}")
    return found


def main():
    manifest = {}
    for line in file("verification/SHA256SUMS").read_text().splitlines():
        checksum, name = line.split("  ", 1)
        require(name not in manifest and HEX.fullmatch(checksum), f"Duplicate or invalid seal {name}")
        require(digest(file(name)) == checksum, f"Release checksum mismatch for {name}")
        manifest[name] = checksum
    require(len(manifest) > 608, "The release manifest is incomplete")

    archives = rows("verification/archives.tsv")
    origin_names = {row["archive"] for row in archives}
    require(len(archives) == len(origin_names) == 3, "Expected three archived lineages")
    for row in archives:
        audit, count, _ = AUDITS[row["scope"]]
        require(row["audit"] == audit and int(row["project_modules"]) == count
                and HEX.fullmatch(row["sha256"]), f"Invalid archive record {row['scope']}")
    origins = rows("verification/source-origins.tsv")
    sources = {}
    for row in origins:
        name = row["path"]
        require(name not in sources and row["sha256"] == manifest.get(name)
                and int(row["bytes"]) == file(name).stat().st_size
                and set(row["release_archives"].split()) <= origin_names,
                f"Invalid source origin for {name}")
        sources[name] = row["sha256"]
    lean = {name for name in sources if name.endswith(".lean")}
    require(len(lean) == 608 and set(sources) - lean == {"lean-toolchain", "lake-manifest.json"}
            and {name for name in manifest if name.endswith(".lean")} == lean,
            "Unexpected proof source inventory")

    require(file("lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1",
            "Incorrect Lean pin")
    config = tomllib.loads(file("lakefile.toml").read_text())
    packages = json.loads(file("lake-manifest.json").read_text())["packages"]
    by_name = {item["name"]: item for item in packages}
    require(len(by_name) == len(packages) == 9 and all(
        item["type"] == "git" and item["url"].startswith("https://")
        and re.fullmatch(r"[0-9a-f]{40}", item["rev"]) for item in packages
    ), "The dependency lock must contain nine pinned HTTPS Git checkouts")
    require(by_name["mathlib"]["rev"] == MATHLIB and config["require"] == [
        {"name": "mathlib", "git": by_name["mathlib"]["url"], "rev": MATHLIB}
    ], "Mathlib source and lock pins differ")
    require(set(config["defaultTargets"]) == {record[0] for record in AUDITS.values()},
            "Lake targets differ from the frozen audit set")

    for scope, (audit, count, declarations) in AUDITS.items():
        modules = rows(f"verification/spark/{scope}-modules.tsv")
        names = {row["module"] for row in modules}
        require(len(names) == len(modules) == count and names == closure(audit, lean) - {audit},
                f"Module receipts do not match the {audit} transitive import closure")
        for row in modules:
            require(sources[module_path(row["module"])] == row["source_sha256"]
                    and (bool(HEX.fullmatch(row["olean_sha256"])) or
                         (scope == "cube" and not row["olean_sha256"])),
                    f"Malformed compile receipt for {row['module']}")
        expected = re.findall(r"^#print axioms (\S+)\s*$", file(module_path(audit)).read_text(), re.M)
        axioms = rows(f"verification/spark/{scope}-axioms.tsv")
        require(len(expected) == len(axioms) == declarations
                and {row["declaration"] for row in axioms} == set(expected)
                and all({a.strip() for a in row["transitive_axioms"].split(",") if a.strip()} <= STANDARD
                        for row in axioms), f"Invalid transitive axiom receipt for {audit}")
    print(f"PASS {len(manifest)} frozen checksums, {len(lean)} Lean sources, nine lock pins and three audit closures")


if __name__ == "__main__":
    main()
