#!/usr/bin/env python3
"""Build deterministic, independently usable cutoff-five release assets."""
import argparse
from hashlib import sha256
from pathlib import Path, PurePosixPath
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

import check_edition
from check_paper import TEX_INPUTS

ROOT = Path(__file__).resolve().parents[1]
STAMP = (2026, 11, 26, 0, 0, 0)
VERSION = "1.1.0"
LICENSING = ("CITATION.cff", "LICENSE", "LICENSE-SCOPE.md", "NOTICE",
             "licenses/MIT-previous-edition.txt")
LEAN_README = b"""# Cutoff-five Lean source

The original unweighted strict-excedance pair interlaces for all upper sizes
from 6. The independent weights on cycle lengths 2, 3 and 4 are covered
from upper size 49. See formal/LongCycleBounds/FiveCutoffVerified.lean and
the public Spark replay and axiom records in verification/spark/.

After installing the Lean toolchain in formal/lean-toolchain, put its
binaries on PATH. Verify the frozen formal sources and run the audit.

    (cd formal && sha256sum -c SHA256SUMS)
    python3 -Bu formal/verify_lean.py formal CutoffFiveFinalAudit --serial

The verifier obtains independently pinned external dependencies and rebuilds
the local proof closure. Alternatively pass --packages PATH to reuse
prepared external dependency caches.
"""
RESEARCH_README = b"""# Cutoff-five research reproduction

See cutoff-five/README.md for the theorem scope, exact arithmetic, PDF
reproduction, and full Lean replay. See LICENSE-SCOPE.md for the source
license and the separate manuscript and accompanying research data.
"""


def zip_files(path, members, compresslevel=None):
    names = sorted(members)
    with ZipFile(path, "w") as archive:
        for name in names:
            relative = PurePosixPath(name)
            if relative.is_absolute() or ".." in relative.parts or relative.as_posix() != name:
                raise ValueError(f"Unsafe ZIP member {name}")
            info = ZipInfo(name, STAMP)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, members[name], ZIP_DEFLATED, compresslevel=compresslevel)
    with ZipFile(path) as archive:
        if archive.namelist() != names or archive.testzip() is not None or any(
            archive.read(name) != members[name] for name in names
        ):
            raise ValueError(f"ZIP readback failed for {path.name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="directory for the sealed assets")
    args = parser.parse_args()
    check_edition.main()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        parser.error("Place the generated assets outside the source edition")
    output.mkdir(parents=True, exist_ok=True)
    (output / "cutoff-five-paper.pdf").write_bytes((ROOT / "paper/main.pdf").read_bytes())
    zip_files(output / "cutoff-five-arxiv-source.zip",
              {name: (ROOT / "paper" / name).read_bytes() for name in TEX_INPUTS})
    manifest = check_edition.inventory(ROOT)
    documents = {name: (ROOT.parent / name).read_bytes() for name in LICENSING}
    lean = {name: (ROOT / name).read_bytes() for name in manifest
            if name.startswith(("formal/", "verification/spark/"))}
    proof_zip = f"cutoff-five-lean-source-v{VERSION}.zip"
    zip_files(output / proof_zip, documents | lean | {"README.md": LEAN_README}, 9)
    research = {"cutoff-five/" + name: (ROOT / name).read_bytes()
                for name in {*manifest, "SHA256SUMS"}}
    research_zip = f"cutoff-five-research-v{VERSION}.zip"
    zip_files(output / research_zip, documents | research | {"README.md": RESEARCH_README}, 9)
    files = ("cutoff-five-paper.pdf", "cutoff-five-arxiv-source.zip", proof_zip, research_zip)
    checks = "".join(f"{sha256((output / name).read_bytes()).hexdigest()}  {name}\n"
                     for name in sorted(files))
    (output / "SHA256SUMS").write_text(checks)
    print(checks, end="")


if __name__ == "__main__":
    main()
