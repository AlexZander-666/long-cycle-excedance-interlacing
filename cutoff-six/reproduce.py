"""Rebuild the PDF from loose TeX and from a fresh source ZIP without changing inputs on failure."""

from hashlib import sha256
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


root = Path(__file__).resolve().parent
paper = root / "paper"
source_zip = root / "arxiv-source.zip"
source_names = ("estimates.tex", "finite.tex", "five.tex", "four.tex", "general-cutoff.tex", "main.tex", "six.tex")
frozen_time = (2026, 11, 26, 0, 0, 0)
local_tex = Path.home() / ".cache/spark-math-research/texlive/2026/bin/aarch64-linux/pdflatex"
pdflatex = os.environ.get("PDFLATEX") or shutil.which("pdflatex")
if pdflatex is None and local_tex.is_file():
    pdflatex = str(local_tex)
if pdflatex is None:
    raise SystemExit("Set PDFLATEX to a TeX Live 2026 pdfLaTeX executable.")
env = dict(os.environ, SOURCE_DATE_EPOCH="1795651200", FORCE_SOURCE_DATE="1", TZ="UTC")


def read_zip(zip_path):
    with ZipFile(zip_path) as archive:
        assert tuple(archive.namelist()) == source_names
        assert archive.testzip() is None
        return {name: archive.read(name) for name in source_names}


def make_source_zip(path, sources):
    with ZipFile(path, "w") as archive:
        for name, data in sources.items():
            member = ZipInfo(name, frozen_time)
            member.external_attr = 0o100644 << 16
            archive.writestr(member, data, ZIP_DEFLATED)


def compile_pdf(sources, label):
    with TemporaryDirectory(prefix="long-cycle-six-tex-") as work:
        folder = Path(work)
        for name, data in sources.items():
            (folder / name).write_bytes(data)
        for pass_number in (1, 2):
            run = subprocess.run(
                [pdflatex, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                cwd=folder, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            if run.returncode:
                raise RuntimeError(run.stdout.decode(errors="replace"))
            print(f"{label} pass {pass_number}: exit 0")
        log = (folder / "main.log").read_text()
        warnings = re.findall(r"^(?:Overfull|Missing character|LaTeX Warning|Package \S+ Warning).*", log, re.M)
        if warnings:
            raise RuntimeError("\n".join(warnings))
        return (folder / "main.pdf").read_bytes()


def main():
    # Read every loose source before writing anything. A ZIP-only layout is valid too.
    has_loose_source = any((paper / name).is_file() for name in source_names)
    if has_loose_source:
        loose = {name: (paper / name).read_bytes() for name in source_names}
    else:
        loose = read_zip(source_zip)
    with TemporaryDirectory(prefix=".cutoff-six-build-", dir=root) as work:
        pending_zip = Path(work) / source_zip.name
        make_source_zip(pending_zip, loose)
        extracted = read_zip(pending_zip)
        assert extracted == loose
        pdf = compile_pdf(loose, "source")
        assert compile_pdf(extracted, "ZIP") == pdf, "fresh ZIP rebuild differs"
        paper.mkdir(exist_ok=True)
        pending_pdf = Path(work) / "main.pdf"
        pending_pdf.write_bytes(pdf)
        pending_pdf.replace(paper / "main.pdf")
        pending_zip.replace(source_zip)
    print("TeX source ZIP CRC and exact membership checked")
    print("Fresh source and ZIP builds yield identical PDF bytes")
    print(f"{sha256(pdf).hexdigest()}  paper/main.pdf")
    print(f"{sha256(source_zip.read_bytes()).hexdigest()}  arxiv-source.zip")


if __name__ == "__main__":
    main()
