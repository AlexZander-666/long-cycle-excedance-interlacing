#!/usr/bin/env python3
"""Rebuild the twelve-page manuscript twice from the six permitted sources."""
import argparse
from hashlib import sha256
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

PAPER = Path(__file__).resolve().parents[1] / "paper"
TEX_INPUTS = ("estimates.tex", "finite.tex", "five.tex", "four.tex", "general-cutoff.tex", "main.tex")
LOG_WARNINGS = re.compile(
    r"^(?:Overfull|Missing character|LaTeX Warning|Package \S+ Warning)|"
    r"undefined references|multiply defined", re.IGNORECASE | re.MULTILINE
)
SOURCE_DATE_EPOCH = "1795651200"


def build(paper=PAPER):
    env = dict(os.environ, SOURCE_DATE_EPOCH=SOURCE_DATE_EPOCH, FORCE_SOURCE_DATE="1", TZ="UTC")
    with tempfile.TemporaryDirectory(prefix="cutoff-five-paper-") as directory:
        work = Path(directory)
        for name in TEX_INPUTS:
            shutil.copyfile(paper / name, work / name)
        for number in (1, 2):
            result = subprocess.run(
                ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                cwd=work, env=env, capture_output=True, text=True
            )
            if result.returncode:
                raise SystemExit(f"PDFLaTeX failed on pass {number}\n{result.stdout}\n{result.stderr}")
        if LOG_WARNINGS.search((work / "main.log").read_text()):
            raise SystemExit("PDFLaTeX final-pass warnings:\n" + (work / "main.log").read_text())
        result = work / "main.pdf"
        info = subprocess.check_output(["pdfinfo", result], env=dict(env, LC_ALL="C"), text=True)
        if not re.search(r"^Pages:\s+12\s*$", info, re.M):
            raise SystemExit("The rebuilt paper does not have twelve pages")
        return result.read_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact", action="store_true", help="compare with the frozen manuscript PDF")
    args = parser.parse_args()
    for command in ("pdflatex", "pdfinfo"):
        if not shutil.which(command):
            parser.error(f"{command} is required")
    print(subprocess.check_output(["pdflatex", "--version"], text=True).splitlines()[0])
    first, second = build(), build()
    if first != second:
        raise SystemExit("Independent builds produced different PDF bytes")
    if args.exact and first != (PAPER / "main.pdf").read_bytes():
        raise SystemExit("The independent PDF builds differ from the frozen edition")
    print(f"PASS two independent two-pass builds of twelve pages, SHA-256 {sha256(first).hexdigest()}"
          + (", frozen PDF bytes match." if args.exact else "."))


if __name__ == "__main__":
    main()
