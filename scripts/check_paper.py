#!/usr/bin/env python3
"""Rebuild the frozen manuscript from its five sources without changing the checkout."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

PAPER = Path(__file__).resolve().parents[1] / "paper"
TEX_INPUTS = ("main.tex", "estimates.tex", "finite.tex", "four.tex", "general-cutoff.tex")
DIAGNOSTICS = re.compile(
    r"overfull|missing character|(?:^|\s)(?:latex|package \S+) warning|"
    r"undefined references|multiply defined",
    re.IGNORECASE | re.MULTILINE,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact", action="store_true", help="Require the released PDF bytes.")
    args = parser.parse_args()
    pdflatex = shutil.which("pdflatex")
    pdfinfo = shutil.which("pdfinfo")
    if not pdflatex or not pdfinfo:
        parser.error("pdfLaTeX and pdfinfo are required")
    env = dict(os.environ, SOURCE_DATE_EPOCH="1795651200", FORCE_SOURCE_DATE="1", TZ="UTC")
    version = subprocess.check_output([pdflatex, "--version"], text=True)
    print(version.splitlines()[0], flush=True)
    with tempfile.TemporaryDirectory(prefix="cycle-paper-replay-") as directory:
        work = Path(directory)
        for name in TEX_INPUTS:
            shutil.copyfile(PAPER / name, work / name)
        for number in (1, 2):
            run = subprocess.run(
                [pdflatex, "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", "-file-line-error", "main.tex"],
                cwd=work, env=env, capture_output=True, text=True,
            )
            output = run.stdout + run.stderr
            if run.returncode or (number == 2 and DIAGNOSTICS.search(output)):
                print(output)
                raise SystemExit(f"pdfLaTeX diagnostics on pass {number}")
        result = work / "main.pdf"
        info = subprocess.check_output([pdfinfo, result], env=dict(env, LC_ALL="C"), text=True)
        if not re.search(r"^Pages:\s+10\s*$", info, re.M):
            raise SystemExit("The rebuilt manuscript does not have ten pages")
        built, released = result.read_bytes(), (PAPER / "main.pdf").read_bytes()
        print(f"Rebuilt PDF SHA-256 {sha256(built).hexdigest()}")
        if args.exact and built != released:
            raise SystemExit("The rebuilt PDF differs from the released PDF")
        print("PASS two pdfLaTeX passes, warning-free final pass, ten pages"
              + (", released PDF bytes match" if args.exact else ""))


if __name__ == "__main__":
    main()
