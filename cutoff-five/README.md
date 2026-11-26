# Cutoff five

The [twelve-page manuscript](paper/main.pdf) compares the actual strict-excedance rows at sizes $n-1$ and $n$. At cutoff five the two quotients strictly interlace with simple negative roots for every upper size $n\ge6$, and the full rows weakly interlace. For $n\ge49$ this also holds for independent weights $w_2,w_3,w_4\in[0,1]$, with fixed-point weight zero and unit weight on all cycles of length at least five. Setting $w_4=1$, or $w_3=w_4=1$, gives the corresponding weighted regions at cutoffs four and three.

The upper sizes 6 through 48 in the finite certificate concern the hard cutoff. The weighted-cube proof begins at 49. [Theorem map and source provenance](verification/README.md)

## Reproduce

From this directory, with Python 3.11 or newer:

```sh
python3 -B scripts/check_edition.py
python3 -B certificates/finite.py
python3 -B certificates/check.py
python3 -B certificates/compact/verify.py
python3 -B certificates/middle/verify.py
python3 -B scripts/check_paper.py
```

The paper verifier needs PDFLaTeX with Latin Modern and Poppler's `pdfinfo`. The `--exact` flag compares both independent PDF builds with the stored paper using the recorded TeX Live 2026 distribution.

For the Lean proof, install the toolchain in `formal/lean-toolchain` and put its binaries on PATH. The independent closure pins Mathlib and eight further Git package revisions.

```sh
elan toolchain install "$(cat formal/lean-toolchain)"
cd formal
export PATH="$(dirname "$(elan which lean)"):$PATH"
cd ..
export LEAN_NUM_THREADS=1
python3 -Bu formal/verify_lean.py formal CutoffFiveFinalAudit --serial
```

The verifier copies only local proof source and dependency locks into its temporary project. It checks each external Git revision, rebuilds the full local closure, audits the named declarations, and replays each project module in a separate Lean kernel process. Use `--packages PATH` to reuse verified external dependency caches.

The software is distributed under Apache-2.0. The manuscript and accompanying research data follow the repository's separate [license scope](../LICENSE-SCOPE.md).
