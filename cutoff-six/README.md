# Cutoff six and an explicit bound for independent short-cycle weights

Bowen Zuo, East China University of Science and Technology.

With minimum cycle length six, consecutive strict-excedance rows at every upper size n≥7 have strict interlacing of their simple negative roots after dividing by the common simple zero. The unmodified rows weakly interlace. For n≥49, the same conclusions hold with four independent weights on cycles of lengths two through five, common to the two rows. Fixed points are excluded and every cycle of length at least six has weight one. The paper also proves the explicit threshold n≥10⁶(k−1)² for arbitrary cutoff k≥3 and all admissible independent weights. [Paper](paper/main.pdf) · [Exact theorem map](verification/STATEMENT-MAP.md) · [Original question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles)

From this directory, run python3 -B reproduce.py with a full TeX Live 2026 installation. Set PDFLATEX to its executable if necessary. The script compares the original loose TeX and a fresh source ZIP with two passes each and updates the output only when the two PDFs agree. [Rebuild transcript](verification/paper-rebuild.log)

Run python3 -B numerics/fixed-six-effective/check.py and then python3 -B cutoff-six-scalar-check.py to reproduce the exact interval and finite-row checks. These use the standard library. [Exact arithmetic transcript](verification/arithmetic.log)

The two frozen Lean acceptance containers are in formal/. They retain the exact sources, dependency locks, kernel replay logs and structured receipts. Extract each inner source ZIP before running its verifier. The cutoff-six audit covers 182 modules and 13 declarations. The independent quadratic audit covers 188 modules and 19 declarations. [Precise verification commands](verification/FORMAL-STATUS.md) · [Comment-only errata for frozen sources](verification/ERRATA.md)

Theorems 2–4 have their frozen sources and proof receipts in the repository root and its verification directory at the v1.1.0 commit. Theorem 5 is also in the cutoff-five release assets. [Precisely pinned previous tree](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/tree/70cad373bce521d78d6de9bcff3d29d07fc7fe9f) · [Previous release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.1.0)

ChatGPT assisted with the analytic derivations, implementation and independent replay of the formal proofs, and preparation of the manuscript. Bowen Zuo takes responsibility for the paper. [License scope](../LICENSE-SCOPE.md)
