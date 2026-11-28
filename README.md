# Interlacing of excedance polynomials with a minimum cycle length

[Nineteen-page cutoff-seven revision](cutoff-seven/paper/main.pdf) lowers the sufficient cutoff-seven threshold for a shared vector of five independent short-cycle weights from $36{,}000{,}000$ to $96$. It gives an independent all-size proof for the hard cutoff. [Proof, exact arithmetic and verification](cutoff-seven/README.md)

The [seventeen-page revision](cutoff-six/paper/main.pdf) treats the hard
cutoff six at all upper sizes $n\ge7$ and four independent short-cycle
weights at upper sizes $n\ge49$. It also gives the explicit sufficient
bound $n\ge10^6(k-1)^2$ for independent short-cycle weights at arbitrary
cutoffs. [Cutoff-six proof and reproduction](cutoff-six/README.md)

The [twelve-page revision](cutoff-five/paper/main.pdf) adds cutoff five.
The unweighted quotients strictly interlace at every upper size $n\ge6$.
For $n\ge49$ this also holds throughout the closed cube of independent
weights on cycles of lengths two, three and four. The two full rows
weakly interlace. [Cutoff-five source and reproduction](cutoff-five/README.md)

The [ten-page v1.0.0 manuscript](paper/main.pdf), its four Lean theorems,
and its exact finite witnesses remain available at the repository root.
The commands below concern that edition. [v1.0.0 release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.0.0)
The upper size is $n$, and each result compares the rows at $n-1$ and $n$.

The principal results are the independent-cycle-weight theorem and
the full unweighted cutoff-four theorem. The cutoff-three case has a
contemporaneous proof by ProgramComputer. The same work gives absolute
eventual bounds for all unweighted cutoffs. This repository supplies an
independent cutoff-three proof and a single Lean development for all
four theorems. [ProgramComputer's manuscript](https://github.com/ProgramComputer/open-math-research/blob/4da48b72ed8f92f96c2faf60e2d63d253b3b507a/topics/long-cycle-excedances/paper.tex)

- For every fixed cutoff $k\ge3$, sufficiently large adjacent rows
  interlace for every choice of independent short-cycle weights in the
  closed unit cube. The size threshold is uniform in those weights.
- At cutoff four the unweighted theorem holds for every nondegenerate
  pair, starting at upper size five. The independent unweighted
  cutoff-three proof starts at upper size four.
- For both cutoffs the weighted families interlace from upper size 512.
  The quotients by their common simple zero strictly interlace at
  simple negative roots and the original rows weakly interlace.

[Theorem-to-source map and verification records](verification/README.md)

## Exact arithmetic and manuscript

Run from the repository root with Python 3.11 or later.

```sh
python3 -B scripts/check_release.py
sha256sum -c paper/SHA256SUMS
python3 -B certificates/k3/verify.py certificates/k3/certificate.txt.gz --last 511
python3 -B certificates/k4/verify.py certificates/k4/certificate.txt.gz --last 511
python3 -B scripts/check_paper.py
```

The two certificate checkers reconstruct the original polynomial rows
and check dyadic endpoint signs with exact arithmetic. The stored
certificates extend through upper size 1023. The finite part used in
the manuscript and in the combined Lean theorems ends at 511.
Omit `--last 511` to replay the entire stored certificate.

The manuscript check needs pdfLaTeX and `pdfinfo`. It runs two passes
in temporary files, rejects final-pass warnings and checks the
ten-page count. Run `python3 -B scripts/check_paper.py --exact` with the
recorded TeX Live 2026 and pdfTeX 1.40.29 to additionally compare the
released PDF bytes.

## Lean

The source requires Lean 4.33.1. The dependency lock pins Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474` and records eight further Git
revisions. The verifier is the original, byte-matched clean verification
script shared by the three source releases.

```sh
elan toolchain install "$(cat lean-toolchain)"
lean_bin=$(dirname "$(elan which lean)")
export PATH="$lean_bin:$PATH"
export LEAN_NUM_THREADS=1
for audit in FixedThreeAllAudit FixedFourAllAudit FixedCutoffCubeAudit; do
  python3 -Bu scripts/verify_lean.py . "$audit" --serial || exit
done
```

Each invocation copies its import closure into a fresh project, checks
the external Git pins, elaborates with warnings as errors, checks
every listed transitive axiom and independently replays every local
project module in that closure. Add
`--packages /absolute/path/to/verified/.lake/packages` to use an existing
external dependency cache. The project's own compiled objects remain
fresh.

## GitHub Actions

Ordinary pushes and pull requests run the three complete Lean audits
on standard Ubuntu 24.04 AMD64, as well as the integrity, finite
arithmetic and TeX checks. The Lean jobs are independent. They run
one audit and one local build target at a time, with one Lean runtime
worker. The first matrix job proves and audits the named general
independent-weight theorem from the manuscript.

The private standard runner has 8 GB RAM. A Spark proof build reached
about 13 GiB in a single process. The hosted workflow removes unused
SDKs on a small runner disk and adds only the swap required for the
audit's envelope, capped at 14 GiB. It reserves 15 GiB for the
general-cutoff audit or 20 GiB for either all-sizes audit, measured
before Lean and Mathlib setup. Each resource failure is reported
explicitly. A manual run can set `lean_runner` to a configured AMD64
larger-runner label for extra headroom or a retry. [Standard runner resources](https://docs.github.com/en/actions/reference/runners/github-hosted-runners) ·
[Larger runner resources](https://docs.github.com/en/actions/reference/runners/larger-runners)

The retained full proof receipts are from an ARM64 NVIDIA DGX Spark.
The unchanged general-cutoff proof also passed a hosted AMD64 replay of
125 project modules and 77 declaration audits in the preceding edition.
The cutoff-five edition has a separate standard AMD64 workflow alongside
the independent Spark ARM64 record. It runs the manuscript and arithmetic in
one job and the full serial Lean closure audit in another. The AMD64 workflow
for this edition has not yet run.

## Citation and license

See [CITATION.cff](CITATION.cff). The original code is distributed under Apache-2.0.
[License scope](LICENSE-SCOPE.md) explains the separate manuscript
rights and the treatment of third-party material.

## Authorship

The tagged releases v1.0.0, v1.1.0, v1.2.0 and v1.3.0 list Bowen Zuo as sole author. They remain unchanged and may be cited as they are. The manuscript prepared for journal submission lists Bowen Zuo and Xiaojuan Luo as authors and identifies Xiaojuan Luo as the corresponding author. Both authors are affiliated with East China University of Science and Technology.
