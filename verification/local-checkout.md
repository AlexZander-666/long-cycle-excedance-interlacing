# Local checkout verification

The merged sources were checked from an independent Git index
checkout on ARM64 DGX Spark. The release checker matched all 608
Lean source files, nine external Git pins, and the three audit
import closures against the release ledgers.

The three complete audit files were elaborated with warnings as
errors. All 27, 12 and 77 transitive axiom sets matched the
respective frozen releases. This check used 282 previously
authenticated cutoff-three objects, 423 cutoff-four objects, and
120 overlapping objects for the independent-weight audit. The five
remaining independent-weight modules were compiled directly from
the frozen sources. Each of the three top-level modules passed a
separate kernel replay.

The original clean verifier was also run from a source-only smoke
project on `LongCycles.ne_fixed_of_allowed`. It checked the nine
external Git revisions, built `LongCycles.Statement` strictly
and independently replayed that module.

Both Python certificates were checked through upper size 511.
The cutoff-three check covered 508 adjacent pairs and the
cutoff-four check covered 507. Each independently checked 129,540
integer endpoint signs.

The clarified manuscript was rebuilt from its five source files in
two separate temporary directories, with two passes in each using
TeX Live 2026. The outputs are byte-identical and contain ten pages
with embedded fonts. The verified PDF digest is
`0601708bd8591099441b13da515a2d687ae41fb1cd4464a6591801b93d5c292f`.
[Manuscript checksums](../paper/SHA256SUMS)

The workflow passed actionlint 1.7.12, syntax checks for all five
Bash steps and dry tests of the resource planner for standard and
larger AMD64 budgets. The citation file passed the official CFF
1.2.0 schema validation. The GitHub-hosted AMD64 jobs have yet to run.
