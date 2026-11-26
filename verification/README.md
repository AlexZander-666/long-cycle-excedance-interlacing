# Theorems and verification records

The paper theorem numbers refer to the frozen [ten-page edition](../paper/main.pdf).
The PDF and its five sources have [separate checksums](../paper/SHA256SUMS).

| Paper theorem | Lean declaration | Scope |
| --- | --- | --- |
| 1, general cutoff | [`LongCycleBounds.FixedCutoff.fixed_cutoff_independent_weights`](../LongCycleBounds/FixedCutoffCubeVerified.lean) | For each fixed $k\ge3$, a common threshold for the independent short-cycle weights. |
| 1, zero-weight specialization | [`LongCycleBounds.FixedCutoff.fixed_cutoff_eventual_original`](../LongCycleBounds/FixedCutoffVerified.lean) | The eventual statement for the original minimum-cycle-$k$ rows. |
| 2 | [`LongCycleBounds.fixed_three_all_sizes`](../LongCycleBounds/FixedThreeAllSizes.lean) | All original adjacent pairs with upper size $n\ge4$. |
| 3 | [`LongCycleBounds.MarkedTwo.Half.marked_interlacing`](../LongCycleBounds/MarkedHalfVerified.lean) | The marked cutoff-three pairs for $n\ge512$. |
| 4, original rows | [`LongCycleBounds.fixed_four_all_sizes`](../LongCycleBounds/FixedFourAllSizes.lean) | All original adjacent pairs with upper size $n\ge5$. |
| 4, weighted rows | [`LongCycleBounds.FixedFour.independent_weights`](../LongCycleBounds/FixedFourVerified.lean) | Independent weights for cycles of lengths two and three for $n\ge512$. |

The finite assembly uses
[`LongCycleFinite.K3.finite_original_4_511`](../LongCycleFinite/K3FiniteOriginal0511.lean)
and [`LongCycleFinite.K4.finite_original_5_511`](../LongCycleFinite/K4FiniteOriginal0511.lean).
Neither finite theorem needs a real-root or interval-order assumption.
The paper's strict and weak interlacing statements refer to the
actual quotients and the actual original permutation rows.

The `Prop` declarations `FixedFirstSplit`, `PairRoots`, `RatioData`
and `ArticleClaim` in [LongCycles/Statement.lean](../LongCycles/Statement.lean)
are auxiliary specifications for the cutoff-12 pair of rows 23 and 24.
The top-level proofs for this paper are listed in the table above.

## Frozen inputs and results

- [archives.tsv](archives.tsv) identifies the three formal archives
  by SHA-256, size and audit module.
- [source-origins.tsv](source-origins.tsv) records each frozen Lean
  source and pin by byte length and hash. The overlapping files have
  identical bytes. The repository combines the Lake audit targets
  in its single configuration.
- [SHA256SUMS](SHA256SUMS) covers the delivered source, paper,
  exact certificates, scripts and public records.

| Scope | Actual ARM64 Spark verification | Receipts |
| --- | --- | --- |
| Cutoff three | All 282 modules built from a fresh project and independently replayed. 27 axiom audits. | [Modules](spark/k3-modules.tsv) · [Axioms](spark/k3-axioms.tsv) · [Summary](spark/k3-summary.txt) |
| Cutoff four | 128 verified tail objects matched byte for byte, with 295 other modules built from source and independently replayed in the combined project. 12 axiom audits. | [Modules](spark/k4-modules.tsv) · [Axioms](spark/k4-axioms.tsv) · [Summary](spark/k4-summary.txt) |
| Eventual cutoff | 121 common modules built and independently replayed in a fresh project, then four independent-weight modules built and individually replayed in a checked incremental copy. 77 axiom audits. | [Modules](spark/cube-modules.tsv) · [Axioms](spark/cube-axioms.tsv) · [Summary](spark/cube-summary.txt) |

These concise records retain module names, exact source hashes,
available object hashes, successful build and replay provenance,
and transitive axioms. The transitive axioms lie in the standard set
`propext`, `Classical.choice`, and `Quot.sound`.

[Local checkout verification](local-checkout.md) records the repeated
top-level audits and kernel checks and the paper, arithmetic and CI
component tests for this merged repository.
