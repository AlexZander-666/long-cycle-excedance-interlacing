# Cutoff-five verification and sources

| Result in Theorem 5 | Lean statement | Proof |
| --- | --- | --- |
| Unweighted upper sizes 6 through 48 | `LongCycleFinite.K5Prefix.finite_original` | [Finite verification](../formal/LongCycleFinite/K5Prefix/All.lean) |
| All unweighted upper sizes from 6 | `LongCycleBounds.FiveCutoff.all_sizes` | [Actual permutation readout](../formal/LongCycleBounds/FiveCutoffVerified.lean) |
| Full independent weight cube from upper size 49 | `LongCycleBounds.FiveCutoff.independent_weights` | [Actual weighted rows](../formal/LongCycleBounds/FiveCutoffVerified.lean) |

The original polynomials count strict excedances and use the same cycle weight sequence in both rows. The audit names the finite theorem, the three analytic regions, the transformation to the actual weighted rows and the readout to the original unweighted pair. [Audit entry point](../formal/CutoffFiveFinalAudit.lean)

The 180 Lean files, three dependency files and standalone verifier are byte copies of the isolated cutoff-five source closure. The compact and middle arithmetic tables and the two independent exact arithmetic routes are included under [certificates](../certificates/). The older proof lineages for Theorems 1–4 remain at the repository root.
