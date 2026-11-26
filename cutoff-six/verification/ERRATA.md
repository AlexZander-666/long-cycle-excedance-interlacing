# Corrections to comments in the frozen cutoff-six Lean source

The table records wording in two comments. The original source archive and the cold-accepted proof archive retain their bytes. Both theorem signatures and their proof bodies use the correct orders.

| Location in the inner cutoff-six source ZIP | Frozen comment | Correct reading |
| --- | --- | --- |
| LongCycleBounds/SixCompactResidue.lean, opening comment | order-44 error | order-43 error, because the shortest row index is n−6 at upper n=49 |
| LongCycleBounds/SixMiddleBudgets.lean, documentation above the half-order pole estimate | shortest quartic insertion coefficient | shortest coefficient for the fifth-degree cutoff-six tilt, with row index n−6 |

The paper states the order and bounds used by the proof. [Unchanged cold receipts and source hashes](FORMAL-STATUS.md)
