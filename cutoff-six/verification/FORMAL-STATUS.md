# Actual formal verification of the cutoff-six revision

Theorem 6 passed an independent source-cold acceptance run on DGX Spark. The input was the exact frozen cutoff-six ZIP. The verifier locked Lean 4.33.1 and all dependency revisions and compiled the project with no prebuilt project modules. It completed 46 strict Lake build batches, independently replayed all 182 project modules, and checked the transitive axioms of 13 declarations in the separate SixCutoffAudit entry. All listed axioms belong to the standard set propext, Classical.choice and Quot.sound. The final receipt records source_cold_verifier_exit=0.

| Exact cutoff-six artifact | SHA-256 |
| --- | --- |
| cutoff-six-all-source.zip | 605cd388a15d43d5c557605007b9f9e12e1db9cebd11ca80cb9abc33d67004c1 |
| cold.log | 8b9efd10b77cc80b6f058365457289adbb7e32d017e29043f37dda698dbb5951 |
| receipt.json | 5937897c30da4405e1f8faa09e2653d3c9877f865b7f211a2dbf2c5b680bdfd8 |
| cutoff-six-all-accepted.zip | 37ec19f48e46eddcaa7a59efb6026b006a61b2a8f753835c585af950bf245527 |
| LongCycleBounds/SixCutoffVerified.lean | b1d9c6548d7a4e516a6e552d24b5ee58eca88527e740d8f05a97c1dfe62a20aa |

The top declarations refer directly to the original permutation rows and their weighted version. The unweighted phase covers 7≤n≤48 with Lean endpoint certificates and all n≥49 with analytic estimates. The four-weight theorem uses the analytic phase. The standalone Python replay independently recomputes both row recurrences and 1029 signed remainder drops for the 42 hard-cutoff pairs. Its 104 interval checks use exact rational arithmetic and uniform estimates for the full four-dimensional cube. The standalone arithmetic supplements the independent Lean cold verification. [Exact declaration map](STATEMENT-MAP.md) · [Arithmetic output](arithmetic.log)

Theorem 1 is carried over from the earlier quadratic candidate. Its separate exact frozen source-cold workflow built and replayed 188 project modules in 47 strict build batches and checked 19 declarations, also with exit 0 and the standard three-axiom bound. Its byte-identical acceptance bundle is included. The other earlier theorems and certificate references are unchanged.

| Earlier quadratic artifact | SHA-256 |
| --- | --- |
| quadratic-all-cutoff-source.zip | 49137a586d281e041b7a50a0e95f0148541b8348a584e9d64b67621a5ff131e3 |
| cold.log | 5a6d953a9cbcdc07542482577251d53eb29e46fdbe84a9adf7346f5aa7277ea6 |
| receipt.json | f57cf41a09cef6f89a6e14d0298213f136b2bef94cc826067c77cc2a10f283c5 |
| quadratic-all-cutoff-accepted.zip | 7ac45ad4e5858b8b985963d9f0384fc58619e57579d3b65d14093e3b8019d3ac |

Extract either acceptance bundle from the formal/ directory of the review ZIP and follow its README. It contains the actual nested frozen source, dependency lock, replay command, transcript and structured receipt. This corrected edition is the private candidate for same-topic review. The earlier formal acceptance and article versions remain distinct.

## Exact extraction commands for the review ZIP layout

Run from the directory of the extracted review ZIP. Add the verifier flag --packages /path/to/.lake/packages to reuse a cache with the exact pinned external revisions.

    unzip -q formal/cutoff-six-all-accepted.zip -d lean-six-accepted
    unzip -q lean-six-accepted/cutoff-six-all-source.zip -d lean-six-src
    (cd lean-six-src && sha256sum -c SHA256SUMS)
    (cd lean-six-src && LEAN_NUM_THREADS=1 python3 -Bu verify_lean.py . SixCutoffAudit --jobs 4)

    unzip -q formal/quadratic-all-cutoff-accepted.zip -d lean-quadratic-accepted
    unzip -q lean-quadratic-accepted/quadratic-all-cutoff-source.zip -d lean-quadratic-src
    (cd lean-quadratic-src && sha256sum -c SHA256SUMS)
    (cd lean-quadratic-src && LEAN_NUM_THREADS=1 python3 -Bu verify_lean.py . QuadraticCutoffAudit --jobs 4)

The bundled acceptance READMEs use “extracted directory” to refer to these inner source directories. The commands above start one layer earlier. [Comment-only errata for the unchanged frozen source](ERRATA.md)
