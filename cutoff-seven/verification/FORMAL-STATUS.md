# Formal verification record for the combined cutoff-seven revision

The frozen cutoff-seven Lean source has 199 project modules and one dedicated audit with 11 requested transitive-axiom reports. Its SHA-256 is acbc05bf6119e341714756e5f42a1b37ef3ccc339be67c536dff6bb14632154b. Its main all-size declaration is LongCycleBounds.SevenCutoff.all_sizes in LongCycleBounds/SevenCutoffAllSizes.lean, source SHA-256 38f02fde5bb0d726c4a4c88e6a04e6839f80811d01db04e501c4ce160470f46e.

The actual three-regime sign and five-weight theorem for upper sizes at least 96 passed a strict development build with 8,878 jobs. Independent leanchecker processes replayed each of the eight new analytic modules, with matching source and object hashes before and after each replay. Their last module is SevenCutoffVerified, which proves the analytic and connected-profile conclusions. The printed transitive axioms are propext, Classical.choice and Quot.sound. The compact-region original sign and its 128-region certificate also passed their separate build and kernel checks. The source and object hashes for the eight new analytic modules appear in verification/middle-exterior-kernel-receipt.log. The finite-prefix modules and the full SevenCutoffAllSizes assembly belong to the separately tracked closure.

The separate exact-arithmetic replay checked the seventh-moment Bernstein ranges, all 128 compact cells, all 88 finite hard pairs with 4,268 lower-root intervals, and the middle and exterior numerical anchors. See verification/cutoff-seven-exact.log. The independent source-cold run for the whole 199-module closure completed. The exact receipt is listed below.

The accepted cutoff-six and quadratic bounds are carried over. Their byte-identical accepted archives include the corresponding frozen source bundle and real acceptance log. The cutoff-six run checked all 182 project modules and 13 declarations. The quadratic run checked all 188 project modules and 19 declarations. Both runs used Lean 4.33.1, warning-as-error builds, independent kernel processes and the three standard axioms.

To replay the cutoff-seven formal source from the extracted review package, run

    unzip -q formal/cutoff-seven-all-source.zip -d lean-seven
    (cd lean-seven && sha256sum -c SHA256SUMS)
    (cd lean-seven && LEAN_NUM_THREADS=1 python3 -Bu verify_lean.py . SevenCutoffAudit --jobs 4)

The verifier accepts --packages /path/to/.lake/packages for the exact locked external dependency cache. It copies the extracted sources to a fresh temporary project and builds the objects there. For the earlier formal archives, first unpack the accepted ZIP and then its nested source ZIP. The corresponding audit names are SixCutoffAudit and QuadraticCutoffAudit. All mathematical statements and their precise cutoffs are in STATEMENT-MAP.md.

# Completed source-cold acceptance

The original cutoff-seven sources were independently built from an empty project object directory. All 199 project modules were separately replayed in the Lean kernel. The 11 targeted transitive-axiom reports use only propext, Classical.choice and Quot.sound. The same proof source was supplied in the reviewed manuscript packet.

Accepted ZIP SHA-256: c70809c75983ca688ce50968acdb6677292b0589b2fe7634229a31544f7d7428
Cold transcript SHA-256: f8cb285dc2b25daf4b68620e3aa9297d36e882ce94eff277fb4c2b0954cd4bb2
