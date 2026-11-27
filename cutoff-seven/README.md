# Cutoff-seven revision

This revision improves the sufficient upper size for interlacing with a shared vector of five independent short-cycle weights from 36,000,000 to 96. It also gives an independent proof for every hard-cutoff-seven pair, starting at upper size 8. The prior ProgramComputer research establishes overlapping all-size hard-cutoff coverage, which the paper cites. [Article](paper/main.pdf) · [Prior material](verification/PRIOR-ART.md) · [Exact statements](verification/STATEMENT-MAP.md)

The coordinates are common to both adjacent rows. Fixed points have weight zero, lengths 2 through 6 have arbitrary independent weights in [0,1], and lengths at least 7 have weight one. The quotients by the common simple zero have strict interlacing at simple negative roots. The original rows weakly interlace.

For the paper and the cutoff-seven arithmetic, run these commands from this directory.

    python3 -B reproduce.py
    python3 -IB numerics/fixed-seven-effective/moment.py
    python3 -IB numerics/fixed-seven-effective/compact.py
    python3 -IB numerics/fixed-seven-effective/prefix.py
    python3 -IB numerics/fixed-seven-effective/middle_outer.py

The first command uses TeX Live 2026 and builds the PDF twice from fresh directories. The remaining commands use the Python standard library. They verify the closed-cell and finite hard-cutoff inputs, including both exact middle-head bounds.

To replay the Lean proof, extract formal/cutoff-seven-all-source.zip into fresh storage and run these commands from the extracted directory.

    sha256sum -c SHA256SUMS
    LEAN_NUM_THREADS=1 python3 -Bu verify_lean.py . SevenCutoffAudit --jobs 4

Install Lean 4.33.1 and use the external revisions in lake-manifest.json. The verifier accepts --packages /path/to/.lake/packages for a cache with matching Git revisions. It builds the project objects in a new temporary source copy. [Verification record](verification/FORMAL-STATUS.md)
