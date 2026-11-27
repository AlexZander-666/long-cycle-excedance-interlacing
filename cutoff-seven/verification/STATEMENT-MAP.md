# Paper-to-Lean correspondence

The input is the actual strict-excedance statistic `LongCycles.excedances` on permutations of `Fin j`. Under `LongCycles.Allowed k` every cycle has length at least k. The source `CycleProfile.row j w` is the genuine derangement sum with the product of its cycle weights. The simple factor t is removed in `weightedQuotient` and `Band.generalCycleQuotient`. The theorem uses the same w and k in both rows. In the root-list definition the lower degree is n−3 and the upper degree is n−2. The strict negative-root statement includes all roots of the two quotients. The weak original-row statement reinstates their common simple root at zero. [Author’s problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles)

| Paper claim | Exact declaration | Source module |
| --- | --- | --- |
| Theorem 1, arbitrary independent profile | `LongCycleBounds.QuadraticCutoff.independent_weights` | `LongCycleBounds.QuadraticCutoffVerified` |
| Theorem 1, hard cutoff | `LongCycleBounds.QuadraticCutoff.original` | `LongCycleBounds.QuadraticCutoffVerified` |
| Theorem 2, k=3 and n≥4 | `LongCycleBounds.fixed_three_all_sizes` | `LongCycleBounds.FixedThreeAllSizes` |
| Theorem 3, mark on two-cycles and n≥512 | `LongCycleBounds.MarkedTwo.Half.marked_interlacing` | `LongCycleBounds.MarkedHalfVerified` |
| Theorem 4, hard cutoff and n≥5 | `LongCycleBounds.fixed_four_all_sizes` | `LongCycleBounds.FixedFourAllSizes` |
| Theorem 4, two independent marks and n≥512 | `LongCycleBounds.FixedFour.independent_weights` | `LongCycleBounds.FixedFourVerified` |
| Theorem 5, hard cutoff and n≥6 | `LongCycleBounds.FiveCutoff.all_sizes` | `LongCycleBounds.FiveCutoffVerified` |
| Theorem 5, three independent marks and n≥49 | `LongCycleBounds.FiveCutoff.independent_weights` | `LongCycleBounds.FiveCutoffVerified` |
| Theorem 6, hard cutoff and n≥7 | `LongCycleBounds.SixCutoff.all_sizes` | `LongCycleBounds.SixCutoffVerified` |
| Theorem 6, four independent marks and n≥49 | `LongCycleBounds.SixCutoff.independent_weights` | `LongCycleBounds.SixCutoffVerified` |

The earlier fixed-cutoff declarations `LongCycleBounds.FixedCutoff.fixed_cutoff_independent_weights` and `fixed_cutoff_eventual_original` correspond to the former existential threshold. The new Theorem 1 is mapped to the explicit-threshold declarations above. The small-cutoff statements and original certificate inputs carry over from the submitted twelve-page version. [Cutoff-three and cutoff-four verification files](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/tree/v1.1.0/verification) · [Cutoff-five verification files](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/tree/v1.1.0/cutoff-five/verification) · [Fixed release assets](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.1.0)

For Theorem 1, $p=n-1$, and `normalizedRow w j x` evaluates the original row at $t=-\exp(-x)$ and divides by $(1-t)^j$. The statements at the half-line boundary use $x=0$. Reciprocity handles $t<-1$.

| Proof step | Declared in the new closure |
| --- | --- |
| Original signed insertion identity | `LongCycleBounds.CycleProfile.normalizedRow_insertion` |
| Radius dilation $V((1+1/d)\rho)\le3V(\rho)$ and tilt costs | `LongCycleBounds.QuadraticCutoff.dilate_cost`, `large_coordinate_costs` |
| Weighted odd-pole head and centered error | `LongCycleBounds.QuadraticCutoff.weighted_odd_pole_sum`, `sharp_original_errors`, `compact_relative_window` |
| Compact sign, $0\le x\le12d+100$ | `LongCycleBounds.QuadraticCutoff.original_compact_sign` |
| Middle sign, $12d+100\le x\le3\sqrt p$ | `LongCycleBounds.QuadraticCutoff.independent_effective_middle_sign` |
| Original exterior series, with $h=i+1$ in Lean | `LongCycleBounds.Occupancy.independent_row_hasSum`, `independent_derivative_hasSum` |
| Exterior head/tail and sign, $3\sqrt p\le x$ | `LongCycleBounds.Occupancy.independent_label_near_full`, `coefficient_moment_error`, `independent_quadratic_exterior_sign` |
| Complete sign at every genuine predecessor zero | `LongCycleBounds.QuadraticCutoff.normalized_sign` |
| Straight-line homotopy to ordinary derangements, reflection and root lists | `LongCycleBounds.CycleProfile.independent_interlacing_of_normalized_sign` |

The paper proves the positive-label formula for arbitrary weights directly by the labelled cycle index. Lean obtains the general bounds from the genuine anchored coefficients and uses their termwise monotonicity to compare with the two endpoint occupancy expressions. The native slot series in Lean uses $(-1)^i$ at the one-based label $h=i+1$, so its values for the row and derivative are $-H_j$ and $H'_p$. The paper uses $(-1)^h$ and computes $H_j$ and $-H'_p$. Both orientations yield the same original sign product. The paper groups the omitted positive labels by the half-window $h>\lfloor\sqrt p/2\rfloor$; the Lean tail uses a geometric series starting at the mode and absorbs this same omitted window.

The upper threshold $n\ge10^6(k-1)^2$ implies $n>k$ and the required exterior floors $p\ge65{,}536$ and $p\ge4k^2$. The quantifier gives one statement for every fixed profile in the closed unit cube. The theorem compares adjacent rows at that profile, and the smaller hard-cutoff sections keep the domains stated in the paper. [Frozen proof archives and precise extraction commands](FORMAL-STATUS.md)

## The cutoff-six proof

The hard case is every consecutive pair of positive-size nonempty rows, beginning at the pair (6,7). The closed four-weight cube includes every independent choice of weights at lengths 2, 3, 4 and 5, with w₁=0 and wₐ=1 for a≥6. The two rows use one common profile. The analytic statement starts at upper n=49, or p=48 in the predecessor notation. The finite hard prefix includes 7≤n≤48.

| Proof step | Declaration or exact source |
| --- | --- |
| Original finite prefix, 42 adjacent pairs | LongCycleFinite.K6Prefix.finite_original in LongCycleFinite/K6Prefix/All.lean |
| Exact sixth cycle moment and coefficient bounds | LongCycleBounds.SixCutoff.sixth_moment, abs_sixth, tilt_factorial, drift_factorial in SixCutoffMoments.lean |
| Compact error at any allowed radius and real marks | LongCycleBounds.AdjustablePoleRadius.profile_error in AdjustableProfileError.lean |
| Compact arithmetic and actual predecessor zero | LongCycleFinite.K6CompactCert and LongCycleBounds.SixCutoff.compact_sign in SixCompactVerified.lean |
| Middle convolution and actual sign | LongCycleBounds.SixCutoff.middle_bias and middle_sign in SixMiddleSign.lean |
| Positive labels and the separate label zero | LongCycleBounds.SixCutoff.Exterior.positive_label, zero_label in SixOuterLabels.lean |
| Exterior raw comparison | LongCycleBounds.SixCutoff.Exterior.insertion_gap and the exterior_sign theorem in SixExteriorVerified.lean |
| Actual derivative sign at all x≥0 | LongCycleBounds.SixCutoff.normalized_sign in SixCutoffVerified.lean |
| Actual permutations to complete root order | LongCycleBounds.CycleProfile.independent_interlacing_of_normalized_sign and CycleProfile.row_zero |

The paper's raw exterior coordinate is Hⱼ/(1+exp(−x)). It uses (−1)ʰ at the positive label h. The signed bare moment may have the opposite orientation in the source's zero-based label i=h−1. The inequalities use absolute values and the actual top-level sign is Hₙ(−H′ₚ)>0.

The section states the same exterior error and upper margin as the Lean argument, 1/(6n) and W/4. The standalone rational checker uses a different valid exterior budget, 1/(40√p) and W/3. The compact certificate uses 104 closed x-intervals and uniform bounds on the four weights. The standalone and Lean rational tables round outwards separately and both imply residue error at most (7/50)sD and insertion budget J at most 15. The standalone finite replay checks signed remainder chains. Lean connects exact coefficient ladders from the actual enumerator to rational endpoint signs and complete root counts by degree.


## The cutoff-seven proof (Theorem 7)

For the hard cutoff, the first pair is (7,8), and the finite and analytic parts cover upper index 8 through 95 and upper index at least 96 respectively. The weighted analytic part quantifies over a single shared five-coordinate short-weight vector. It includes zero and unit weights. At lengths 2 through 6 the weights lie independently in [0,1], at length 1 the weight is zero, and at lengths at least 7 the weights are all one.

| Proof step | Lean declaration and source |
| --- | --- |
| Actual seventh cycle moment and rational envelopes | LongCycleBounds.SevenCutoff.seventh_moment and seventh_envelopes in SevenCycleMoment.lean |
| Tilt and insertion coefficients | LongCycleBounds.SevenCutoff.tilt_factorial and drift_sixth in SevenProfile.lean |
| Compact original sign | LongCycleBounds.SevenCutoff.compact_sign in SevenCompactVerified.lean |
| Middle convolution through order n−7, plus actual sign | LongCycleBounds.SevenCutoff.middle_bias and middle_sign in SevenMiddle.lean |
| Positive and zero label estimates | LongCycleBounds.SevenCutoff.Exterior.positive_label and zero_label in SevenOuterLabels.lean |
| Exterior raw insertion and actual sign | LongCycleBounds.SevenCutoff.Exterior.insertion_gap and LongCycleBounds.SevenCutoff.exterior_sign in SevenExterior.lean |
| All-region root sign and five-weight result for n≥96 | LongCycleBounds.SevenCutoff.normalized_sign and independent_weights in SevenCutoffVerified.lean |
| Hard-cutoff specialization for n≥96 | LongCycleBounds.SevenCutoff.original in SevenCutoffVerified.lean |
| Exact hard prefix, n=8,…,95 | LongCycleFinite.K7Prefix.finite_original in LongCycleFinite/K7Prefix/All.lean |
| Complete hard result, all upper n≥8 | LongCycleBounds.SevenCutoff.all_sizes in SevenCutoffAllSizes.lean |

The mathematical compact replay gives a maximum combined bound 246041/1250000. The kernel-checked compact table rounds selected intermediate terms outwards and uses 1968337/10000000. Both are less than one. The paper applies 21/20 only to the sixth drift and gets J<2/5 in the middle region. The Lean proof applies that factor uniformly to the six terms there and uses J≤1/2. Both bounds suffice for the same actual sign. Below 96 the prefix verifies the hard cutoff.
