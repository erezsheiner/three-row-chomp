# Independent mathematical cross-check of the selected release

This renewed review is model-assisted mathematical examination. It is separate from the compiler, exhaustive dependency inspection, finite computations and paper author's own argument. It is not a claim of human peer review, novelty, or a second independent proof-assistant implementation.

## Actual-game uniqueness and the encoding bridge

I read the complete `ChompLean.Statement`, `ChompLean.Game` and `ChompLean.Encoding` interfaces and definitions, the recurrence-model fields in `ChompLean.Proof`, their actual-game instantiation, and the final actual-target uniqueness argument. The physical position uses ordered row lengths. First-row cuts are strictly positive; second- and third-row cuts include zero. Thus the poisoned square is excluded, and the poison-only board is a P-position under the stated convention. The theorem's rectangle domain is positive width.

Existence of the P-position encoding is obtained independently by strong induction on the two shorter coordinates. It is not obtained by assuming the desired uniqueness. The actual game discharges the recurrence-model assumptions. The first-row opening is excluded by the separate strategy-stealing argument; the other two opening families are covered by the positive diagonal/row-start partition. The final theorem states uniqueness of the actual legal target P-position, not merely uniqueness of an abstract encoding value.

As a separate error-detection check, direct physical cell removal agreed with the three row-cut formulas on 164 boards of maximum row length eight and 1,816 nonpoison choices. A direct game solver examined 50,115 positions through maximum row length 65 and found one winning opening on each rectangle of widths 1–65. The literal positive-MEX/COPY table agreed with the independent game on 561 complete triangular cells through row 32. These finite checks do not establish the universal theorem; the exact Lean statement and kernel proof do that.

## Counting service budget and strict improvement

The complete service-budget and extremizer proofs were reconstructed from the primary mathematical sections. They are included as public supplements and received a separate review by the formal-audit agent. I checked the distinction between nonbirth diagonal services and the later slope proof's birth-inclusive services; the two counts must not be interchanged.

The baseline budget uses the exact nonbirth count, sorted diagonal majorization, and layer-cake conversion of the rank sum. Static and birth exceptions are paid by the explicit compensating service identity. Distinct high awards cancel the sampled high area; the low-area contribution and endpoint square remain. No order relation between blocker rank and victim position is assumed. The fixed parameter is held before the large-horizon limit and only subsequently tends to the liminf count parameter. Conversion back to a diagonal liminf uses injectivity and a counting argument, not an ordered inverse.

For the improvement, the excess decomposition, ramp deficit, rank deficit and reach-excluded victim count are nonnegative with their stated definitions. The good-source interval [0.30,0.31] and good-target interval [0.56,0.58] are separated, the target interval lies outside the ramp, and the additional source-time exclusion is disjoint from the baseline charge. The product inequality yields the explicit positive gain without counting the same victim twice. Exact rational polynomial checks were rerun; a second reviewer additionally used a different rational Horner interval checker. No convergence or limsup conclusion is inferred.

## Existing-slope theorem

I reconstructed the repaired proof in `audit/full/paper-b/SLOPE-REPAIR.md`. The existence of the slope remains an explicit hypothesis. First-crossing asymptotics do not assume that the diagonals are monotone. The booker-union supplier separates earlier dead victims from reach-inaccessible victims; neither ordering of victim positions nor an unproved global transport law is used.

The two journal lower lines retain the immortal term and are integrated with the correct birth threshold. The large-slope range is excluded before optimizing the remaining range. Weighted multiplicative intervals give the logarithmic average lower bound for the immortal fraction. The Stieltjes conversion has a bounded primitive boundary term and summable jump error. The concave integrand is bounded below by its chord on the established interval, and the sign/root deduction uses exact polynomial evidence. This remains an upper bound on an existing slope, not a proof that the slope exists.

## Pell-type cumulative contraction and composed-count density

For the cumulative recurrence, the two-step contraction uses the positive minimum of the two indicated coefficients, the cap on the normalized forcing, and summability of the error. Divergence on at least one parity suffices to force the two-step maximum to zero, hence both subsequences. The zero/subunit boundary cases in the cap were retained.

For the composed-count statement, cluster values lie in [1/3,1/2]. The induced map and inverse interval contraction force the cluster set to be a singleton; this proves the stated count-density limit. It does not imply an ordered diagonal slope without a further argument.

## Two-owner MEX statements

The finite insertion model uses zero-based MEX, unlike the positive-MEX canonical Chomp table. In each owner order, the smaller output is the least value absent from the shared context and common owner set; which owner can emit it is determined by membership in the private memories. The response-content equivalence follows from this exact two-output normal form.

Large test values recover the common memory; the least asymmetric label and the first missing value then reconstruct the remaining phase information. The finite extremal response class uses the explicit empty/singleton private sets and respects the lower bound on the ambient maximum. The commutation criterion follows by testing the first asymmetric label above the union MEX. This is output-set commutation in the stated model; it does not identify all private memory states.

## New public definitions and transport supplements

I read the canonical definition sheet and the ghost/owner-transport supplement, including all timing conventions. After-row liveness differs from START liveness. Equality at an owner's death belongs to the postdeath class. The ghost graph has increasing host-to-owner edges; the ledger includes isolated live vertices and dead endpoints. The available-endpoint matching saturates the smaller of edge count and available vertices and does not imply an asymptotic matching estimate.

The completed-demand cap gives the three piecewise integral contributions 25/288, 9/288 and 12/288, hence 23/144. The owner two-label partition retains prebirth, exceptional, unserved and postdeath terms. Its stock keeps negative intervals and actual host death dates. The multigraph retains parallel walks and isolated endpoints; contraction preserves signed charge and degree two. The chronological rank ray's cut formula is a rank identity, not a causal-source bound. The reverse-source forest can terminate at an unpaid postdeath endpoint. The corrected death identity retains the immediate-death indicator.

The dated matching uses actual inversion sources and earliest-positive/latest-negative selections; each matched edge contributes the difference of its two crossing indicators. Immortal mass obstructs only mortal-only matching, and the forward same-host source construction assumes an immortal physical host and imposes no free-token or delay bound.

I also reconstructed the source-time/tightness supplement. Width exclusion separates the exact affine rail from finite base checks and small-column tail proofs. Terminal capacity uses the penultimate MEX exclusion of past diagonals and distinct source dates. E=0 alone does not imply F=0, record status, or that the last label is a blocker. The tight suffix injection uses actual distinct deaths. The predecessor dichotomy and record-tight adjacent-swap argument retain the strict earlier-record boundary and cover the small indices separately.

## Count-clock implication and explicit abstract counterexample

The clipped downward-clock condition controls a proportional forward or backward interval of a large signed error. Signed prefix balance then rules out such an interval. This first establishes count-clock tracking. The exact double count supplies a positive lower count density. Locally uniform scaling limits follow from the Lipschitz bound; a plateau would require more distinct diagonal labels than the clock's minimum spacing permits. Strict increase of every scaling limit converts clock tracking to pointwise label tracking. No unique scaling limit is assumed.

The 170-residue counterexample has opposite-parity phase images and excludes every adjacent floor collision within a phase. Its count density is 7/17, with the two nonzero discrepancy coefficients 18/85 and -16/85 canceling over each period. The explicit multi-owner barrier has strict asymptotic margins. Positive-density high-to-low transitions violate the clipped-tail hypothesis. This is an abstract sequence counterexample, with no asserted canonical triangular realization.

## Formal semantic coverage owned by this reviewer

`ROOT-LEAN-SEMANTIC-CHUNK.json` records the renewed individual examination of sorted module rows 160–199, including 260 named source interfaces. Each entry gives the actual retained hypotheses and what the conclusion does and does not establish. In particular, Event-E certificates preserve UnitDip and the numerical-margin/dip conditions; terminal states are not silently replaced by contradictions; reductions of RM2 failure are not advertised as proofs of RM2. Integration-only modules are not counted as new mathematical theorems.

The other two reviewers cover rows 0–159 and 200–264. Fresh compiler/kernel evidence and the complete merged correspondence ledger supply the separate formal and coverage layers.

## Strict liminf strengthening

I independently read the full strict-liminf derivation and its asymptotic crosscheck. I reconstructed the row Abel identity with retained nonnegative chronology slack, the sorted-rank bound, the first-crossing Hall argument, the two separated anchor samples (coefficient 11/(15a²)), the reciprocal-loss term (1/(3γa²)), and the column-capacity excess bound (coefficient 3). The missing-rank interval is converted into positive local excess through the written MEX exclusion, and the averaging boundary errors vanish with the specified fixed scale. I checked that the tiny positive constants are used only after the relevant large-index thresholds and that the conclusion is a strict liminf inequality; convergence is not inferred.

The separately rerun exact Sympy checker reduced the rational identities to zero and verified the displayed rational brackets and sign bounds. It replays the preserved algebra checker and does not itself justify analytic uniformity. See `strict-gap-algebra.json` and `replay_strict_gap_algebra.py`.

## Lag 124 and its finite reduction

I independently reconstructed the proof in `papers/supplements/lag124-proof.md`, including the reply classification, the history-dependent closure, the low-host buffers, least-failure descent for lags 121 and 122, all eight exclusions for the auxiliary position, and the final target-set equality. The source hash and individual checks are recorded in `LAG124-INDEPENDENT-REVIEW.json`. The finite certificate replay verifies its finite inputs; the reviewed induction is the bridge to all indices.
