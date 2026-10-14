# Exact mathematical correspondence of the public Lean claims

This review separates semantic meaning from kernel acceptance. Exact elaborated types and expression trees are in the companion JSON; the final gate supplies source-bound kernel evidence. There are thirteen baseline principal entries, including two import umbrellas and the statement module, plus one promoted dependency. The ten original principal declarations are not ten independent unconditional Chomp theorems.

## Three-row Chomp: definitions and uniqueness statement

Defines sorted three-row positions, legal moves that avoid poison, recursively losing positions, and the uniqueness claim for positive rectangular boards.

**Premises and domain.** Rows are natural numbers p >= q >= r; a rectangle has n > 0 squares per row. Poison-taking moves are excluded because they lose immediately.

**Correspondence review.** Move.first cuts the top row to a positive smaller length and truncates both lower rows; second/third moves truncate the corresponding suffix. IsP requires a nonempty board and every legal move to be non-P, recursively on total squares. This is a statement/definition module, not a proof of the uniqueness claim.

**Not established.** No uniqueness proof is asserted by this module alone.

Source: `lean/core/ChompLean/Statement.lean`, SHA256 `9b9cdeb61ba7421a3cf5cda0e80d8c93e2106d30fb96cf9261394bac4c85505f`.

Declarations: `ChompLean.Move`, `ChompLean.IsP`, `ChompLean.UniqueActualWinningTargetClaim`.

## Unique winning opening in positive three-row rectangles

For every n > 0, the three-row n-by-3 rectangle has exactly one legal non-poison target that is a losing position for the next player.

**Premises and domain.** Only n > 0 remains in the final mathematical statement. All recurrence-model fields are discharged from the recursively defined actual game.

**Correspondence review.** gameF is built from the actual P-position encoding. game_encodes, game_complete and game_lower_blocked discharge the model rather than assume the desired uniqueness. actualWins_iff_wins connects its diagonal/second-cut opening representation to actual P-targets. uniqueActualWinningTarget_checked expands the exact quantified claim. The independent review checks the move-to-target correspondence and poison convention.

**Not established.** No efficient algorithm or diagonal asymptotic follows from uniqueness.

Source: `lean/core/ChompLean/Proof.lean`, SHA256 `1901e75c943286a6f1aeba809bf812c0f2df328ce4786af0235eb91364f11aaa`.

Declarations: `ChompLean.game_encodes`, `ChompLean.game_complete`, `ChompLean.game_lower_blocked`, `ChompLean.actualWins_iff_wins`, `ChompLean.uniqueActualWinningTarget_checked`.

## Canonical game reconstruction and blocker-count bounds

Identifies the canonical blocker-union orbit with the actual game at row n+1, including normalized diagonal output and positive blocker counts; derives quadratic and square-root count certificates.

**Premises and domain.** The orbit starts at canonicalSeed = ([[0]],[0]), equal to canonicalQState 1. The all-row step uses forcing [0] at row 0 and [] thereafter. The square-root certificate assumes R*R <= 2*N, for natural N and R.

**Correspondence review.** sourceQueue and rowQueue normalize exact historical and current-row source values by the row cut. The scan proof identifies both outputs and survivors. canonical_step and canonicalOrbit_eq_state inductively bind that quotient to gameF. Output is gameF(n+1,n+1)-(n+1), with truncated natural subtraction; absolute target and hole-count bridges account for the index shift. The count A(N) satisfies 2*N <= A(N)^2+5*A(N)+2 and R-2 <= A(N) when R^2 <= 2*N.

**Not established.** No equivalence for an arbitrary initial quotient state. No SJS.dword bridge: SJS uses different state definitions.

Source: `lean/core/XGameFOrderedBlockerUnionReconstruction.lean`, SHA256 `6feaa1e0a416914a70ba1515a87a237d5941d0f13ef12fc14efe3c18a9bdc605`.

Declarations: `ChompLean.OBUQ.canonical_step`, `ChompLean.OBUQ.canonical_output`, `ChompLean.OBUQ.canonicalOrbit_eq_state`, `ChompLean.OBUQ.canonical_absoluteHoleCount_eq_gameFBlockerCountThrough`, `ChompLean.OBUQ.gameFBlockerCountThrough_sqrt_certificate`.

## Deadline cuts with explicit low-offset thresholds

Partitions a diagonal owner of q+k into disjoint old and new arms. For q >= 3 and k < 3, q+k is a blocker exactly when it has no old diagonal owner.

**Premises and domain.** The general blocker complement requires q+k > 0. The low-offset simplification requires q >= 3 and k < 3; finite landing-window statements retain k < H.

**Correspondence review.** YoungDiag means an owner a<q with d(a)=q+k; NewDiagAfterCut means an owner q+i with i<k. Injectivity and d(a)>a make this an exhaustive disjoint split. D/S partition supplies the positive blocker complement. The absence of a new owner at k<3 is a separate thresholded game theorem, not a general NoTriple assumption.

**Not established.** No low-offset formula outside the stated q and k domain.

Source: `lean/core/XDeadlineCutYoungDiag.lean`, SHA256 `c542c05d9d82ade03c0edebfa056c843e338e48f2c276a40fcf3fd3edb38e185`.

Declarations: `ChompLean.diagonalOwner_cut_partition`, `ChompLean.youngDiag_disjoint_newDiagAfterCut`, `ChompLean.blocker_iff_cut_deadline_absent`, `ChompLean.blocker_iff_not_youngDiag_of_lt_three`, `ChompLean.gameF_deadlineLandingOffset_cut_iff`.

## Canonical rank-three prefix and peeled tail

For q >= 10, the canonical live columns start [0,2,5], with queues [0], [0,1], [0,1,2,3]; scanning them emits [1,2,4] before the remaining tail.

**Premises and domain.** The canonical-game prefix requires q >= 10. The separate scan identity holds for any supplied queue tail T, with empty initial forcing and history.

**Correspondence review.** The actual-game source-queue theorems discharge each of the three fixed queues. liveCols_rank3_prefix and canonicalQState_rank3_prefix preserve the filtered live tail from columns 6 through q-1. scanQueues_rank3_peel is an exact equality retaining both output and survivor tails; canonical_rank3_peeled_tail bundles these identities.

**Not established.** No finite bound or independent algorithm for the moving tail.

Source: `lean/core/ClaudeCanonicalRankThreePrefix.lean`, SHA256 `2b3bccc61e52a7f2eeb32ba01bfdefb58585125549576ff4cd21cffabc63c5c8`.

Declarations: `ChompLean.OBUQ.sourceQueue_col0`, `ChompLean.OBUQ.sourceQueue_col2`, `ChompLean.OBUQ.sourceQueue_col5`, `ChompLean.OBUQ.canonical_rank3_peeled_tail`.

## Actual-game diagonal slack and blocker-count bounds

Proves d(a)+2 <= 2*a for a >= 9; 3*a+5 <= 2*d(a) for a >= 16; 2*A(a)+4 <= a+1 for a >= 16; and v <= 3*A(v-1)+2 for v >= 26.

**Premises and domain.** All indices are natural numbers and the displayed thresholds are required. A(n) counts positive actual-game blockers through n.

**Correspondence review.** gameF_diagDoubleSlack closes the actual-game supplier chain. gameF_FloorPlus uses an explicit k=d(a), not an arbitrary k. The ceiling and AFloor theorems specialize to the actual blocker count; no residual generic recurrence assumption remains.

**Not established.** The stronger d(a)+10 <= 2*a from a >= 37 is not this theorem and is not supplied by its +2 bound.

Source: `lean/core/R201DiagDoubleSlackCeilingChain.lean`, SHA256 `dd664f7253fbb68f681398f4c271b6a2dcff2ae4ebd601a70ed2da31c9ddab93`.

Declarations: `ChompLean.gameF_diagDoubleSlack`, `ChompLean.gameF_FloorPlus`, `ChompLean.gameFBlockerCountThrough_ceiling`, `ChompLean.gameFBlockerCountThrough_AFloor`.

## Positive EAA freeze-seat gap

For q >= 50, k=A(q), h=A(k)+2*k-q >= 1 and a freeze gameF(q,f)=q with f<q, proves q-k<f and 2*h-1 <= 5*(f-(q-k)).

**Premises and domain.** The positive height and actual freeze are explicit premises. Subtractions are natural-number subtractions.

**Correspondence review.** The theorem combines the independently proved terminal three-fifths floor with the stated positive EAA height. It bounds a supplied freeze seat and proves uniqueness separately; it does not manufacture a blocker, positive height, or a later record.

**Not established.** The cross-record RecordFreezeRefractory assertion remains outside this result.

Source: `lean/core/XEAARecordFreezeGap.lean`, SHA256 `35af08fc0e1798ae2d896ece38b62053e74d6086c26657df3de2fc1dccadebb5`.

Declarations: `ChompLean.gameF_positiveEAA_ranked_freeze_gap`, `ChompLean.gameF_positiveEAA_freeze_gap`, `ChompLean.gameF_freeze_seat_unique`.

## Conditional finite sparse-failure bound

An abstract natural-valued sequence with at most B bad indices through N has x(r) <= 2*B+3 for all r <= N under the stated one-sided growth and good-index bounds.

**Premises and domain.** x(0)=0; x(j)<=x(i)+2*(j-i) for i<=j; not bad(a) implies x(a)<=3; no injection from Fin(B+1) into bad indices <=N.

**Correspondence review.** The budget is the finite-cardinality formulation of at most B bad indices. The growth hypothesis is one-sided, not an absolute Lipschitz assertion. sparseDualFailures_uniform packages the pointwise bracketing theorem. The module is abstract and contains no Chomp-specific instantiation or limit argument.

**Not established.** No density-one statement, o(n) bound, or Chomp AA application is established here.

Source: `lean/core/SparseDualFailures.lean`, SHA256 `49ec5fc20e9efc22651acc10f4604b957d97b6f07239a0d866874cf30d0b2f22`.

Declarations: `ChompLean.sparseDualFailures_bracket`, `ChompLean.sparseDualFailures_uniform`.

## Conditional finite block inequalities

For natural-valued u and err satisfying the minimum-error addition hypothesis, bounds u(k*q) and u(k*q+r) by repeated q-blocks and an explicit remainder.

**Premises and domain.** u(m+n)<=u(m)+u(n)+err(n) whenever 0<n<=m; q,k>0; the remainder formula also assumes 0<r<q.

**Correspondence review.** The elaborated inequalities are u(k*q)<=k*u(q)+(k-1)*err(q) and u(k*q+r)<=k*u(q)+(k-1)*err(q)+u(r)+err(r). Induction iterates the smaller summand q, then applies the small remainder r. Natural codomain, positivity and ordering are essential to the actual statement.

**Not established.** No analytic limit-existence theorem, real-valued generalization, or actual Chomp subadditivity supplier appears in this module.

Source: `lean/core/MinErrorFekete.lean`, SHA256 `17d1b1e4fb78dfb9e817a76cce66d5c2ced2faa45e0851d5921042ab6f25e5ef`.

Declarations: `ChompLean.minErrorFekete_mul`, `ChompLean.minErrorFekete_mul_add`.

## Conditional forward-freeze exchange and lag-eight restriction

Constructs unique exchange witnesses from an actual forward-freeze collision. In the stated lag-eight seven-host schedule and row window, a collision can only occur at row q and freeze at q+1 or q+2.

**Premises and domain.** The exchange retains all host/freeze equalities and strict index inequalities. The lag-eight theorem requires q>=26, Lag8TargetSevenHostSchedule q g host, q-4<=t<=q+2, c=host(t), c<k, gameF(k,c)=k and k<q+3.

**Correspondence review.** The companion witness lies below c, equals k in row t, and is unique by row injectivity. The full exchange additionally reconstructs v at row k left of its original victim. The specialized schedule theorem rules out all but its two dynamic rows only after the supplied schedule is unfolded.

**Not established.** No existence theorem for the seven-host schedule or a global collision bound.

Source: `lean/core/R182ForwardFreezeCollisionExchange.lean`, SHA256 `35adbf863c651122dd09e9ba8863aa4da8e4483482fd0c2872be8a95219f7913`.

Declarations: `ChompLean.gameF_forward_freeze_collision_forces_left_companion`, `ChompLean.gameF_terminal_relay_forward_collision_exchange`, `ChompLean.gameF_lag8_tail_forward_collision_only_dynamic_topTwo`.

## Abstract conditional composition interface

Composes supplied stage-correctness implications for arbitrary carriers and predicates. The winning-move conclusion is conditional on that interface and an exact initial state; the cost theorem projects an assumed inequality.

**Premises and domain.** Eight arbitrary carrier types; all functions and correctness predicates supplied in EndToEndInvariantPortfolio; an initial StateExact hypothesis. stepCostWithinLogBudget is assumed and logBudget is arbitrary.

**Correspondence review.** The theorem expands stage definitions and applies portfolio fields in sequence. StateExact can be identically false, so no inhabited exact state is established. WinningMove can be any predicate, so the result alone is not actual Chomp correctness. Functions may consult arbitrary data. The cost conclusion follows directly from its field and has no mathematical logarithm requirement. Documentation was corrected without changing code tokens.

**Not established.** No concrete Chomp algorithm, oracle restriction, initialized exact state, or logarithmic complexity theorem.

Source: `lean/core/EndToEndInvariantAssembly.lean`, SHA256 `87000282ec957cacd1780352a6b2360e39b4ca272214fc50f630ef2e0794e7e1`.

Declarations: `ChompLean.EndToEndInvariantPortfolio`, `ChompLean.endToEnd_step_exact`, `ChompLean.endToEnd_emits_winning_move`, `ChompLean.endToEnd_step_cost_bound`.

## Research core: nine principal import roots

Imports the nine principal research modules. Each linked declaration retains its own exact assumptions and scope.

**Premises and domain.** This umbrella has no independent theorem statement.

**Correspondence review.** The source consists of imports. Its successful build and replay attest its import closure; they do not create a stronger combined theorem.

**Not established.** No additional mathematical claim is inferred from an umbrella import.

Source: `lean/core/ResearchCore.lean`, SHA256 `2cfec9ec8e9b59963b4d991ebe8443fa51f07f384a8bfe81ff69238d5d645a90`.

## Uniqueness: statement and proof entry point

Imports the actual-game uniqueness proof and statement.

**Premises and domain.** This umbrella has no independent theorem statement.

**Correspondence review.** The source is an import entry point. The mathematical claim and its semantic review belong to ChompLean.Statement and ChompLean.Proof.

**Not established.** No separate theorem is counted for this import entry point.

Source: `lean/core/ChompLean.lean`, SHA256 `31b8b7d7a287688f3f6983a37f299ecf58170be1b76b8b63f96fbc6a4adb3db1`.

## Actual-game future-freeze diagonal inequality

For natural c<q, if gameF(q,c)=q then q<gameF(c,c). Also supplies the prehost consequence and an independent recurrence-based specialization.

**Premises and domain.** The actual-game theorem has only c<q and the freeze equality as premises. The abstract model theorem additionally requires a no-repeat property, discharged in the actual game.

**Correspondence review.** Propagation assigns every intermediate row a host left of c. No-repeat and row injectivity inject those rows into row-c values strictly between c and d(c), giving q<=d(c). D/S disjointness rules out equality. The adjacent case follows from diagonal growth and the same disjointness. The original source was omitted from the core; its exact bytes are promoted as dependency 265, preserving the baseline 264 count.

**Not established.** This does not supply the stronger diagonal slack +10 from row37.

Source: `lean/core/ClaudeFutureFreezeDiagonal.lean`, SHA256 `f92ad3a06d1adfeec5d0603bc98cb2ad8f1041eb158238e6901d15079ac9d1f8`.

Declarations: `ChompLean.gameF_futureFreezeDiagonal`, `ChompLean.gameF_futureFreezeDiagonal_via_recurrence`, `ChompLean.gameF_freezeSeatPrehost`.
