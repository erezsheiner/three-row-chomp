# Independent semantic review: the actual-game uniqueness theorem

Reviewer: publication integrator, independent of the current Lean kernel-audit lane. Date: 13 October 2026.

Semantic verdict: **accepted for the exact statement below**. The separate exhaustive kernel audit must bind this review to the final source hashes. This review asserts neither a fast algorithm nor any diagonal-density limit.

## Exact mathematical statement

For every positive integer n, ordinary poisoned-square Chomp on a three-row rectangle with n squares in each row has exactly one winning opening move. Winning means that, after the move, the opponent is in a losing position under optimal play. The board has a poisoned square in the top left; taking that square loses immediately.

The final declaration is `ChompLean.uniqueActualWinningTarget_checked`, with type `ChompLean.UniqueActualWinningTargetClaim`. Expanding the latter gives a universal quantifier over natural n with the explicit hypothesis 0<n, followed by existence of a legal non-poison target y that is a P-position, and equality to y of every other legal P-target. There are no recurrence, density, numerical-range or algorithmic hypotheses in this final statement.

## Board and move dictionary

`Statement.lean:44` represents a board by natural row lengths p,q,r and proofs r≤q≤p. This describes exactly the down-closed three-row shapes reachable from a rectangle. Proof fields add no game information; `Pos.ext` identifies boards by their three lengths.

For a square in row i and column j, put a=j−1. Chomping that square removes precisely the suffix starting there and all lower-row squares in those columns. The three resulting triples are (a,min(a,q),min(a,r)), (p,a,min(a,r)), and (p,q,a). These are exactly `firstCut`, `secondCut` and `thirdCut`; the strict bound on a says the selected square was present. Top-row a=0 is precisely the poisoned square. Top-row a>0 and all second/third-row cuts are exactly the non-poison actions enumerated by `Move` at line118. There is no omitted winning action: the only excluded physical action loses immediately.

Every reachable non-poison state has p>0. A non-poison move strictly decreases p+q+r (`move_size_lt`). The only such board with no non-poison move is (1,0,0): if p>1 the top row can be shortened positively, and if q>0 the second row can be shortened; r>0 implies q>0. At (1,0,0) the player must take poison and lose. Thus replacing the immediately losing poison action by absence from the option relation preserves P/N classification, by induction on board size.

`IsP` at line155 is exactly that induction: p>0 and every non-poison option is non-P. `not_isP_has_move_to_P` supplies the converse for nonempty boards. Its use of classical logic is ordinary finite-game reasoning, not an extra Chomp assumption. The empty board is deliberately not a P-position and is unreachable by non-poison play; it cannot affect the theorem.

## Non-vacuity and the base case

For n=1 the three-row board is (1,1,1). The second-row cut to0 gives (1,0,0), a P-position. The third-row cut to0 gives (1,1,0), which has a move to (1,0,0) and is non-P. There is no positive top-row cut. Therefore the quantifier includes n=1 with a genuine unique winner. The n=0 board is excluded explicitly, not hidden in a recurrence convention.

## Recurrence hypotheses are discharged by the actual game

`Encoding.lean:14` defines an encoded value using actual `IsP`: either r<p<q and (p,p,r) is P, or r<p and q≤p and (p,q,r) is P. This agrees with the two cases of the encoded P-position, rather than defining P-positions in terms of a desired recurrence.

`encodedPosition_unique` (line35) is justified by an actual top-row move between any two distinct candidate P-positions. `encoded_exists_from_game` (line534) uses strong induction on q+r. The blockers from smaller lower pairs form a finite list. Choosing p larger than q and its sum prevents a second/third-row P-option. Either a first-row P-option provides the required encoding, or the chosen board itself is P. The auxiliary rectangle-N fact is proved by the standard one-square stealing move and lifting every reply (`rectangle_to_stolen`, `stolen_move_lifts`, `rectangle_not_isP`, lines384–425), without assuming uniqueness.

`gameF` (`Proof.lean:512`) chooses the established encoding, and `game_encodes`/`game_complete` supply its two directions. The arbitrary value assigned outside r≤q is unused by the theorem. Every field of `gameRecurrenceModel` (line525) is filled by previously proved declarations about this `gameF`; the structure is not a parameter of the final theorem. In particular, lower blocking and both recurrence branches are derived from encoding and game options. The finite interval injection argument supplies the rightmost-hole input without numerical testing.

## From encoded winners back to actual actions

`actualWins_iff_wins` (line563) proves both directions for second-row targets (n,a,a) and third-row targets (n,n,r). `uniqueActualWinningTarget` (line877) additionally handles every constructor of `Move`: a positive top-row cut produces a smaller rectangle and cannot be winning, and the other two constructors are converted to the encoded opening classes.

Target uniqueness is genuine action uniqueness here. Within each row, the shortened length determines the chosen square. Different rows produce distinct targets: a top-row move reduces p, a second-row move keeps p=n but reduces q, and a third-row move keeps p=q=n but reduces r. Thus no pair of physically different opening squares is collapsed by the target representation. This argument does not identify game-tree paths with actions or rely on proof-field identity.

## Published mathematics comparison

The public reference inspected was [Sheiner, arXiv:2605.23837v2](https://arxiv.org/html/2605.23837v2), Theorem1.1 and the definitions in Sections1–2. Its game convention, positive-n domain and uniqueness claim match the interface above. The proof architecture also matches: encoding, interval blocking, row-start propagation and separation of the two opening classes. This is a correspondence assessment of the local formal development; it makes no independent claim about historical priority.

## Publication wording

Approved: “For every positive n, the three-row n-column Chomp rectangle has exactly one winning opening move. The proof uses the ordinary poisoned-square rules and is formalized by `ChompLean.uniqueActualWinningTarget_checked`.”

Not established by this theorem: an executable efficient strategy, an O(n log n) running time, a silver-ratio limit, or equivalence of an independently implemented journal engine with `gameF` at every index.
