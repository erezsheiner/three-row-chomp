import R56TopTwoHoles
import DipZRehostRM2Reduction

/-!
# R124 — FLOOR rank quotient (Tasks A, B, C)

Floor-side (pivot direction). **RM2 not proved.** Small axiom-audited kernel:
* Task A — `gameF_v1_lt_diagonal` : `V1(q) < d(q)` (DGV1), directly from the two mex clauses
  of `gameF_top_two_positive_holes`; no empirical gap bound.
* Task B — `gameF_floor_at_new_record_v1_target` : the target-new-record FLOOR branch, via
  `V1(t) < d(t) ≤ RMax(t+1) < V1(t+2)`.
* Task C — the abstract integer rank-quotient identity and its `≤`-equivalence (the floor-side
  analog of the E-band / allocation-displacement structure). `Int`, no truncated subtraction.

Status fences honoured: nothing about Rank-FLOOR / V1-FLOOR / SETTLE-0 / bounded H band / RM2 is
assumed. Task D (same-fibre + NoTriple combinatorics) is left out — see report for the missing
range-membership interface (not banking a blocker-count axiom just to compile).
-/

set_option autoImplicit false

namespace ChompLean

/-- **Task A — DGV1.**  The first hole `V1(q)=gameF q (q-1)` is strictly below the diagonal
`d(q)=gameF q q`, directly from the two mex clauses (the diagonal is the *second* positive
hole, hence `≠ V1` and not `< V1`). -/
theorem gameF_v1_lt_diagonal {q : Nat} (hq : 0 < q) :
    gameF q (q - 1) < gameF q q := by
  obtain ⟨hmex1, hmex2⟩ := gameF_top_two_positive_holes hq
  obtain ⟨_, _hv_notin, hv_cov⟩ := hmex1
  obtain ⟨hd0, hd_notin, _⟩ := hmex2
  rcases Nat.lt_trichotomy (gameF q (q - 1)) (gameF q q) with h | h | h
  · exact h
  · exact absurd (Or.inr h.symm) hd_notin
  · exact absurd (Or.inl (hv_cov (gameF q q) hd0 h)) hd_notin

/-- **Task B — target-new-record FLOOR branch.**  If the row-`t+2` first hole beats the running
maximum through `t+1`, then it is strictly above `V1(t)`.  Proof: `V1(t) < d(t) ≤ RMax(t+1) < V1(t+2)`. -/
theorem gameF_floor_at_new_record_v1_target
    {t : Nat} (ht : 0 < t)
    (hnew : RMax gameRecurrenceModel (t + 1) < gameF (t + 2) (t + 1)) :
    gameF t (t - 1) < gameF (t + 2) (t + 1) := by
  have hv1 : gameF t (t - 1) < gameF t t := gameF_v1_lt_diagonal ht
  have hdle : gameF t t ≤ RMax gameRecurrenceModel (t + 1) :=
    rmax_ge gameRecurrenceModel (t + 1) t (by omega)
  omega

/-- **Task C — the V1 rank height.** `t − rank(V1(t))`, over an abstract rank/value pair. -/
def V1RankHeight (rangeRank v1 : Nat → Nat) (t : Nat) : Int :=
  (t : Int) - (rangeRank (v1 t) : Int)

/-- Exact lag-two increment of the rank height. -/
theorem v1RankHeight_lagTwo_delta (rangeRank v1 : Nat → Nat) (t : Nat) :
    V1RankHeight rangeRank v1 (t + 2) - V1RankHeight rangeRank v1 t
      = 2 + (rangeRank (v1 t) : Int) - (rangeRank (v1 (t + 2)) : Int) := by
  unfold V1RankHeight
  omega

/-- The rank-monotone step is exactly a bounded rank-height increment `≤ 2`. -/
theorem v1RankHeight_lagTwo_le_iff (rangeRank v1 : Nat → Nat) (t : Nat) :
    rangeRank (v1 t) ≤ rangeRank (v1 (t + 2)) ↔
    V1RankHeight rangeRank v1 (t + 2) ≤ V1RankHeight rangeRank v1 t + 2 := by
  unfold V1RankHeight
  omega

end ChompLean

#print axioms ChompLean.gameF_v1_lt_diagonal
#print axioms ChompLean.gameF_floor_at_new_record_v1_target
#print axioms ChompLean.v1RankHeight_lagTwo_delta
#print axioms ChompLean.v1RankHeight_lagTwo_le_iff
