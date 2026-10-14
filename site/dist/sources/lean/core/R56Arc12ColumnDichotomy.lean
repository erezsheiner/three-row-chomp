import R56EchoLeft

set_option autoImplicit false

namespace ChompLean

/-!
R56 Arc-12 audit: exact first-hole column dichotomies.

These are the sound, minimality-free consequences behind the proposed
"minimal-violation forcing" step.  At row `t+1`, a cell left of the V1
catch is either already below V1, or the V-catch gate makes its column a
strict prior-host column of V1.  The exact column-age lemmas then list all
possible recent hosts.

In row-`T` notation, substitute `t = T-1`.  The first theorem concerns
column `T-2`; the second concerns column `T-3`.  In particular, the latter
has two genuine historical alternatives, V1 at row `T-2` and V2 at row
`T-1`; neither can be discarded by column arithmetic alone.
-/

/-- At the current V2 cell, either the occupant is below the first hole,
or the first hole is exactly the preceding row's V1 value. -/
theorem gameF_first_hole_v2_below_or_previous_v1
    {t : Nat} (ht : 1 <= t) :
    gameF (t + 1) (t - 1) < gameF (t + 1) t \/
      gameF t (t - 1) = gameF (t + 1) t := by
  by_cases hbelow :
      gameF (t + 1) (t - 1) < gameF (t + 1) t
  · exact Or.inl hbelow
  · right
    have hne :
        gameF (t + 1) (t - 1) ≠ gameF (t + 1) t := by
      intro hEq
      have hcol : t - 1 = t :=
        gameRecurrenceModel.fixed_q_injective (by omega) (by omega) hEq
      omega
    have hhigher :
        gameF (t + 1) t < gameF (t + 1) (t - 1) := by
      omega
    have hpast : PastHostColumn gameRecurrenceModel (t + 1)
        (gameF (t + 1) t) (t - 1) :=
      gameF_first_hole_vCatch_gate t (t - 1) (by omega) hhigher
    exact
      (pastHostColumn_t_sub_one_exact gameRecurrenceModel ht).mp hpast

/-- One column farther left, the exact sound alternative has two recent
history branches.  The V1-at-`t-1` branch is essential and cannot be
silently removed by the V-catch gate or by non-pastness. -/
theorem gameF_first_hole_three_back_dichotomy
    {t : Nat} (ht : 2 <= t) :
    gameF (t + 1) (t - 2) < gameF (t + 1) t \/
      gameF (t - 1) (t - 2) = gameF (t + 1) t \/
      gameF t (t - 2) = gameF (t + 1) t := by
  by_cases hbelow :
      gameF (t + 1) (t - 2) < gameF (t + 1) t
  · exact Or.inl hbelow
  · right
    have hne :
        gameF (t + 1) (t - 2) ≠ gameF (t + 1) t := by
      intro hEq
      have hcol : t - 2 = t :=
        gameRecurrenceModel.fixed_q_injective (by omega) (by omega) hEq
      omega
    have hhigher :
        gameF (t + 1) t < gameF (t + 1) (t - 2) := by
      omega
    have hpast : PastHostColumn gameRecurrenceModel (t + 1)
        (gameF (t + 1) t) (t - 2) :=
      gameF_first_hole_vCatch_gate t (t - 2) (by omega) hhigher
    exact
      (pastHostColumn_t_sub_two_exact gameRecurrenceModel ht).mp hpast

#print axioms gameF_first_hole_v2_below_or_previous_v1
#print axioms gameF_first_hole_three_back_dichotomy

end ChompLean
