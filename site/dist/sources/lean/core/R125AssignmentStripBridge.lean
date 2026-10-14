import SelectorColHistCausalDepth

set_option autoImplicit false

namespace ChompLean

/-!
Small theorem-grade core for the assignment/strip bridge audit.

The game-specific max-plus assignment law remains an explicit open target.
The arithmetic lemma below records exactly how it would turn a preview-host
envelope into the width-one freeze band.  The last theorem deletes the
`q=t+3` OLD-LOSS boundary using only the already proved column-zero rail and
fixed-row injectivity (packaged by `gameF_lag_one_host_only_col0`).
-/

def FreezeBand (g c : Nat) : Prop :=
  g <= c + 1 /\ c <= g + 1

def PreviewEnvelope (g previousFreeze previewHost : Nat) : Prop :=
  g <= max previousFreeze previewHost + 2 /\
  max previousFreeze previewHost <= g

theorem freezeBand_iff_previewEnvelope_of_maxPlus
    {g c previousFreeze previewHost : Nat}
    (hmax : c = max previousFreeze previewHost + 1) :
    FreezeBand g c <-> PreviewEnvelope g previousFreeze previewHost := by
  subst c
  simp only [FreezeBand, PreviewEnvelope]
  omega

/-- The lower half of the max-plus assignment law follows from the two strict
orders.  Its upper half is the genuine no-gap/MEX-saturation obligation. -/
theorem maxPlus_lower_of_previous_and_preview_lt_freeze
    {previousFreeze previewHost c : Nat}
    (hprevious : previousFreeze < c)
    (hpreview : previewHost < c) :
    max previousFreeze previewHost + 1 <= c := by
  omega

/-- In the `q=t+4` OLD-LOSS boundary, R126 places the preview host at least
three columns left of `T=t+2`, while the row-start freeze is at or right of
`T`.  Under the max-plus assignment law the preview cannot win the maximum:
the previous freeze must dominate by at least two columns and the new freeze
is exactly its successor.  This isolates the previous-freeze queue as the
only remaining assignment mechanism on that boundary. -/
theorem oldLoss_t_add_four_maxPlus_previous_dominates
    {T c previousFreeze previewHost : Nat}
    (hpreview : previewHost + 3 <= T)
    (hfreeze : T <= c)
    (hmax : c = max previousFreeze previewHost + 1) :
    previewHost + 2 <= previousFreeze /\
      c = previousFreeze + 1 := by
  by_cases hle : previousFreeze <= previewHost
  · have hmaxEq : max previousFreeze previewHost = previewHost :=
      Nat.max_eq_right hle
    rw [hmaxEq] at hmax
    omega
  · have hge : previewHost <= previousFreeze := by omega
    have hmaxEq : max previousFreeze previewHost = previousFreeze :=
      Nat.max_eq_left hge
    rw [hmaxEq] at hmax
    exact ⟨by omega, hmax⟩

/-- R126's proposed nearest OLD-LOSS boundary `q=t+3` is already impossible:
on row `t+2`, the value `t+3` is uniquely hosted at column zero, so it cannot
also occupy the V1 column `t+1` when `t>=3`. -/
theorem oldLoss_V1_boundary_t_add_three_impossible
    {t : Nat} (ht : 3 <= t)
    (hV1 : gameF (t + 2) (t + 1) = t + 3) : False := by
  have hhost : gameF ((t + 1) + 1) (t + 1) = (t + 1) + 2 := by
    have hrow : (t + 1) + 1 = t + 2 := by omega
    have hvalue : (t + 1) + 2 = t + 3 := by omega
    rw [hrow, hvalue]
    exact hV1
  have hcol : t + 1 = 0 :=
    gameF_lag_one_host_only_col0 (q := t + 1) (c := t + 1)
      (by omega) hhost
  omega

#print axioms freezeBand_iff_previewEnvelope_of_maxPlus
#print axioms maxPlus_lower_of_previous_and_preview_lt_freeze
#print axioms oldLoss_t_add_four_maxPlus_previous_dominates
#print axioms oldLoss_V1_boundary_t_add_three_impossible

end ChompLean
