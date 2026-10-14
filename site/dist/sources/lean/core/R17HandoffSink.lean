import R15ParkedValueSwap

set_option autoImplicit false

namespace ChompLean

/-!
R17: the source-algebra wrapper for the proposed one-step sink law.

The substantive open assertion is the schedule dichotomy

  f t (e + 1) = z  or  f (e + 2) (e + 2) = z.

Once either branch is known, the value has entered a permanent channel:
the fixed current-row prefix in the first branch, or the diagonal prefix in
the second.  This file deliberately proves only that mechanical implication;
it does not assume or claim the open schedule assertion.
-/

/-- Coverage by one of the two channels that are monotone to the right. -/
def PermanentCover
    (f : Nat -> Nat -> Nat) (t e z : Nat) : Prop :=
  DiagPrefix f t e z \/ C f t e z

theorem permanentCover_mem_source
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (h : PermanentCover f t e z) :
    B f t e z := by
  rcases h with hdiag | hrow
  · left
    exact R_iff_diagPrefix_or_colTail.mpr (Or.inl hdiag)
  · exact Or.inr hrow

/-- Permanent coverage is monotone when the source column moves right. -/
theorem permanentCover_mono
    {f : Nat -> Nat -> Nat} {t e r z : Nat}
    (h : PermanentCover f t e z) (her : e <= r) :
    PermanentCover f t r z := by
  rcases h with hdiag | hrow
  · rcases hdiag with ⟨a, hat, hae, hval⟩
    exact Or.inl ⟨a, hat, Nat.le_trans hae her, hval⟩
  · rcases hrow with ⟨b, hbe, hval⟩
    exact Or.inr ⟨b, Nat.lt_of_lt_of_le hbe her, hval⟩

/-- A fresh emission at `e+1` is permanent from source column `e+2`. -/
theorem fresh_successor_enters_permanent
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hfresh : f t (e + 1) = z) :
    PermanentCover f t (e + 2) z := by
  exact Or.inr ⟨e + 1, by omega, hfresh⟩

/-- The owner at `e+2` is permanent once that diagonal is available. -/
theorem next_diagonal_enters_permanent
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (ht : e + 2 < t) (hdiag : f (e + 2) (e + 2) = z) :
    PermanentCover f t (e + 2) z := by
  exact Or.inl ⟨e + 2, ht, Nat.le_refl _, hdiag⟩

/--
The proposed death dichotomy is exactly sufficient to put the lost value in
a permanent channel two source columns after its old support.
-/
theorem death_dichotomy_enters_permanent
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hsink :
      f t (e + 1) = z \/
      (e + 2 < t /\ f (e + 2) (e + 2) = z)) :
    PermanentCover f t (e + 2) z := by
  rcases hsink with hfresh | ⟨ht, hdiag⟩
  · exact fresh_successor_enters_permanent hfresh
  · exact next_diagonal_enters_permanent ht hdiag

/-- Hence the value stays covered at every later source column. -/
theorem death_dichotomy_covers_later_source
    {f : Nat -> Nat -> Nat} {t e r z : Nat}
    (hsink :
      f t (e + 1) = z \/
      (e + 2 < t /\ f (e + 2) (e + 2) = z))
    (her : e + 2 <= r) :
    B f t r z := by
  apply permanentCover_mem_source
  exact permanentCover_mono
    (death_dichotomy_enters_permanent hsink) her

/-!
The blocker handoff receipt has a different index from an actual death:
it emits `z` at cell `e+2`, so it enters the row-prefix source at `e+3`.
Keeping this theorem separate prevents the cell/source off-by-one from being
hidden by the typed range branch, whose diagonal owner already enters at
source column `e+2`.
-/
theorem blocker_handoff_fresh_sink_covers_later_source
    {f : Nat -> Nat -> Nat} {t e r z : Nat}
    (hfresh : f t (e + 2) = z)
    (her : e + 3 <= r) :
    B f t r z := by
  exact fresh_emission_persists_in_all_later_sources hfresh (by omega)

/-- The range handoff branch is already permanent at source column `e+2`. -/
theorem range_handoff_diagonal_sink_covers_later_source
    {f : Nat -> Nat -> Nat} {t e r z : Nat}
    (ht : e + 2 < t)
    (hdiag : f (e + 2) (e + 2) = z)
    (her : e + 2 <= r) :
    B f t r z := by
  apply permanentCover_mem_source
  exact permanentCover_mono
    (next_diagonal_enters_permanent ht hdiag) her

/--
Packaged for an actual one-edge source loss.  The source algebra supplies
`ParkedOnly`; the open schedule dichotomy supplies permanent recovery.
-/
theorem parked_death_dichotomy_closes_by_backstop
    {f : Nat -> Nat -> Nat} {t e c3 z : Nat}
    (hcurrent : B f t e z)
    (hlost : Not (B f t (e + 1) z))
    (hsink :
      f t (e + 1) = z \/
      (e + 2 < t /\ f (e + 2) (e + 2) = z))
    (hedge : e + 2 <= c3) :
    ParkedOnly f t e z /\ B f t c3 z := by
  constructor
  · exact source_loss_implies_parkedOnly hcurrent hlost
  · exact death_dichotomy_covers_later_source hsink hedge

end ChompLean
