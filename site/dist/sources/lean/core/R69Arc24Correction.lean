import R33DipHoleNextEmissionEquivalence
import TerminalBackfillSourceLoss
import R60FirstRMaxEvent
import R14FrontierLaw

/-!
# R69 — Arc-24 correction: the valid fall-machine theorem

**RM2 not proved.**  This file banks the *corrected* logical interface (per the R69 brief):
the unsupported `NIE + FC ⟹ TwoStepDiagonalRecordLaw` is **not** stated.  The valid theorems are

* `NIE + FC ⟹ NoConsecutiveDips`  (Task B), and
* `UnitDip + NIE + FC ⟹ TwoStepDiagonalRecordLaw`  (conditional closure, via R33).

`NoInteriorEaten` gives `d(q+1)=V1(q)` at a dip; it is **not** equivalent to tightness (which would
additionally require `V1(q)+1=d(q)`).  All catches are stated with `C`, not a receipt predicate.
Total Nat-subtraction convention throughout, so the `s=0` transition is covered.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-- First hole value of row `q`: the cell immediately left of the diagonal. -/
noncomputable def FirstHoleValue (q : Nat) : Nat := gameF q (q - 1)

/-- **NoInteriorEaten** — every diagonal dip `q → q+1` lands exactly on `V1(q)`. -/
def NoInteriorEaten : Prop :=
  ∀ q, gameF (q + 1) (q + 1) < gameF q q → gameF (q + 1) (q + 1) = FirstHoleValue q

/-- **ForcedCatch** — a strictly falling first hole `V1(q+1) < V1(q)` is caught in row `q+2`. -/
def ForcedCatch : Prop :=
  ∀ q, FirstHoleValue (q + 1) < FirstHoleValue q →
    C gameF (q + 2) (q + 2) (FirstHoleValue (q + 1))

/-- **Task B — the valid fall-machine theorem.**  `NIE + FC ⟹ NoConsecutiveDips`.
No unit-dip and no R56 top-two input are needed. -/
theorem noConsecutiveDips_of_noInteriorEaten_forcedCatch
    (hNIE : NoInteriorEaten) (hFC : ForcedCatch) :
    NoConsecutiveDips gameRecurrenceModel := by
  intro s hdip_s hdip_s1
  -- NIE at `s`: `d(s+1) = V1(s)`.
  have hev_s : gameF (s + 1) (s + 1) = FirstHoleValue s := hNIE s hdip_s
  -- `V1(s+1) < d(s+1)` by fixed-row maximality.
  have hmax : gameF (s + 1) s < gameF (s + 1) (s + 1) :=
    recurrence_strict_row_diagonal_maximal gameRecurrenceModel (by omega)
  have hV1lt : FirstHoleValue (s + 1) < gameF (s + 1) (s + 1) := by
    unfold FirstHoleValue; rw [show (s + 1) - 1 = s from by omega]; exact hmax
  -- Hence `V1(s+1) < V1(s)`, so FC catches `V1(s+1)` in row `s+2`.
  have hfall : FirstHoleValue (s + 1) < FirstHoleValue s := by rw [← hev_s]; exact hV1lt
  have hC : C gameF (s + 2) (s + 2) (FirstHoleValue (s + 1)) := hFC s hfall
  -- NIE at `s+1`: `d(s+2) = V1(s+1)`.
  have hev_s1 : gameF (s + 2) (s + 2) = FirstHoleValue (s + 1) := hNIE (s + 1) hdip_s1
  -- Destruct the catch and contradict fixed-row injectivity.
  obtain ⟨b, hb, hbval⟩ := hC
  have heq : gameF (s + 2) b = gameF (s + 2) (s + 2) := by rw [hbval, hev_s1]
  have hbeq := gameRecurrenceModel.fixed_q_injective (Nat.le_of_lt hb) (Nat.le_refl (s + 2)) heq
  omega

/-- **Conditional RM2 closure.**  `UnitDip + NIE + FC ⟹ TwoStepDiagonalRecordLaw` — the only
valid record-law statement in this interface; obtained via R33. -/
theorem twoStepRecordLaw_of_unitDip_noInteriorEaten_forcedCatch
    (hU : UnitDip gameRecurrenceModel)
    (hNIE : NoInteriorEaten) (hFC : ForcedCatch) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel :=
  twoStepRecordLaw_of_unitDip_noConsecutiveDips gameRecurrenceModel hU
    (noConsecutiveDips_of_noInteriorEaten_forcedCatch hNIE hFC)

/-- Contrapositive interface: with `NIE`, `FC`, and a failure of the record law, `UnitDip` fails. -/
theorem not_unitDip_of_noInteriorEaten_forcedCatch_not_recordLaw
    (hNIE : NoInteriorEaten) (hFC : ForcedCatch)
    (hNotRec : ¬ TwoStepDiagonalRecordLaw gameRecurrenceModel) :
    ¬ UnitDip gameRecurrenceModel :=
  fun hU => hNotRec (twoStepRecordLaw_of_unitDip_noInteriorEaten_forcedCatch hU hNIE hFC)

/-- **Task C step 1 — strict first failure.**  At the least failed two-step record comparison,
`d(k+2)` is strictly below the running maximum: it cannot *equal* `RMax(k)` (that would repeat a
prefix diagonal, violating diagonal injectivity), so the `≥` from failure sharpens to `<`. -/
theorem firstFailure_diagonal_strictly_below_rmax
    {k : Nat}
    (hfail : ¬ (RMax gameRecurrenceModel k < gameF (k + 2) (k + 2))) :
    gameF (k + 2) (k + 2) < RMax gameRecurrenceModel k := by
  have hle : gameF (k + 2) (k + 2) ≤ RMax gameRecurrenceModel k := Nat.not_lt.mp hfail
  rcases Nat.lt_or_ge (gameF (k + 2) (k + 2)) (RMax gameRecurrenceModel k) with h | h
  · exact h
  · exfalso
    have heq : gameF (k + 2) (k + 2) = RMax gameRecurrenceModel k := by omega
    obtain ⟨j, hjk, hjval⟩ := rmax_witness gameRecurrenceModel k
    rw [hjval] at heq
    have hjeq := diagonal_injective gameRecurrenceModel heq
    omega

/-- **Task C step 2 — running maximum is the current diagonal** in the arm `d(k+1) < d(k+2)`.
An older maximum `RMax(k) = d(j)` with `j ≤ k-2` gives `RMax(k) < d(j+2) ≤ RMax(k)` via the
prefix; `j = k-1` gives `RMax(k) ≤ RMax(k-1) < d(k+1) < d(k+2) < RMax(k)`.  So `j = k`. -/
theorem firstFailure_rmax_is_current_diagonal
    {k : Nat}
    (hprefix : RMaxTwoStepPrefix gameRecurrenceModel k)
    (hfail : ¬ (RMax gameRecurrenceModel k < gameF (k + 2) (k + 2)))
    (hrise : gameF (k + 1) (k + 1) < gameF (k + 2) (k + 2)) :
    RMax gameRecurrenceModel k = gameF k k := by
  have hstrict := firstFailure_diagonal_strictly_below_rmax hfail
  obtain ⟨j, hjk, hjval⟩ := rmax_witness gameRecurrenceModel k
  have hjval' : RMax gameRecurrenceModel k = gameF j j := hjval
  rcases Nat.lt_or_ge j k with hjlt | hjge
  · exfalso
    rcases Nat.lt_or_ge (j + 2) (k + 1) with h1 | h2
    · -- `j + 2 ≤ k`
      have hj2k : j + 2 ≤ k := by omega
      have hp : RMax gameRecurrenceModel j < gameF (j + 2) (j + 2) := hprefix j (by omega)
      have hgej : gameF j j ≤ RMax gameRecurrenceModel j :=
        rmax_ge gameRecurrenceModel j j (Nat.le_refl j)
      have hle2 : gameF (j + 2) (j + 2) ≤ RMax gameRecurrenceModel k :=
        rmax_ge gameRecurrenceModel k (j + 2) hj2k
      omega
    · -- `j + 1 = k`, so `j + 2 = k + 1`
      have hjj : j + 2 = k + 1 := by omega
      have hp : RMax gameRecurrenceModel j < gameF (j + 2) (j + 2) := hprefix j (by omega)
      rw [hjj] at hp
      have hgej : gameF j j ≤ RMax gameRecurrenceModel j :=
        rmax_ge gameRecurrenceModel j j (Nat.le_refl j)
      omega
  · have hjeqk : j = k := by omega
    rw [hjeqk] at hjval'
    exact hjval'

/-- **Task C — arm dichotomy.**  At a first two-step record failure the two arms are exactly
`d(k+1) < d(k+2)` (DEEP-GAP-RELAY ordering; `RMax(k) = d(k)` by the previous theorem) or
`d(k+2) < d(k+1)` (LANDING-CROSS ordering).  Equality is excluded by diagonal injectivity. -/
theorem firstFailure_arm_dichotomy
    {k : Nat}
    (hfail : ¬ (RMax gameRecurrenceModel k < gameF (k + 2) (k + 2))) :
    gameF (k + 1) (k + 1) < gameF (k + 2) (k + 2) ∨
    gameF (k + 2) (k + 2) < gameF (k + 1) (k + 1) := by
  rcases Nat.lt_or_ge (gameF (k + 1) (k + 1)) (gameF (k + 2) (k + 2)) with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    rcases Nat.lt_or_ge (gameF (k + 2) (k + 2)) (gameF (k + 1) (k + 1)) with h2 | h2
    · exact h2
    · exfalso
      have heq : gameF (k + 1) (k + 1) = gameF (k + 2) (k + 2) := by omega
      have := diagonal_injective gameRecurrenceModel heq
      omega

end ChompLean

#print axioms ChompLean.noConsecutiveDips_of_noInteriorEaten_forcedCatch
#print axioms ChompLean.twoStepRecordLaw_of_unitDip_noInteriorEaten_forcedCatch
#print axioms ChompLean.not_unitDip_of_noInteriorEaten_forcedCatch_not_recordLaw
#print axioms ChompLean.firstFailure_diagonal_strictly_below_rmax
#print axioms ChompLean.firstFailure_rmax_is_current_diagonal
#print axioms ChompLean.firstFailure_arm_dichotomy
