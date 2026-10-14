import R189Lag8StrictIntermediateRelayCover
import R159LiveTerminalPredecessorLag3Reduction

set_option autoImplicit false

namespace ChompLean

/-!
# Future-seat containment: recurrence-level core

This file isolates the unconditional part of the proposed terminal-strip
classification.  Let `u` be a row-start blocker, freezing in column `c`, and
let `x<c` be a column which is still live at a terminal row `r<u` and has no
old copy of `u` before that row.  Then exactly the advertised dichotomy is
available:

* either `x` freezes at some row strictly between `r` and `u`; or
* `x` hosts `u` at some row in `[r,u)`.

Writing the latter row as `u-m` gives a future lag-seat with
`0<m<=u-r`.  In particular the endpoint `m=u-r` is included.  No density,
rolling-cover, midpoint, or W4 hypothesis is used here.  The further claim
that only the skipped lags remain is a separate finite rail-exclusion layer.
-/

/-- A physical column is a future seat of `u`, as viewed from row `r`, if it
hosts `u` on one of the rows from `r` through `u-1`. -/
def FutureSeatFrom (u r x : Nat) : Prop :=
  exists a, r <= a /\ a < u /\ gameF a x = u

/-- A column is a near-freeze seat in the terminal strip `(r,u)` if its own
row-start value freezes there. -/
def NearFreezeSeatBetween (u r x : Nat) : Prop :=
  exists w, r < w /\ w < u /\ gameF w x = w

/-- Lag-coordinate form of `FutureSeatFrom`.  The upper endpoint is
inclusive: a host on the terminal row itself has lag `u-r`. -/
def FutureLagSeatFrom (u r x : Nat) : Prop :=
  exists m, 0 < m /\ m <= u - r /\ gameF (u - m) x = u

/-- The six non-affine lag seats at depth at most twenty.  This is the
precise output of the finite rail-exclusion layer; the present file does not
assume the rail identities which establish that layer. -/
def SkippedSeat20 (u x : Nat) : Prop :=
  gameF (u - 3) x = u \/
  gameF (u - 8) x = u \/
  gameF (u - 10) x = u \/
  gameF (u - 13) x = u \/
  gameF (u - 18) x = u \/
  gameF (u - 20) x = u

/-- Interface supplied by the affine rails: at every non-skipped lag at
most twenty, `x` is not the host of `u`. -/
def NoRealizedLagHost20 (u x : Nat) : Prop :=
  forall m, 0 < m -> m <= 20 ->
    m ≠ 3 -> m ≠ 8 -> m ≠ 10 -> m ≠ 13 -> m ≠ 18 -> m ≠ 20 ->
    gameF (u - m) x ≠ u

/-- Realized affine lags up to depth twenty. -/
def RealizedLag20 (m : Nat) : Prop :=
  m = 1 \/ m = 2 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/
  m = 9 \/ m = 11 \/ m = 12 \/ m = 14 \/ m = 15 \/ m = 16 \/
  m = 17 \/ m = 19

/-- The fixed affine rail column serving each realized lag. -/
def realizedRailCol20 : Nat -> Nat
  | 1 => 0
  | 2 => 2
  | 4 => 5
  | 5 => 7
  | 6 => 9
  | 7 => 11
  | 9 => 14
  | 11 => 17
  | 12 => 19
  | 14 => 22
  | 15 => 24
  | 16 => 26
  | 17 => 28
  | 19 => 31
  | _ => 0

/-- Finite L1 interface required by the depth-twenty theorem. -/
def AffineRails20At (u : Nat) : Prop :=
  forall m, RealizedLag20 m ->
    gameF (u - m) (realizedRailCol20 m) = u

/-- Candidate-side exclusion of the stabilized affine rail columns. -/
def AvoidsAffineRail20 (x : Nat) : Prop :=
  forall m, RealizedLag20 m -> x ≠ realizedRailCol20 m

theorem realizedLag20_railCol_le_thirtyOne
    {m : Nat} (hm : RealizedLag20 m) :
    realizedRailCol20 m <= 31 := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- The affine identities plus physical candidate-column exclusion supply
the `NoRealizedLagHost20` interface used above. -/
theorem noRealizedLagHost20_of_affineRails
    {u x : Nat}
    (hu : 51 <= u)
    (hx20 : x <= u - 20)
    (hrails : AffineRails20At u)
    (havoid : AvoidsAffineRail20 x) :
    NoRealizedLagHost20 u x := by
  intro m hmpos hmle hm3 hm8 hm10 hm13 hm18 hm20
  have hmRealized : RealizedLag20 m := by
    unfold RealizedLag20
    omega
  intro hxhost
  have hxrow : x <= u - m := by omega
  have hrailCol : realizedRailCol20 m <= u - m := by
    have h31 := realizedLag20_railCol_le_thirtyOne hmRealized
    omega
  have hxeq : x = realizedRailCol20 m :=
    gameRecurrenceModel.fixed_q_injective
      hxrow hrailCol (hxhost.trans (hrails m hmRealized).symm)
  exact (havoid m hmRealized) hxeq

/-- LAG0 saturation in the exact form needed by the containment theorem.
If `x` is still live below `u` and lies left of the freeze column of `u`,
then the fixed history of `x` already contains `u` before row `u`.

The proof is the short recurrence argument described in the research note:
a live cell on row `u` is a MEX cell above `u`; hence its source contains
`u`.  A same-row occurrence is impossible by row injectivity against the
freeze cell, while a diagonal occurrence is disjoint from a row start.
Thus the occurrence is a literal `ColTail` witness. -/
theorem gameF_lag0_saturation_of_live_left_of_freeze
    {u c x : Nat}
    (hu : 0 < u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hxc : x < c)
    (hlive : ColumnLiveBelow u x) :
    ColTail gameF u x u := by
  have hxu : x < u := by omega
  have hnotCarry :
      Not (x < u /\ gameF (u - 1) x < u) := by
    rintro ⟨_hxu, hprev⟩
    have hxprev : x <= u - 1 := by omega
    have hlow : gameF (u - 1) x <= u - 1 := by omega
    have hrow := gameF_low_cell_has_rowstart hxprev hlow
    exact hlive (gameF (u - 1) x) hrow.1 (by omega) hrow.2
  have hmex : IsMex (B gameF u x) (gameF u x) :=
    gameF_brouwerRecurrence.2 (by omega) hnotCarry
  have hout : u < gameF u x := by
    by_cases hlt : gameF u x < u
    · have hrow := gameF_low_cell_has_rowstart
          (q := u) (c := x) (by omega) (by omega)
      exact False.elim
        (hlive (gameF u x) hrow.1 hlt hrow.2)
    · by_cases heq : gameF u x = u
      · have hxeq : x = c :=
          gameRecurrenceModel.fixed_q_injective
            (by omega) (by omega) (heq.trans hfreeze.symm)
        omega
      · omega
  have hsource : B gameF u x u := hmex.2.2 u hu hout
  rcases hsource with hR | hC
  · exact (gameF_rowstart_R_iff_colTail hcu hfreeze).mp hR
  · rcases hC with ⟨b, hbx, hbhost⟩
    have hbc : b = c :=
      gameRecurrenceModel.fixed_q_injective
        (by omega) (by omega) (hbhost.trans hfreeze.symm)
    omega

/-- Recurrence-level FutureSeatContainment.  A candidate which is alive
through the terminal row and `u`-clear before it is either a future physical
seat of `u`, or a column whose freeze occurs inside the terminal strip. -/
theorem gameF_futureSeatContainment_core
    {u c r x : Nat}
    (hru : r < u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hxc : x < c)
    (haliveAtR : ColumnLiveBelow (r + 1) x)
    (hclearAtR : Not (ColTail gameF r x u)) :
    FutureSeatFrom u r x \/ NearFreezeSeatBetween u r x := by
  by_cases hnear : NearFreezeSeatBetween u r x
  · exact Or.inr hnear
  · left
    have hliveToU : ColumnLiveBelow u x := by
      intro w hxw hwu hwfreeze
      have hrw : r < w := by
        apply Nat.lt_of_not_ge
        intro hwr
        exact haliveAtR w hxw (by omega) hwfreeze
      exact hnear ⟨w, hrw, hwu, hwfreeze⟩
    have htail : ColTail gameF u x u :=
      gameF_lag0_saturation_of_live_left_of_freeze
        (by omega) hcu hfreeze hxc hliveToU
    rcases htail with ⟨a, hau, hxa, hahost⟩
    have hra : r <= a := by
      apply Nat.le_of_not_gt
      intro har
      exact hclearAtR ⟨a, har, hxa, hahost⟩
    exact ⟨a, hra, hau, hahost⟩

/-- The same theorem in lag coordinates.  The `m <= u-r` inequality is
non-strict, which records the endpoint correction forced by the data. -/
theorem gameF_futureLagSeatContainment_core
    {u c r x : Nat}
    (hru : r < u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hxc : x < c)
    (haliveAtR : ColumnLiveBelow (r + 1) x)
    (hclearAtR : Not (ColTail gameF r x u)) :
    FutureLagSeatFrom u r x \/ NearFreezeSeatBetween u r x := by
  rcases gameF_futureSeatContainment_core
      hru hcu hfreeze hxc haliveAtR hclearAtR with hfuture | hfreezeNear
  · left
    rcases hfuture with ⟨a, hra, hau, hahost⟩
    refine ⟨u - a, by omega, by omega, ?_⟩
    have hua : u - (u - a) = a := by omega
    simpa [hua] using hahost
  · exact Or.inr hfreezeNear

/-- Host-row and lag-coordinate versions of a future seat are equivalent. -/
theorem futureSeatFrom_iff_futureLagSeatFrom
    {u r x : Nat} (hru : r < u) :
    FutureSeatFrom u r x <-> FutureLagSeatFrom u r x := by
  constructor
  · rintro ⟨a, hra, hau, hahost⟩
    refine ⟨u - a, by omega, by omega, ?_⟩
    have hua : u - (u - a) = a := by omega
    simpa [hua] using hahost
  · rintro ⟨m, hmpos, hmL, hmhost⟩
    refine ⟨u - m, ?_, by omega, hmhost⟩
    omega

/-- Pure finite part of the ladder reduction.  Once all realized affine
lags have been excluded, a future seat of depth at most twenty is one of the
six skipped seats. -/
theorem futureLagSeatFrom_twenty_of_noRealized_is_skipped
    {u x : Nat}
    (hu : 20 <= u)
    (hfuture : FutureLagSeatFrom u (u - 20) x)
    (hnoRealized : NoRealizedLagHost20 u x) :
    SkippedSeat20 u x := by
  rcases hfuture with ⟨m, hmpos, hm20, hmhost⟩
  have hmle : m <= 20 := by omega
  by_cases hm3 : m = 3
  · left
    simpa [hm3] using hmhost
  by_cases hm8 : m = 8
  · right; left
    simpa [hm8] using hmhost
  by_cases hm10 : m = 10
  · right; right; left
    simpa [hm10] using hmhost
  by_cases hm13 : m = 13
  · right; right; right; left
    simpa [hm13] using hmhost
  by_cases hm18 : m = 18
  · right; right; right; right; left
    simpa [hm18] using hmhost
  by_cases hm20eq : m = 20
  · right; right; right; right; right
    simpa [hm20eq] using hmhost
  exact False.elim
    (hnoRealized m hmpos hmle hm3 hm8 hm10 hm13 hm18 hm20eq hmhost)

/-- Correct depth-twenty containment after exposing the rail interface. -/
theorem gameF_futureSkippedSeat20_or_nearFreeze
    {u c x : Nat}
    (hu : 20 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hxc : x < c)
    (haliveAt20 : ColumnLiveBelow (u - 20 + 1) x)
    (hclearAt20 : Not (ColTail gameF (u - 20) x u))
    (hnoRealized : NoRealizedLagHost20 u x) :
    SkippedSeat20 u x \/ NearFreezeSeatBetween u (u - 20) x := by
  rcases gameF_futureLagSeatContainment_core
      (r := u - 20) (by omega) hcu hfreeze hxc
        haliveAt20 hclearAt20 with hfuture | hnear
  · exact Or.inl
      (futureLagSeatFrom_twenty_of_noRealized_is_skipped
        hu hfuture hnoRealized)
  · exact Or.inr hnear

/-- The exact content of the proposed double-coincidence cascade.  If `x`
hosts `u-5` at its lag eight row and `u-7` at its lag three row, then the
lag-13 and lag-10 seats of `u` are impossible at `x`.  A six-seat
FutureSeat classification therefore leaves precisely lags 3, 8, 18, 20.

This theorem is deliberately honest: it does not delete the lag-3 or lag-8
arms.  Deleting those two arms is exactly the empirical pre-emption atom. -/
theorem skippedSeat20_doubleRelay_reduces_to_3_8_18_20
    {u x : Nat}
    (hu : 20 <= u)
    (hu5 : gameF (u - 13) x = u - 5)
    (hu7 : gameF (u - 10) x = u - 7)
    (hseat : SkippedSeat20 u x) :
    gameF (u - 3) x = u \/
    gameF (u - 8) x = u \/
    gameF (u - 18) x = u \/
    gameF (u - 20) x = u := by
  rcases hseat with h3 | h8 | h10 | h13 | h18 | h20
  · exact Or.inl h3
  · exact Or.inr (Or.inl h8)
  · have hfalse : u = u - 7 := h10.symm.trans hu7
    omega
  · have hfalse : u = u - 5 := h13.symm.trans hu5
    omega
  · exact Or.inr (Or.inr (Or.inl h18))
  · exact Or.inr (Or.inr (Or.inr h20))

/-- Under the same four-seat reduction, excluding the two late landing
arms forces the measured early pre-emption at lag 18 or 20. -/
theorem doubleRelay_early_preemption_of_no_lag3_no_lag8
    {u x : Nat}
    (hu : 20 <= u)
    (hu5 : gameF (u - 13) x = u - 5)
    (hu7 : gameF (u - 10) x = u - 7)
    (hseat : SkippedSeat20 u x)
    (hno3 : gameF (u - 3) x ≠ u)
    (hno8 : gameF (u - 8) x ≠ u) :
    gameF (u - 18) x = u \/ gameF (u - 20) x = u := by
  rcases skippedSeat20_doubleRelay_reduces_to_3_8_18_20
      hu hu5 hu7 hseat with h3 | h8 | h18 | h20
  · exact False.elim (hno3 h3)
  · exact False.elim (hno8 h8)
  · exact Or.inl h18
  · exact Or.inr h20

#print axioms gameF_lag0_saturation_of_live_left_of_freeze
#print axioms gameF_futureSeatContainment_core
#print axioms gameF_futureLagSeatContainment_core
#print axioms futureSeatFrom_iff_futureLagSeatFrom
#print axioms futureLagSeatFrom_twenty_of_noRealized_is_skipped
#print axioms gameF_futureSkippedSeat20_or_nearFreeze
#print axioms skippedSeat20_doubleRelay_reduces_to_3_8_18_20
#print axioms doubleRelay_early_preemption_of_no_lag3_no_lag8
#print axioms realizedLag20_railCol_le_thirtyOne
#print axioms noRealizedLagHost20_of_affineRails

end ChompLean
