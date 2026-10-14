import R22L3PastRangeEscape

set_option autoImplicit false

namespace ChompLean

/-!
R23: the future-diagonal residual in R22 is exactly a two-step record-law
failure.

The rescue inequality puts the old diagonal `d(c+1)` strictly above `u`.
Thus a sub-`u` value `z` cannot have a diagonal owner `a >= c+3` in any
model satisfying the two-step record law: that law would put
`d(c+1) < d(a)=z<u<d(c+1)`.

This does not prove the open two-step record law (`RM2Law`).  It proves a
useful dependency merge: modulo the independently required RM2/ceiling
companion, every sub-`u` diagonal species is already in the final rescue
source, and the only residual species is a row-start/blocker.
-/

/-- Pointwise form of `RM2Law`: every diagonal is larger than every diagonal
at least two rows earlier.  This is equivalent to
`d(a) > max_{i <= a-2} d(i)`, without introducing a running maximum. -/
def TwoStepDiagonalRecordLaw (M : RecurrenceModel) : Prop :=
  forall {i a}, i + 2 <= a -> M.f i i < M.f a a

/-- A future owner of a sub-`u` rescue debt is an explicit witness against
the two-step diagonal record law. -/
theorem future_sub_u_owner_forces_two_step_record_failure
    (M : RecurrenceModel) {c u z a : Nat}
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hzu : z < u)
    (haFuture : c + 3 <= a)
    (haOwner : M.f a a = z) :
    c + 1 + 2 <= a /\ M.f a a < M.f (c + 1) (c + 1) := by
  constructor
  · omega
  · rw [haOwner]
    omega

/-- Under the two-step record law, every sub-`u` diagonal value is already
in the final rescue source, regardless of whether its owner was initially
presented as past or future. -/
theorem rescue_sub_u_diagonal_final_cover_of_two_step_record_law
    (M : RecurrenceModel) {c u z a : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hzu : z < u)
    (haOwner : M.f a a = z)
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    B M.f (c + 3) c z := by
  by_cases haPast : a < c + 3
  · exact rescue_sub_u_past_range_final_cover
      M huSeat hPrevDiagonalAbove hzu haPast haOwner
  · have haFuture : c + 3 <= a := by omega
    have hfailure := future_sub_u_owner_forces_two_step_record_failure
      M hPrevDiagonalAbove hzu haFuture haOwner
    have hrecord := hRM2 hfailure.1
    omega

/-- R22's row-start/future-owner dichotomy sharpens to a row-start/RM2-
failure dichotomy.  In the second branch the future owner itself and the
older diagonal `c+1` are the complete failure certificate. -/
theorem missing_final_sub_u_is_rowstart_or_two_step_record_failure
    (M : RecurrenceModel) {c u z : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hz : 0 < z) (hzu : z < u)
    (hzMissingFinal : Not (B M.f (c + 3) c z)) :
    (exists r, r < z /\ M.f z r = z) \/
      (exists a,
        c + 3 <= a /\ a < z /\ M.f a a = z /\
          M.f a a < M.f (c + 1) (c + 1)) := by
  rcases missing_final_sub_u_is_rowstart_or_future_diagonal
      M huSeat hPrevDiagonalAbove hz hzu hzMissingFinal with
      hRowStart | hFuture
  · exact Or.inl hRowStart
  · right
    rcases hFuture with ⟨a, haFuture, haz, haOwner⟩
    have hfailure := future_sub_u_owner_forces_two_step_record_failure
      M hPrevDiagonalAbove hzu haFuture haOwner
    exact ⟨a, haFuture, haz, haOwner, hfailure.2⟩

/-- Consequently, under `RM2Law`, a positive sub-`u` value missing from the
final rescue source must be a row-start/blocker value. -/
theorem missing_final_sub_u_is_rowstart_of_two_step_record_law
    (M : RecurrenceModel) {c u z : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hz : 0 < z) (hzu : z < u)
    (hzMissingFinal : Not (B M.f (c + 3) c z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    exists r, r < z /\ M.f z r = z := by
  rcases missing_final_sub_u_is_rowstart_or_two_step_record_failure
      M huSeat hPrevDiagonalAbove hz hzu hzMissingFinal with
      hRowStart | hFailure
  · exact hRowStart
  · rcases hFailure with ⟨a, haFuture, _haz, _haOwner, hdrop⟩
    have hrecord : M.f (c + 1) (c + 1) < M.f a a :=
      hRM2 (by omega)
    omega

/-- R21 mixed-pair transport with the future-owner branch removed by RM2.
For every rescue length `L>=3`, if the persistent value is any diagonal
value (past or nominally future), both it and R21's lower new loss reach the
backstop. -/
theorem rescue_unserved_diagonal_pair_reaches_backstop_of_two_step_record_law
    (M : RecurrenceModel) {e L u z a : Nat}
    (hL : 3 <= L)
    (hmexEntry :
      IsMex (B M.f (e + L + 3) e) (M.f (e + L + 3) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f (e + L + 3) e y) ->
        Not (B M.f (e + L + 3) e z) -> y = z)
    (hmexOne :
      IsMex (B M.f (e + L + 3) (e + 1))
        (M.f (e + L + 3) (e + 1)))
    (hmexTwo :
      IsMex (B M.f (e + L + 3) (e + 2))
        (M.f (e + L + 3) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + L + 3) e x ->
          Not (B M.f (e + L + 3) (e + 1) x) ->
        B M.f (e + L + 3) e y ->
          Not (B M.f (e + L + 3) (e + 1) y) ->
        B M.f (e + L + 3) e z ->
          Not (B M.f (e + L + 3) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + L + 3) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + L + 3) (e + 2) z))
    (hNotServed : M.f (e + L + 3) (e + 2) ≠ z)
    (huSeat : M.f (e + L + 2) (e + L + 1) = u)
    (hPrevDiagonalAbove : u < M.f (e + L + 1) (e + L + 1))
    (haOwner : M.f a a = z)
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    let q := M.f (e + L + 3) (e + 2)
    0 < q /\ q < z /\
      B M.f (e + L + 3) (e + 1) q /\
      Not (B M.f (e + L + 3) (e + 2) q) /\
      B M.f (e + L + 3) (e + L) q /\
      B M.f (e + L + 3) (e + L) z := by
  let q := M.f (e + L + 3) (e + 2)
  have hobs := unserved_persistent_hole_forces_lower_new_loss
    hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
    hz hzu hzMissingOne hzMissingTwo hNotServed
  have hqFinal : B M.f (e + L + 3) (e + L) q := by
    exact fresh_emission_persists_in_all_later_sources
      (f := M.f) (t := e + L + 3) (e := e + 2) (z := q) rfl (by omega)
  have huSeat' : M.f ((e + L) + 2) ((e + L) + 1) = u := by
    simpa [Nat.add_assoc] using huSeat
  have hPrev' : u < M.f ((e + L) + 1) ((e + L) + 1) := by
    simpa [Nat.add_assoc] using hPrevDiagonalAbove
  have hzFinal : B M.f ((e + L) + 3) (e + L) z :=
    rescue_sub_u_diagonal_final_cover_of_two_step_record_law
      M huSeat' hPrev' hzu haOwner hRM2
  have hzFinal' : B M.f (e + L + 3) (e + L) z := by
    simpa [Nat.add_assoc] using hzFinal
  exact ⟨hobs.1, hobs.2.1, hobs.2.2.1, hobs.2.2.2,
    hqFinal, hzFinal'⟩

/-- Full `L=3` backstop closure for every diagonal persistent value under
RM2.  The RM2 law first rules out a future owner; R22 then supplies the full
past-range closure using the two capacity bounds and the last-edge seal. -/
theorem l3_backstop_of_unserved_diagonal_of_two_step_record_law
    (M : RecurrenceModel) {e u z a : Nat}
    (hmexEntry : IsMex (B M.f (e + 6) e) (M.f (e + 6) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f (e + 6) e y) -> Not (B M.f (e + 6) e z) -> y = z)
    (hmexOne : IsMex (B M.f (e + 6) (e + 1)) (M.f (e + 6) (e + 1)))
    (hmexTwo : IsMex (B M.f (e + 6) (e + 2)) (M.f (e + 6) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + 6) e x -> Not (B M.f (e + 6) (e + 1) x) ->
        B M.f (e + 6) e y -> Not (B M.f (e + 6) (e + 1) y) ->
        B M.f (e + 6) e z -> Not (B M.f (e + 6) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hPosOneSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + 6) (e + 1) y -> Not (B M.f (e + 6) (e + 2) y) ->
        B M.f (e + 6) (e + 1) z -> Not (B M.f (e + 6) (e + 2) z) -> y = z)
    (hLastSeal :
      forall w, 0 < w -> w < u ->
        B M.f (e + 6) (e + 2) w -> B M.f (e + 6) (e + 3) w)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + 6) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (hNotServed : M.f (e + 6) (e + 2) ≠ z)
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (haOwner : M.f a a = z)
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    forall w, 0 < w -> w < u -> B M.f (e + 6) (e + 3) w := by
  have haPast : a < e + 6 := by
    by_cases h : a < e + 6
    · exact h
    · have hfuture : e + 6 <= a := Nat.le_of_not_gt h
      have hrecord : M.f (e + 4) (e + 4) < M.f a a :=
        hRM2 (by omega)
      rw [haOwner] at hrecord
      omega
  exact l3_backstop_of_unserved_past_range
    M hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
    hPosOneSingle hLastSeal hz hzu hzMissingOne hzMissingTwo
    hNotServed huSeat hPrevDiagonalAbove haPast haOwner

end ChompLean
