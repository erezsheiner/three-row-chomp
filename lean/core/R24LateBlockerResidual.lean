import R23FutureOwnerRM2Escape
import R23BlockerFreezeFrontier
import R23TailEscape

set_option autoImplicit false

namespace ChompLean

/-!
R24: after the R22--R23 reductions, RM2 leaves exactly one rescue species:
a row-start/blocker whose freeze column is at or to the right of the
backstop.

This file combines three independently proved facts:

* R22: a missing sub-`u` value is a row start or a future diagonal;
* R23/RM2: the future-diagonal alternative contradicts the two-step record
  law;
* R23/blocker frontier: a row start strictly left of a source is already
  covered by that source.

It also packages the result with the R21 MEX obstruction and with the R23
tail-swap normal form.  Thus the remaining wall is named without hiding any
source loss or diagonal branch: a late blocker undergoing an exact
no-replacement parked swap.
-/

/-- Under RM2, every positive sub-`u` value missing from the final rescue
source is a row-start value whose freeze column is at or to the right of the
backstop. -/
theorem missing_rescue_final_is_late_rowstart_of_two_step_record_law
    (M : RecurrenceModel) {c u z : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hz : 0 < z) (hzu : z < u)
    (hzMissingFinal : Not (B M.f (c + 3) c z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    exists r, c <= r /\ r < z /\ M.f z r = z := by
  rcases missing_final_sub_u_is_rowstart_of_two_step_record_law
      M huSeat hPrevDiagonalAbove hz hzu hzMissingFinal hRM2 with
      ⟨r, hrz, hstart⟩
  have hcr : c <= r :=
    missing_rowstart_forces_freeze_at_or_right
      M (by omega) hrz hstart hzMissingFinal
  exact ⟨r, hcr, hrz, hstart⟩

/-- On the large-value branch `c+3<z`, equality at the frontier is also
impossible: row-start propagation would already place the blocker in the
source.  Hence the freeze column is strictly beyond the backstop. -/
theorem missing_large_rescue_final_is_strictly_late_rowstart_of_rm2
    (M : RecurrenceModel) {c u z : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hz : 0 < z) (hzu : z < u) (htz : c + 3 < z)
    (hzMissingFinal : Not (B M.f (c + 3) c z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    exists r, c < r /\ r < z /\ M.f z r = z := by
  rcases missing_rescue_final_is_late_rowstart_of_two_step_record_law
      M huSeat hPrevDiagonalAbove hz hzu hzMissingFinal hRM2 with
      ⟨r, hcr, hrz, hstart⟩
  have hstrict : c < r := by
    by_cases h : c < r
    · exact h
    · have hrc : r = c := by omega
      subst r
      have hcovered : C M.f (c + 3) c z :=
        rowStartPropagation M hstart hrz (by omega) htz
      exact False.elim (hzMissingFinal (Or.inr hcovered))
  exact ⟨r, hstrict, hrz, hstart⟩

/-- Under RM2, the full R23 tail-escape normal form has only the late
row-start branch.  In particular, a value escaping from `B2` was transient
already at `B2` and suffers an exact no-replacement swap on the tail. -/
theorem rescue_B2_escape_is_exact_late_blocker_of_rm2
    (M : RecurrenceModel) {e L u z : Nat}
    (hL : 2 < L)
    (huSeat : M.f (e + L + 2) (e + L + 1) = u)
    (hPrevDiagonalAbove : u < M.f (e + L + 1) (e + L + 1))
    (hz : 0 < z) (hzu : z < u)
    (hB2 : B M.f (e + L + 3) (e + 2) z)
    (hzMissingBackstop : Not (B M.f (e + L + 3) (e + L) z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    ParkedOnly M.f (e + L + 3) (e + 2) z /\
    (exists k,
      e + 2 <= k /\ k < e + L /\
      B M.f (e + L + 3) k z /\
      Not (B M.f (e + L + 3) (k + 1) z) /\
      ParkedOnly M.f (e + L + 3) k z /\
      Not (k + 1 < e + L + 3 /\ M.f (k + 1) (k + 1) = z) /\
      Not (ColTail M.f (e + L + 3) (k + 1) z) /\
      M.f (e + L + 3) k ≠ z) /\
    (exists r, e + L <= r /\ r < z /\ M.f z r = z) := by
  have hnormal := rescue_B2_escape_normal_form
    M hL huSeat hPrevDiagonalAbove hz hzu hB2 hzMissingBackstop
  refine ⟨hnormal.1, hnormal.2.1, ?_⟩
  have huSeat' : M.f ((e + L) + 2) ((e + L) + 1) = u := by
    simpa [Nat.add_assoc] using huSeat
  have hPrev' : u < M.f ((e + L) + 1) ((e + L) + 1) := by
    simpa [Nat.add_assoc] using hPrevDiagonalAbove
  have hmissing' : Not (B M.f ((e + L) + 3) (e + L) z) := by
    simpa [Nat.add_assoc] using hzMissingBackstop
  have hlate := missing_rescue_final_is_late_rowstart_of_two_step_record_law
    M huSeat' hPrev' hz hzu hmissing' hRM2
  simpa [Nat.add_assoc] using hlate

/-- Consequently RM2 reduces full `B2`-to-backstop preservation to one
honest scheduler input: exclusion of late row starts.  No independent
future-owner hypothesis is needed. -/
theorem rescue_B2_tail_preservation_of_no_late_rowstart_and_rm2
    (M : RecurrenceModel) {e L u : Nat}
    (hL : 2 < L)
    (huSeat : M.f (e + L + 2) (e + L + 1) = u)
    (hPrevDiagonalAbove : u < M.f (e + L + 1) (e + L + 1))
    (hNoLateRowStart :
      forall z, 0 < z -> z < u ->
        Not (exists r, e + L <= r /\ r < z /\ M.f z r = z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    forall z, 0 < z -> z < u ->
      B M.f (e + L + 3) (e + 2) z ->
      B M.f (e + L + 3) (e + L) z := by
  intro z hz hzu hB2
  by_cases hfinal : B M.f (e + L + 3) (e + L) z
  · exact hfinal
  · have hescape := rescue_B2_escape_is_exact_late_blocker_of_rm2
      M hL huSeat hPrevDiagonalAbove hz hzu hB2 hfinal hRM2
    exact False.elim (hNoLateRowStart z hz hzu hescape.2.2)

/-- Exact R21 residual under RM2.  If the persistent value is not served and
is still absent at the backstop, R21 supplies the lower fresh loss (which
does reach the backstop), while R24 proves that the unpaid value is a late
blocker.  This names the sole remaining mixed-pair obstruction. -/
theorem rescue_unserved_missing_backstop_is_lower_loss_plus_late_blocker
    (M : RecurrenceModel) {e L u z : Nat}
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
    (hzMissingBackstop : Not (B M.f (e + L + 3) (e + L) z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    let q := M.f (e + L + 3) (e + 2)
    0 < q /\ q < z /\
      B M.f (e + L + 3) (e + 1) q /\
      Not (B M.f (e + L + 3) (e + 2) q) /\
      B M.f (e + L + 3) (e + L) q /\
      (exists r, e + L <= r /\ r < z /\ M.f z r = z) := by
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
  have hmissing' : Not (B M.f ((e + L) + 3) (e + L) z) := by
    simpa [Nat.add_assoc] using hzMissingBackstop
  have hlate := missing_rescue_final_is_late_rowstart_of_two_step_record_law
    M huSeat' hPrev' hz hzu hmissing' hRM2
  have hlate' : exists r, e + L <= r /\ r < z /\ M.f z r = z := by
    simpa [Nat.add_assoc] using hlate
  exact ⟨hobs.1, hobs.2.1, hobs.2.2.1, hobs.2.2.2,
    hqFinal, hlate'⟩

end ChompLean
