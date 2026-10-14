import R21MexSecondService

set_option autoImplicit false

namespace ChompLean

/-!
R22: the past-range branch of an `L=3` persistent rescue debt is harmless.

Put `e=c*=s-5`, so the current row is `t=s+1=e+6`, the persistent
source is `B(t,e+2)`, and the final diagonal entering at the next source is
`d(s-2)=f(e+3,e+3)`.  If a persistent sub-`u` hole already has a diagonal
owner below `t`, source absence forces that owner to lie after `e+2`.
The `L=3` rescue inequality excludes rows `s-1=e+4` and strict row
maximality excludes `s=e+5`.  Hence the owner is exactly `s-2=e+3`.
-/

/-- General rescue theorem, with no window-length hypothesis.  Put
`c=s-2`.  Every sub-`u` diagonal value whose owner is below the current row
`s+1=c+3` is already in the final source `B(s+1,s-2)`.

Only the two top possible owners need exclusion: `s-1=c+1` is above `u`
by the rescue inequality, and `s=c+2` is strictly above the seated value
`u=V1(s)` by diagonal maximality plus fixed-row injectivity. -/
theorem rescue_sub_u_past_range_final_cover
    (M : RecurrenceModel) {c u z a : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hzu : z < u)
    (haPast : a < c + 3)
    (haOwner : M.f a a = z) :
    B M.f (c + 3) c z := by
  have hCurrentDiagonalAbove : u < M.f (c + 2) (c + 2) := by
    have hle : M.f (c + 2) (c + 1) <= M.f (c + 2) (c + 2) :=
      diagonalMaximal M (by omega)
    have hne : M.f (c + 2) (c + 1) ≠ M.f (c + 2) (c + 2) := by
      intro heq
      have hcols := M.fixed_q_injective (by omega) (Nat.le_refl _) heq
      omega
    rw [huSeat] at hle hne
    omega
  have haNotPrev : a ≠ c + 1 := by
    intro ha
    subst a
    rw [haOwner] at hPrevDiagonalAbove
    omega
  have haNotCurrent : a ≠ c + 2 := by
    intro ha
    subst a
    rw [haOwner] at hCurrentDiagonalAbove
    omega
  have haLe : a <= c := by omega
  left
  exact R_iff_diagPrefix_or_colTail.mpr
    (Or.inl ⟨a, haPast, haLe, haOwner⟩)

/-- Exact residual species after the general past-range theorem.  A positive
sub-`u` value missing from the final rescue source is either represented by
a row-start opening (the blocker species) or has an un-emitted diagonal
owner at or after the current row.  The past-diagonal branch supplied by
`opening_cover` is eliminated by
`rescue_sub_u_past_range_final_cover`. -/
theorem missing_final_sub_u_is_rowstart_or_future_diagonal
    (M : RecurrenceModel) {c u z : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hz : 0 < z) (hzu : z < u)
    (hzMissingFinal : Not (B M.f (c + 3) c z)) :
    (exists r, r < z /\ M.f z r = z) \/
      (exists a, c + 3 <= a /\ a < z /\ M.f a a = z) := by
  rcases M.opening_cover hz with hDiagonal | hRowStart
  · right
    rcases hDiagonal with ⟨a, haz, haOwner⟩
    refine ⟨a, ?_, haz, haOwner⟩
    by_cases haPast : a < c + 3
    · exact False.elim (hzMissingFinal
        (rescue_sub_u_past_range_final_cover
          M huSeat hPrevDiagonalAbove hzu haPast haOwner))
    · omega
  · left
    exact hRowStart

/-- In an `L=3` rescue coordinate, a persistent sub-`u` value with a past
diagonal owner is exactly the final diagonal value. -/
theorem l3_persistent_past_owner_is_final_diagonal
    (M : RecurrenceModel) {e u z a : Nat}
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hzu : z < u)
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (haPast : a < e + 6)
    (haOwner : M.f a a = z) :
    M.f (e + 3) (e + 3) = z := by
  have haAfter : e + 2 < a := by
    by_cases hle : a <= e + 2
    · exfalso
      apply hzMissingTwo
      left
      exact R_iff_diagPrefix_or_colTail.mpr
        (Or.inl ⟨a, haPast, hle, haOwner⟩)
    · omega
  have hCurrentDiagonalAbove : u < M.f (e + 5) (e + 5) := by
    have hle : M.f (e + 5) (e + 4) <= M.f (e + 5) (e + 5) :=
      diagonalMaximal M (by omega)
    have hne : M.f (e + 5) (e + 4) ≠ M.f (e + 5) (e + 5) := by
      intro heq
      have hcols := M.fixed_q_injective (by omega) (Nat.le_refl _) heq
      omega
    rw [huSeat] at hle hne
    omega
  have haNotPrev : a ≠ e + 4 := by
    intro ha
    subst a
    rw [haOwner] at hPrevDiagonalAbove
    omega
  have haNotCurrent : a ≠ e + 5 := by
    intro ha
    subst a
    rw [haOwner] at hCurrentDiagonalAbove
    omega
  have haFinal : a = e + 3 := by omega
  simpa [haFinal] using haOwner

/-- The same owner pin stated as the actual final-source coverage channel. -/
theorem l3_persistent_past_range_enters_final_source
    (M : RecurrenceModel) {e u z a : Nat}
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hzu : z < u)
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (haPast : a < e + 6)
    (haOwner : M.f a a = z) :
    B M.f (e + 6) (e + 3) z := by
  have hfinal := l3_persistent_past_owner_is_final_diagonal
    M huSeat hPrevDiagonalAbove hzu hzMissingTwo haPast haOwner
  left
  exact R_iff_diagPrefix_or_colTail.mpr
    (Or.inl ⟨e + 3, by omega, Nat.le_refl _, hfinal⟩)

/-- Combine the Chomp-specific owner pin with the R21 obstruction.  If the
second post-entry MEX does not serve a persistent past-range debt, R21
produces a lower new loss `q`; nevertheless the final source contains both
`q` (fresh row channel) and `z` (the final diagonal channel). -/
theorem l3_unserved_past_range_pair_closes
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
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + 6) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (hNotServed : M.f (e + 6) (e + 2) ≠ z)
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (haPast : a < e + 6)
    (haOwner : M.f a a = z) :
    let q := M.f (e + 6) (e + 2)
    0 < q /\ q < z /\
      B M.f (e + 6) (e + 1) q /\
      Not (B M.f (e + 6) (e + 2) q) /\
      B M.f (e + 6) (e + 3) q /\
      B M.f (e + 6) (e + 3) z := by
  let q := M.f (e + 6) (e + 2)
  have hobs := unserved_persistent_hole_forces_lower_new_loss
    hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
    hz hzu hzMissingOne hzMissingTwo hNotServed
  have hqFinal : B M.f (e + 6) (e + 3) q := by
    simpa [q, Nat.add_assoc] using
      (fresh_emission_closes_next
        (e := e + 2) (f := M.f) (t := e + 6) (z := q) rfl)
  have hzFinal := l3_persistent_past_range_enters_final_source
    M huSeat hPrevDiagonalAbove hzu hzMissingTwo haPast haOwner
  exact ⟨hobs.1, hobs.2.1, hobs.2.2.1, hobs.2.2.2,
    hqFinal, hzFinal⟩

/-- Window-length-independent version of the mixed-pair closure.  For every
rescue window of length `L>=3`, the R21 lower new loss emitted at `e+2`
persists in the row prefix through the backstop `e+L`, while every sub-`u`
past-range debt is already in that final source by
`rescue_sub_u_past_range_final_cover`. -/
theorem rescue_unserved_past_range_pair_reaches_backstop
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
    (haPast : a < e + L + 3)
    (haOwner : M.f a a = z) :
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
  have haPast' : a < (e + L) + 3 := by
    simpa [Nat.add_assoc] using haPast
  have hzFinal : B M.f ((e + L) + 3) (e + L) z :=
    rescue_sub_u_past_range_final_cover
      M huSeat' hPrev' hzu haPast' haOwner
  have hzFinal' : B M.f (e + L + 3) (e + L) z := by
    simpa [Nat.add_assoc] using hzFinal
  exact ⟨hobs.1, hobs.2.1, hobs.2.2.1, hobs.2.2.2,
    hqFinal, hzFinal'⟩

/-- Full backstop closure for the unserved past-range branch.  R20 bounds
persistent holes by one, the position-one cap bounds new losses by one, R21
names the lower new loss `q`, and the two final channels close `q` and `z`.
No `NO-LOWER-NEW-LOSS` premise is needed in this branch. -/
theorem l3_backstop_of_unserved_past_range
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
    (haPast : a < e + 6)
    (haOwner : M.f a a = z) :
    forall w, 0 < w -> w < u -> B M.f (e + 6) (e + 3) w := by
  let q := M.f (e + 6) (e + 2)
  have hpair := l3_unserved_past_range_pair_closes
    M hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
    hz hzu hzMissingOne hzMissingTwo hNotServed
    huSeat hPrevDiagonalAbove haPast haOwner
  have hq : 0 < q := hpair.1
  have hqz : q < z := hpair.2.1
  have hqu : q < u := Nat.lt_trans hqz hzu
  have hqOne : B M.f (e + 6) (e + 1) q := hpair.2.2.1
  have hqTwo : Not (B M.f (e + 6) (e + 2) q) := hpair.2.2.2.1
  have hqFinal : B M.f (e + 6) (e + 3) q := hpair.2.2.2.2.1
  have hzFinal : B M.f (e + 6) (e + 3) z := hpair.2.2.2.2.2
  have hPersistentSingle := persistent_holes_unique_of_entry_loss_cap_two
    hmexEntry honeEntry hmexOne hEntryLossCapTwo
  intro w hw hwu
  by_cases hwTwo : B M.f (e + 6) (e + 2) w
  · exact hLastSeal w hw hwu hwTwo
  · by_cases hwOne : B M.f (e + 6) (e + 1) w
    · have hwq := hPosOneSingle w q hw hwu hq hqu
        hwOne hwTwo hqOne hqTwo
      simpa [hwq] using hqFinal
    · have hwz := hPersistentSingle w z hw hwu hz hzu
        hwOne hwTwo hzMissingOne hzMissingTwo
      simpa [hwz] using hzFinal

end ChompLean
