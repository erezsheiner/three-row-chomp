import ChompLean.Proof

set_option autoImplicit false

namespace ChompLean

/-!
Exact source audit for rescue continuations.

The parameter `r` is chosen so that the continuation row is `r+2`:

* previous seat: `f (r+1) r`;
* current seat:  `f (r+2) (r+1)`;
* previous diagonal: `f (r+1) (r+1)`.
-/

/-- A rescue at row `r+1`, written without truncated subtraction. -/
def RescueAfter (f : Nat -> Nat -> Nat) (r : Nat) : Prop :=
  f (r + 1) r < f r r

/-- A rescue continuation at row `r+2`. -/
def RescueContinuation (f : Nat -> Nat -> Nat) (r : Nat) : Prop :=
  RescueAfter f r ∧ RescueAfter f (r + 1) ∧
    f (r + 2) (r + 1) = f (r + 1) r

/-- The low-point rescue is not continued to the following row. -/
def ForwardSingletonRescue (f : Nat -> Nat -> Nat) (r : Nat) : Prop :=
  RescueAfter f r ∧ ¬ RescueAfter f (r + 1)

/-! ## Exact source expansions -/

/-- Source of the preceding `V1(r+1)`. -/
theorem previous_seat_source_expansion
    {f : Nat -> Nat -> Nat} {r z : Nat} :
    B f (r + 1) r z ↔
      (∃ a, a < r + 1 ∧ f a a = z) ∨
      (∃ b, b < r ∧ f (r + 1) b = z) := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · left
      rcases hR with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      have har : a ≤ r := by omega
      simpa [Nat.min_eq_left har] using hfa
    · exact Or.inr hC
  · intro h
    rcases h with hD | hP
    · left
      rcases hD with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      have har : a ≤ r := by omega
      simpa [Nat.min_eq_left har] using hfa
    · exact Or.inr hP

/-- Source of the current `V1(r+2)`. -/
theorem current_seat_source_expansion
    {f : Nat -> Nat -> Nat} {r z : Nat} :
    B f (r + 2) (r + 1) z ↔
      (∃ a, a < r + 2 ∧ f a a = z) ∨
      (∃ b, b < r + 1 ∧ f (r + 2) b = z) := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · left
      rcases hR with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      have har : a ≤ r + 1 := by omega
      simpa [Nat.min_eq_left har] using hfa
    · exact Or.inr hC
  · intro h
    rcases h with hD | hP
    · left
      rcases hD with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      have har : a ≤ r + 1 := by omega
      simpa [Nat.min_eq_left har] using hfa
    · exact Or.inr hP

/-- The diagonal source is the current seat source with the seat adjoined. -/
theorem current_diagonal_source_expansion
    {f : Nat -> Nat -> Nat} {r z : Nat} :
    B f (r + 2) (r + 2) z ↔
      B f (r + 2) (r + 1) z ∨ f (r + 2) (r + 1) = z := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · left
      left
      rcases hR with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      have ha1 : a ≤ r + 1 := by omega
      have ha2 : a ≤ r + 2 := by omega
      simpa [Nat.min_eq_left ha1, Nat.min_eq_left ha2] using hfa
    · rcases hC with ⟨b, hb, hfb⟩
      by_cases hb1 : b < r + 1
      · exact Or.inl (Or.inr ⟨b, hb1, hfb⟩)
      · have hbe : b = r + 1 := by omega
        subst b
        exact Or.inr hfb
  · intro h
    rcases h with hSeat | hLast
    · rcases hSeat with hR | hC
      · left
        rcases hR with ⟨a, ha, hfa⟩
        refine ⟨a, ha, ?_⟩
        have ha1 : a ≤ r + 1 := by omega
        have ha2 : a ≤ r + 2 := by omega
        simpa [Nat.min_eq_left ha1, Nat.min_eq_left ha2] using hfa
      · right
        rcases hC with ⟨b, hb, hfb⟩
        exact ⟨b, by omega, hfb⟩
    · right
      exact ⟨r + 1, by omega, hLast⟩

/-- The preceding diagonal source is the preceding seat source plus its seat. -/
theorem previous_diagonal_source_expansion
    {f : Nat -> Nat -> Nat} {r z : Nat} :
    B f (r + 1) (r + 1) z ↔
      B f (r + 1) r z ∨ f (r + 1) r = z := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · left
      left
      rcases hR with ⟨a, ha, hfa⟩
      refine ⟨a, ha, ?_⟩
      have ha0 : a ≤ r := by omega
      have ha1 : a ≤ r + 1 := by omega
      simpa [Nat.min_eq_left ha0, Nat.min_eq_left ha1] using hfa
    · rcases hC with ⟨b, hb, hfb⟩
      by_cases hb0 : b < r
      · exact Or.inl (Or.inr ⟨b, hb0, hfb⟩)
      · have hbe : b = r := by omega
        subst b
        exact Or.inr hfb
  · intro h
    rcases h with hSeat | hLast
    · rcases hSeat with hR | hC
      · left
        rcases hR with ⟨a, ha, hfa⟩
        refine ⟨a, ha, ?_⟩
        have ha0 : a ≤ r := by omega
        have ha1 : a ≤ r + 1 := by omega
        simpa [Nat.min_eq_left ha0, Nat.min_eq_left ha1] using hfa
      · right
        rcases hC with ⟨b, hb, hfb⟩
        exact ⟨b, by omega, hfb⟩
    · right
      exact ⟨r, by omega, hLast⟩

/-! ## The exact seat-to-diagonal MEX interface -/

/--
The strongest local statement: above the seated value, the diagonal is
exactly the first hole of the `V1` source.  This is an iff, not merely a
sufficient condition.
-/
theorem diagonal_eq_iff_first_seat_source_hole
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f) {r n : Nat}
    (hAboveSeat : M.f (r + 2) (r + 1) < n) :
    M.f (r + 2) (r + 2) = n ↔
      (¬ B M.f (r + 2) (r + 1) n) ∧
      (∀ z, 0 < z -> z < n -> z ≠ M.f (r + 2) (r + 1) ->
        B M.f (r + 2) (r + 1) z) := by
  have hdiagBranch :
      ¬ (r + 2 < r + 2 ∧ M.f (r + 1) (r + 2) < r + 2) := by
    omega
  have hmex := hrec.2 (q := r + 2) (r := r + 2)
    (Nat.le_refl (r + 2)) hdiagBranch
  constructor
  · intro heq
    constructor
    · intro hSeat
      apply hmex.2.1
      rw [heq]
      exact (current_diagonal_source_expansion).2 (Or.inl hSeat)
    · intro z hz0 hzn hzneq
      have hDiag : B M.f (r + 2) (r + 2) z := by
        apply hmex.2.2 z hz0
        rw [heq]
        exact hzn
      rcases (current_diagonal_source_expansion).1 hDiag with hSeat | hlast
      · exact hSeat
      · exact False.elim (hzneq hlast.symm)
  · rintro ⟨hnAbsent, hBelow⟩
    have hnDiagAbsent : ¬ B M.f (r + 2) (r + 2) n := by
      intro hDiag
      rcases (current_diagonal_source_expansion).1 hDiag with hSeat | hlast
      · exact hnAbsent hSeat
      · omega
    have hcandidateCover : ∀ z, 0 < z -> z < n ->
        B M.f (r + 2) (r + 2) z := by
      intro z hz0 hzn
      by_cases hzx : z = M.f (r + 2) (r + 1)
      · exact (current_diagonal_source_expansion).2 (Or.inr hzx.symm)
      · exact (current_diagonal_source_expansion).2
          (Or.inl (hBelow z hz0 hzn hzx))
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hngt
      exact hnDiagAbsent (hmex.2.2 n (by omega) hngt)
    · apply Nat.le_of_not_gt
      intro hvlt
      exact hmex.2.1 (hcandidateCover _ hmex.1 hvlt)

/--
If the current rescue source has retained every old value below `l` except
the seat, the exact obstruction to a `+1` diagonal step is membership of
`l+1` in that source.
-/
theorem rescue_step_plus_one_iff_no_exception
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f) {r : Nat}
    (hrescue : M.f (r + 2) (r + 1) < M.f (r + 1) (r + 1))
    (hlower : ∀ z, 0 < z -> z < M.f (r + 1) (r + 1) ->
      z ≠ M.f (r + 2) (r + 1) -> B M.f (r + 2) (r + 1) z) :
    M.f (r + 2) (r + 2) = M.f (r + 1) (r + 1) + 1 ↔
      ¬ B M.f (r + 2) (r + 1) (M.f (r + 1) (r + 1) + 1) := by
  let x := M.f (r + 2) (r + 1)
  let l := M.f (r + 1) (r + 1)
  have hfirst := diagonal_eq_iff_first_seat_source_hole M hrec
    (r := r) (n := l + 1) (by dsimp [x, l]; omega)
  rw [hfirst]
  constructor
  · intro h
    exact h.1
  · intro habs
    refine ⟨habs, ?_⟩
    intro z hz0 hzlt hzx
    by_cases hzl : z < l
    · exact hlower z hz0 (by simpa [l] using hzl) (by simpa [x] using hzx)
    · have hzeq : z = l := by omega
      subst z
      left
      refine ⟨r + 1, by omega, ?_⟩
      simp [l]

/--
Under the same lower retention, `+2` is characterized by the two adjacent
source bits: `l+1` is present and `l+2` is the next hole.
-/
theorem rescue_step_plus_two_iff_exception_bits
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f) {r : Nat}
    (hrescue : M.f (r + 2) (r + 1) < M.f (r + 1) (r + 1))
    (hlower : ∀ z, 0 < z -> z < M.f (r + 1) (r + 1) ->
      z ≠ M.f (r + 2) (r + 1) -> B M.f (r + 2) (r + 1) z) :
    M.f (r + 2) (r + 2) = M.f (r + 1) (r + 1) + 2 ↔
      B M.f (r + 2) (r + 1) (M.f (r + 1) (r + 1) + 1) ∧
      ¬ B M.f (r + 2) (r + 1) (M.f (r + 1) (r + 1) + 2) := by
  let x := M.f (r + 2) (r + 1)
  let l := M.f (r + 1) (r + 1)
  have hfirst := diagonal_eq_iff_first_seat_source_hole M hrec
    (r := r) (n := l + 2) (by dsimp [x, l]; omega)
  rw [hfirst]
  constructor
  · intro h
    constructor
    · exact h.2 (l + 1) (by omega) (by omega) (by dsimp [x, l]; omega)
    · exact h.1
  · rintro ⟨hplus, habs⟩
    refine ⟨habs, ?_⟩
    intro z hz0 hzlt hzx
    by_cases hzl : z < l
    · exact hlower z hz0 (by simpa [l] using hzl) (by simpa [x] using hzx)
    by_cases hzeq : z = l
    · subst z
      left
      refine ⟨r + 1, by omega, ?_⟩
      simp [l]
    · have hzplus : z = l + 1 := by omega
      simpa [l, hzplus] using hplus

/-! ## Persistence reduces lower coverage to one explicit transport guard -/

/--
For a persistent rescue, preservation of the preceding seat source below the
old diagonal supplies exactly the `hlower` premise above.  This theorem makes
the completion-vs-loss hypothesis explicit.
-/
theorem continuation_step_plus_one_iff
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f) {r : Nat}
    (hcont : RescueContinuation M.f r)
    (htransport : ∀ z, 0 < z -> z < M.f (r + 1) (r + 1) ->
      z ≠ M.f (r + 2) (r + 1) ->
      B M.f (r + 1) r z -> B M.f (r + 2) (r + 1) z) :
    M.f (r + 2) (r + 2) = M.f (r + 1) (r + 1) + 1 ↔
      ¬ B M.f (r + 2) (r + 1) (M.f (r + 1) (r + 1) + 1) := by
  rcases hcont with ⟨_hprevRescue, hcurrentRescue, hpersist⟩
  have hprevDiagBranch :
      ¬ (r + 1 < r + 1 ∧ M.f r (r + 1) < r + 1) := by
    omega
  have hprevDiagMex := hrec.2 (q := r + 1) (r := r + 1)
    (Nat.le_refl (r + 1)) hprevDiagBranch
  apply rescue_step_plus_one_iff_no_exception M hrec hcurrentRescue
  intro z hz0 hzlt hzx
  apply htransport z hz0 hzlt hzx
  have hDiag : B M.f (r + 1) (r + 1) z :=
    hprevDiagMex.2.2 z hz0 hzlt
  rcases (previous_diagonal_source_expansion).1 hDiag with hSeat | hlast
  · exact hSeat
  · exfalso
    apply hzx
    rw [hpersist]
    exact hlast.symm

/-! ## Dip rescue and the exact no-reclaim equivalence -/

/-- A unit dip forces the low-point row to be a rescue. -/
theorem dip_forces_lowpoint_rescue
    (M : RecurrenceModel) {r : Nat}
    (hdip : M.f r r = M.f (r + 1) (r + 1) + 1) :
    RescueAfter M.f r := by
  have hle : M.f (r + 1) r ≤ M.f (r + 1) (r + 1) :=
    diagonalMaximal M (by omega)
  have hne : M.f (r + 1) r ≠ M.f (r + 1) (r + 1) := by
    intro heq
    have hidx : r = r + 1 :=
      M.fixed_q_injective (by omega) (Nat.le_refl (r + 1)) heq
    omega
  dsimp [RescueAfter]
  omega

/-- `not rescue at r+2` is definitionally the no-reclaim inequality. -/
theorem no_reclaim_iff_not_next_rescue
    {f : Nat -> Nat -> Nat} {r : Nat} :
    (¬ RescueAfter f (r + 1)) ↔
      f (r + 1) (r + 1) ≤ f (r + 2) (r + 1) := by
  constructor
  · intro hnot
    have hle : f (r + 1) (r + 1) ≤ f ((r + 1) + 1) (r + 1) :=
      Nat.le_of_not_gt (by simpa [RescueAfter] using hnot)
    simpa [Nat.add_assoc] using hle
  · intro hle hrescue
    have hlt : f (r + 2) (r + 1) < f (r + 1) (r + 1) := by
      simpa [RescueAfter, Nat.add_assoc] using hrescue
    omega

/--
Under a dip, forward singleton rescue is exactly NO-RECLAIM.  A full maximal
singleton chain would additionally require that row `r` itself is not a
rescue; that predecessor condition is not a consequence of the local dip
equation proved here.
-/
theorem dip_singleton_iff_no_reclaim
    (M : RecurrenceModel) {r : Nat}
    (hdip : M.f r r = M.f (r + 1) (r + 1) + 1) :
    ForwardSingletonRescue M.f r ↔
      M.f (r + 1) (r + 1) ≤ M.f (r + 2) (r + 1) := by
  have hrescue := dip_forces_lowpoint_rescue M hdip
  constructor
  · intro hsingle
    exact (no_reclaim_iff_not_next_rescue).1 hsingle.2
  · intro hnoreclaim
    exact ⟨hrescue, (no_reclaim_iff_not_next_rescue).2 hnoreclaim⟩

/--
The exact completion statement behind every singleton rescue: if the next
V1 source already covers all positive values below the current diagonal, the
next row cannot be a rescue.  The cell is automatically on its MEX branch
because its predecessor is the current diagonal.
-/
theorem seat_source_saturation_kills_next_rescue
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f) {s : Nat}
    (hcover : ∀ z, 0 < z -> z < M.f s s -> B M.f (s + 1) s z) :
    M.f s s ≤ M.f (s + 1) s := by
  have hdiag := M.diagonal_gt s
  have hbranch : ¬ (s < s + 1 ∧ M.f s s < s + 1) := by
    omega
  have hmex := hrec.2 (q := s + 1) (r := s) (by omega) hbranch
  apply Nat.le_of_not_gt
  intro hseatLow
  have hpos : 0 < M.f (s + 1) s := by
    have hgt := M.value_gt_index (q := s + 1) (r := s) (by omega)
    omega
  exact hmex.2.1 (hcover (M.f (s + 1) s) hpos hseatLow)

/--
Exact form of the completion-vs-loss race: no rescue on the next row is
equivalent to saturation of the next V1 source below the current diagonal.
-/
theorem no_next_rescue_iff_seat_source_saturated
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f) {s : Nat} :
    M.f s s ≤ M.f (s + 1) s ↔
      (∀ z, 0 < z -> z < M.f s s -> B M.f (s + 1) s z) := by
  have hdiag := M.diagonal_gt s
  have hbranch : ¬ (s < s + 1 ∧ M.f s s < s + 1) := by
    omega
  have hmex := hrec.2 (q := s + 1) (r := s) (by omega) hbranch
  constructor
  · intro hge z hz0 hzl
    exact hmex.2.2 z hz0 (by omega)
  · intro hcover
    exact seat_source_saturation_kills_next_rescue M hrec hcover

end ChompLean
