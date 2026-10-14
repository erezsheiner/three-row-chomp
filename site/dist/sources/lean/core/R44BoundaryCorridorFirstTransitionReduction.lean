import R43BoundaryLowCorridorCapacity
import R40FutureDiagonalPrehostCharge

set_option autoImplicit false

namespace ChompLean

/-!
R44: reduce the first transition of the short boundary corridor.

R43 says a nontrivial low corridor begins with a genuine dip at row `s+1`.
The four R33 outcomes are sharpened here as follows.

* A unit first step has an exact two-MEX queue normal form at the new `V1`.
* Either diagonal first-gap branch becomes a future-diagonal prehost episode
  with a concrete no-repeat column desert.
* The late-blocker branch is a strict descent to a smaller blocker value and
  inherits R37's half-freeze charge.

Thus the near-midpoint triangle is reduced to an endpoint or three smaller
local atoms.  No RM2 or UnitDip is assumed.
-/

/-- Exact queue normal form left by a unit first transition. -/
def BoundaryCorridorUnitQueue (s : Nat) : Prop :=
  let u := s + 1
  let q := gameF (u + 1) u
  let d := gameF (u + 1) (u + 1)
  d + 1 = gameF u u /\
  IsMex (B gameF (u + 1) u) q /\
  q < d /\
  (forall v, 0 < v -> v < d ->
    (B gameF (u + 1) u v <-> v ≠ q))

/-- Both diagonal branches are merged into one actual-game chronology atom:
a future owner, an old host, and a lower column which cannot carry the value
again before that owner.  The charged value is strictly below the original
first-gap blocker. -/
def BoundaryCorridorDiagonalDesert (s : Nat) : Prop :=
  exists q a x b,
    q < a /\ b < q /\ gameF q b = x /\
    (forall t, q < t -> t < a -> gameF t b ≠ x) /\
    x < DipFirstGap gameRecurrenceModel s

/-- The late branch is a strict descent to the next row's smaller first-gap
blocker, together with its R37 coordinates and charge. -/
def BoundaryCorridorSmallerLateBlocker (s : Nat) : Prop :=
  let w := DipFirstGap gameRecurrenceModel (s + 1)
  DipFirstGapLateBlockerLoss gameRecurrenceModel (s + 1) /\
  w < DipFirstGap gameRecurrenceModel s /\
  exists b r,
    b < s + 1 /\ s + 2 <= r /\ r < w /\
    gameF (s + 1) b = w /\ gameF w r = w /\
    w <= r + r

/-- A unit dip followed by the diagonal cell has the exact one-hole queue
normal form displayed above. -/
theorem gameF_unit_first_transition_has_queue_normal_form
    {s : Nat}
    (hunit : gameF (s + 2) (s + 2) + 1 =
      gameF (s + 1) (s + 1)) :
    BoundaryCorridorUnitQueue s := by
  dsimp only [BoundaryCorridorUnitQueue]
  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  let q := gameF (s + 2) (s + 1)
  let d := gameF (s + 2) (s + 2)
  have hprevHigh : s + 1 < gameF (s + 1) (s + 1) :=
    gameRecurrenceModel.diagonal_gt (s + 1)
  have hnotCarry :
      Not (s + 1 < s + 2 /\ gameF (s + 1) (s + 1) < s + 2) := by
    omega
  have hmexQ : IsMex (B gameF (s + 2) (s + 1)) q := by
    dsimp [q]
    exact hrec.2 (by omega) hnotCarry
  have hmexD : IsMex (B gameF (s + 2) (s + 2)) d := by
    dsimp [d]
    exact recurrence_diagonal_exact_mex gameRecurrenceModel (s + 2)
  have hqLe : q <= d := by
    dsimp [q, d]
    exact diagonalMaximal gameRecurrenceModel (by omega)
  have hqNe : q ≠ d := by
    intro hEq
    have hcols := gameRecurrenceModel.fixed_q_injective
      (q := s + 2) (b₁ := s + 1) (b₂ := s + 2)
      (by omega) (Nat.le_refl _) hEq
    omega
  have hqd : q < d := by omega
  have hsource : forall v, 0 < v -> v < d ->
      (B gameF (s + 2) (s + 1) v <-> v ≠ q) := by
    intro v hvPos hvd
    constructor
    · intro hB hvq
      subst v
      exact hmexQ.2.1 hB
    · intro hvq
      have hBDiag : B gameF (s + 2) (s + 2) v :=
        hmexD.2.2 v hvPos hvd
      rcases (previous_diagonal_source
          (f := gameF) (r := s + 1) (p := v)).1 hBDiag with hB | hlast
      · exact hB
      · have hEq : q = v := by simpa [q] using hlast
        exact False.elim (hvq hEq.symm)
  exact ⟨hunit, hmexQ, hqd, hsource⟩

/-- A diagonal first-transition branch has a strict-below prehost desert. -/
theorem gameF_boundary_corridor_diagonal_branch_has_smaller_desert
    {s r : Nat}
    (hnext : s + 2 <= r)
    (hcorridor : forall y, s + 1 <= y -> y <= r ->
      gameF y y < DipFirstGap gameRecurrenceModel s)
    (hDiagonal :
      DipFirstGapPastDiagonal gameRecurrenceModel (s + 1) \/
      DipFirstGapFutureDiagonalLoss gameRecurrenceModel (s + 1)) :
    BoundaryCorridorDiagonalDesert s := by
  rcases hDiagonal with hPast | hFuture
  · rcases past_first_gap_forces_predecessor_future_prehost_loss
      gameRecurrenceModel hPast with ⟨q, _hqs, _hqOwner, hloss⟩
    rcases game_futureDiagonalPrehost_has_column_desert hloss with
      ⟨b, hbq, hhost, hdesert⟩
    have hxlt := hcorridor (s + 2) (by omega) hnext
    exact ⟨q, s + 2, gameF (s + 2) (s + 2), b,
      hloss.1, hbq, hhost, hdesert, hxlt⟩
  · rcases future_first_gap_is_future_prehost_loss
      gameRecurrenceModel hFuture with ⟨a, _ha, hloss⟩
    rcases game_futureDiagonalPrehost_has_column_desert hloss with
      ⟨b, hbq, hhost, hdesert⟩
    have hxlt : DipFirstGap gameRecurrenceModel (s + 1) <
        DipFirstGap gameRecurrenceModel s := by
      have hgap := hFuture.1
      dsimp [DipFirstGap] at hgap ⊢
      omega
    exact ⟨s + 1, a, DipFirstGap gameRecurrenceModel (s + 1), b,
      hloss.1, hbq, hhost, hdesert, hxlt⟩

/-- The late first-transition branch descends to a strictly smaller blocker
and inherits the full R37 coordinate package. -/
theorem gameF_boundary_corridor_late_branch_is_strict_descent
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel (s + 1)) :
    BoundaryCorridorSmallerLateBlocker s := by
  dsimp only [BoundaryCorridorSmallerLateBlocker]
  have hwz : DipFirstGap gameRecurrenceModel (s + 1) <
      DipFirstGap gameRecurrenceModel s := by
    have hgap := hLate.1
    dsimp [DipFirstGap] at hgap ⊢
    omega
  rcases gameF_dip_first_gap_late_blocker_sharp_coordinates hLate with
    ⟨b, r, hbs, hrLate, hrw, hpreview, hstart,
      _hMissing, _hcap, hhalf, _hcorridor⟩
  exact ⟨hLate, hwz, b, r, hbs, hrLate, hrw,
    hpreview, hstart, hhalf⟩

/-- Three-atom reduction of every nontrivial boundary corridor. -/
theorem gameF_boundary_low_corridor_first_transition_reduction
    {s r : Nat}
    (hnext : s + 2 <= r)
    (hcorridor : forall y, s + 1 <= y -> y <= r ->
      gameF y y < DipFirstGap gameRecurrenceModel s) :
    BoundaryCorridorUnitQueue s \/
      BoundaryCorridorDiagonalDesert s \/
      BoundaryCorridorSmallerLateBlocker s := by
  rcases gameF_boundary_low_corridor_first_transition
      hnext hcorridor with ⟨_hdip, hcase⟩
  rcases hcase with hunit | hPast | hFuture | hLate
  · exact Or.inl (gameF_unit_first_transition_has_queue_normal_form hunit)
  · exact Or.inr (Or.inl
      (gameF_boundary_corridor_diagonal_branch_has_smaller_desert
        hnext hcorridor (Or.inl hPast)))
  · exact Or.inr (Or.inl
      (gameF_boundary_corridor_diagonal_branch_has_smaller_desert
        hnext hcorridor (Or.inr hFuture)))
  · exact Or.inr (Or.inr
      (gameF_boundary_corridor_late_branch_is_strict_descent hLate))

/-- Final near-midpoint normal form: a bounded endpoint, an exact unit
queue, a smaller diagonal desert, or a strictly smaller late blocker. -/
theorem gameF_boundary_v1_near_midpoint_short_triangle_reduction
    {s r : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1)
    (hrLate : s + 1 <= r)
    (hrz : r < DipFirstGap gameRecurrenceModel s)
    (hstart : gameF (DipFirstGap gameRecurrenceModel s) r =
      DipFirstGap gameRecurrenceModel s)
    (hnear : DipFirstGap gameRecurrenceModel s + 1 = r + r) :
    r + 2 <= s + s /\
    (forall y, s + 1 <= y -> y <= r ->
      gameF y y < DipFirstGap gameRecurrenceModel s) /\
    (r = s + 1 \/
      BoundaryCorridorUnitQueue s \/
      BoundaryCorridorDiagonalDesert s \/
      BoundaryCorridorSmallerLateBlocker s) := by
  have hshort := gameF_boundary_v1_near_midpoint_forces_short_low_corridor
    hLate hboundary hrLate hrz hstart hnear
  refine ⟨hshort.1, hshort.2, ?_⟩
  by_cases hendpoint : r = s + 1
  · exact Or.inl hendpoint
  · have hnext : s + 2 <= r := by omega
    rcases gameF_boundary_low_corridor_first_transition_reduction
        hnext hshort.2 with hunit | hdiag | hlate
    · exact Or.inr (Or.inl hunit)
    · exact Or.inr (Or.inr (Or.inl hdiag))
    · exact Or.inr (Or.inr (Or.inr hlate))

end ChompLean
