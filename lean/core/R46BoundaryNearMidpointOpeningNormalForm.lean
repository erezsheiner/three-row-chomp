import R45BoundaryUnitQueueOpeningPacket

set_option autoImplicit false

namespace ChompLean

/-!
R46: remove the opaque `UnitQueue` alternative from the near-midpoint
late-blocker corridor.  R44 leaves an endpoint, a unit queue, a diagonal
desert, or a smaller late blocker.  R45 opens the queue into either a future
diagonal two-prehost packet or a row-start packet with its sharp charge.
-/

/-- Final opening-aware normal form for the current near-midpoint corridor. -/
theorem gameF_boundary_v1_near_midpoint_opening_normal_form
    {s r : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1)
    (hrLate : s + 1 <= r)
    (hrz : r < DipFirstGap gameRecurrenceModel s)
    (hstart : gameF (DipFirstGap gameRecurrenceModel s) r =
      DipFirstGap gameRecurrenceModel s)
    (hnear : DipFirstGap gameRecurrenceModel s + 1 = r + r) :
    r + 2 <= s + s ∧
    (forall y, s + 1 <= y -> y <= r ->
      gameF y y < DipFirstGap gameRecurrenceModel s) ∧
    (r = s + 1 ∨
      BoundaryUnitQueueFutureDiagonalPacket s ∨
      BoundaryUnitQueueRowstartPacket s ∨
      BoundaryCorridorDiagonalDesert s ∨
      BoundaryCorridorSmallerLateBlocker s) := by
  rcases gameF_boundary_v1_near_midpoint_short_triangle_reduction
      hLate hboundary hrLate hrz hstart hnear with
    ⟨hbound, hcorridor, hcase⟩
  refine ⟨hbound, hcorridor, ?_⟩
  rcases hcase with hendpoint | hqueue | hdesert | hsmaller
  · exact Or.inl hendpoint
  · rcases gameF_boundary_unit_queue_forces_future_diagonal_or_rowstart_packet
        hLate hboundary hqueue with hfuture | hrow
    · exact Or.inr (Or.inl hfuture)
    · exact Or.inr (Or.inr (Or.inl hrow))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hdesert)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hsmaller)))

#print axioms gameF_boundary_v1_near_midpoint_opening_normal_form

end ChompLean
