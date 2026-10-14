import R46BoundaryNearMidpointOpeningNormalForm

set_option autoImplicit false

namespace ChompLean

/-!
R47: remove the near-midpoint hypothesis from the late-blocker analysis.

For every boundary `V1` late blocker, independently of the numerical value
of `z-2*r`, there are only two parametric geometries:

* an additional pre-freeze rehost, with the stronger charge `z+2<=2*r`;
* a full low-diagonal corridor, which is short (`r+2<=2*s`) and ends in an
  endpoint, a two-prehost diagonal packet, a row-start packet, a diagonal
  desert, or a strictly smaller late blocker.

The final theorem also removes the boundary assumption.  Every
`DipFirstGapLateBlockerLoss` is either in that boundary normal form or has a
high `V1` and the R27 future-gap/source-gap/boundary-owner packet.  No RM2,
UnitDip, or near-midpoint equality is used.
-/

def BoundaryLateBlockerParametricNormalForm (s : Nat) : Prop :=
  let z := DipFirstGap gameRecurrenceModel s
  DipBoundaryV1SourceNormalForm s /\
  exists b r,
    b < s /\ s + 1 <= r /\ r < z /\
    gameF s b = z /\ gameF z r = z /\
    z - r < r /\
    ((((exists y, s + 1 < y /\ y <= r /\ C gameF y y z) /\
        z + 2 <= r + r)) \/
     ((forall y, s + 1 <= y -> y <= r -> gameF y y < z) /\
      r + 2 <= s + s /\
      (r = s + 1 \/
       BoundaryUnitQueueFutureDiagonalPacket s \/
       BoundaryUnitQueueRowstartPacket s \/
       BoundaryCorridorDiagonalDesert s \/
       BoundaryCorridorSmallerLateBlocker s)))

def LateBlockerHighQGapPacket (s : Nat) : Prop :=
  let z := DipFirstGap gameRecurrenceModel s
  let q := gameF (s + 1) s
  exists b r x,
    b < s /\ s + 1 <= r /\ r < z /\
    gameF s b = z /\ gameF z r = z /\ z <= r + r /\
    s + 1 < q /\ q < z /\
    s + 1 < x /\ x < z /\ Not (C gameF x s z) /\
    (x <= r \/
      Not (B gameF x s z) \/
      exists a, s < a /\ a < x /\ gameF a s = z)

/-- Boundary theorem with a slack-parametric conclusion; no relation such
as `z+1=2*r` is assumed. -/
theorem gameF_boundary_late_blocker_parametric_normal_form
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1) :
    BoundaryLateBlockerParametricNormalForm s := by
  dsimp only [BoundaryLateBlockerParametricNormalForm]
  have hSourceNF :=
    gameF_late_blocker_boundary_v1_exact_source_normal_form
      hLate hboundary
  rcases gameF_late_blocker_boundary_v1_rehost_or_low_diagonal_corridor
      hLate hboundary with
    ⟨b, r, hbs, hrLate, hrz, hpreview, hstart, hstrict, hcase⟩
  have hsub : DipFirstGap gameRecurrenceModel s - r < r := by omega
  refine ⟨hSourceNF, b, r, hbs, hrLate, hrz, hpreview, hstart,
    hsub, ?_⟩
  rcases hcase with hRehost | hCorridor
  · exact Or.inl hRehost
  · have hcap := gameF_boundary_low_diagonal_corridor_capacity
      hLate hboundary hrLate hCorridor
    refine Or.inr ⟨hCorridor, hcap, ?_⟩
    by_cases hendpoint : r = s + 1
    · exact Or.inl hendpoint
    · have hnext : s + 2 <= r := by omega
      rcases gameF_boundary_low_corridor_first_transition_reduction
          hnext hCorridor with hQueue | hDiagonal | hSmaller
      · rcases gameF_boundary_unit_queue_forces_future_diagonal_or_rowstart_packet
          hLate hboundary hQueue with hFuture | hRow
        · exact Or.inr (Or.inl hFuture)
        · exact Or.inr (Or.inr (Or.inl hRow))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hDiagonal)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hSmaller)))

/-- Global late-blocker normal form.  The boundary analysis above and the
high-`q` R27 packet cover every case. -/
theorem gameF_dip_first_gap_late_blocker_parametric_normal_form
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    BoundaryLateBlockerParametricNormalForm s \/
      LateBlockerHighQGapPacket s := by
  let z := DipFirstGap gameRecurrenceModel s
  let q := gameF (s + 1) s
  have hData := hLate
  rcases hData with
    ⟨_hgap, _rData, _hrLateData, _hrzData, _hstartData,
      _hOldCData, hNewMissing⟩
  have hqLower : s < q := by
    have hgt := gameRecurrenceModel.value_gt_index
      (q := s + 1) (r := s) (by omega)
    change s < q at hgt
    exact hgt
  have hqMax : q <= gameF (s + 1) (s + 1) := by
    dsimp [q]
    exact diagonalMaximal gameRecurrenceModel (by omega)
  have hqz : q < z := by
    change q < gameRecurrenceModel.f (s + 1) (s + 1) + 1
    change q <= gameRecurrenceModel.f (s + 1) (s + 1) at hqMax
    omega
  by_cases hboundary : q = s + 1
  · left
    apply gameF_boundary_late_blocker_parametric_normal_form hLate
    simpa [q] using hboundary
  · right
    dsimp only [LateBlockerHighQGapPacket]
    have hhigh : s + 1 < q := by omega
    rcases gameF_dip_first_gap_late_blocker_sharp_coordinates hLate with
      ⟨b, r, hbs, hrLate, hrz, hpreview, hstart,
        _hMissing, _hcap, hhalf, _hcorridor⟩
    have hgapC : Not (C gameF (s + 1) s z) := by
      rintro ⟨c, hcs, hhost⟩
      apply hNewMissing
      right
      exact ⟨c, by omega, hhost⟩
    rcases gameF_future_gap_prefreeze_or_source_gap_or_boundary_owner
        (c := s) (t := s + 1) (q := q) (z := z) (r := r)
        (by omega) rfl hhigh hqz hgapC hrz hstart with
      ⟨x, htx, hxz, hxgap, hxcase⟩
    exact ⟨b, r, x, hbs, hrLate, hrz, hpreview, hstart, hhalf,
      hhigh, hqz, htx, hxz, hxgap, hxcase⟩

end ChompLean
