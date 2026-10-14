import R54EventEThirdDipBoundarySaturation
import R54EventEFourPrefixDiagonalCapacity
import R54EventEFourthEdgeTrichotomy

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R54 integration: close the next-to-maximal defect layer and replace the
four R53 atoms by their exact strengthened terminals.

The genuinely global gain is

  `delta + 6 <= s`.

The third-dip branches get the compressed/boundary certificates.  In the
no-third-dip branch, the strict shared-owner `+9` estimate either leaves no
four-prefix survivor (the deep-quiet terminal), or a survivor is selected
and the fourth edge is propagated exhaustively.
-/

/-- The exact R54 terminal menu.  The last alternative contains a named
four-prefix survivor and the exhaustive propagation across the fourth
edge. -/
def EventENonmaxR54TerminalAtom
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBandHitCompressedCertificate s delta z c b0 \/
  EventEThirdDipBoundarySaturationCertificate s delta z c b0 \/
  EventENonDipDeepQuietTerminalCertificate s delta z c b0 \/
  (EventENonDipStrictSharedOwnerCertificate s delta z c b0 /\
    (exists g, g ∈ EventEFourPrefixBandSlots s delta c b0) /\
    (EventEFourthDipPacketHitCertificate s delta z c b0 \/
     EventEFourthDipExtraForbiddenCertificate s delta z c b0 \/
     EventENoFourthDipFivePrefixSharedOwnerCertificate
       s delta z c b0))

/-- Every nonmaximal Event-E residual has two full units of slack beyond
the maximal defect face.  This combines the third-dip prehost staircase
with the four-prefix diagonal-capacity argument in the no-dip branch. -/
theorem gameF_nonmax_eventE_R54_defect_gap
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    delta + 6 <= s := by
  dsimp only
  have htri := gameF_nonmax_eventE_R53_shared_owner_trichotomy hU hres
  rcases htri with ⟨c, b0, hcross, hHit | hExtra | hNoDip⟩
  · have hcompressed :=
      gameF_nonmax_eventE_third_dip_band_hit_compressed
        hU hres hcross hHit
    exact hcompressed.2.1.1
  · have hsaturated :=
      gameF_nonmax_eventE_third_dip_extra_boundary_saturation
        hU hres hcross hExtra
    exact hsaturated.2.1.1
  · have hstrict :=
      gameF_nonmax_eventE_nondip_strict_shared_owner_saturation
        hU hres hcross hNoDip.1
    exact (gameF_nonmax_eventE_nondip_strict_defect_gap
      hres hcross hstrict).2

/-- Game-level form of the new gap: every Event E under UnitDip, before
choosing any propagated atom, already satisfies `delta+6 <= s`. -/
theorem gameF_margin_eventE_R54_defect_gap
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hEvent : MarginEventECounterexample s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    delta + 6 <= s := by
  dsimp only
  rcases hEvent with ⟨hdip, hmargin, hnextDip⟩
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  have hNotMax : Not (delta + 4 = s) :=
    gameF_margin_eventE_maximal_defect_impossible
      hU hdip hmargin hnextDip
  have hnonmax : delta + 5 <= s := by
    have hupper := hInv.2.1
    omega
  have hcross := gameF_margin_eventE_cross_edge_survivor_bound
    hU hdip hmargin hnextDip
  change exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  have hres : NonmaxMarginEventECrossEdgeResidual s := by
    dsimp only [NonmaxMarginEventECrossEdgeResidual]
    exact ⟨⟨hdip, hmargin, hnextDip⟩, hInv, hnonmax, hcross⟩
  exact gameF_nonmax_eventE_R54_defect_gap hU hres

/-- Explicit closure of the entire next-to-maximal face
`delta+5=s`. -/
theorem gameF_no_margin_eventE_next_to_max_defect
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hEvent : MarginEventECounterexample s) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    Not (delta + 5 = s) := by
  dsimp only
  have hgap := gameF_margin_eventE_R54_defect_gap hU hEvent
  omega

/-- Exhaustive R54 refinement of the R53 four-atom menu. -/
theorem gameF_nonmax_eventE_R54_terminal_reduction
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 /\
      EventENonmaxR54TerminalAtom s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have htri := gameF_nonmax_eventE_R53_shared_owner_trichotomy hU hres
  change exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 /\
      (EventEThirdDipPenultimateHitCertificate s delta z c b0 \/
       EventEThirdDipExtraForbiddenCertificate s delta z c b0 \/
       EventENonDipSharedOwnerSaturationCertificate s delta z c b0)
    at htri
  rcases htri with ⟨c, b0, hcross, hHit | hExtra | hNoDip⟩
  · refine ⟨c, b0, hcross, Or.inl ?_⟩
    exact gameF_nonmax_eventE_third_dip_band_hit_compressed
      hU hres hcross hHit
  · refine ⟨c, b0, hcross, Or.inr (Or.inl ?_)⟩
    exact gameF_nonmax_eventE_third_dip_extra_boundary_saturation
      hU hres hcross hExtra
  · have hstrict :=
      gameF_nonmax_eventE_nondip_strict_shared_owner_saturation
        hU hres hcross hNoDip.1
    change EventENonDipStrictSharedOwnerCertificate
      s delta z c b0 at hstrict
    by_cases hnil : EventEFourPrefixBandSlots s delta c b0 = []
    · have hdeepBound := hstrict.2.2.2
      rw [hnil] at hdeepBound
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hdeepBound
      have hquiet : 2 * delta + 7 <= s := by omega
      have hquietReduction :=
        eventE_nondip_quiet_strict_owner_reduction hstrict hquiet
      rcases hquietReduction with hsurvivor | hdeep
      · rcases hsurvivor with ⟨g, hg⟩
        rw [hnil] at hg
        simp at hg
      · exact ⟨c, b0, hcross, Or.inr (Or.inr (Or.inl hdeep))⟩
    · have hsurvivor :
          exists g, g ∈ EventEFourPrefixBandSlots s delta c b0 :=
        List.exists_mem_of_ne_nil _ hnil
      have hedge := gameF_nonmax_eventE_fourth_edge_trichotomy
        hU hres hcross hstrict.1
      exact ⟨c, b0, hcross,
        Or.inr (Or.inr (Or.inr ⟨hstrict, hsurvivor, hedge⟩))⟩

/-- The strengthened residual used in the exact R54 formulation of RM2
failure. -/
def NonmaxMarginEventER54TerminalResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  NonmaxMarginEventECrossEdgeResidual s /\
  delta + 6 <= s /\
  exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 /\
    EventENonmaxR54TerminalAtom s delta z c b0

/-- Exact R54 reduction: under UnitDip, RM2 failure is equivalent to one
of the strengthened terminal atoms, and the whole next-to-maximal defect
layer has disappeared. -/
theorem gameF_unitDip_not_RM2_iff_R54_terminal_residual
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      exists s, NonmaxMarginEventER54TerminalResidual s := by
  constructor
  · intro hNotRM2
    rcases (gameF_unitDip_not_RM2_iff_R53_nonmax_finite_residual hU).mp
        hNotRM2 with ⟨s, hR53⟩
    have hcrossResidual : NonmaxMarginEventECrossEdgeResidual s := hR53.1
    have hgap := gameF_nonmax_eventE_R54_defect_gap hU hcrossResidual
    have hterminal :=
      gameF_nonmax_eventE_R54_terminal_reduction hU hcrossResidual
    exact ⟨s, hcrossResidual, hgap, hterminal⟩
  · rintro ⟨s, hres⟩
    apply (gameF_unitDip_not_RM2_iff_exists_eventE hU).mpr
    exact ⟨s, hres.1.1⟩

/-- Positive dual of the exact R54 reduction. -/
theorem gameF_unitDip_RM2_iff_no_R54_terminal_residual
    (hU : UnitDip gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel <->
      Not (exists s, NonmaxMarginEventER54TerminalResidual s) := by
  constructor
  · intro hRM2 hResidual
    exact ((gameF_unitDip_not_RM2_iff_R54_terminal_residual hU).mpr
      hResidual) hRM2
  · intro hNoResidual
    apply Classical.byContradiction
    intro hNotRM2
    exact hNoResidual
      ((gameF_unitDip_not_RM2_iff_R54_terminal_residual hU).mp
        hNotRM2)

#print axioms gameF_nonmax_eventE_R54_defect_gap
#print axioms gameF_margin_eventE_R54_defect_gap
#print axioms gameF_no_margin_eventE_next_to_max_defect
#print axioms gameF_nonmax_eventE_R54_terminal_reduction
#print axioms gameF_unitDip_not_RM2_iff_R54_terminal_residual
#print axioms gameF_unitDip_RM2_iff_no_R54_terminal_residual

end ChompLean
