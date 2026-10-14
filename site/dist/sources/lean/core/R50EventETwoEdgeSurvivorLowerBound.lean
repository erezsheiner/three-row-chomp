import R49EventETwoEdgeTriplePrefix

set_option autoImplicit false

namespace ChompLean

/-!
R50: exact survivor count from the two Event-E missing-edge charges.

Let `M1` be the canonical band values missing from row `s+1`, let `M2` be
the first-edge survivors missing from row `s+2`, and let `T` survive in all
three strict prefixes.  The partition and R49 edge bounds are

`delta = |M1|+|M2|+|T|`,
`2*|M1|+5 <= s`,
`2*|M2|+5 <= s+1`.

Their exact integral consequence is

`delta+5 <= s+|T|`.

Equivalently, `s+t<=delta+5` forces at least `t` triple-prefix survivors.
No additional path or placement assumption is used.
-/

/-- Pure two-edge arithmetic.  The one-row offset between the two bounds
is exactly what makes the integral constant `5` survive after summation. -/
theorem two_edge_missing_partition_survivor_lower_bound
    {s delta m1 m2 t : Nat}
    (hpartition : delta = m1 + m2 + t)
    (hfirst : 2 * m1 + 5 <= s)
    (hsecond : 2 * m2 + 5 <= s + 1) :
    delta + 5 <= s + t := by
  omega

/-- Threshold form: a defect excess of `t` over `s-5` forces `t`
survivors. -/
theorem two_edge_survivor_threshold
    {s delta survivors target : Nat}
    (hlower : delta + 5 <= s + survivors)
    (hthreshold : s + target <= delta + 5) :
    target <= survivors := by
  omega

/-- Honest sharpness audit for the two inequalities alone.  At
`delta=s-5`, their missing capacities can cover the whole band with zero
survivors. -/
theorem two_edge_bounds_allow_zero_survivors_at_defect_s_sub_five
    {s : Nat} (hs : 5 <= s) :
    exists m1 m2,
      s - 5 = m1 + m2 /\
      2 * m1 + 5 <= s /\
      2 * m2 + 5 <= s + 1 := by
  refine ⟨(s - 5) / 2, (s - 5) - (s - 5) / 2, ?_⟩
  omega

/-- Because the Event-E invariant has `delta+4<=s`, the threshold furnished
by the two edge bounds can demand at most one survivor.  Multiple survivors
would require an additional structural/no-reuse input. -/
theorem eventE_defect_range_threshold_at_most_one
    {s delta target : Nat}
    (hdefectRange : delta + 4 <= s)
    (hthreshold : s + target <= delta + 5) :
    target <= 1 := by
  omega

/-- Complete count certificate for the canonical two-edge partition. -/
def EventETwoEdgeSurvivorCountCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventEForcedForbiddenAmortizedCertificate s delta z c b0 /\
    2 * (EventESecondMissingBandSlots s delta c b0).length + 5 <= s + 1 /\
    (EventEDefectBandSlots s delta c b0).length =
      (EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length +
      (EventETriplePrefixBandSlots s delta c b0).length /\
    delta + 5 <=
      s + (EventETriplePrefixBandSlots s delta c b0).length

/-- Exact Event-E survivor lower bound for every permitted defect, not only
the maximal defect. -/
theorem gameF_margin_eventE_two_edge_survivor_lower_bound
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventETwoEdgeSurvivorCountCertificate s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1

  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  rcases hInv with
    ⟨_hdeltaPos, _hdeltaUpper, _hdeltaSum, hzDiag,
      c, b0, b1, _dc, _d0, _d1,
      hc, hb0, hb1, _hcNe, _hbNe, hSucc, hBase, hHost1,
      _hcWindow, _hb0Window, _hb1Window,
      _hdc, _hd0, _hd1, _hcOffset, _hb0Offset, _hb1Offset,
      _hTransitions⟩

  have hfirst := gameF_margin_eventE_forced_forbidden_amortized_bound
    hU hdip hmargin hnextDip
  change exists cf bf,
    EventEForcedForbiddenAmortizedCertificate s delta z cf bf at hfirst
  rcases hfirst with ⟨cf, bf, hfirstCertificate⟩
  have hfirstData := hfirstCertificate
  rcases hfirstData with ⟨hfirstBase, hbound1⟩
  have hbaseData := hfirstBase
  rcases hbaseData with
    ⟨hcf, hbf, _hcfNe, hSuccF, hBaseF,
      hslotsNodupF, hslotsLenF, hslotsPropsF, _hweak⟩
  have hcfEq : cf = c := by
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hcf) (Nat.le_of_lt hc)
      (hSuccF.trans hSucc.symm)
  have hbfEq : bf = b0 := by
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hbf) (Nat.le_of_lt hb0)
      (hBaseF.trans hBase.symm)
  subst cf
  subst bf

  let slots := EventEDefectBandSlots s delta c b0
  let missing1 := EventEMissingBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let missing2 := EventESecondMissingBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  have hslotsNodup : slots.Nodup := hslotsNodupF
  have hslotsLen : slots.length = delta := hslotsLenF
  have hslotsData : forall g, g ∈ slots ->
      g < s /\ gameF s g < z := by
    intro g hg
    have hdata := hslotsPropsF g hg
    have htransition := hdata.2.2.2
    have hLower : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    exact ⟨hdata.1, hLower⟩
  have hunitNext := hU (s + 1) hnextDip
  change gameF (s + 2) (s + 2) + 1 = d at hunitNext
  have hEmit : gameF (s + 2) (s + 2) = z := by omega
  have hbound2 : 2 * missing2.length + 5 <= s + 1 := by
    exact gameF_eventE_second_edge_missing_bound
      hnextDip hHost1 hb1 hEmit hslotsNodup hslotsData

  have hpart1Raw := List.length_eq_countP_add_countP
    (fun g => decide
      (gameF s g ∈ StrictRowPrefixValues gameF (s + 1)))
    (l := slots)
  simp only [List.countP_eq_length_filter] at hpart1Raw
  have hpart1 : slots.length = survivors.length + missing1.length := by
    simpa [survivors, missing1, EventESurvivingBandSlots,
      EventEMissingBandSlots] using hpart1Raw
  have hpart2Raw := List.length_eq_countP_add_countP
    (fun g => decide
      (gameF s g ∈ StrictRowPrefixValues gameF (s + 2)))
    (l := survivors)
  simp only [List.countP_eq_length_filter] at hpart2Raw
  have hpart2 : survivors.length = triple.length + missing2.length := by
    simpa [triple, missing2, EventETriplePrefixBandSlots,
      EventESecondMissingBandSlots] using hpart2Raw
  have hpartition : slots.length =
      missing1.length + missing2.length + triple.length := by
    omega
  have hsurvivorLower : delta + 5 <= s + triple.length := by
    apply two_edge_missing_partition_survivor_lower_bound
      (m1 := missing1.length) (m2 := missing2.length)
    · omega
    · exact hbound1
    · exact hbound2
  refine ⟨c, b0, ?_⟩
  change EventETwoEdgeSurvivorCountCertificate s delta z c b0
  exact ⟨hfirstCertificate, hbound2, hpartition, hsurvivorLower⟩

/-- Sharp threshold specialization: if the defect is large enough that
`s+target<=delta+5`, at least `target` canonical values survive all three
prefixes. -/
theorem gameF_margin_eventE_two_edge_forces_t_survivors
    (hU : UnitDip gameRecurrenceModel) {s target : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    s + target <= delta + 5 ->
      exists c b0,
        EventETwoEdgeSurvivorCountCertificate s delta z c b0 /\
        target <= (EventETriplePrefixBandSlots s delta c b0).length := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hthreshold
  have hcert := gameF_margin_eventE_two_edge_survivor_lower_bound
    hU hdip hmargin hnextDip
  change exists c b0,
    EventETwoEdgeSurvivorCountCertificate s delta z c b0 at hcert
  rcases hcert with ⟨c, b0, hcertificate⟩
  have hlower := hcertificate.2.2.2
  refine ⟨c, b0, hcertificate, ?_⟩
  exact two_edge_survivor_threshold hlower hthreshold

/-- Maximal-defect specialization of the count theorem.  It recovers one
triple-prefix survivor; the existing R49 theorem further extracts a
concrete slot and value from this positivity. -/
theorem gameF_margin_eventE_maximal_defect_has_survivor_count
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    delta + 4 = s ->
      exists c b0,
        EventETwoEdgeSurvivorCountCertificate s delta z c b0 /\
        1 <= (EventETriplePrefixBandSlots s delta c b0).length := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hthreshold := gameF_margin_eventE_two_edge_forces_t_survivors
    (target := 1) hU hdip hmargin hnextDip
  change s + 1 <= delta + 5 ->
      exists c b0,
        EventETwoEdgeSurvivorCountCertificate s delta z c b0 /\
        1 <= (EventETriplePrefixBandSlots s delta c b0).length
    at hthreshold
  change delta + 4 = s at hmax
  have harg : s + 1 <= delta + 5 := by
    calc
      s + 1 = (delta + 4) + 1 := by rw [hmax]
      _ = delta + 5 := by omega
      _ <= delta + 5 := Nat.le_refl _
  exact hthreshold harg

#print axioms two_edge_missing_partition_survivor_lower_bound
#print axioms two_edge_survivor_threshold
#print axioms two_edge_bounds_allow_zero_survivors_at_defect_s_sub_five
#print axioms eventE_defect_range_threshold_at_most_one
#print axioms gameF_margin_eventE_two_edge_survivor_lower_bound
#print axioms gameF_margin_eventE_two_edge_forces_t_survivors
#print axioms gameF_margin_eventE_maximal_defect_has_survivor_count

end ChompLean
