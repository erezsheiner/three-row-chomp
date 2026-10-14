import R48EventEAmortizedMissingBand
import R49EventEForcedForbiddenAmortization

set_option autoImplicit false

namespace ChompLean

/-!
R49: use both consecutive dips of event E.

The canonical defect band is first partitioned into values missing from row
`s+1` and values surviving there.  The surviving values are then partitioned
into values missing from row `s+2` and values surviving in all three strict
prefixes.  Adding the old `z+1` packet to the first forbidden family and the
old `z` packet to the second sharpens the two amortized bounds to

`2*|M1|+5 <= s` and `2*|M2|+5 <= s+1`.

At maximal defect `delta+4=s`, the two missing families cannot cover all
`delta` band slots.  Hence a concrete lower value occurs in the strict
prefixes of rows `s`, `s+1`, and `s+2`.
-/

noncomputable def EventESurvivingBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventEDefectBandSlots s delta c b0).filter (fun g =>
    decide (gameF s g ∈ StrictRowPrefixValues gameF (s + 1)))

noncomputable def EventESecondMissingBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventESurvivingBandSlots s delta c b0).filter (fun g =>
    !(decide (gameF s g ∈ StrictRowPrefixValues gameF (s + 2))))

noncomputable def EventETriplePrefixBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventESurvivingBandSlots s delta c b0).filter (fun g =>
    decide (gameF s g ∈ StrictRowPrefixValues gameF (s + 2)))

private theorem r49_nodup_map_of_injective_on
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) (xs : List alpha)
    (hxs : xs.Nodup)
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.map_cons]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hay⟩
        have hay' : a = y :=
          hinj a (by simp) y (by simp [hy]) hay.symm
        subst y
        exact hxs.1 hy
      · apply ih hxs.2
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

/-- A diagonal value is absent from its own strict row prefix. -/
theorem diagonal_value_absent_strict_prefix
    (M : RecurrenceModel) (q : Nat) :
    M.f q q ∉ StrictRowPrefixValues M.f q := by
  intro hmem
  rcases mem_strictRowPrefixValues_iff_C.mp hmem with ⟨b, hb, hvalue⟩
  have hcols := M.fixed_q_injective
    (q := q) (b₁ := b) (b₂ := q)
    (Nat.le_of_lt hb) (Nat.le_refl _) hvalue
  omega

/-- First-edge sharpening.  The missing band values plus the always-missing
old packet value `z+1` form the forbidden family. -/
theorem gameF_eventE_first_edge_missing_bound
    {s delta z c b0 : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hc : c < s)
    (hSucc : gameF s c = z + 1)
    (hNextDiag : gameF (s + 1) (s + 1) = z + 1)
    (hslotsNodup : (EventEDefectBandSlots s delta c b0).Nodup)
    (hslotsData : ∀ g, g ∈ EventEDefectBandSlots s delta c b0 →
      g < s ∧ gameF s g < z) :
    2 * (EventEMissingBandSlots s delta c b0).length + 5 ≤ s := by
  let slots := EventEDefectBandSlots s delta c b0
  let missing := EventEMissingBandSlots s delta c b0
  let missingValues := missing.map (fun g => gameF s g)
  let forbidden := missingValues ++ [z + 1]
  have hmissingNodup : missing.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hmissingValuesNodup : missingValues.Nodup := by
    apply r49_nodup_map_of_injective_on (fun g => gameF s g)
      missing hmissingNodup
    intro g hg k hk heq
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hk).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) heq
  have hspecialDisjoint : ∀ v, v ∈ missingValues →
      ∀ w, w ∈ [z + 1] → v ≠ w := by
    intro v hv w hw heq
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hgz := (hslotsData g hgSlots).2
    omega
  have hforbiddenNodup : forbidden.Nodup := by
    exact List.nodup_append.mpr
      ⟨hmissingValuesNodup, by simp, hspecialDisjoint⟩
  have hforbiddenSub : forbidden ⊆ StrictRowPrefixValues gameF s := by
    intro v hv
    rcases List.mem_append.mp hv with hvMissing | hvSpecial
    · rcases List.mem_map.mp hvMissing with ⟨g, hg, rfl⟩
      have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
      exact List.mem_map.mpr
        ⟨g, List.mem_range.mpr (hslotsData g hgSlots).1, rfl⟩
    · simp only [List.mem_singleton] at hvSpecial
      subst v
      exact List.mem_map.mpr
        ⟨c, List.mem_range.mpr hc, hSucc⟩
  have hforbiddenMissing : ∀ v, v ∈ forbidden →
      v ∉ StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvMissing | hvSpecial
    · rcases List.mem_map.mp hvMissing with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing, EventEMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvSpecial
      subst v
      rw [← hNextDiag]
      exact diagonal_value_absent_strict_prefix gameRecurrenceModel (s + 1)
  have hbound := game_adjacent_dip_forbidden_upper_half_bound
    hdip hforbiddenNodup hforbiddenSub hforbiddenMissing
  have hlen : forbidden.length = missing.length + 1 := by
    simp [forbidden, missingValues]
  change 2 * missing.length + 5 ≤ s
  omega

/-- Second-edge sharpening.  Among the first-edge survivors, take those
missing from row `s+2` and add the always-missing old packet value `z`. -/
theorem gameF_eventE_second_edge_missing_bound
    {s delta z c b0 b1 : Nat}
    (hnextDip : gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1))
    (hHost1 : gameF (s + 1) b1 = z)
    (hb1 : b1 < s + 1)
    (hEmit : gameF (s + 2) (s + 2) = z)
    (hslotsNodup : (EventEDefectBandSlots s delta c b0).Nodup)
    (hslotsData : ∀ g, g ∈ EventEDefectBandSlots s delta c b0 →
      g < s ∧ gameF s g < z) :
    2 * (EventESecondMissingBandSlots s delta c b0).length + 5 ≤ s + 1 := by
  let slots := EventEDefectBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let missing2 := EventESecondMissingBandSlots s delta c b0
  let missingValues := missing2.map (fun g => gameF s g)
  let forbidden := missingValues ++ [z]
  have hsurvivorsNodup : survivors.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hmissingNodup : missing2.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hmissingValuesNodup : missingValues.Nodup := by
    apply r49_nodup_map_of_injective_on (fun g => gameF s g)
      missing2 hmissingNodup
    intro g hg k hk heq
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hkSurv : k ∈ survivors := (List.mem_filter.mp hk).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) heq
  have hspecialDisjoint : ∀ v, v ∈ missingValues →
      ∀ w, w ∈ [z] → v ≠ w := by
    intro v hv w hw
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    exact Nat.ne_of_lt (hslotsData g hgSlots).2
  have hforbiddenNodup : forbidden.Nodup := by
    exact List.nodup_append.mpr
      ⟨hmissingValuesNodup, by simp, hspecialDisjoint⟩
  have hforbiddenSub : forbidden ⊆
      StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvMissing | hvSpecial
    · rcases List.mem_map.mp hvMissing with ⟨g, hg, rfl⟩
      have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
      have hfilter := (List.mem_filter.mp hgSurv).2
      simpa [survivors, EventESurvivingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvSpecial
      subst v
      exact List.mem_map.mpr
        ⟨b1, List.mem_range.mpr hb1, hHost1⟩
  have hforbiddenMissing : ∀ v, v ∈ forbidden →
      v ∉ StrictRowPrefixValues gameF (s + 2) := by
    intro v hv
    rcases List.mem_append.mp hv with hvMissing | hvSpecial
    · rcases List.mem_map.mp hvMissing with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing2, EventESecondMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvSpecial
      subst v
      rw [← hEmit]
      exact diagonal_value_absent_strict_prefix gameRecurrenceModel (s + 2)
  have hbound := game_adjacent_dip_forbidden_upper_half_bound
    hnextDip hforbiddenNodup hforbiddenSub hforbiddenMissing
  have hlen : forbidden.length = missing2.length + 1 := by
    simp [forbidden, missingValues]
  change 2 * missing2.length + 5 ≤ s + 1
  omega

/-- Maximal-defect two-edge certificate.  At `delta+4=s`, some canonical
lower-band value occurs in all three consecutive strict prefixes. -/
theorem gameF_margin_eventE_maximal_defect_forces_triple_prefix_value
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    delta + 4 = s →
      ∃ c b0 b1 g,
        c < s ∧ b0 < s ∧ b1 < s + 1 ∧
        gameF s c = z + 1 ∧ gameF s b0 = z ∧
        gameF (s + 1) b1 = z ∧
        g ∈ EventEDefectBandSlots s delta c b0 ∧
        g < s ∧ g ≠ c ∧ g ≠ b0 ∧
        0 < gameF s g ∧ gameF s g < z ∧
        C gameF (s + 1) (s + 1) (gameF s g) ∧
        C gameF (s + 2) (s + 2) (gameF s g) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax

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
  change ∃ cf bf,
    EventEForcedForbiddenAmortizedCertificate s delta z cf bf at hfirst
  rcases hfirst with ⟨cf, bf, hfirstBase, hbound1⟩
  rcases hfirstBase with
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
  have hslotsData : ∀ g, g ∈ slots → g < s ∧ gameF s g < z := by
    intro g hg
    have hdata := hslotsPropsF g hg
    have htransition := hdata.2.2.2
    have hLower : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    exact ⟨hdata.1, hLower⟩
  have hunitNext := hU (s + 1) hnextDip
  change gameF (s + 2) (s + 2) + 1 = d at hunitNext
  have hEmit : gameF (s + 2) (s + 2) = z := by omega
  have hbound2 : 2 * missing2.length + 5 ≤ s + 1 := by
    exact gameF_eventE_second_edge_missing_bound
      hnextDip hHost1 hb1 hEmit hslotsNodup hslotsData
  have hbound1' : 2 * missing1.length + 5 ≤ s := by
    exact hbound1

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
  have htriplePos : 0 < triple.length := by
    omega
  have htripleNe : triple ≠ [] := by
    intro hnil
    rw [hnil] at htriplePos
    simp at htriplePos
  rcases List.exists_mem_of_ne_nil triple htripleNe with ⟨g, hgTriple⟩
  have hgTripleFilter := List.mem_filter.mp hgTriple
  have hgSurvivors : g ∈ survivors := hgTripleFilter.1
  have hgNew2 : gameF s g ∈ StrictRowPrefixValues gameF (s + 2) := by
    simpa [triple, EventETriplePrefixBandSlots] using hgTripleFilter.2
  have hgSurvivorFilter := List.mem_filter.mp hgSurvivors
  have hgSlots : g ∈ slots := hgSurvivorFilter.1
  have hgNew1 : gameF s g ∈ StrictRowPrefixValues gameF (s + 1) := by
    simpa [survivors, EventESurvivingBandSlots] using hgSurvivorFilter.2
  have hgData := hslotsPropsF g hgSlots
  have htransition := hgData.2.2.2
  have hqPos : 0 < gameF s g := by
    simpa [EventELowerTransition] using htransition.1
  have hqLower : gameF s g < z := by
    simpa [EventELowerTransition] using htransition.2.1
  exact ⟨c, b0, b1, g, hc, hb0, hb1,
    hSucc, hBase, hHost1, hgSlots,
    hgData.1, hgData.2.1, hgData.2.2.1,
    hqPos, hqLower,
    mem_strictRowPrefixValues_iff_C.mp hgNew1,
    mem_strictRowPrefixValues_iff_C.mp hgNew2⟩

#print axioms gameF_eventE_first_edge_missing_bound
#print axioms gameF_eventE_second_edge_missing_bound
#print axioms gameF_margin_eventE_maximal_defect_forces_triple_prefix_value

end ChompLean
