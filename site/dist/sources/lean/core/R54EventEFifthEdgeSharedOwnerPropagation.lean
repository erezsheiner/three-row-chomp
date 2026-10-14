import R54EventEFourPrefixFifthEdgeFreeze

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R54, second stage: if the fourth diagonal edge does not dip, every value
lost from the four-prefix packet has a past diagonal owner in exactly the
same upper-half interval as the two original backfill packets and the
third-edge loss packet.  Thus it can be absorbed into the existing shared
owner budget.
-/

/-- The no-fourth-dip strengthening.  It records the literal four-packet
owner packing and propagates the sharp R53 inequality from `Q4` to `Q5`
without changing its constant. -/
def EventENoFourthDipFivePrefixSharedOwnerCertificate
    (s delta z c b0 : Nat) : Prop :=
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF s)
    (StrictRowPrefixValues gameF (s + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (s + 1))
    (StrictRowPrefixValues gameF (s + 2))
  Not (gameF (s + 4) (s + 4) < gameF (s + 3) (s + 3)) ∧
  EventEFifthEdgeFrozenCarryCertificate s delta z c b0 ∧
  2 * (back0.length + back1.length +
      (EventEThirdMissingBandSlots s delta c b0).length +
      (EventEFourthMissingBandSlots s delta c b0).length) <= s + 1 ∧
  2 * delta + 7 <=
    s + 2 * (EventEFivePrefixBandSlots s delta c b0).length

private theorem r54b_nodup_map_of_injective_on
    (f : Nat -> Nat) (xs : List Nat)
    (hxs : xs.Nodup)
    (hinj : ∀ x, x ∈ xs -> ∀ y, y ∈ xs ->
      f x = f y -> x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      change (f a :: as.map f).Nodup
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

/-- In the no-fourth-dip branch, the fourth-edge loss packet joins the
original shared owner packing and the exact survivor inequality propagates
from four prefixes to five. -/
theorem gameF_nonmax_eventE_no_fourth_dip_five_prefix_shared_owner
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hcert : EventENonDipSharedOwnerSaturationCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hnoDip3 : Not
      (gameF (s + 4) (s + 4) < gameF (s + 3) (s + 3))) :
    EventENoFourthDipFivePrefixSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  classical
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change MarginEventECounterexample s ∧
      EventEDefectPacketInvariant s d delta z ∧
      delta + 5 <= s ∧
      ∃ c b0, EventECrossEdgeSurvivorCertificate s delta z c b0
    at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipSharedOwnerSaturationCertificate
    s delta z c b0 at hcert
  rcases hres with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨hdip0, _hmargin, hdip1⟩
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzDiag : z + 1 = d := hInv.2.2.2.1
  have hunit0 := hU s hdip0
  change d + 1 = gameF s s at hunit0
  have hdiag0 : gameF s s = z + 2 := by omega
  have hdiag1 : gameF (s + 1) (s + 1) = z + 1 := by omega
  have hunit1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hunit1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by omega
  have hnoDip2 := hcert.1.1
  have hzLeDiag3 : z <= gameF (s + 3) (s + 3) := by omega
  have hdiag3Le4 : gameF (s + 3) (s + 3) <=
      gameF (s + 4) (s + 4) := by omega

  have hfrozen := gameF_nonmax_eventE_four_prefix_fifth_edge_freeze
    (s := s) (c := c) (b0 := b0)
    (by
      change NonmaxMarginEventECrossEdgeResidual s
      exact ⟨⟨hdip0, _hmargin, hdip1⟩, hInv, _hnonmax, _hexists⟩)
    hcross hcert
  change EventEFifthEdgeFrozenCarryCertificate s delta z c b0 at hfrozen

  let slots := EventEDefectBandSlots s delta c b0
  let missing0 := EventEMissingBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let missing1 := EventESecondMissingBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let missing3 := EventEThirdMissingBandSlots s delta c b0
  let four := EventEFourPrefixBandSlots s delta c b0
  let missing4 := EventEFourthMissingBandSlots s delta c b0
  let five := EventEFivePrefixBandSlots s delta c b0
  let low0 := missing0.map (fun g => gameF s g)
  let low1 := missing1.map (fun g => gameF s g)
  let persistent3 := missing3.map (fun g => gameF s g)
  let persistent4 := missing4.map (fun g => gameF s g)
  let persistent := persistent3 ++ persistent4
  let forbidden0 := low0 ++ [z + 1]
  let forbidden1 := low1 ++ [z]
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF s)
    (StrictRowPrefixValues gameF (s + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (s + 1))
    (StrictRowPrefixValues gameF (s + 2))

  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨hc, _hb0, _hcNe, hSucc, _hBase,
      hslotsNodup, hslotsLen, hslotsProps, _hweak⟩
  rcases hInv with
    ⟨_hdeltaPos, _hdeltaUpper, _hsum, _hz,
      _ci, _bi, b1, _dc, _d0, _d1,
      _hci, _hbi, hb1, _hciNe, _hbiNe,
      _hSuccI, _hBaseI, hHost1, _hInvRest⟩

  have hslotsData : ∀ g, g ∈ slots ->
      g < s ∧ gameF s g < z := by
    intro g hg
    have hdata := hslotsProps g hg
    have hLower : gameF s g < z := by
      simpa [EventELowerTransition] using hdata.2.2.2.2.1
    exact ⟨hdata.1, hLower⟩
  have hmissing0Nodup : missing0.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hsurvivorsNodup : survivors.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hmissing1Nodup : missing1.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have htripleNodup : triple.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hmissing3Nodup : missing3.Nodup :=
    List.filter_sublist.nodup htripleNodup
  have hfourNodup : four.Nodup :=
    List.filter_sublist.nodup htripleNodup
  have hmissing4Nodup : missing4.Nodup :=
    List.filter_sublist.nodup hfourNodup

  have hslotOfMissing3 : ∀ g, g ∈ missing3 -> g ∈ slots := by
    intro g hg
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
    exact (List.mem_filter.mp hgSurv).1
  have hslotOfMissing4 : ∀ g, g ∈ missing4 -> g ∈ slots := by
    intro g hg
    have hgFour : g ∈ four := (List.mem_filter.mp hg).1
    have hgTriple : g ∈ triple := (List.mem_filter.mp hgFour).1
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
    exact (List.mem_filter.mp hgSurv).1

  have hlow0Nodup : low0.Nodup := by
    apply r54b_nodup_map_of_injective_on
      (fun g => gameF s g) missing0 hmissing0Nodup
    intro g hg k hk hEq
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hk).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) hEq
  have hlow1Nodup : low1.Nodup := by
    apply r54b_nodup_map_of_injective_on
      (fun g => gameF s g) missing1 hmissing1Nodup
    intro g hg k hk hEq
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hkSurv : k ∈ survivors := (List.mem_filter.mp hk).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) hEq
  have hpersistent3Nodup : persistent3.Nodup := by
    apply r54b_nodup_map_of_injective_on
      (fun g => gameF s g) missing3 hmissing3Nodup
    intro g hg k hk hEq
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g (hslotOfMissing3 g hg)).1)
      (Nat.le_of_lt (hslotsData k (hslotOfMissing3 k hk)).1) hEq
  have hpersistent4Nodup : persistent4.Nodup := by
    apply r54b_nodup_map_of_injective_on
      (fun g => gameF s g) missing4 hmissing4Nodup
    intro g hg k hk hEq
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g (hslotOfMissing4 g hg)).1)
      (Nat.le_of_lt (hslotsData k (hslotOfMissing4 k hk)).1) hEq
  have hpersistentCross : ∀ v, v ∈ persistent3 ->
      ∀ w, w ∈ persistent4 -> v ≠ w := by
    intro v hv w hw hEq
    rcases List.mem_map.mp hv with ⟨g, hg, hgv⟩
    rcases List.mem_map.mp hw with ⟨k, hk, hkw⟩
    have hgk : g = k := gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g (hslotOfMissing3 g hg)).1)
      (Nat.le_of_lt (hslotsData k (hslotOfMissing4 k hk)).1)
      (hgv.trans (hEq.trans hkw.symm))
    subst k
    have hnotRow3 : gameF s g ∉
        StrictRowPrefixValues gameF (s + 3) := by
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing3, EventEThirdMissingBandSlots] using hfilter
    have hgFour : g ∈ four := (List.mem_filter.mp hk).1
    have hrow3 : gameF s g ∈
        StrictRowPrefixValues gameF (s + 3) := by
      have hfilter := (List.mem_filter.mp hgFour).2
      simpa [four, EventEFourPrefixBandSlots] using hfilter
    exact hnotRow3 hrow3
  have hpersistentNodup : persistent.Nodup :=
    List.nodup_append.mpr
      ⟨hpersistent3Nodup, hpersistent4Nodup, hpersistentCross⟩

  have hdisjoint0 : ∀ v, v ∈ low0 ->
      ∀ w, w ∈ [z + 1] -> v ≠ w := by
    intro v hv w hw hEq
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hLower := (hslotsData g hgSlots).2
    omega
  have hdisjoint1 : ∀ v, v ∈ low1 ->
      ∀ w, w ∈ [z] -> v ≠ w := by
    intro v hv w hw
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    exact Nat.ne_of_lt (hslotsData g hgSlots).2
  have hforbidden0Nodup : forbidden0.Nodup :=
    List.nodup_append.mpr ⟨hlow0Nodup, by simp, hdisjoint0⟩
  have hforbidden1Nodup : forbidden1.Nodup :=
    List.nodup_append.mpr ⟨hlow1Nodup, by simp, hdisjoint1⟩

  have hsub0 : forbidden0 ⊆ StrictRowPrefixValues gameF s := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
      exact List.mem_map.mpr
        ⟨g, List.mem_range.mpr (hslotsData g hgSlots).1, rfl⟩
    · simp only [List.mem_singleton] at hvHigh
      subst v
      exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, hSucc⟩
  have hmissingFirst : ∀ v, v ∈ forbidden0 ->
      v ∉ StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing0, EventEMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      rw [← hdiag1]
      exact diagonal_value_absent_strict_prefix
        gameRecurrenceModel (s + 1)
  have hsub1 : forbidden1 ⊆
      StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
      have hfilter := (List.mem_filter.mp hgSurv).2
      simpa [survivors, EventESurvivingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      exact List.mem_map.mpr ⟨b1, List.mem_range.mpr hb1, hHost1⟩
  have hmissingSecond : ∀ v, v ∈ forbidden1 ->
      v ∉ StrictRowPrefixValues gameF (s + 2) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing1, EventESecondMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      rw [← hdiag2]
      exact diagonal_value_absent_strict_prefix
        gameRecurrenceModel (s + 2)

  have hpersistent0 : persistent ⊆ StrictRowPrefixValues gameF s := by
    intro v hv
    rcases List.mem_append.mp hv with hv3 | hv4
    · rcases List.mem_map.mp hv3 with ⟨g, hg, rfl⟩
      exact List.mem_map.mpr
        ⟨g, List.mem_range.mpr
          (hslotsData g (hslotOfMissing3 g hg)).1, rfl⟩
    · rcases List.mem_map.mp hv4 with ⟨g, hg, rfl⟩
      exact List.mem_map.mpr
        ⟨g, List.mem_range.mpr
          (hslotsData g (hslotOfMissing4 g hg)).1, rfl⟩
  have hpersistent1 : persistent ⊆
      StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hv3 | hv4
    · rcases List.mem_map.mp hv3 with ⟨g, hg, rfl⟩
      have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
      have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
      have hfilter := (List.mem_filter.mp hgSurv).2
      simpa [survivors, EventESurvivingBandSlots] using hfilter
    · rcases List.mem_map.mp hv4 with ⟨g, hg, rfl⟩
      have hgFour : g ∈ four := (List.mem_filter.mp hg).1
      have hgTriple : g ∈ triple := (List.mem_filter.mp hgFour).1
      have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
      have hfilter := (List.mem_filter.mp hgSurv).2
      simpa [survivors, EventESurvivingBandSlots] using hfilter

  have hpersistentOwner3 : ∀ v, v ∈ persistent3 ->
      ∃ i, i <= s ∧ s < i + i ∧ gameF i i = v := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, hgv⟩
    have hpacket := hcert.1.2.2.2.2 g hg
    rcases hpacket with
      ⟨i, _b, hi, _hb, howner, _hhost, hhigh, _hbelow⟩
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel i
    change gameF i i <= i + i + 1 at hcap
    have hhighOwner : s + 2 < gameF i i := by
      rw [howner]
      exact hhigh
    exact ⟨i, Nat.le_of_lt hi, by omega, howner.trans hgv⟩
  have hpersistentOwner4 : ∀ v, v ∈ persistent4 ->
      ∃ i, i <= s ∧ s < i + i ∧ gameF i i = v := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, hgv⟩
    have hgeom := hfrozen.2.2.2 g hg
    rcases hgeom with ⟨b, hb, hhost, hhigh, hvBelow⟩
    have hvPos : 0 < gameF s g := by
      have hgData := hslotsProps g (hslotOfMissing4 g hg)
      simpa [EventELowerTransition] using hgData.2.2.2.1
    have hvBelow4 : gameF s g < gameF (s + 4) (s + 4) := by
      omega
    have hvAbsent : gameF s g ∉
        StrictRowPrefixValues gameF (s + 4) := by
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing4, EventEFourthMissingBandSlots] using hfilter
    rcases old_diagonal_mex_backfill_has_past_owner
        gameRecurrenceModel hvPos hvBelow4 hvAbsent with
      ⟨i, hi4, howner⟩
    change gameF i i = gameF s g at howner
    have hi : i < s := by
      by_cases his : i < s
      · exact his
      · have hicases : i = s ∨ i = s + 1 ∨
            i = s + 2 ∨ i = s + 3 := by omega
        rcases hicases with hi0 | hi1 | hi2 | hi3
        · rw [hi0, hdiag0] at howner
          omega
        · rw [hi1, hdiag1] at howner
          omega
        · rw [hi2, hdiag2] at howner
          omega
        · rw [hi3] at howner
          omega
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel i
    change gameF i i <= i + i + 1 at hcap
    have hhighOwner : s + 3 < gameF i i := by
      rw [howner]
      exact hhigh
    exact ⟨i, Nat.le_of_lt hi, by omega, howner.trans hgv⟩
  have hpersistentOwner : ∀ v, v ∈ persistent ->
      ∃ i, i <= s ∧ s < i + i ∧ gameF i i = v := by
    intro v hv
    rcases List.mem_append.mp hv with hv3 | hv4
    · exact hpersistentOwner3 v hv3
    · exact hpersistentOwner4 v hv4

  have hshared :=
    game_consecutive_dips_two_forbidden_with_persistent_owner_packet
      hdip0 hdip1
      hforbidden0Nodup hsub0 hmissingFirst
      hforbidden1Nodup hsub1 hmissingSecond
      hpersistentNodup hpersistent0 hpersistent1 hpersistentOwner
  change 2 * (back0.length + back1.length + persistent.length) <= s + 1 ∧
      2 * (forbidden0.length + forbidden1.length + persistent.length) + 3
        <= s at hshared
  have hforbidden0Len : forbidden0.length = missing0.length + 1 := by
    simp [forbidden0, low0]
  have hforbidden1Len : forbidden1.length = missing1.length + 1 := by
    simp [forbidden1, low1]
  have hpersistentLen : persistent.length =
      missing3.length + missing4.length := by
    simp [persistent, persistent3, persistent4]
  have hsharedPack :
      2 * (back0.length + back1.length +
        missing3.length + missing4.length) <= s + 1 := by
    omega
  have habsorbed :
      2 * (missing0.length + missing1.length +
        missing3.length + missing4.length) + 7 <= s := by
    omega

  have hcountPartition := hcross.1.2.2.1
  change slots.length =
    missing0.length + missing1.length + triple.length at hcountPartition
  change slots.length = delta at hslotsLen
  have hthirdPartition := hcert.1.2.1
  change triple.length = four.length + missing3.length at hthirdPartition
  have hfourthPartition := hfrozen.1
  change four.length = five.length + missing4.length at hfourthPartition
  have hpropagated : 2 * delta + 7 <= s + 2 * five.length := by
    omega
  have hresult : EventENoFourthDipFivePrefixSharedOwnerCertificate
      s delta z c b0 :=
    ⟨hnoDip3, hfrozen, hsharedPack, hpropagated⟩
  simpa [delta, z, d] using hresult

/-- In the high-defect branch, absence of a fourth dip forces a concrete
five-prefix survivor at the original half-defect threshold. -/
theorem eventE_no_fourth_dip_high_defect_forces_five_prefix_value
    {s delta z c b0 : Nat}
    (hcert : EventENoFourthDipFivePrefixSharedOwnerCertificate
      s delta z c b0)
    (hlarge : s < 2 * delta + 7) :
    ∃ g, g ∈ EventEFivePrefixBandSlots s delta c b0 := by
  have hbound := hcert.2.2.2
  have hpos : 0 < (EventEFivePrefixBandSlots s delta c b0).length := by
    omega
  have hne : EventEFivePrefixBandSlots s delta c b0 ≠ [] := by
    intro hnil
    rw [hnil] at hpos
    simp at hpos
  exact List.exists_mem_of_ne_nil _ hne

#print axioms gameF_nonmax_eventE_no_fourth_dip_five_prefix_shared_owner
#print axioms eventE_no_fourth_dip_high_defect_forces_five_prefix_value

end ChompLean
