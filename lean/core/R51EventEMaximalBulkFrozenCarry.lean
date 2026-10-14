import R51EventECrossEdgeSurvivorExplosion
import R51EventEFrozenBranchTerminalReduction

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R51 bulk consequence.  Cross-edge packing supplies linearly many
triple-prefix survivors at maximal defect.  Since their row-`s` values are
distinct and all at most `s+2`, at most two have owner time after `s`.
All remaining survivors are completed same-column frozen carries.
-/

noncomputable def EventEFrozenTripleBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventETriplePrefixBandSlots s delta c b0).filter
    (fun g => decide (gameF s g <= s))

private theorem r51_bulk_nodup_map_of_injective_on
    (f : Nat -> Nat) (xs : List Nat)
    (hxs : xs.Nodup)
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
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

/-- Complete bulk certificate for the maximal-defect layer. -/
def EventEMaximalBulkFrozenCarryCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventECrossEdgeSurvivorCertificate s delta z c b0 /\
  z = s + 3 /\
  s / 2 <= (EventETriplePrefixBandSlots s delta c b0).length /\
  (EventETriplePrefixBandSlots s delta c b0).length <=
    (EventEFrozenTripleBandSlots s delta c b0).length + 2 /\
  s / 2 <= (EventEFrozenTripleBandSlots s delta c b0).length + 2 /\
  forall g, g ∈ EventEFrozenTripleBandSlots s delta c b0 ->
    EventEFrozenCarryTerminal s z g (gameF s g)

/-- At maximal defect, all but at most two of the linear-size survivor
family are already-completed frozen row starts. -/
theorem gameF_margin_eventE_maximal_defect_bulk_frozen_carries
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
        EventEMaximalBulkFrozenCarryCertificate s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hhalf := gameF_margin_eventE_maximal_defect_half_band_survives
    hU hdip hmargin hnextDip hmax
  change exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 /\
    s / 2 <= (EventETriplePrefixBandSlots s delta c b0).length
    at hhalf
  rcases hhalf with ⟨c, b0, hcross, hhalf⟩

  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzSucc : z + 1 = d := hInv.2.2.2.1
  have hzExact : z = s + 3 := by omega

  let slots := EventEDefectBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let frozen := EventEFrozenTripleBandSlots s delta c b0
  let late := triple.filter (fun g => decide (s < gameF s g))
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hsurvivorsNodup :
      (EventESurvivingBandSlots s delta c b0).Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have htripleNodup : triple.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hlateNodup : late.Nodup :=
    List.filter_sublist.nodup htripleNodup
  have hlateValuesNodup : (late.map (fun g => gameF s g)).Nodup := by
    apply r51_bulk_nodup_map_of_injective_on
      (fun g => gameF s g) late hlateNodup
    intro g hg k hk hEq
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    have hkTriple : k ∈ triple := (List.mem_filter.mp hk).1
    have hgSurv := (List.mem_filter.mp hgTriple).1
    have hkSurv := (List.mem_filter.mp hkTriple).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsProps g hgSlots).1)
      (Nat.le_of_lt (hslotsProps k hkSlots).1) hEq
  have hlateValuesSub : late.map (fun g => gameF s g) ⊆
      List.range' (s + 1) 2 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨g, hgLate, rfl⟩
    have hgTriple : g ∈ triple := (List.mem_filter.mp hgLate).1
    have hnotLow := (List.mem_filter.mp hgLate).2
    have hgSurv := (List.mem_filter.mp hgTriple).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have htransition := (hslotsProps g hgSlots).2.2.2
    have hpz : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    have hslt : s < gameF s g := by
      simpa [late] using hnotLow
    apply List.mem_range'_1.mpr
    constructor <;> omega
  have hlateCap :=
    nodup_subset_length_le hlateValuesNodup hlateValuesSub
  simp only [List.length_map, List.length_range'] at hlateCap

  have hpartitionRaw := List.length_eq_countP_add_countP
    (fun g => decide (gameF s g <= s)) (l := triple)
  simp only [List.countP_eq_length_filter] at hpartitionRaw
  have hpartition : triple.length = frozen.length + late.length := by
    simpa [frozen, late, triple, EventEFrozenTripleBandSlots] using
      hpartitionRaw
  have hmostlyFrozen : triple.length <= frozen.length + 2 := by omega
  change s / 2 <= triple.length at hhalf
  have hbulk : s / 2 <= frozen.length + 2 := by omega

  have hterminals : forall g, g ∈ frozen ->
      EventEFrozenCarryTerminal s z g (gameF s g) := by
    intro g hgFrozen
    have hgTriple : g ∈ triple := (List.mem_filter.mp hgFrozen).1
    have hpLow : gameF s g <= s := by
      simpa [frozen, EventEFrozenTripleBandSlots] using
        (List.mem_filter.mp hgFrozen).2
    have hgSurv : g ∈ EventESurvivingBandSlots s delta c b0 :=
      (List.mem_filter.mp hgTriple).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hmem1 : gameF s g ∈
        StrictRowPrefixValues gameF (s + 1) := by
      simpa [EventESurvivingBandSlots] using
        (List.mem_filter.mp hgSurv).2
    have hmem2 : gameF s g ∈
        StrictRowPrefixValues gameF (s + 2) := by
      simpa [triple, EventETriplePrefixBandSlots] using
        (List.mem_filter.mp hgTriple).2
    have hC1 := mem_strictRowPrefixValues_iff_C.mp hmem1
    have hC2 := mem_strictRowPrefixValues_iff_C.mp hmem2
    have hdata := hslotsProps g hgSlots
    have htransition := hdata.2.2.2
    have hpPos : 0 < gameF s g := by
      simpa [EventELowerTransition] using htransition.1
    have hpz : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    have hregime := gameF_three_prefix_host_freeze_regime
      hdata.1 rfl hC1 hC2 (by omega)
    exact threePrefixFreezeRegime_low_is_carry_terminal
      hdata.1 rfl hpPos hpz hregime hpLow
  exact ⟨c, b0, hcross, hzExact, hhalf,
    hmostlyFrozen, hbulk, hterminals⟩

#print axioms gameF_margin_eventE_maximal_defect_bulk_frozen_carries

end ChompLean
