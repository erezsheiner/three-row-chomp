import R52NonmaxEventEThirdEdgePropagation

set_option autoImplicit false

namespace ChompLean

/-!
R53: absorb the third-edge no-dip losses into the original two-edge owner
budget.

The two adjacent dips create backfill packets `back0` and `back1`.  A value
which was present before both dips is disjoint from both packets: `back0`
is absent from the first old prefix, and `back1` is absent from the middle
prefix.  If such persistent values also have upper-half diagonal owners,
all three packets share a single finite owner interval.

For the R52 no-third-dip branch, the persistent values are exactly the
third-edge losses `M3`.  R52 gives their high past-diagonal owners.  Shared
packing therefore absorbs all of `M3` and upgrades

  `2*delta+7 <= s+2*|T|`

to the same inequality with the four-prefix packet `Q` in place of `T`.
-/

private theorem r53_nodup_map_of_injective_on
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

/-- Generic three-packet packing theorem.  The first two packets are the
new-only values created by consecutive dips.  The third packet consists of
values present in both old prefixes and already equipped with owners in the
same weak upper half.  It is therefore disjoint from both backfill packets
and consumes the same owner capacity. -/
theorem game_consecutive_dips_two_forbidden_with_persistent_owner_packet
    {q : Nat} {forbidden0 forbidden1 persistent : List Nat}
    (hdip0 : gameF (q + 1) (q + 1) < gameF q q)
    (hdip1 : gameF (q + 2) (q + 2) < gameF (q + 1) (q + 1))
    (hforbidden0 : forbidden0.Nodup)
    (hsub0 : forbidden0 ⊆ StrictRowPrefixValues gameF q)
    (hmissing0 : forall v, v ∈ forbidden0 ->
      v ∉ StrictRowPrefixValues gameF (q + 1))
    (hforbidden1 : forbidden1.Nodup)
    (hsub1 : forbidden1 ⊆ StrictRowPrefixValues gameF (q + 1))
    (hmissing1 : forall v, v ∈ forbidden1 ->
      v ∉ StrictRowPrefixValues gameF (q + 2))
    (hpersistent : persistent.Nodup)
    (hpersistent0 : persistent ⊆ StrictRowPrefixValues gameF q)
    (hpersistent1 : persistent ⊆
      StrictRowPrefixValues gameF (q + 1))
    (hpersistentOwner : forall v, v ∈ persistent ->
      exists i, i <= q ∧ q < i + i ∧ gameF i i = v) :
    let back0 := PrefixBackfillValues
      (StrictRowPrefixValues gameF q)
      (StrictRowPrefixValues gameF (q + 1))
    let back1 := PrefixBackfillValues
      (StrictRowPrefixValues gameF (q + 1))
      (StrictRowPrefixValues gameF (q + 2))
    2 * (back0.length + back1.length + persistent.length) <= q + 1 ∧
    2 * (forbidden0.length + forbidden1.length + persistent.length) + 3
      <= q := by
  dsimp only
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF q)
    (StrictRowPrefixValues gameF (q + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (q + 1))
    (StrictRowPrefixValues gameF (q + 2))
  let back01 := back0 ++ back1
  let values := back01 ++ persistent

  have hpkg0 := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    gameRecurrenceModel hdip0 hforbidden0 hsub0 hmissing0
  change forbidden0.length + 1 <= back0.length ∧
      back0.Nodup ∧
      forall v, v ∈ back0 -> exists i, i < q ∧ gameF i i = v
    at hpkg0
  have hpkg1 := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    gameRecurrenceModel hdip1 hforbidden1 hsub1 hmissing1
  change forbidden1.length + 1 <= back1.length ∧
      back1.Nodup ∧
      forall v, v ∈ back1 -> exists i, i < q + 1 ∧ gameF i i = v
    at hpkg1

  have hcross01 : forall a, a ∈ back0 ->
      forall b, b ∈ back1 -> a ≠ b := by
    intro a ha b hb hEq
    subst b
    exact consecutive_prefix_backfill_packets_disjoint q a ha hb
  have hback01Nodup : back01.Nodup := by
    exact List.nodup_append.mpr ⟨hpkg0.2.1, hpkg1.2.1, hcross01⟩
  have hcrossPersistent : forall a, a ∈ back01 ->
      forall b, b ∈ persistent -> a ≠ b := by
    intro a ha b hb hEq
    rcases List.mem_append.mp ha with ha0 | ha1
    · have haNotOld : a ∉ StrictRowPrefixValues gameF q := by
        have hfilter := (List.mem_filter.mp ha0).2
        simpa [back0, PrefixBackfillValues] using hfilter
      apply haNotOld
      rw [hEq]
      exact hpersistent0 hb
    · have haNotMiddle : a ∉
          StrictRowPrefixValues gameF (q + 1) := by
        have hfilter := (List.mem_filter.mp ha1).2
        simpa [back1, PrefixBackfillValues] using hfilter
      apply haNotMiddle
      rw [hEq]
      exact hpersistent1 hb
  have hvaluesNodup : values.Nodup := by
    exact List.nodup_append.mpr
      ⟨hback01Nodup, hpersistent, hcrossPersistent⟩

  have hownerExists : forall v, v ∈ values ->
      exists i, i <= q ∧ q < i + i ∧ gameF i i = v := by
    intro v hv
    rcases List.mem_append.mp hv with hvBack | hvPersistent
    · rcases List.mem_append.mp hvBack with hv0 | hv1
      · rcases hpkg0.2.2 v hv0 with ⟨i, hiq, hdiag⟩
        have hvNew := (List.mem_filter.mp hv0).1
        rcases mem_strictRowPrefixValues_iff_C.mp hvNew with
          ⟨b, hb, hcell⟩
        have hhigh := game_past_diagonal_reemission_is_high
          (i := i) (t := q + 1) (b := b)
          (Nat.le_of_lt hb) (hdiag.trans hcell.symm)
        have hcap := recurrence_diagonal_source_capacity
          gameRecurrenceModel i
        change gameF i i <= i + i + 1 at hcap
        exact ⟨i, by omega, by omega, hdiag⟩
      · rcases hpkg1.2.2 v hv1 with ⟨i, hiq, hdiag⟩
        have hvNew := (List.mem_filter.mp hv1).1
        rcases mem_strictRowPrefixValues_iff_C.mp hvNew with
          ⟨b, hb, hcell⟩
        have hhigh := game_past_diagonal_reemission_is_high
          (i := i) (t := q + 2) (b := b)
          (Nat.le_of_lt hb) (hdiag.trans hcell.symm)
        have hcap := recurrence_diagonal_source_capacity
          gameRecurrenceModel i
        change gameF i i <= i + i + 1 at hcap
        exact ⟨i, by omega, by omega, hdiag⟩
    · exact hpersistentOwner v hvPersistent

  let owner : Nat -> Nat := fun v =>
    if hv : v ∈ values then Classical.choose (hownerExists v hv) else 0
  have howner : forall v, v ∈ values ->
      owner v <= q ∧ q < owner v + owner v ∧
        gameF (owner v) (owner v) = v := by
    intro v hv
    dsimp [owner]
    rw [dif_pos hv]
    exact Classical.choose_spec (hownerExists v hv)
  have hownerInj : forall v, v ∈ values -> forall w, w ∈ values ->
      owner v = owner w -> v = w := by
    intro v hv w hw hEq
    have hvDiag := (howner v hv).2.2
    have hwDiag := (howner w hw).2.2
    rw [hEq] at hvDiag
    exact hvDiag.symm.trans hwDiag
  have hownersNodup : (values.map owner).Nodup :=
    r53_nodup_map_of_injective_on owner values hvaluesNodup hownerInj
  have hownersBand : forall i, i ∈ values.map owner ->
      i <= q ∧ q < i + i := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨v, hv, rfl⟩
    exact ⟨(howner v hv).1, (howner v hv).2.1⟩
  have hpack := weak_upper_half_owner_packing hownersNodup hownersBand
  simp only [List.length_map] at hpack
  have hshared :
      2 * (back0.length + back1.length + persistent.length) <= q + 1 := by
    change 2 * values.length <= q + 1 at hpack
    simpa [values, back01, back0, back1, Nat.add_assoc] using hpack
  have hforbiddenBound :
      2 * (forbidden0.length + forbidden1.length + persistent.length) + 3
        <= q := by
    omega
  exact ⟨hshared, hforbiddenBound⟩

/-- The strengthened no-third-dip certificate.  In addition to the R52
high-loss packet, it records the literal shared owner packing and the fully
propagated cross-edge inequality with `Q` replacing `T`. -/
def EventENonDipSharedOwnerSaturationCertificate
    (s delta z c b0 : Nat) : Prop :=
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF s)
    (StrictRowPrefixValues gameF (s + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (s + 1))
    (StrictRowPrefixValues gameF (s + 2))
  EventENonDipHighLossPacketCertificate s delta z c b0 ∧
  2 * (back0.length + back1.length +
    (EventEThirdMissingBandSlots s delta c b0).length) <= s + 1 ∧
  2 * delta + 7 <=
    s + 2 * (EventEFourPrefixBandSlots s delta c b0).length

/-- Event-E application of the shared-packet theorem.  Every third-edge
loss in the no-dip branch is absorbed by the same owner budget which paid
for the first two forbidden packets. -/
theorem gameF_nonmax_eventE_nondip_shared_owner_saturation
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hnondip : EventENonDipHighLossPacketCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventENonDipSharedOwnerSaturationCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  classical
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change MarginEventECounterexample s ∧
      EventEDefectPacketInvariant s d delta z ∧
      delta + 5 <= s ∧
      exists c b0, EventECrossEdgeSurvivorCertificate s delta z c b0
    at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipHighLossPacketCertificate s delta z c b0 at hnondip
  rcases hres with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨hdip0, _hmargin, hdip1⟩
  rcases hInv with
    ⟨_hdeltaPos, _hdeltaUpper, hsum, hzDiag,
      _ci, _bi, b1, _dc, _d0, _d1,
      _hci, _hbi, hb1, _hciNe, _hbiNe,
      _hSuccI, _hBaseI, hHost1, _hInvRest⟩
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨hc, hb0, _hcNe, hSucc, _hBase,
      hslotsNodup, hslotsLen, hslotsProps, _hweak⟩

  let slots := EventEDefectBandSlots s delta c b0
  let missing0 := EventEMissingBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let missing1 := EventESecondMissingBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let missing3 := EventEThirdMissingBandSlots s delta c b0
  let four := EventEFourPrefixBandSlots s delta c b0
  let low0 := missing0.map (fun g => gameF s g)
  let low1 := missing1.map (fun g => gameF s g)
  let persistent := missing3.map (fun g => gameF s g)
  let forbidden0 := low0 ++ [z + 1]
  let forbidden1 := low1 ++ [z]
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF s)
    (StrictRowPrefixValues gameF (s + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (s + 1))
    (StrictRowPrefixValues gameF (s + 2))

  have hslotsData : forall g, g ∈ slots ->
      g < s ∧ gameF s g < z := by
    intro g hg
    have hdata := hslotsProps g hg
    have htransition := hdata.2.2.2
    have hLower : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
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

  have hlow0Nodup : low0.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) missing0 hmissing0Nodup
    intro g hg k hk hEq
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hk).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) hEq
  have hlow1Nodup : low1.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) missing1 hmissing1Nodup
    intro g hg k hk hEq
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hkSurv : k ∈ survivors := (List.mem_filter.mp hk).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) hEq
  have hpersistentNodup : persistent.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) missing3 hmissing3Nodup
    intro g hg k hk hEq
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    have hkTriple : k ∈ triple := (List.mem_filter.mp hk).1
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
    have hkSurv : k ∈ survivors := (List.mem_filter.mp hkTriple).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) hEq

  have hdisjoint0 : forall v, v ∈ low0 ->
      forall w, w ∈ [z + 1] -> v ≠ w := by
    intro v hv w hw hEq
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hLower := (hslotsData g hgSlots).2
    omega
  have hdisjoint1 : forall v, v ∈ low1 ->
      forall w, w ∈ [z] -> v ≠ w := by
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

  have hdiag1 : gameF (s + 1) (s + 1) = z + 1 := by
    change d = z + 1
    omega
  have hunit1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hunit1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by omega

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
  have hmissingFirst : forall v, v ∈ forbidden0 ->
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
  have hmissingSecond : forall v, v ∈ forbidden1 ->
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
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    exact List.mem_map.mpr
      ⟨g, List.mem_range.mpr (hslotsData g hgSlots).1, rfl⟩
  have hpersistent1 : persistent ⊆
      StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
    have hfilter := (List.mem_filter.mp hgSurv).2
    simpa [survivors, EventESurvivingBandSlots] using hfilter
  have hpersistentOwner : forall v, v ∈ persistent ->
      exists i, i <= s ∧ s < i + i ∧ gameF i i = v := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, hgv⟩
    have hpacket := hnondip.2.2.2.2 g hg
    rcases hpacket with
      ⟨i, _b, hi, _hb, howner, _hhost, hhigh, _hbelow⟩
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel i
    change gameF i i <= i + i + 1 at hcap
    have hhighOwner : s + 2 < gameF i i := by
      rw [howner]
      exact hhigh
    exact ⟨i, Nat.le_of_lt hi, by omega, howner.trans hgv⟩

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
  have habsorbed :
      2 * (missing0.length + missing1.length + missing3.length) + 7 <= s := by
    have hpersistentLen : persistent.length = missing3.length := by
      simp [persistent]
    omega

  have hcountPartition := hcross.1.2.2.1
  change slots.length =
    missing0.length + missing1.length + triple.length at hcountPartition
  change slots.length = delta at hslotsLen
  have hdeltaFirst : delta =
      missing0.length + missing1.length + triple.length := by
    omega
  have hthirdPartition := hnondip.2.1
  change triple.length = four.length + missing3.length at hthirdPartition
  have hpropagated : 2 * delta + 7 <= s + 2 * four.length := by
    omega
  have hsharedPack :
      2 * (back0.length + back1.length + missing3.length) <= s + 1 := by
    have hpersistentLen : persistent.length = missing3.length := by
      simp [persistent]
    omega
  change EventENonDipSharedOwnerSaturationCertificate
    s delta z c b0
  exact ⟨hnondip, hsharedPack, hpropagated⟩

/-- R53 replacement of the R52 trichotomy: the two third-dip branches are
unchanged, while the no-dip branch now carries the shared-owner saturation
and the propagated four-prefix inequality. -/
theorem gameF_nonmax_eventE_R53_shared_owner_trichotomy
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 ∧
      (EventEThirdDipPenultimateHitCertificate s delta z c b0 ∨
       EventEThirdDipExtraForbiddenCertificate s delta z c b0 ∨
       EventENonDipSharedOwnerSaturationCertificate s delta z c b0) := by
  dsimp only
  have hR52 := gameF_nonmax_eventE_third_edge_propagation_trichotomy
    hU hres
  rcases hR52 with ⟨c, b0, hcross, hHit | hExtra | hNoDip⟩
  · exact ⟨c, b0, hcross, Or.inl hHit⟩
  · exact ⟨c, b0, hcross, Or.inr (Or.inl hExtra)⟩
  · have hshared := gameF_nonmax_eventE_nondip_shared_owner_saturation
      hU hres hcross hNoDip
    exact ⟨c, b0, hcross, Or.inr (Or.inr hshared)⟩

/-- Exact threshold form of the propagated inequality: whenever `t` slots
would not suffice numerically, strictly more than `t` four-prefix survivors
are forced. -/
theorem eventE_nondip_shared_owner_four_prefix_threshold
    {s delta z c b0 t : Nat}
    (hcert : EventENonDipSharedOwnerSaturationCertificate
      s delta z c b0)
    (hthreshold : s + 2 * t < 2 * delta + 7) :
    t < (EventEFourPrefixBandSlots s delta c b0).length := by
  have hbound := hcert.2.2
  omega

/-- In particular, above the half-defect threshold the strengthened no-dip
branch contains a concrete four-prefix survivor. -/
theorem eventE_nondip_shared_owner_forces_four_prefix_value
    {s delta z c b0 : Nat}
    (hcert : EventENonDipSharedOwnerSaturationCertificate
      s delta z c b0)
    (hlarge : s < 2 * delta + 7) :
    exists g, g ∈ EventEFourPrefixBandSlots s delta c b0 := by
  have hpos : 0 <
      (EventEFourPrefixBandSlots s delta c b0).length :=
    eventE_nondip_shared_owner_four_prefix_threshold
      hcert (t := 0) (by simpa using hlarge)
  have hne : EventEFourPrefixBandSlots s delta c b0 ≠ [] := by
    intro hnil
    rw [hnil] at hpos
    simp at hpos
  exact List.exists_mem_of_ne_nil _ hne

#print axioms game_consecutive_dips_two_forbidden_with_persistent_owner_packet
#print axioms gameF_nonmax_eventE_nondip_shared_owner_saturation
#print axioms gameF_nonmax_eventE_R53_shared_owner_trichotomy
#print axioms eventE_nondip_shared_owner_four_prefix_threshold
#print axioms eventE_nondip_shared_owner_forces_four_prefix_value

end ChompLean
