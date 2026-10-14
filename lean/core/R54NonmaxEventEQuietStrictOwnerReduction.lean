import R53EventEMaximalBackfillOwnerEquality
import R53NonmaxEventENonDipSharedOwnerSaturation

set_option autoImplicit false

namespace ChompLean

/-!
R54: sharpen the non-dip shared-owner packet and isolate the genuinely
deep quiet residual.

R53 packed the two consecutive backfill packets together with the
third-edge loss packet in the weak upper half `i <= s`.  All owners in the
third-edge packet are already strictly before `s`, and R53's strict
cross-edge theorem removes the endpoint `s` from the second backfill packet
as well.  Hence the whole three-packet family lives in the strict upper
half.  This improves the propagated constant from `7` to `9`.

Consequently, a quiet atom (`2*delta+7 <= s`) either already contains a
four-prefix survivor, or it has no such survivor and satisfies the strictly
deeper inequality `2*delta+9 <= s`.  The latter is the exact part not
decided by owner counting alone.
-/

private theorem r54_nodup_map_of_injective_on
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

/-- Strict version of the R53 three-packet packing theorem.  The persistent
packet is supplied with genuinely past (`i<q`) upper-half owners; the two
backfill packets use the canonical R53 owners, whose apparent endpoint was
already excluded by the second consecutive dip. -/
theorem game_consecutive_dips_two_forbidden_with_strict_persistent_packet
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
      exists i, i < q /\ q < i + i /\ gameF i i = v) :
    let back0 := PrefixBackfillValues
      (StrictRowPrefixValues gameF q)
      (StrictRowPrefixValues gameF (q + 1))
    let back1 := PrefixBackfillValues
      (StrictRowPrefixValues gameF (q + 1))
      (StrictRowPrefixValues gameF (q + 2))
    2 * (back0.length + back1.length + persistent.length) + 1 <= q /\
    2 * (forbidden0.length + forbidden1.length + persistent.length) + 5
      <= q := by
  dsimp only
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF q)
    (StrictRowPrefixValues gameF (q + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (q + 1))
    (StrictRowPrefixValues gameF (q + 2))

  have hpkg0 := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    gameRecurrenceModel hdip0 hforbidden0 hsub0 hmissing0
  change forbidden0.length + 1 <= back0.length /\ _ at hpkg0
  have hpkg1 := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    gameRecurrenceModel hdip1 hforbidden1 hsub1 hmissing1
  change forbidden1.length + 1 <= back1.length /\ _ at hpkg1

  have hcrossPersistent : forall a,
      a ∈ ConsecutiveBackfillValues q ->
      forall b, b ∈ persistent -> a ≠ b := by
    intro a ha b hb hEq
    change a ∈ back0 ++ back1 at ha
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

  let persistentOwner : Nat -> Nat := fun v =>
    if hv : v ∈ persistent then
      Classical.choose (hpersistentOwner v hv)
    else 0
  have hpersistentOwnerSpec : forall v, v ∈ persistent ->
      persistentOwner v < q /\ q < persistentOwner v + persistentOwner v /\
        gameF (persistentOwner v) (persistentOwner v) = v := by
    intro v hv
    dsimp [persistentOwner]
    rw [dif_pos hv]
    exact Classical.choose_spec (hpersistentOwner v hv)
  have hpersistentOwnerInj : forall v, v ∈ persistent ->
      forall w, w ∈ persistent ->
        persistentOwner v = persistentOwner w -> v = w := by
    intro v hv w hw hEq
    have hvDiag := (hpersistentOwnerSpec v hv).2.2
    have hwDiag := (hpersistentOwnerSpec w hw).2.2
    rw [hEq] at hvDiag
    exact hvDiag.symm.trans hwDiag
  have hpersistentOwnersNodup :
      (persistent.map persistentOwner).Nodup :=
    r54_nodup_map_of_injective_on persistentOwner persistent
      hpersistent hpersistentOwnerInj

  let owners := ConsecutiveBackfillOwners q ++
    persistent.map persistentOwner
  have hcrossOwners : forall a, a ∈ ConsecutiveBackfillOwners q ->
      forall b, b ∈ persistent.map persistentOwner -> a ≠ b := by
    intro a ha b hb hEq
    rcases List.mem_map.mp ha with ⟨v, hv, rfl⟩
    rcases List.mem_map.mp hb with ⟨w, hw, rfl⟩
    apply hcrossPersistent v hv w hw
    have hvDiag := (consecutiveBackfillOwner_spec hdip0 hdip1 hv).2.2
    have hwDiag := (hpersistentOwnerSpec w hw).2.2
    rw [hEq] at hvDiag
    exact hvDiag.symm.trans hwDiag
  have hownersNodup : owners.Nodup := by
    exact List.nodup_append.mpr
      ⟨consecutiveBackfillOwners_nodup hdip0 hdip1,
       hpersistentOwnersNodup, hcrossOwners⟩
  have hownersBand : forall i, i ∈ owners ->
      i < q /\ q < i + i := by
    intro i hi
    rcases List.mem_append.mp hi with hiBack | hiPersistent
    · rcases List.mem_map.mp hiBack with ⟨v, hv, rfl⟩
      exact ⟨consecutiveBackfillOwner_lt_firstRow hdip0 hdip1 hv,
        (consecutiveBackfillOwner_spec hdip0 hdip1 hv).2.1⟩
    · rcases List.mem_map.mp hiPersistent with ⟨v, hv, rfl⟩
      exact ⟨(hpersistentOwnerSpec v hv).1,
        (hpersistentOwnerSpec v hv).2.1⟩
  have hownersLen : owners.length =
      back0.length + back1.length + persistent.length := by
    simp [owners, ConsecutiveBackfillOwners,
      ConsecutiveBackfillValues, back0, back1, Nat.add_assoc]
  have hownersPositive : 0 < owners.length := by
    rw [hownersLen]
    omega
  have hpack := strict_upper_half_owner_packing
    hownersNodup hownersPositive hownersBand
  have hstrict :
      2 * (back0.length + back1.length + persistent.length) + 1 <= q := by
    rw [hownersLen] at hpack
    exact hpack
  have hforbiddenBound :
      2 * (forbidden0.length + forbidden1.length + persistent.length) + 5
        <= q := by
    omega
  exact ⟨hstrict, hforbiddenBound⟩

/-- The strict shared-owner certificate.  Besides the R53 certificate it
records the actual strict owner packing, the absorbed missing-population
bound, and the propagated `+9` inequality for the four-prefix packet. -/
def EventENonDipStrictSharedOwnerCertificate
    (s delta z c b0 : Nat) : Prop :=
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF s)
    (StrictRowPrefixValues gameF (s + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (s + 1))
    (StrictRowPrefixValues gameF (s + 2))
  EventENonDipSharedOwnerSaturationCertificate s delta z c b0 /\
  2 * (back0.length + back1.length +
    (EventEThirdMissingBandSlots s delta c b0).length) + 1 <= s /\
  2 * ((EventEMissingBandSlots s delta c b0).length +
    (EventESecondMissingBandSlots s delta c b0).length +
    (EventEThirdMissingBandSlots s delta c b0).length) + 9 <= s /\
  2 * delta + 9 <=
    s + 2 * (EventEFourPrefixBandSlots s delta c b0).length

/-- The exact deep-quiet remainder after the strict owner improvement.
Every triple-prefix slot is lost on the third edge, and the former quiet
threshold has two additional units of slack. -/
def EventENonDipDeepQuietTerminalCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventENonDipStrictSharedOwnerCertificate s delta z c b0 /\
  EventEFourPrefixBandSlots s delta c b0 = [] /\
  (EventETriplePrefixBandSlots s delta c b0).length =
    (EventEThirdMissingBandSlots s delta c b0).length /\
  2 * delta + 7 <= s /\
  2 * delta + 9 <= s

/-- Every nonmaximal no-third-dip Event E satisfies the strict shared-owner
certificate.  This is the game-level `+9` replacement for R53's `+7`
propagation. -/
theorem gameF_nonmax_eventE_nondip_strict_shared_owner_saturation
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hnondip : EventENonDipHighLossPacketCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  classical
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hOld := gameF_nonmax_eventE_nondip_shared_owner_saturation
    hU hres hcross hnondip
  change EventENonDipSharedOwnerSaturationCertificate
    s delta z c b0 at hOld
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists c b0, EventECrossEdgeSurvivorCertificate s delta z c b0
    at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipHighLossPacketCertificate s delta z c b0 at hnondip
  rcases hres with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨hdip0, _hmargin, hdip1⟩
  rcases hInv with
    ⟨_deltaPos, _deltaUpper, _hsum, _hzDiag,
      _ci, _bi, b1, _dc, _d0, _d1,
      _hci, _hbi, hb1, _hciNe, _hbiNe,
      _hSuccI, _hBaseI, hHost1, _hInvRest⟩
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨hc, _hb0, _hcNe, hSucc, _hBase,
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
      g < s /\ gameF s g < z := by
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
    apply r54_nodup_map_of_injective_on
      (fun g => gameF s g) missing0 hmissing0Nodup
    intro g hg k hk hEq
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hk).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) hEq
  have hlow1Nodup : low1.Nodup := by
    apply r54_nodup_map_of_injective_on
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
    apply r54_nodup_map_of_injective_on
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
    intro v hv w hw _hEq
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
      exists i, i < s /\ s < i + i /\ gameF i i = v := by
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
    exact ⟨i, hi, by omega, howner.trans hgv⟩

  have hstrict :=
    game_consecutive_dips_two_forbidden_with_strict_persistent_packet
      hdip0 hdip1
      hforbidden0Nodup hsub0 hmissingFirst
      hforbidden1Nodup hsub1 hmissingSecond
      hpersistentNodup hpersistent0 hpersistent1 hpersistentOwner
  change
      2 * (back0.length + back1.length + persistent.length) + 1 <= s /\
      2 * (forbidden0.length + forbidden1.length + persistent.length) + 5
        <= s at hstrict
  have hforbidden0Len : forbidden0.length = missing0.length + 1 := by
    simp [forbidden0, low0]
  have hforbidden1Len : forbidden1.length = missing1.length + 1 := by
    simp [forbidden1, low1]
  have hpersistentLen : persistent.length = missing3.length := by
    simp [persistent]
  have habsorbed :
      2 * (missing0.length + missing1.length + missing3.length) + 9 <= s := by
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
  have hpropagated : 2 * delta + 9 <= s + 2 * four.length := by
    omega
  have hstrictPack :
      2 * (back0.length + back1.length + missing3.length) + 1 <= s := by
    omega
  change EventENonDipStrictSharedOwnerCertificate s delta z c b0
  exact ⟨hOld, hstrictPack, habsorbed, hpropagated⟩

/-- A quiet no-dip atom is either already absorbed by the four-prefix atom,
or it lies in the deeper empty-four terminal. -/
theorem eventE_nondip_quiet_strict_owner_reduction
    {s delta z c b0 : Nat}
    (hcert : EventENonDipStrictSharedOwnerCertificate
      s delta z c b0)
    (hquiet : 2 * delta + 7 <= s) :
    (exists g, g ∈ EventEFourPrefixBandSlots s delta c b0) \/
      EventENonDipDeepQuietTerminalCertificate s delta z c b0 := by
  classical
  by_cases hne : EventEFourPrefixBandSlots s delta c b0 = []
  · right
    have hpartition := hcert.1.1.2.1
    have hlenFour :
        (EventEFourPrefixBandSlots s delta c b0).length = 0 := by
      rw [hne]
      simp
    have htripleMissing :
        (EventETriplePrefixBandSlots s delta c b0).length =
          (EventEThirdMissingBandSlots s delta c b0).length := by
      omega
    have hdeep := hcert.2.2.2
    rw [hne] at hdeep
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hdeep
    exact ⟨hcert, hne, htripleMissing, hquiet, hdeep⟩
  · left
    exact List.exists_mem_of_ne_nil _ hne

/-- The two boundary values formerly admitted by the quiet threshold are
not genuine quiet terminals: if `s < 2*delta+9`, a four-prefix survivor is
forced. -/
theorem eventE_nondip_quiet_boundary_forces_four_prefix_value
    {s delta z c b0 : Nat}
    (hcert : EventENonDipStrictSharedOwnerCertificate
      s delta z c b0)
    (hboundary : s < 2 * delta + 9) :
    exists g, g ∈ EventEFourPrefixBandSlots s delta c b0 := by
  have hbound := hcert.2.2.2
  have hpos : 0 <
      (EventEFourPrefixBandSlots s delta c b0).length := by
    omega
  have hne : EventEFourPrefixBandSlots s delta c b0 ≠ [] := by
    intro hnil
    rw [hnil] at hpos
    simp at hpos
  exact List.exists_mem_of_ne_nil _ hne

/-- In the deep terminal the description is pointwise, not merely a length
identity: every triple-prefix slot is absent on row `s+3` and is a high
past-diagonal echo with an explicit owner and row-`s+2` host. -/
theorem eventE_deep_quiet_every_triple_is_high_past_owner_loss
    {s delta z c b0 : Nat}
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s delta z c b0) :
    forall g, g ∈ EventETriplePrefixBandSlots s delta c b0 ->
      g ∈ EventEThirdMissingBandSlots s delta c b0 /\
      exists i b,
        i < s /\ b < s + 2 /\
        gameF i i = gameF s g /\
        gameF (s + 2) b = gameF s g /\
        s + 2 < gameF s g /\ gameF s g < z := by
  intro g hgTriple
  have hfourEmpty := hterm.2.1
  have hnotRow3 : gameF s g ∉
      StrictRowPrefixValues gameF (s + 3) := by
    intro hrow3
    have hgFour : g ∈ EventEFourPrefixBandSlots s delta c b0 := by
      apply List.mem_filter.mpr
      refine ⟨hgTriple, ?_⟩
      simpa [EventEFourPrefixBandSlots] using hrow3
    rw [hfourEmpty] at hgFour
    simp at hgFour
  have hgMissing : g ∈
      EventEThirdMissingBandSlots s delta c b0 := by
    apply List.mem_filter.mpr
    refine ⟨hgTriple, ?_⟩
    simpa [EventEThirdMissingBandSlots] using hnotRow3
  have hnondip := hterm.1.1.1
  exact ⟨hgMissing, hnondip.2.2.2.2 g hgMissing⟩

/-- Arithmetic consistency check: the numerical constraints displayed in
the following existential statement are simultaneously satisfiable. This
is a counterframe to exclusion by those constraints alone, not a realization
of the complete game terminal or a completeness claim about later bounds. -/
theorem eventE_deep_quiet_count_constraints_are_consistent :
    exists s delta m0 m1 m3 q,
      1 <= delta /\ delta + 5 <= s /\
      delta = m0 + m1 + m3 + q /\ q = 0 /\
      2 * (m0 + m1 + m3) + 9 <= s /\
      m3 + delta + 4 <= s /\
      2 * delta + 9 <= s := by
  exact ⟨11, 1, 0, 0, 1, 0, by omega⟩

#print axioms game_consecutive_dips_two_forbidden_with_strict_persistent_packet
#print axioms gameF_nonmax_eventE_nondip_strict_shared_owner_saturation
#print axioms eventE_nondip_quiet_strict_owner_reduction
#print axioms eventE_nondip_quiet_boundary_forces_four_prefix_value
#print axioms eventE_deep_quiet_every_triple_is_high_past_owner_loss
#print axioms eventE_deep_quiet_count_constraints_are_consistent

end ChompLean
