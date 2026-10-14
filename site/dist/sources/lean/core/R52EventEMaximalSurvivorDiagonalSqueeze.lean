import R51EventEMaximalBulkFrozenCarry

set_option autoImplicit false

namespace ChompLean

/-!
R52: squeeze the maximal-defect triple-survivor population between the
cross-edge lower bound and an independent diagonal/row-start capacity.

Early diagonal values are bounded by `d(i)<=2*i+1`, so a long initial block
of distinct diagonal values lies in `[1,s+3]`.  Every triple survivor is a
completed row-start value in the same interval and is disjoint from every
diagonal value.  Counting the two species together gives the matching upper
half bound.
-/

private theorem r52_nodup_map_of_injective_on
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

/-- Complete survivor-window certificate at maximal defect. -/
def EventEMaximalSurvivorDiagonalSqueezeCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventECrossEdgeSurvivorCertificate s delta z c b0 /\
  z = s + 3 /\
  s / 2 <= (EventETriplePrefixBandSlots s delta c b0).length /\
  (EventETriplePrefixBandSlots s delta c b0).length <= s / 2

/-- At maximal defect the survivor count is squeezed exactly to
`floor(s/2)`.  For odd `s`, the apparently extra diagonal slot is forced
below `s+4` because `s+4` already has diagonal owner `s+1`. -/
theorem gameF_margin_eventE_maximal_survivor_diagonal_squeeze
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
        EventEMaximalSurvivorDiagonalSqueezeCertificate
          s delta z c b0 := by
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
  rcases hhalf with ⟨c, b0, hcrossCert, hLower⟩

  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  have hdeltaPos := hInv.1
  have hdeltaUpper := hInv.2.1
  have hsum := hInv.2.2.1
  have hzSucc := hInv.2.2.2.1
  have hsFive : 5 <= s := by omega
  have hzExact : z = s + 3 := by omega
  have hdExact : d = s + 4 := by omega
  have hunitNext := hU (s + 1) hnextDip
  change gameF (s + 2) (s + 2) + 1 = d at hunitNext
  have hEmit : gameF (s + 2) (s + 2) = z := by omega

  let slots := EventEDefectBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let horizon := (s + 3) / 2 + 1
  let earlyDiag := (List.range horizon).map (fun i => gameF i i)
  let diagValues := earlyDiag ++ [z]
  let startValues := triple.map (fun g => gameF s g)

  have hbase := hcrossCert.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hsurvivorsNodup :
      (EventESurvivingBandSlots s delta c b0).Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have htripleNodup : triple.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hstartValuesNodup : startValues.Nodup := by
    apply r52_nodup_map_of_injective_on
      (fun g => gameF s g) triple htripleNodup
    intro g hg k hk hEq
    have hgSurv := (List.mem_filter.mp hg).1
    have hkSurv := (List.mem_filter.mp hk).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsProps g hgSlots).1)
      (Nat.le_of_lt (hslotsProps k hkSlots).1) hEq

  have hearlyNodup : earlyDiag.Nodup := by
    apply r52_nodup_map_of_injective_on
      (fun i => gameF i i) (List.range horizon) List.nodup_range
    intro i hi j hj hEq
    exact diagonal_injective gameRecurrenceModel hEq
  have hzNotEarly : z ∉ earlyDiag := by
    intro hzMem
    rcases List.mem_map.mp hzMem with ⟨i, hi, hiValue⟩
    have hiRange : i < horizon := List.mem_range.mp hi
    have hiOwner : gameF i i = z := hiValue
    have hiEq : i = s + 2 :=
      diagonal_injective gameRecurrenceModel (hiOwner.trans hEmit.symm)
    dsimp [horizon] at hiRange
    omega
  have hdiagValuesNodup : diagValues.Nodup := by
    exact List.nodup_append.mpr
      ⟨hearlyNodup, by simp, by
        intro a ha b hb hEq
        simp only [List.mem_singleton] at hb
        have haZ : a = z := hEq.trans hb
        rw [haZ] at ha
        exact hzNotEarly ha⟩

  have hcompleted : forall p, p ∈ startValues ->
      exists r, r < p /\ gameF p r = p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨g, hgTriple, rfl⟩
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
    have htransition := (hslotsProps g hgSlots).2.2.2
    have hpz : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    rcases gameF_three_prefix_value_has_completed_rowstart
        (hslotsProps g hgSlots).1 rfl
        (mem_strictRowPrefixValues_iff_C.mp hmem1)
        (mem_strictRowPrefixValues_iff_C.mp hmem2)
        (by omega) with ⟨r, hr, hstart, _hregime⟩
    exact ⟨r, hr, hstart⟩

  have hspeciesDisjoint : forall a, a ∈ diagValues ->
      forall p, p ∈ startValues -> a ≠ p := by
    intro a ha p hp hEq
    rcases hcompleted p hp with ⟨r, hrp, hstart⟩
    rcases List.mem_append.mp ha with haEarly | haZ
    · rcases List.mem_map.mp haEarly with ⟨i, _hi, hiValue⟩
      exact disjoint_D_S gameRecurrenceModel
        ⟨i, hiValue.trans hEq⟩ ⟨r, hrp, hstart⟩
    · simp only [List.mem_singleton] at haZ
      have hzP : z = p := haZ.symm.trans hEq
      exact disjoint_D_S gameRecurrenceModel
        ⟨s + 2, hEmit.trans hzP⟩ ⟨r, hrp, hstart⟩
  have hunionNodup : (diagValues ++ startValues).Nodup :=
    List.nodup_append.mpr
      ⟨hdiagValuesNodup, hstartValuesNodup, hspeciesDisjoint⟩

  have hunionSub : diagValues ++ startValues ⊆
      List.range' 1 (s + 3) := by
    intro v hv
    rcases List.mem_append.mp hv with hvDiag | hvStart
    · rcases List.mem_append.mp hvDiag with hvEarly | hvZ
      · rcases List.mem_map.mp hvEarly with ⟨i, hi, rfl⟩
        have hiRange : i < horizon := List.mem_range.mp hi
        have hpos := gameRecurrenceModel.diagonal_gt i
        have hcap := recurrence_diagonal_source_capacity
          gameRecurrenceModel i
        change i < gameF i i at hpos
        change gameF i i <= i + i + 1 at hcap
        have hneTop : gameF i i ≠ d := by
          intro hEq
          have hiEq : i = s + 1 :=
            diagonal_injective gameRecurrenceModel hEq
          dsimp [horizon] at hiRange
          omega
        apply List.mem_range'_1.mpr
        dsimp [horizon] at hiRange
        constructor <;> omega
      · simp only [List.mem_singleton] at hvZ
        subst v
        apply List.mem_range'_1.mpr
        constructor <;> omega
    · rcases List.mem_map.mp hvStart with ⟨g, hgTriple, rfl⟩
      have hgSurv := (List.mem_filter.mp hgTriple).1
      have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
      have htransition := (hslotsProps g hgSlots).2.2.2
      have hpPos : 0 < gameF s g := by
        simpa [EventELowerTransition] using htransition.1
      have hpz : gameF s g < z := by
        simpa [EventELowerTransition] using htransition.2.1
      apply List.mem_range'_1.mpr
      constructor <;> omega
  have hcapacity := nodup_subset_length_le hunionNodup hunionSub
  have hdiagLen : diagValues.length = horizon + 1 := by
    simp [diagValues, earlyDiag]
  have hstartLen : startValues.length = triple.length := by
    simp [startValues]
  have hrangeLen : (List.range' 1 (s + 3)).length = s + 3 := by
    simp
  rw [List.length_append, hdiagLen, hstartLen, hrangeLen] at hcapacity
  have hUpper : triple.length <= s / 2 := by
    dsimp [horizon] at hcapacity
    omega
  exact ⟨c, b0, hcrossCert, hzExact, hLower, hUpper⟩

/-- The cross-edge and diagonal capacities are simultaneously saturated at
every maximal-defect event E. -/
theorem gameF_margin_eventE_maximal_survivor_count_exact
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
        EventEMaximalSurvivorDiagonalSqueezeCertificate
          s delta z c b0 /\
        (EventETriplePrefixBandSlots s delta c b0).length = s / 2 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hcert := gameF_margin_eventE_maximal_survivor_diagonal_squeeze
    hU hdip hmargin hnextDip hmax
  change exists c b0,
    EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z c b0
    at hcert
  rcases hcert with ⟨c, b0, hcert⟩
  have hLower := hcert.2.2.1
  have hUpper := hcert.2.2.2
  exact ⟨c, b0, hcert, Nat.le_antisymm hUpper hLower⟩

/-- The complementary missing population is exact as well.  Its size plus
the four forced exchange backfills equals the complete weak-upper-half
owner capacity. -/
theorem gameF_margin_eventE_maximal_missing_total_exact
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
        EventEMaximalSurvivorDiagonalSqueezeCertificate
          s delta z c b0 /\
        (EventEMissingBandSlots s delta c b0).length +
          (EventESecondMissingBandSlots s delta c b0).length + 4 =
            (s + 1) / 2 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hcert := gameF_margin_eventE_maximal_survivor_count_exact
    hU hdip hmargin hnextDip hmax
  change exists c b0,
    EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z c b0 /\
    (EventETriplePrefixBandSlots s delta c b0).length = s / 2
    at hcert
  rcases hcert with ⟨c, b0, hsqueeze, htriple⟩
  have hcount := hsqueeze.1.1
  have hpartition := hcount.2.2.1
  have hbase := hcount.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      _hslotsNodup, hslotsLen, _hslotsProps, _hweak⟩
  change (EventEDefectBandSlots s delta c b0).length =
      (EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length +
      (EventETriplePrefixBandSlots s delta c b0).length at hpartition
  change (EventEDefectBandSlots s delta c b0).length = delta at hslotsLen
  change (EventETriplePrefixBandSlots s delta c b0).length = s / 2
    at htriple
  have hdeltaPart : delta =
      (EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length +
      (EventETriplePrefixBandSlots s delta c b0).length := by
    omega
  refine ⟨c, b0, hsqueeze, ?_⟩
  change (EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length + 4 =
        (s + 1) / 2
  omega

/-- Backwards-compatible even-row specialization. -/
theorem gameF_margin_eventE_maximal_even_survivor_count_exact
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1))
    (_hEven : s % 2 = 0) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    delta + 4 = s ->
      exists c b0,
        EventEMaximalSurvivorDiagonalSqueezeCertificate
          s delta z c b0 /\
        (EventETriplePrefixBandSlots s delta c b0).length = s / 2 :=
  gameF_margin_eventE_maximal_survivor_count_exact
    hU hdip hmargin hnextDip

#print axioms gameF_margin_eventE_maximal_survivor_diagonal_squeeze
#print axioms gameF_margin_eventE_maximal_survivor_count_exact
#print axioms gameF_margin_eventE_maximal_missing_total_exact
#print axioms gameF_margin_eventE_maximal_even_survivor_count_exact

end ChompLean
