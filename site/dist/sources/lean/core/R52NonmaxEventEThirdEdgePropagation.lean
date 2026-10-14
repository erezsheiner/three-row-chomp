import R51RM2CrossEdgeResidualCollapse

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R52: propagate the nonmaximal event-E cross-edge survivors through one
further row.

Write `T` for the canonical band slots whose row-`s` values occur in the
strict prefixes of rows `s+1` and `s+2`.  We partition `T` into the values
which disappear at row `s+3` and those which survive a fourth prefix.

If the diagonal dips once more, its new value `z-1` is forced into the old
prefix and out of the new prefix.  Thus either `z-1` is itself a member of
the `T` packet, or it is an additional forbidden value and sharpens the
third-edge packing bound from `+3` to `+5`.

If the diagonal does not dip, every disappearing `T` value is below the new
diagonal.  Exact MEX then gives it a past diagonal owner.  Since it was
re-emitted on row `s+2`, it is high: `s+2 < v < z`.  The interval has exactly
`s-delta-4` available values, producing a new quantitative fourth-prefix
survivor inequality.
-/

noncomputable def EventEThirdMissingBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventETriplePrefixBandSlots s delta c b0).filter (fun g =>
    !(decide (gameF s g ∈ StrictRowPrefixValues gameF (s + 3))))

noncomputable def EventEFourPrefixBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventETriplePrefixBandSlots s delta c b0).filter (fun g =>
    decide (gameF s g ∈ StrictRowPrefixValues gameF (s + 3)))

/-- Third dip, with the next diagonal value already contained in `T`. -/
def EventEThirdDipPenultimateHitCertificate
    (s delta z c b0 : Nat) : Prop :=
  gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2) ∧
  (EventETriplePrefixBandSlots s delta c b0).length =
    (EventEFourPrefixBandSlots s delta c b0).length +
      (EventEThirdMissingBandSlots s delta c b0).length ∧
  2 * (EventEThirdMissingBandSlots s delta c b0).length + 3 <= s + 2 ∧
  delta + 4 <= s + (EventEFourPrefixBandSlots s delta c b0).length ∧
  exists g, g ∈ EventEThirdMissingBandSlots s delta c b0 ∧
    gameF s g = z - 1

/-- Third dip, with `z-1` outside `T`; it is then an extra forbidden value. -/
def EventEThirdDipExtraForbiddenCertificate
    (s delta z c b0 : Nat) : Prop :=
  gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2) ∧
  (EventETriplePrefixBandSlots s delta c b0).length =
    (EventEFourPrefixBandSlots s delta c b0).length +
      (EventEThirdMissingBandSlots s delta c b0).length ∧
  (forall g, g ∈ EventETriplePrefixBandSlots s delta c b0 ->
    gameF s g ≠ z - 1) ∧
  2 * (EventEThirdMissingBandSlots s delta c b0).length + 5 <= s + 2 ∧
  delta + 5 <= s + (EventEFourPrefixBandSlots s delta c b0).length

/-- No third dip.  Every loss is a high past-diagonal echo, so the whole
loss packet fits in the short value interval `(s+2,z)`. -/
def EventENonDipHighLossPacketCertificate
    (s delta z c b0 : Nat) : Prop :=
  Not (gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2)) ∧
  (EventETriplePrefixBandSlots s delta c b0).length =
    (EventEFourPrefixBandSlots s delta c b0).length +
      (EventEThirdMissingBandSlots s delta c b0).length ∧
  (EventEThirdMissingBandSlots s delta c b0).length + delta + 4 <= s ∧
  4 * delta + 15 <=
    3 * s + 2 * (EventEFourPrefixBandSlots s delta c b0).length ∧
  forall g, g ∈ EventEThirdMissingBandSlots s delta c b0 ->
    exists i b,
      i < s ∧ b < s + 2 ∧
      gameF i i = gameF s g ∧
      gameF (s + 2) b = gameF s g ∧
      s + 2 < gameF s g ∧ gameF s g < z

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

/-- Every nonmaximal cross-edge residual has one of three exhaustive
third-row outcomes: a penultimate hit, an extra forced forbidden value, or
a quantitatively bounded packet of high past-diagonal losses. -/
theorem gameF_nonmax_eventE_third_edge_propagation_trichotomy
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 ∧
      (EventEThirdDipPenultimateHitCertificate s delta z c b0 ∨
       EventEThirdDipExtraForbiddenCertificate s delta z c b0 ∨
       EventENonDipHighLossPacketCertificate s delta z c b0) := by
  classical
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change MarginEventECounterexample s ∧
      EventEDefectPacketInvariant s d delta z ∧
      delta + 5 <= s ∧
      exists c b0, EventECrossEdgeSurvivorCertificate s delta z c b0
    at hres
  rcases hres with ⟨hEvent, hInv, hnonmax, c, b0, hcross⟩
  rcases hEvent with ⟨hdip0, _hmargin, hdip1⟩

  let triple := EventETriplePrefixBandSlots s delta c b0
  let missing := EventEThirdMissingBandSlots s delta c b0
  let four := EventEFourPrefixBandSlots s delta c b0
  let missingValues := missing.map (fun g => gameF s g)
  let slots := EventEDefectBandSlots s delta c b0

  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hsurvivorsNodup :
      (EventESurvivingBandSlots s delta c b0).Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have htripleNodup : triple.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hmissingNodup : missing.Nodup :=
    List.filter_sublist.nodup htripleNodup

  have hmissingSlot : forall g, g ∈ missing -> g ∈ slots := by
    intro g hg
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    have hgSurvivor :
        g ∈ EventESurvivingBandSlots s delta c b0 :=
      (List.mem_filter.mp hgTriple).1
    exact (List.mem_filter.mp hgSurvivor).1
  have hmissingInRow2 : forall g, g ∈ missing ->
      gameF s g ∈ StrictRowPrefixValues gameF (s + 2) := by
    intro g hg
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    simpa [triple, EventETriplePrefixBandSlots] using
      (List.mem_filter.mp hgTriple).2
  have hmissingNotRow3 : forall g, g ∈ missing ->
      gameF s g ∉ StrictRowPrefixValues gameF (s + 3) := by
    intro g hg
    have hfilter := (List.mem_filter.mp hg).2
    simpa [missing, EventEThirdMissingBandSlots] using hfilter

  have hmissingValuesNodup : missingValues.Nodup := by
    apply r52_nodup_map_of_injective_on
      (fun g => gameF s g) missing hmissingNodup
    intro g hg k hk hEq
    have hgData := hslotsProps g (hmissingSlot g hg)
    have hkData := hslotsProps k (hmissingSlot k hk)
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hgData.1) (Nat.le_of_lt hkData.1) hEq
  have hmissingValuesSub : missingValues ⊆
      StrictRowPrefixValues gameF (s + 2) := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    exact hmissingInRow2 g hg
  have hmissingValuesAbsent : forall v, v ∈ missingValues ->
      v ∉ StrictRowPrefixValues gameF (s + 3) := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    exact hmissingNotRow3 g hg

  have hpartitionRaw := List.length_eq_countP_add_countP
    (fun g => decide
      (gameF s g ∈ StrictRowPrefixValues gameF (s + 3)))
    (l := triple)
  simp only [List.countP_eq_length_filter] at hpartitionRaw
  have hpartition : triple.length = four.length + missing.length := by
    simpa [four, missing, EventEFourPrefixBandSlots,
      EventEThirdMissingBandSlots] using hpartitionRaw

  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzDiag : z + 1 = d := hInv.2.2.2.1
  have hunit0 := hU s hdip0
  change d + 1 = gameF s s at hunit0
  have hdiag0 : gameF s s = z + 2 := by omega
  have hdiag1 : gameF (s + 1) (s + 1) = z + 1 := by omega
  have hunit1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hunit1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by omega
  have hglobal := hcross.2.2
  change 2 * delta + 7 <= s + 2 * triple.length at hglobal

  refine ⟨c, b0, hcross, ?_⟩
  by_cases hdip2 :
      gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2)
  · have hunit2 := hU (s + 2) hdip2
    have hdiag3 : gameF (s + 3) (s + 3) = z - 1 := by
      change gameF (s + 3) (s + 3) + 1 =
        gameF (s + 2) (s + 2) at hunit2
      have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
      change s + 3 < gameF (s + 3) (s + 3) at hgt
      omega
    have hbasicBound : 2 * missing.length + 3 <= s + 2 := by
      have h := game_adjacent_dip_forbidden_amortized_bound
        (q := s + 2) (forbidden := missingValues)
        (by simpa [Nat.add_assoc] using hdip2)
        hmissingValuesNodup hmissingValuesSub hmissingValuesAbsent
      simpa [missingValues] using h
    have hbasicFour : delta + 4 <= s + four.length := by
      omega
    by_cases hhit : exists g, g ∈ triple ∧ gameF s g = z - 1
    · rcases hhit with ⟨g, hgTriple, hgValue⟩
      have hgMissing : g ∈ missing := by
        apply List.mem_filter.mpr
        refine ⟨hgTriple, ?_⟩
        have hnot : gameF s g ∉
            StrictRowPrefixValues gameF (s + 3) := by
          rw [hgValue, ← hdiag3]
          exact diagonal_value_absent_strict_prefix
            gameRecurrenceModel (s + 3)
        simpa [missing, EventEThirdMissingBandSlots] using hnot
      left
      exact ⟨hdip2, hpartition, hbasicBound, hbasicFour,
        g, hgMissing, hgValue⟩
    · have hnohit : forall g, g ∈ triple -> gameF s g ≠ z - 1 := by
        intro g hg hEq
        exact hhit ⟨g, hg, hEq⟩
      have hspecialOld : z - 1 ∈
          StrictRowPrefixValues gameF (s + 2) := by
        have hzPredPos : 0 < z - 1 := by
          have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
          change s + 3 < gameF (s + 3) (s + 3) at hgt
          omega
        have hzPredBelow : z - 1 < gameF (s + 2) (s + 2) := by
          omega
        have hB : B gameF (s + 2) (s + 2) (z - 1) :=
          gameRecurrenceModel.mex_no_skip
            (Nat.le_refl (s + 2))
            (gameRecurrenceModel.diagonal_gt (s + 2))
            hzPredPos hzPredBelow
        rcases hB with hR | hC
        · rcases hR with ⟨a, ha, hvalue⟩
          have hmin : min a (s + 2) = a :=
            Nat.min_eq_left (Nat.le_of_lt ha)
          rw [hmin] at hvalue
          have hEqDiag : gameF a a = gameF (s + 3) (s + 3) := by
            exact hvalue.trans hdiag3.symm
          have hidx := diagonal_injective gameRecurrenceModel hEqDiag
          omega
        · exact mem_strictRowPrefixValues_iff_C.mpr hC
      have hspecialAbsent : z - 1 ∉
          StrictRowPrefixValues gameF (s + 3) := by
        rw [← hdiag3]
        exact diagonal_value_absent_strict_prefix
          gameRecurrenceModel (s + 3)
      let forbidden := missingValues ++ [z - 1]
      have hdisjoint : forall v, v ∈ missingValues ->
          forall w, w ∈ [z - 1] -> v ≠ w := by
        intro v hv w hw hEq
        simp only [List.mem_singleton] at hw
        rcases List.mem_map.mp hv with ⟨g, hg, hgv⟩
        have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
        apply hnohit g hgTriple
        exact hgv.trans (hEq.trans hw)
      have hforbiddenNodup : forbidden.Nodup :=
        List.nodup_append.mpr
          ⟨hmissingValuesNodup, by simp, hdisjoint⟩
      have hforbiddenSub : forbidden ⊆
          StrictRowPrefixValues gameF (s + 2) := by
        intro v hv
        rcases List.mem_append.mp hv with hvMissing | hvSpecial
        · exact hmissingValuesSub hvMissing
        · simp only [List.mem_singleton] at hvSpecial
          subst v
          exact hspecialOld
      have hforbiddenAbsent : forall v, v ∈ forbidden ->
          v ∉ StrictRowPrefixValues gameF (s + 3) := by
        intro v hv
        rcases List.mem_append.mp hv with hvMissing | hvSpecial
        · exact hmissingValuesAbsent v hvMissing
        · simp only [List.mem_singleton] at hvSpecial
          subst v
          exact hspecialAbsent
      have hsharpRaw := game_adjacent_dip_forbidden_amortized_bound
        (q := s + 2) (forbidden := forbidden)
        (by simpa [Nat.add_assoc] using hdip2)
        hforbiddenNodup hforbiddenSub hforbiddenAbsent
      have hsharp : 2 * missing.length + 5 <= s + 2 := by
        simpa [forbidden, missingValues] using hsharpRaw
      have hsharpFour : delta + 5 <= s + four.length := by
        omega
      right
      left
      exact ⟨hdip2, hpartition, hnohit, hsharp, hsharpFour⟩
  · have hzLeDiag3 : z <= gameF (s + 3) (s + 3) := by
      omega
    have hpacket : forall g, g ∈ missing ->
        exists i b,
          i < s ∧ b < s + 2 ∧
          gameF i i = gameF s g ∧
          gameF (s + 2) b = gameF s g ∧
          s + 2 < gameF s g ∧ gameF s g < z := by
      intro g hg
      have hgData := hslotsProps g (hmissingSlot g hg)
      have htransition := hgData.2.2.2
      have hvPos : 0 < gameF s g := by
        simpa [EventELowerTransition] using htransition.1
      have hvBelowZ : gameF s g < z := by
        simpa [EventELowerTransition] using htransition.2.1
      have hvBelow3 : gameF s g < gameF (s + 3) (s + 3) := by
        omega
      have hvNot3 := hmissingNotRow3 g hg
      rcases old_diagonal_mex_backfill_has_past_owner
          gameRecurrenceModel hvPos hvBelow3 hvNot3 with
        ⟨i, hi3, howner⟩
      change gameF i i = gameF s g at howner
      have hi : i < s := by
        by_cases his : i < s
        · exact his
        · have hicases : i = s ∨ i = s + 1 ∨ i = s + 2 := by omega
          rcases hicases with hi0 | hi1 | hi2
          · rw [hi0, hdiag0] at howner
            omega
          · rw [hi1, hdiag1] at howner
            omega
          · rw [hi2, hdiag2] at howner
            omega
      rcases mem_strictRowPrefixValues_iff_C.mp
          (hmissingInRow2 g hg) with ⟨b, hb, hhost⟩
      have hhigh := game_past_diagonal_reemission_is_high
        (i := i) (t := s + 2) (b := b)
        (Nat.le_of_lt hb) (howner.trans hhost.symm)
      rw [howner] at hhigh
      exact ⟨i, b, hi, hb, howner, hhost, hhigh, hvBelowZ⟩
    have hzWindow : s + 3 <= z := by omega
    have hvalueInterval : missingValues ⊆
        List.range' (s + 3) (z - (s + 3)) := by
      intro v hv
      rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
      rcases hpacket g hg with
        ⟨_i, _b, _hi, _hb, _howner, _hhost, hhigh, hvBelowZ⟩
      apply List.mem_range'_1.mpr
      constructor <;> omega
    have hintervalCap :=
      nodup_subset_length_le hmissingValuesNodup hvalueInterval
    have hlossBound : missing.length + delta + 4 <= s := by
      have hintervalCap' : missing.length <= z - (s + 3) := by
        simpa [missingValues] using hintervalCap
      omega
    have hfourBound :
        4 * delta + 15 <= 3 * s + 2 * four.length := by
      omega
    right
    right
    exact ⟨hdip2, hpartition, hlossBound, hfourBound, hpacket⟩

/-- In the no-dip branch, defect above the `3/4` threshold forces a
concrete value to survive in all four strict prefixes. -/
theorem eventE_nonDip_high_defect_forces_four_prefix_value
    {s delta z c b0 : Nat}
    (hcert : EventENonDipHighLossPacketCertificate s delta z c b0)
    (hlarge : 3 * s < 4 * delta + 15) :
    exists g, g ∈ EventEFourPrefixBandSlots s delta c b0 := by
  have hbound := hcert.2.2.2.1
  have hpos : 0 <
      (EventEFourPrefixBandSlots s delta c b0).length := by
    omega
  have hne : EventEFourPrefixBandSlots s delta c b0 ≠ [] := by
    intro hnil
    rw [hnil] at hpos
    simp at hpos
  exact List.exists_mem_of_ne_nil _ hne

#print axioms gameF_nonmax_eventE_third_edge_propagation_trichotomy
#print axioms eventE_nonDip_high_defect_forces_four_prefix_value

end ChompLean
