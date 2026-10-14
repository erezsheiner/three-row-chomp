import R54EventEFifthEdgeSharedOwnerPropagation

set_option autoImplicit false

namespace ChompLean

/-!
Exact fourth-edge continuation of the R53 four-prefix atom.  A dip either
hits the next diagonal value inside the packet, or contributes that value
as one extra forbidden source.  With no dip, R54's shared-owner theorem
absorbs the whole loss packet and propagates the original inequality to the
five-prefix packet.
-/

def EventEFourthDipPacketHitCertificate
    (s delta z c b0 : Nat) : Prop :=
  gameF (s + 4) (s + 4) < gameF (s + 3) (s + 3) ∧
  EventEFifthEdgeFrozenCarryCertificate s delta z c b0 ∧
  2 * (EventEFourthMissingBandSlots s delta c b0).length + 3 <= s + 3 ∧
  ∃ g, g ∈ EventEFourthMissingBandSlots s delta c b0 ∧
    gameF s g = gameF (s + 4) (s + 4)

def EventEFourthDipExtraForbiddenCertificate
    (s delta z c b0 : Nat) : Prop :=
  gameF (s + 4) (s + 4) < gameF (s + 3) (s + 3) ∧
  EventEFifthEdgeFrozenCarryCertificate s delta z c b0 ∧
  (∀ g, g ∈ EventEFourPrefixBandSlots s delta c b0 ->
    gameF s g ≠ gameF (s + 4) (s + 4)) ∧
  2 * (EventEFourthMissingBandSlots s delta c b0).length + 5 <= s + 3

private theorem r54c_nodup_map_of_injective_on
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

/-- The R53 no-dip/four-prefix branch has an exhaustive fourth-edge
trichotomy: packet hit, extra forbidden value, or five-prefix shared-owner
propagation. -/
theorem gameF_nonmax_eventE_fourth_edge_trichotomy
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hcert : EventENonDipSharedOwnerSaturationCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventEFourthDipPacketHitCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0 ∨
    EventEFourthDipExtraForbiddenCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0 ∨
    EventENoFourthDipFivePrefixSharedOwnerCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0 := by
  classical
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipSharedOwnerSaturationCertificate
    s delta z c b0 at hcert
  have hfrozen := gameF_nonmax_eventE_four_prefix_fifth_edge_freeze
    (s := s) (c := c) (b0 := b0) hres hcross hcert
  change EventEFifthEdgeFrozenCarryCertificate s delta z c b0 at hfrozen
  by_cases hdip3 :
      gameF (s + 4) (s + 4) < gameF (s + 3) (s + 3)
  · let four := EventEFourPrefixBandSlots s delta c b0
    let missing := EventEFourthMissingBandSlots s delta c b0
    let missingValues := missing.map (fun g => gameF s g)
    have hbase := hcross.1.1.1
    rcases hbase with
      ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
        hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
    have hsurvivorsNodup :
        (EventESurvivingBandSlots s delta c b0).Nodup :=
      List.filter_sublist.nodup hslotsNodup
    have htripleNodup :
        (EventETriplePrefixBandSlots s delta c b0).Nodup :=
      List.filter_sublist.nodup hsurvivorsNodup
    have hfourNodup : four.Nodup :=
      List.filter_sublist.nodup htripleNodup
    have hmissingNodup : missing.Nodup :=
      List.filter_sublist.nodup hfourNodup
    have hmissingFour : ∀ g, g ∈ missing -> g ∈ four := by
      intro g hg
      exact (List.mem_filter.mp hg).1
    have hmissingSlots : ∀ g, g ∈ missing ->
        g ∈ EventEDefectBandSlots s delta c b0 := by
      intro g hg
      have hgFour := hmissingFour g hg
      have hgTriple : g ∈ EventETriplePrefixBandSlots s delta c b0 :=
        (List.mem_filter.mp hgFour).1
      have hgSurv : g ∈ EventESurvivingBandSlots s delta c b0 :=
        (List.mem_filter.mp hgTriple).1
      exact (List.mem_filter.mp hgSurv).1
    have hmissingValuesNodup : missingValues.Nodup := by
      apply r54c_nodup_map_of_injective_on
        (fun g => gameF s g) missing hmissingNodup
      intro g hg k hk hEq
      have hgData := hslotsProps g (hmissingSlots g hg)
      have hkData := hslotsProps k (hmissingSlots k hk)
      exact gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hgData.1) (Nat.le_of_lt hkData.1) hEq
    have hmissingValuesSub : missingValues ⊆
        StrictRowPrefixValues gameF (s + 3) := by
      intro v hv
      rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
      have hgFour := hmissingFour g hg
      have hfilter := (List.mem_filter.mp hgFour).2
      simpa [four, EventEFourPrefixBandSlots] using hfilter
    have hmissingValuesAbsent : ∀ v, v ∈ missingValues ->
        v ∉ StrictRowPrefixValues gameF (s + 4) := by
      intro v hv
      rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing, EventEFourthMissingBandSlots] using hfilter
    have hbasicRaw := game_adjacent_dip_forbidden_amortized_bound
      (q := s + 3) (forbidden := missingValues)
      (by simpa [Nat.add_assoc] using hdip3)
      hmissingValuesNodup hmissingValuesSub hmissingValuesAbsent
    have hbasic : 2 * missing.length + 3 <= s + 3 := by
      simpa [missingValues] using hbasicRaw

    have hspecialOld : gameF (s + 4) (s + 4) ∈
        StrictRowPrefixValues gameF (s + 3) := by
      have hwPos : 0 < gameF (s + 4) (s + 4) := by
        have hgt := gameRecurrenceModel.diagonal_gt (s + 4)
        change s + 4 < gameF (s + 4) (s + 4) at hgt
        omega
      have hB : B gameF (s + 3) (s + 3)
          (gameF (s + 4) (s + 4)) :=
        gameRecurrenceModel.mex_no_skip
          (Nat.le_refl (s + 3))
          (gameRecurrenceModel.diagonal_gt (s + 3))
          hwPos hdip3
      rcases hB with hR | hC
      · rcases hR with ⟨a, ha, hvalue⟩
        have hmin : min a (s + 3) = a :=
          Nat.min_eq_left (Nat.le_of_lt ha)
        rw [hmin] at hvalue
        have hidx := diagonal_injective gameRecurrenceModel hvalue
        omega
      · exact mem_strictRowPrefixValues_iff_C.mpr hC
    have hspecialAbsent : gameF (s + 4) (s + 4) ∉
        StrictRowPrefixValues gameF (s + 4) :=
      diagonal_value_absent_strict_prefix
        gameRecurrenceModel (s + 4)

    by_cases hhit : ∃ g, g ∈ four ∧
        gameF s g = gameF (s + 4) (s + 4)
    · rcases hhit with ⟨g, hgFour, hgValue⟩
      have hgMissing : g ∈ missing := by
        apply List.mem_filter.mpr
        refine ⟨hgFour, ?_⟩
        have hnot : gameF s g ∉
            StrictRowPrefixValues gameF (s + 4) := by
          rw [hgValue]
          exact hspecialAbsent
        simpa [missing, EventEFourthMissingBandSlots] using hnot
      left
      have hresult : EventEFourthDipPacketHitCertificate
          s delta z c b0 :=
        ⟨hdip3, hfrozen, hbasic, g, hgMissing, hgValue⟩
      simpa [delta, z, d] using hresult
    · have hnohit : ∀ g, g ∈ four ->
          gameF s g ≠ gameF (s + 4) (s + 4) := by
        intro g hg hEq
        exact hhit ⟨g, hg, hEq⟩
      let forbidden := missingValues ++ [gameF (s + 4) (s + 4)]
      have hdisjoint : ∀ v, v ∈ missingValues ->
          ∀ w, w ∈ [gameF (s + 4) (s + 4)] -> v ≠ w := by
        intro v hv w hw hEq
        simp only [List.mem_singleton] at hw
        rcases List.mem_map.mp hv with ⟨g, hg, hgv⟩
        apply hnohit g (hmissingFour g hg)
        exact hgv.trans (hEq.trans hw)
      have hforbiddenNodup : forbidden.Nodup :=
        List.nodup_append.mpr
          ⟨hmissingValuesNodup, by simp, hdisjoint⟩
      have hforbiddenSub : forbidden ⊆
          StrictRowPrefixValues gameF (s + 3) := by
        intro v hv
        rcases List.mem_append.mp hv with hvMissing | hvSpecial
        · exact hmissingValuesSub hvMissing
        · simp only [List.mem_singleton] at hvSpecial
          subst v
          exact hspecialOld
      have hforbiddenAbsent : ∀ v, v ∈ forbidden ->
          v ∉ StrictRowPrefixValues gameF (s + 4) := by
        intro v hv
        rcases List.mem_append.mp hv with hvMissing | hvSpecial
        · exact hmissingValuesAbsent v hvMissing
        · simp only [List.mem_singleton] at hvSpecial
          subst v
          exact hspecialAbsent
      have hsharpRaw := game_adjacent_dip_forbidden_amortized_bound
        (q := s + 3) (forbidden := forbidden)
        (by simpa [Nat.add_assoc] using hdip3)
        hforbiddenNodup hforbiddenSub hforbiddenAbsent
      have hsharp : 2 * missing.length + 5 <= s + 3 := by
        simpa [forbidden, missingValues] using hsharpRaw
      right
      left
      have hresult : EventEFourthDipExtraForbiddenCertificate
          s delta z c b0 :=
        ⟨hdip3, hfrozen, hnohit, hsharp⟩
      simpa [delta, z, d] using hresult
  · right
    right
    exact gameF_nonmax_eventE_no_fourth_dip_five_prefix_shared_owner
      hU (s := s) (c := c) (b0 := b0)
      hres hcross hcert hdip3

/-- The form used by the high-defect R53 atom.  The numerical hypothesis
which originally selected a four-prefix value is deliberately retained;
in the no-dip branch it now selects a concrete five-prefix value. -/
theorem gameF_nonmax_eventE_high_four_prefix_R54_atoms
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hcert : EventENonDipSharedOwnerSaturationCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hlarge : s <
      2 * (2 * s - gameF (s + 1) (s + 1)) + 7) :
    EventEFourthDipPacketHitCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0 ∨
    EventEFourthDipExtraForbiddenCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0 ∨
    (EventENoFourthDipFivePrefixSharedOwnerCertificate
        s (2 * s - gameF (s + 1) (s + 1))
          (gameF (s + 1) (s + 1) - 1) c b0 ∧
      ∃ g, g ∈ EventEFivePrefixBandSlots
        s (2 * s - gameF (s + 1) (s + 1)) c b0) := by
  have htri := gameF_nonmax_eventE_fourth_edge_trichotomy
    hU (s := s) (c := c) (b0 := b0) hres hcross hcert
  rcases htri with hHit | hExtra | hNoDip
  · exact Or.inl hHit
  · exact Or.inr (Or.inl hExtra)
  · have hfive :=
      eventE_no_fourth_dip_high_defect_forces_five_prefix_value
        hNoDip hlarge
    exact Or.inr (Or.inr ⟨hNoDip, hfive⟩)

#print axioms gameF_nonmax_eventE_fourth_edge_trichotomy
#print axioms gameF_nonmax_eventE_high_four_prefix_R54_atoms

end ChompLean
