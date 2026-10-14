import R55BoundaryGlobalGeometry
import R55OverlapLedgerEventEEchoStaircase

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace ChompLean

/-!
R55: connect the global boundary echo cascade to the exact overlap ledger.

The key new point is chronological rather than another cardinal rewrite.
A value hosted in two consecutive strict prefixes, and different from the
old diagonal, has the same past-diagonal/fresh status on both rows.  The two
echoes forced by the wide boundary are therefore *persistent*: they cannot
be the values responsible for the `+2` jump in the overlap ledger.  Each
edge must create at least two additional, genuinely new diagonal echoes.
-/

/-- Echoes which occur in row `t+1` but not in row `t`. -/
noncomputable def NewPastDiagonalEchoValues (t : Nat) : List Nat :=
  (PastDiagonalEchoValues (t + 1)).filter (fun v =>
    !(decide (v ∈ PastDiagonalEchoValues t)))

theorem newPastDiagonalEchoValues_nodup (t : Nat) :
    (NewPastDiagonalEchoValues t).Nodup := by
  exact List.filter_sublist.nodup
    (List.filter_sublist.nodup
      (strictRowPrefixValues_nodup gameRecurrenceModel (t + 1)))

/-- A cardinal increase of `k` in the echo ledger creates at least `k`
new values.  Old echoes may disappear, so this statement is strictly
stronger than merely subtracting the two displayed cardinalities. -/
theorem new_past_diagonal_echo_length_of_growth
    {t k : Nat}
    (hgrowth : (PastDiagonalEchoValues t).length + k <=
      (PastDiagonalEchoValues (t + 1)).length) :
    k <= (NewPastDiagonalEchoValues t).length := by
  let old := PastDiagonalEchoValues t
  let next := PastDiagonalEchoValues (t + 1)
  let kept := next.filter (fun v => decide (v ∈ old))
  let fresh := next.filter (fun v => !(decide (v ∈ old)))
  have hpartRaw := List.length_eq_countP_add_countP
    (fun v => decide (v ∈ old)) (l := next)
  simp only [List.countP_eq_length_filter] at hpartRaw
  have hpart : next.length = kept.length + fresh.length := by
    simpa [kept, fresh] using hpartRaw
  have hkeptNodup : kept.Nodup := by
    exact List.filter_sublist.nodup
      (List.filter_sublist.nodup
        (strictRowPrefixValues_nodup gameRecurrenceModel (t + 1)))
  have hkeptSub : kept ⊆ old := by
    intro v hv
    have hvFilter := (List.mem_filter.mp hv).2
    simpa [kept, old] using hvFilter
  have hcap := nodup_subset_length_le hkeptNodup hkeptSub
  change old.length + k <= next.length at hgrowth
  change k <= fresh.length
  omega

/-- A value carried by two consecutive strict prefixes cannot switch
between `fresh` and `past-diagonal echo` unless the intervening old
diagonal itself owns that value. -/
theorem past_diagonal_echo_membership_stable_of_two_hosts
    {t v b0 b1 : Nat}
    (hb0 : b0 < t) (hb1 : b1 < t + 1)
    (hhost0 : gameF t b0 = v)
    (hhost1 : gameF (t + 1) b1 = v)
    (hvBelow0 : v < gameF t t)
    (hvBelow1 : v < gameF (t + 1) (t + 1))
    (hnotOldDiag : gameF t t ≠ v) :
    v ∈ PastDiagonalEchoValues t <->
      v ∈ PastDiagonalEchoValues (t + 1) := by
  constructor
  · intro hvOld
    have hvData := List.mem_filter.mp hvOld
    have hvPast : v ∈ PastLowerDiagonalValues t := by
      simpa [PastDiagonalEchoValues] using hvData.2
    rcases mem_pastLowerDiagonalValues_iff.mp hvPast with
      ⟨i, hit, hiOwner, _hvlt⟩
    apply List.mem_filter.mpr
    constructor
    · exact mem_strictRowPrefixValues_iff_C.mpr
        ⟨b1, hb1, hhost1⟩
    · have hvPastNext : v ∈ PastLowerDiagonalValues (t + 1) :=
        mem_pastLowerDiagonalValues_iff.mpr
          ⟨i, by omega, hiOwner, hvBelow1⟩
      simpa [PastDiagonalEchoValues] using hvPastNext
  · intro hvNext
    have hvData := List.mem_filter.mp hvNext
    have hvPast : v ∈ PastLowerDiagonalValues (t + 1) := by
      simpa [PastDiagonalEchoValues] using hvData.2
    rcases mem_pastLowerDiagonalValues_iff.mp hvPast with
      ⟨i, hiNext, hiOwner, _hvlt⟩
    have hit : i < t := by
      apply Nat.lt_of_not_ge
      intro hge
      have hiEq : i = t := by omega
      subst i
      exact hnotOldDiag hiOwner
    apply List.mem_filter.mpr
    constructor
    · exact mem_strictRowPrefixValues_iff_C.mpr
        ⟨b0, hb0, hhost0⟩
    · have hvPastOld : v ∈ PastLowerDiagonalValues t :=
        mem_pastLowerDiagonalValues_iff.mpr
          ⟨i, hit, hiOwner, hvBelow0⟩
      simpa [PastDiagonalEchoValues] using hvPastOld

/-- A ledger-stable carried value is not one of the genuinely new echoes
on that edge. -/
theorem stable_echo_not_mem_new
    {t v : Nat}
    (hstable : v ∈ PastDiagonalEchoValues t <->
      v ∈ PastDiagonalEchoValues (t + 1)) :
    v ∉ NewPastDiagonalEchoValues t := by
  intro hvNew
  have hvData := List.mem_filter.mp hvNew
  have hvNext : v ∈ PastDiagonalEchoValues (t + 1) := hvData.1
  have hvNotOld : v ∉ PastDiagonalEchoValues t := by
    simpa [NewPastDiagonalEchoValues] using hvData.2
  exact hvNotOld (hstable.mpr hvNext)

/-- Bounded version of the R54 chronology normal form.  The original
normal form retained the sharp lower bounds but did not expose the host
upper bounds already present in the boundary certificate.  Those bounds
are needed when the chronology is charged against row injectivity and the
overlap ledger. -/
def EventEThirdDipBoundedChronologyCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBoundarySaturationCertificate s delta z c b0 /\
  exists g b1 b2,
    g = s - delta - 3 /\
    g < s /\ b1 < s + 1 /\ b2 < s + 2 /\
    3 <= g /\ g - 1 <= b1 /\ g - 2 <= b2 /\
    g ≠ b1 /\ b1 ≠ b2 /\ g ≠ b2 /\
    gameF s g = z - 1 /\
    gameF (s + 1) b1 = z - 1 /\
    gameF (s + 2) b2 = z - 1 /\
    IsMex (B gameF s g) (z - 1) /\
    IsMex (B gameF (s + 1) b1) (z - 1) /\
    IsMex (B gameF (s + 2) b2) (z - 1) /\
    (WideBoundarySouthwestExactChain s (z - 1) g b1 b2 \/
      WideBoundaryRightEscape s (z - 1) g b1 b2)

theorem eventE_third_dip_boundary_bounded_chronology_normal_form
    {s delta z c b0 : Nat}
    (hcert : EventEThirdDipBoundarySaturationCertificate
      s delta z c b0) :
    EventEThirdDipBoundedChronologyCertificate s delta z c b0 := by
  have hcertFull := hcert
  rcases hcert with
    ⟨_hextra, hstair, _hlast, _hweighted, _hfour,
      g, b1, b2, hgEq, hg, hb1, hb2,
      hhost0, hhost1, hhost2, hgb1, hb1b2, hgb2,
      hcapacity, hsat0⟩
  rcases hstair with
    ⟨_hdeltaSix, _hdiag0, _hdiag1, _hdiag2, hdiag3, _hhosts⟩
  have hgThree : 3 <= g := by omega
  have hpHigh3 : s + 3 < z - 1 := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    rw [hdiag3] at hgt
    exact hgt
  have hmex0 : IsMex (B gameF s g) (z - 1) :=
    gameF_high_cell_exact_mex (Nat.le_of_lt hg) (by omega) hhost0
  have hmex1 : IsMex (B gameF (s + 1) b1) (z - 1) :=
    gameF_high_cell_exact_mex (Nat.le_of_lt hb1) (by omega) hhost1
  have hmex2 : IsMex (B gameF (s + 2) b2) (z - 1) :=
    gameF_high_cell_exact_mex (Nat.le_of_lt hb2) (by omega) hhost2
  have hcap1 := high_cell_output_source_capacity
    gameRecurrenceModel (q := s + 1) (r := b1) (m := z - 1)
      (Nat.le_of_lt hb1) (by omega) hhost1
  have hcap2 := high_cell_output_source_capacity
    gameRecurrenceModel (q := s + 2) (r := b2) (m := z - 1)
      (Nat.le_of_lt hb2) (by omega) hhost2
  have hb1Lower : g - 1 <= b1 := by omega
  have hb2Lower : g - 2 <= b2 := by omega
  refine ⟨hcertFull, g, b1, b2, hgEq, hg, hb1, hb2,
    hgThree, hb1Lower, hb2Lower, hgb1, hb1b2, hgb2,
    hhost0, hhost1, hhost2, hmex0, hmex1, hmex2, ?_⟩
  by_cases hb1Exact : b1 + 1 = g
  · by_cases hb2Exact : b2 + 2 = g
    · left
      have hperm0 := lowerSaturated_exact_source_perm hsat0 hcapacity
      have hsat1 : LowerSaturated gameF (s + 1) b1 (z - 1) :=
        hmex1.2.2
      have hsat2 : LowerSaturated gameF (s + 2) b2 (z - 1) :=
        hmex2.2.2
      have hcapExact1 : (z - 1) - 1 = (s + 1) + b1 := by omega
      have hcapExact2 : (z - 1) - 1 = (s + 2) + b2 := by omega
      have hperm1 := lowerSaturated_exact_source_perm hsat1 hcapExact1
      have hperm2 := lowerSaturated_exact_source_perm hsat2 hcapExact2
      exact ⟨hgThree, hb1Exact, hb2Exact,
        hhost0, hhost1, hhost2, hmex0, hmex1, hmex2,
        hperm0, hperm1, hperm2⟩
    · right
      right
      exact ⟨by omega, by omega⟩
  · right
    left
    exact ⟨by omega, by omega⟩

/-- The integrated ledger certificate attached to every wide boundary
atom.  Besides the exact four ledger values and the global envelope budget,
it records two persistent forced echoes and three separate `>=2` new-echo
charges. -/
def EventEThirdDipBoundaryPersistentEchoLedgerCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBoundarySaturationCertificate s delta z c b0 /\
  StrictRowEchoCount s = delta /\
  StrictRowEchoCount (s + 1) = delta + 2 /\
  StrictRowEchoCount (s + 2) = delta + 4 /\
  StrictRowEchoCount (s + 3) = delta + 6 /\
  2 * delta + 15 <= s /\
  2 <= (NewPastDiagonalEchoValues s).length /\
  2 <= (NewPastDiagonalEchoValues (s + 1)).length /\
  2 <= (NewPastDiagonalEchoValues (s + 2)).length /\
  exists g b1 b2 a1 a2,
    g = s - delta - 3 /\
    gameF s g = z - 1 /\
    gameF (s + 1) b1 = z - 1 /\
    gameF (s + 2) b2 = z - 1 /\
    a1 < b1 /\ a2 < b2 /\
    gameF (s + 2) b1 = gameF (s + 1) a1 /\
    gameF (s + 3) b2 = gameF (s + 2) a2 /\
    s + 1 < gameF (s + 2) b1 /\
    gameF (s + 2) b1 < z - 1 /\
    s + 2 < gameF (s + 3) b2 /\
    gameF (s + 3) b2 < z - 1 /\
    (gameF (s + 2) b1 ∈ PastDiagonalEchoValues (s + 1) <->
      gameF (s + 2) b1 ∈ PastDiagonalEchoValues (s + 2)) /\
    (gameF (s + 3) b2 ∈ PastDiagonalEchoValues (s + 2) <->
      gameF (s + 3) b2 ∈ PastDiagonalEchoValues (s + 3)) /\
    gameF (s + 2) b1 ∉ NewPastDiagonalEchoValues (s + 1) /\
    gameF (s + 3) b2 ∉ NewPastDiagonalEchoValues (s + 2) /\
    WideBoundaryDoublePrefixEcho s (z - 1) b1 b2

/-- Every nonmaximal event-E boundary atom satisfies the persistent echo
ledger certificate. -/
theorem gameF_nonmax_eventE_boundary_persistent_echo_ledger
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    forall {c b0},
      EventEThirdDipBoundarySaturationCertificate s delta z c b0 ->
      EventEThirdDipBoundaryPersistentEchoLedgerCertificate
        s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro c b0 hcert
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\ _ at hresData
  rcases hresData.1 with ⟨hdip0, hmargin, hdip1⟩
  have hdip2 : gameF (s + 3) (s + 3) <
      gameF (s + 2) (s + 2) := hcert.1.1
  have hW012 := gameF_margin_eventE_overlap_echo_staircase
    hU hdip0 hmargin hdip1
  change StrictRowEchoCount s = delta /\
      StrictRowEchoCount (s + 1) = delta + 2 /\
      StrictRowEchoCount (s + 2) = delta + 4 at hW012
  have hW3 := gameF_margin_eventE_third_dip_overlap_echo
    hU hdip0 hmargin hdip1 hdip2
  change StrictRowEchoCount (s + 3) = delta + 6 at hW3
  have henv := gameF_margin_eventE_third_dip_env_defect_bound
    hU hdip0 hmargin hdip1 hdip2
  change delta + (s + 4) / 2 + 6 <= s /\
      2 * delta + 15 <= s at henv
  have hnew0 : 2 <= (NewPastDiagonalEchoValues s).length := by
    apply new_past_diagonal_echo_length_of_growth
    simpa [StrictRowEchoCount] using (show
      StrictRowEchoCount s + 2 <= StrictRowEchoCount (s + 1) by omega)
  have hnew1 : 2 <=
      (NewPastDiagonalEchoValues (s + 1)).length := by
    apply new_past_diagonal_echo_length_of_growth
    simpa [StrictRowEchoCount] using (show
      StrictRowEchoCount (s + 1) + 2 <=
        StrictRowEchoCount (s + 2) by omega)
  have hnew2 : 2 <=
      (NewPastDiagonalEchoValues (s + 2)).length := by
    apply new_past_diagonal_echo_length_of_growth
    simpa [StrictRowEchoCount] using (show
      StrictRowEchoCount (s + 2) + 2 <=
        StrictRowEchoCount (s + 3) by omega)
  have hdouble := eventE_third_dip_boundary_forces_double_prefix_echo hcert
  rcases hdouble with
    ⟨g, b1, b2, hgEq, hg, hb1, hb2,
      hhost0, hhost1, hhost2, hdouble⟩
  have hdoubleFull := hdouble
  rcases hdouble with
    ⟨a1, a2, ha1, ha2, heq1, heq2,
      hlo1, hhi1, hlo2, hhi2, _habs1, _habs2, _hcollision⟩
  have hstair := hcert.2.1
  rcases hstair with
    ⟨_hdeltaSix, _hdiag0, hdiag1, hdiag2, hdiag3, _hhosts⟩
  have hstable1 :
      gameF (s + 2) b1 ∈ PastDiagonalEchoValues (s + 1) <->
        gameF (s + 2) b1 ∈ PastDiagonalEchoValues (s + 2) := by
    apply past_diagonal_echo_membership_stable_of_two_hosts
      (t := s + 1) (v := gameF (s + 2) b1)
      (b0 := a1) (b1 := b1) (by omega) (by omega) heq1.symm rfl
    · rw [hdiag1]
      omega
    · rw [hdiag2]
      omega
    · rw [hdiag1]
      omega
  have hstable2 :
      gameF (s + 3) b2 ∈ PastDiagonalEchoValues (s + 2) <->
        gameF (s + 3) b2 ∈ PastDiagonalEchoValues (s + 3) := by
    apply past_diagonal_echo_membership_stable_of_two_hosts
      (t := s + 2) (v := gameF (s + 3) b2)
      (b0 := a2) (b1 := b2) (by omega) (by omega) heq2.symm rfl
    · rw [hdiag2]
      omega
    · rw [hdiag3]
      exact hhi2
    · rw [hdiag2]
      omega
  have hnotNew1 :
      gameF (s + 2) b1 ∉ NewPastDiagonalEchoValues (s + 1) :=
    stable_echo_not_mem_new hstable1
  have hnotNew2 :
      gameF (s + 3) b2 ∉ NewPastDiagonalEchoValues (s + 2) :=
    stable_echo_not_mem_new hstable2
  exact ⟨hcert, hW012.1, hW012.2.1, hW012.2.2,
    hW3, henv.2, hnew0, hnew1, hnew2,
    g, b1, b2, a1, a2, hgEq, hhost0, hhost1, hhost2,
    ha1, ha2, heq1, heq2, hlo1, hhi1, hlo2, hhi2,
    hstable1, hstable2, hnotNew1, hnotNew2, hdoubleFull⟩

/-- Final R55 boundary terminal.  The south-west branch now carries two
distinct persistent echoes plus a named strict horizontal source loss; the
right-escape branch carries its own double persistent-echo certificate.
Both branches sit on top of the exact ledger/new-echo core. -/
def EventEThirdDipBoundaryEchoLedgerTerminal
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBoundaryPersistentEchoLedgerCertificate s delta z c b0 /\
  EventEThirdDipBoundedChronologyCertificate s delta z c b0 /\
  ((exists g b1 b2,
      g = s - delta - 3 /\
      g < s /\ b1 < s + 1 /\ b2 < s + 2 /\
      WideBoundarySouthwestExactChain s (z - 1) g b1 b2 /\
      WideBoundarySouthwestDistinctEchoCascade s (z - 1) b1 b2 /\
      WideBoundarySouthwestFirstEchoLoss s (z - 1) b1 b2) \/
    (exists g b1 b2,
      g = s - delta - 3 /\
      g < s /\ b1 < s + 1 /\ b2 < s + 2 /\
      WideBoundaryRightEscape s (z - 1) g b1 b2 /\
      WideBoundaryDoublePrefixEcho s (z - 1) b1 b2))

theorem gameF_nonmax_eventE_boundary_echo_ledger_terminal
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    forall {c b0},
      EventEThirdDipBoundarySaturationCertificate s delta z c b0 ->
      EventEThirdDipBoundaryEchoLedgerTerminal s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro c b0 hcert
  have hcore := gameF_nonmax_eventE_boundary_persistent_echo_ledger
    hU hres hcert
  have hbounded :=
    eventE_third_dip_boundary_bounded_chronology_normal_form hcert
  have hstair := hcert.2.1
  rcases hstair with
    ⟨_hdeltaSix, _hdiag0, _hdiag1, hdiag2, hdiag3, _hhosts⟩
  have hboundedData := hbounded.2
  rcases hboundedData with
    ⟨g, b1, b2, hgEq, hg, hb1, hb2,
      _hgThree, _hb1Lower, _hb2Lower,
      _hgb1, _hb1b2, _hgb2,
      _hhost0, hhost1, hhost2,
      _hmex0, _hmex1, _hmex2, hsplit⟩
  refine ⟨hcore, hbounded, ?_⟩
  rcases hsplit with hchain | hescape
  · left
    have hcascade :=
      wideBoundary_southwest_chain_forces_distinct_echo_cascade
        hchain hg hb1 hb2 hdiag2 hdiag3
    have hloss :=
      wideBoundary_southwest_chain_first_echo_is_strict_source_loss
        hchain hg hb1 hdiag2 hdiag3
    exact ⟨g, b1, b2, hgEq, hg, hb1, hb2,
      hchain, hcascade, hloss⟩
  · right
    have hdoubleRaw :=
      eventE_third_dip_boundary_forces_double_prefix_echo hcert
    rcases hdoubleRaw with
      ⟨gx, bx1, bx2, _hgEqx, _hgx, hbx1, hbx2,
        _hhost0x, hhost1x, hhost2x, hdouble⟩
    have hb1Eq : b1 = bx1 :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hb1) (Nat.le_of_lt hbx1)
        (hhost1.trans hhost1x.symm)
    have hb2Eq : b2 = bx2 :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hb2) (Nat.le_of_lt hbx2)
        (hhost2.trans hhost2x.symm)
    subst bx1
    subst bx2
    exact ⟨g, b1, b2, hgEq, hg, hb1, hb2,
      hescape, hdouble⟩

#print axioms new_past_diagonal_echo_length_of_growth
#print axioms past_diagonal_echo_membership_stable_of_two_hosts
#print axioms stable_echo_not_mem_new
#print axioms eventE_third_dip_boundary_bounded_chronology_normal_form
#print axioms gameF_nonmax_eventE_boundary_persistent_echo_ledger
#print axioms gameF_nonmax_eventE_boundary_echo_ledger_terminal

end ChompLean
