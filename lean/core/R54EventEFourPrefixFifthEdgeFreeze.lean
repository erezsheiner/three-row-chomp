import R53NonmaxEventENonDipSharedOwnerSaturation

set_option autoImplicit false

namespace ChompLean

/-!
R54: propagate the concrete four-prefix survivor through one further row.

There is a useful asymmetry at the fourth edge which does not require a
case split on the next diagonal.  A value already hosted in the strict
prefix of row `s+3` cannot disappear on row `s+4` while it is below
`s+4`: the constant branch copies the very same host.  Consequently every
fourth-edge loss lies in the short value interval `[s+4,z)`.

We record both the pointwise host/freeze geometry and its cardinal
consequence.  The latter upgrades the R53 inequality

  `2*delta+7 <= s+2*|Q|`

to

  `4*delta+17 <= 3*s+2*|Q5|`,

where `Q5` is the packet surviving all five strict prefixes.
-/

/-- Members of the four-prefix packet which disappear from the strict
prefix of row `s+4`. -/
noncomputable def EventEFourthMissingBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventEFourPrefixBandSlots s delta c b0).filter (fun g =>
    !(decide (gameF s g ∈ StrictRowPrefixValues gameF (s + 4))))

/-- Members of the canonical Event-E band whose values occur in the strict
prefixes of all five rows `s,...,s+4`. -/
noncomputable def EventEFivePrefixBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventEFourPrefixBandSlots s delta c b0).filter (fun g =>
    decide (gameF s g ∈ StrictRowPrefixValues gameF (s + 4)))

/-- Exact fourth-edge packet certificate.  Besides the partition and the
new count, it retains a literal row-`s+3` host for every loss and the sharp
value window in which such a loss can occur. -/
def EventEFifthEdgeFrozenCarryCertificate
    (s delta z c b0 : Nat) : Prop :=
  (EventEFourPrefixBandSlots s delta c b0).length =
      (EventEFivePrefixBandSlots s delta c b0).length +
        (EventEFourthMissingBandSlots s delta c b0).length ∧
  (EventEFourthMissingBandSlots s delta c b0).length + delta + 5 <= s ∧
  4 * delta + 17 <=
      3 * s + 2 * (EventEFivePrefixBandSlots s delta c b0).length ∧
  ∀ g, g ∈ EventEFourthMissingBandSlots s delta c b0 ->
    ∃ b, b < s + 3 ∧
      gameF (s + 3) b = gameF s g ∧
      s + 4 <= gameF s g ∧ gameF s g < z

private theorem r54_nodup_map_of_injective_on
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

/-- Pointwise normal form for a four-prefix survivor.  A low survivor has
already completed an actual row start and is hence hosted on every later
row.  The only alternative is the genuinely high interval `[s+4,z)`.

This is stronger than merely saying that a low value reaches the fifth
prefix: it identifies the permanent blocker responsible for that carry. -/
theorem gameF_eventE_four_prefix_value_rowstart_or_high
    {s delta z c b0 g : Nat}
    (hcross : EventECrossEdgeSurvivorCertificate s delta z c b0)
    (hg : g ∈ EventEFourPrefixBandSlots s delta c b0) :
    (∃ p r, p = gameF s g ∧ p <= s + 3 ∧ r < p ∧
      gameF p r = p ∧
      ∀ t, p < t -> C gameF t t p) ∨
    (s + 4 <= gameF s g ∧ gameF s g < z) := by
  let slots := EventEDefectBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let four := EventEFourPrefixBandSlots s delta c b0
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      _hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  change g ∈ four at hg
  have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
  have hrow3 : gameF s g ∈ StrictRowPrefixValues gameF (s + 3) := by
    have hfilter := (List.mem_filter.mp hg).2
    simpa [four, EventEFourPrefixBandSlots] using hfilter
  have hgSurvivor : g ∈ survivors :=
    (List.mem_filter.mp hgTriple).1
  have hrow2 : gameF s g ∈ StrictRowPrefixValues gameF (s + 2) := by
    have hfilter := (List.mem_filter.mp hgTriple).2
    simpa [triple, EventETriplePrefixBandSlots] using hfilter
  have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurvivor).1
  have hrow1 : gameF s g ∈ StrictRowPrefixValues gameF (s + 1) := by
    have hfilter := (List.mem_filter.mp hgSurvivor).2
    simpa [survivors, EventESurvivingBandSlots] using hfilter
  have hgData := hslotsProps g hgSlots
  have hglt : g < s := hgData.1
  have hvltz : gameF s g < z := by
    simpa [EventELowerTransition] using hgData.2.2.2.2.1
  have hC1 : C gameF (s + 1) (s + 1) (gameF s g) :=
    mem_strictRowPrefixValues_iff_C.mp hrow1
  have hC2 : C gameF (s + 2) (s + 2) (gameF s g) :=
    mem_strictRowPrefixValues_iff_C.mp hrow2
  have hC3 : C gameF (s + 3) (s + 3) (gameF s g) :=
    mem_strictRowPrefixValues_iff_C.mp hrow3
  by_cases hlow : gameF s g <= s + 3
  · left
    by_cases hlow2 : gameF s g <= s + 2
    · have hstart := gameF_three_prefix_value_has_completed_rowstart
        hglt rfl hC1 hC2 hlow2
      rcases hstart with ⟨r, hr, hrowstart, _hregime⟩
      refine ⟨gameF s g, r, rfl, hlow, hr, hrowstart, ?_⟩
      intro t hpt
      apply (rowstart_hosted_iff_below_diagonal
        gameRecurrenceModel hr hrowstart).2
      have hdiag := gameRecurrenceModel.diagonal_gt t
      omega
    · have hpExact : gameF s g = s + 3 := by omega
      rcases hC3 with ⟨r, hr3, hhost3⟩
      have hrp : r < gameF s g := by omega
      refine ⟨gameF s g, r, rfl, hlow, hrp, ?_, ?_⟩
      · simpa [hpExact] using hhost3
      · intro t hpt
        apply (rowstart_hosted_iff_below_diagonal
          gameRecurrenceModel hrp (by simpa [hpExact] using hhost3)).2
        have hdiag := gameRecurrenceModel.diagonal_gt t
        omega
  · right
    exact ⟨by omega, hvltz⟩

/-- The literal frozen-carry step: a four-prefix value below the next row
index stays in the same host column and therefore enters the fifth prefix. -/
theorem eventE_four_prefix_low_value_frozen_to_fifth
    {s delta c b0 g : Nat}
    (hg : g ∈ EventEFourPrefixBandSlots s delta c b0)
    (hlow : gameF s g < s + 4) :
    g ∈ EventEFivePrefixBandSlots s delta c b0 := by
  have hrow3 : gameF s g ∈ StrictRowPrefixValues gameF (s + 3) := by
    have hfilter := (List.mem_filter.mp hg).2
    simpa [EventEFourPrefixBandSlots] using hfilter
  rcases mem_strictRowPrefixValues_iff_C.mp hrow3 with
    ⟨b, hb, hhost⟩
  have hcarry : gameF (s + 4) b = gameF (s + 3) b := by
    apply gameRecurrenceModel.constant_step
      (q := s + 3) (r := b) hb
    change gameF (s + 3) b < s + 3 + 1
    rw [hhost]
    simpa [Nat.add_assoc] using hlow
  have hrow4 : gameF s g ∈ StrictRowPrefixValues gameF (s + 4) := by
    apply List.mem_map.mpr
    refine ⟨b, List.mem_range.mpr (by omega), ?_⟩
    exact hcarry.trans hhost
  apply List.mem_filter.mpr
  refine ⟨hg, ?_⟩
  simpa [EventEFivePrefixBandSlots] using hrow4

/-- Every R53 no-dip/shared-owner certificate admits the exact fifth-edge
frozen-carry refinement.  No hypothesis on the fourth diagonal step is
needed. -/
theorem gameF_nonmax_eventE_four_prefix_fifth_edge_freeze
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hcert : EventENonDipSharedOwnerSaturationCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventEFifthEdgeFrozenCarryCertificate
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
  rcases hres with ⟨_hEvent, hInv, hnonmax, _hexists⟩
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzDiag : z + 1 = d := hInv.2.2.2.1

  let slots := EventEDefectBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let four := EventEFourPrefixBandSlots s delta c b0
  let missing := EventEFourthMissingBandSlots s delta c b0
  let five := EventEFivePrefixBandSlots s delta c b0
  let missingValues := missing.map (fun g => gameF s g)

  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hsurvivorsNodup : survivors.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have htripleNodup : triple.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hfourNodup : four.Nodup :=
    List.filter_sublist.nodup htripleNodup
  have hmissingNodup : missing.Nodup :=
    List.filter_sublist.nodup hfourNodup

  have hmissingFour : ∀ g, g ∈ missing -> g ∈ four := by
    intro g hg
    exact (List.mem_filter.mp hg).1
  have hmissingSlots : ∀ g, g ∈ missing -> g ∈ slots := by
    intro g hg
    have hgFour := hmissingFour g hg
    have hgTriple : g ∈ triple := (List.mem_filter.mp hgFour).1
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
    exact (List.mem_filter.mp hgSurv).1
  have hmissingAbsent : ∀ g, g ∈ missing ->
      gameF s g ∉ StrictRowPrefixValues gameF (s + 4) := by
    intro g hg
    have hfilter := (List.mem_filter.mp hg).2
    simpa [missing, EventEFourthMissingBandSlots] using hfilter

  have hlossGeometry : ∀ g, g ∈ missing ->
      ∃ b, b < s + 3 ∧
        gameF (s + 3) b = gameF s g ∧
        s + 4 <= gameF s g ∧ gameF s g < z := by
    intro g hg
    have hgFour := hmissingFour g hg
    have hrow3 : gameF s g ∈
        StrictRowPrefixValues gameF (s + 3) := by
      have hfilter := (List.mem_filter.mp hgFour).2
      simpa [four, EventEFourPrefixBandSlots] using hfilter
    rcases mem_strictRowPrefixValues_iff_C.mp hrow3 with
      ⟨b, hb, hhost⟩
    have hvHigh : s + 4 <= gameF s g := by
      by_cases hge : s + 4 <= gameF s g
      · exact hge
      · have hlow : gameF s g < s + 4 := by omega
        have hcarry : gameF (s + 4) b = gameF (s + 3) b := by
          apply gameRecurrenceModel.constant_step
            (q := s + 3) (r := b) hb
          change gameF (s + 3) b < s + 3 + 1
          rw [hhost]
          simpa [Nat.add_assoc] using hlow
        exfalso
        apply hmissingAbsent g hg
        apply List.mem_map.mpr
        exact ⟨b, List.mem_range.mpr (by omega), hcarry.trans hhost⟩
    have hgData := hslotsProps g (hmissingSlots g hg)
    have hvBelow : gameF s g < z := by
      simpa [EventELowerTransition] using hgData.2.2.2.2.1
    exact ⟨b, hb, hhost, hvHigh, hvBelow⟩

  have hmissingValuesNodup : missingValues.Nodup := by
    apply r54_nodup_map_of_injective_on
      (fun g => gameF s g) missing hmissingNodup
    intro g hg k hk hEq
    have hgData := hslotsProps g (hmissingSlots g hg)
    have hkData := hslotsProps k (hmissingSlots k hk)
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hgData.1) (Nat.le_of_lt hkData.1) hEq
  have hwindow : s + 4 <= z := by omega
  have hmissingValuesSub : missingValues ⊆
      List.range' (s + 4) (z - (s + 4)) := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    rcases hlossGeometry g hg with
      ⟨_b, _hb, _hhost, hvHigh, hvBelow⟩
    apply List.mem_range'_1.mpr
    constructor <;> omega
  have hintervalCap :=
    nodup_subset_length_le hmissingValuesNodup hmissingValuesSub
  have hlossBound : missing.length + delta + 5 <= s := by
    have hcap : missing.length <= z - (s + 4) := by
      simpa [missingValues] using hintervalCap
    omega

  have hpartitionRaw := List.length_eq_countP_add_countP
    (fun g => decide
      (gameF s g ∈ StrictRowPrefixValues gameF (s + 4)))
    (l := four)
  simp only [List.countP_eq_length_filter] at hpartitionRaw
  have hpartition : four.length = five.length + missing.length := by
    simpa [five, missing, EventEFivePrefixBandSlots,
      EventEFourthMissingBandSlots] using hpartitionRaw
  have hR53 := hcert.2.2
  change 2 * delta + 7 <= s + 2 * four.length at hR53
  have hpropagated : 4 * delta + 17 <= 3 * s + 2 * five.length := by
    omega
  have hresult : EventEFifthEdgeFrozenCarryCertificate
      s delta z c b0 :=
    ⟨hpartition, hlossBound, hpropagated, hlossGeometry⟩
  simpa [delta, z, d] using hresult

/-- Above the new three-quarter threshold the four-prefix atom necessarily
propagates to a concrete fifth-prefix survivor. -/
theorem eventE_fifth_edge_high_defect_forces_five_prefix_value
    {s delta z c b0 : Nat}
    (hcert : EventEFifthEdgeFrozenCarryCertificate s delta z c b0)
    (hlarge : 3 * s < 4 * delta + 17) :
    ∃ g, g ∈ EventEFivePrefixBandSlots s delta c b0 := by
  have hbound := hcert.2.2.1
  have hpos : 0 < (EventEFivePrefixBandSlots s delta c b0).length := by
    omega
  have hne : EventEFivePrefixBandSlots s delta c b0 ≠ [] := by
    intro hnil
    rw [hnil] at hpos
    simp at hpos
  exact List.exists_mem_of_ne_nil _ hne

/-- Honest finite reduction of the R53 four-prefix atom: either it lies in
the narrower numerical corridor `4*delta+17 <= 3*s`, or it has propagated
to an explicit five-prefix value. -/
theorem eventE_four_prefix_atom_reduces_to_corridor_or_five_prefix
    {s delta z c b0 : Nat}
    (hfour : ∃ g, g ∈ EventEFourPrefixBandSlots s delta c b0)
    (hfifth : EventEFifthEdgeFrozenCarryCertificate s delta z c b0) :
    (4 * delta + 17 <= 3 * s ∧
      ∃ g, g ∈ EventEFourPrefixBandSlots s delta c b0) ∨
    (∃ g, g ∈ EventEFivePrefixBandSlots s delta c b0) := by
  by_cases hlarge : 3 * s < 4 * delta + 17
  · exact Or.inr
      (eventE_fifth_edge_high_defect_forces_five_prefix_value
        hfifth hlarge)
  · exact Or.inl ⟨by omega, hfour⟩

#print axioms gameF_eventE_four_prefix_value_rowstart_or_high
#print axioms eventE_four_prefix_low_value_frozen_to_fifth
#print axioms gameF_nonmax_eventE_four_prefix_fifth_edge_freeze
#print axioms eventE_fifth_edge_high_defect_forces_five_prefix_value
#print axioms eventE_four_prefix_atom_reduces_to_corridor_or_five_prefix

end ChompLean
