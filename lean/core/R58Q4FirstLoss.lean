import R57ExactResidualAudit
import R55BoundaryGlobalGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

private theorem add_two_le_of_lt_sub_one {a t : Nat} (h : a < t - 1) :
    a + 2 <= t := by
  omega

/-!
R58: exact sharpening of a named certified Q4 loss edge.

The edge is not asserted minimal: the finite fate certificate supplies
previous-row presence and current-row absence, with no earlier-loss
exclusion. The conclusions below retain their displayed hypotheses.

Under `UnitDip`, the R57 alternative `d(t) <= p` collapses to the exact
capture `d(t)=p`, with predecessor `d(t-1)=p+1`.  The other alternative
remains a past-diagonal echo whose previous-row host lies left of its owner.
Consequently a row-start value which is present on row `t-1` cannot suffer
such a strict-prefix loss.

The final packet lemma records an owner interval from the R55 geometry:
a past owner is either before row `s` (and then the original packet host
lies left of it), or lies in `[s+4,t-1)`. This theorem does not assert
optimality; the later R59 no-recross argument eliminates the late-owner
arm under the full Q4 residual hypotheses.
-/

/-- Unit dips turn the above-diagonal arm of R57 into an exact diagonal
capture. -/
theorem gameF_unitDip_prefix_loss_exact_capture_or_left_echo
    (hU : UnitDip gameRecurrenceModel)
    {t p : Nat} (ht : 1 <= t)
    (hpresent : p ∈ StrictRowPrefixValues gameF (t - 1))
    (habsent : p ∉ StrictRowPrefixValues gameF t) :
    (gameF t t = p ∧ gameF (t - 1) (t - 1) = p + 1) ∨
      exists a b,
        b < a ∧ a < t - 1 ∧ b < t - 1 ∧
        gameF a a = p ∧ gameF (t - 1) b = p := by
  rcases gameF_strict_prefix_loss_above_or_left_echo
      ht hpresent habsent with hdiagLe | hpast
  · left
    have hpBand := gameF_strict_prefix_value_band hpresent
    have hdiagNe : gameF t t ≠ gameF (t - 1) (t - 1) := by
      intro hEq
      have hidx := diagonal_injective gameRecurrenceModel hEq
      omega
    have hdip : gameF t t < gameF (t - 1) (t - 1) := by
      omega
    have htStep : t - 1 + 1 = t := by omega
    have hunitRaw := hU (t - 1) (by
      rw [htStep]
      exact hdip)
    have hunit : gameF t t + 1 = gameF (t - 1) (t - 1) := by
      simpa [htStep] using hunitRaw
    omega
  · exact Or.inr hpast

/-- Under UnitDip, an already hosted row-start value is retained in the
next strict prefix.  A loss would force either a current or a past diagonal
owner, both disjoint from row-start values. -/
theorem gameF_unitDip_rowstart_prefix_retention
    (hU : UnitDip gameRecurrenceModel)
    {t p : Nat} (ht : 1 <= t)
    (hpresent : p ∈ StrictRowPrefixValues gameF (t - 1))
    (hrowstart : S gameF p) :
    p ∈ StrictRowPrefixValues gameF t := by
  apply Classical.byContradiction
  intro habsent
  have hclass := gameF_unitDip_prefix_loss_exact_capture_or_left_echo
    hU ht hpresent habsent
  rcases hclass with hcapture | hpast
  · exact False.elim
      (disjoint_D_S gameRecurrenceModel ⟨t, hcapture.1⟩ hrowstart)
  · rcases hpast with ⟨a, _b, _hba, _hat, _hbt, howner, _hhost⟩
    exact False.elim
      (disjoint_D_S gameRecurrenceModel ⟨a, howner⟩ hrowstart)

/-- R58 finite fate.  In the loss arm the selected value is certified not
to be a row start, and its loss is classified as exact diagonal capture or
past echo. -/
def EventEFourPrefixFiniteFateR58
    (s z g : Nat) : Prop :=
  (exists p r,
    p = gameF s g ∧ r < p ∧ gameF p r = p ∧
    forall t, p < t -> C gameF t t p) ∨
  (exists t,
    s + 4 <= t ∧ t <= gameF s g ∧ t < z ∧
    gameF s g ∈ StrictRowPrefixValues gameF (t - 1) ∧
    gameF s g ∉ StrictRowPrefixValues gameF t ∧
    Not (S gameF (gameF s g)) ∧
    ((gameF t t = gameF s g ∧
        gameF (t - 1) (t - 1) = gameF s g + 1) ∨
      exists a b,
        b < a ∧ a < t - 1 ∧ b < t - 1 ∧
        gameF a a = gameF s g ∧
        gameF (t - 1) b = gameF s g))

/-- Conditional exactness: under UnitDip, R58 is equivalent to the original
R55 finite fate. -/
theorem eventE_four_prefix_finite_fate_iff_R58
    (hU : UnitDip gameRecurrenceModel) {s z g : Nat} :
    EventEFourPrefixFiniteFate s z g <->
      EventEFourPrefixFiniteFateR58 s z g := by
  constructor
  · intro hfate
    rcases hfate with hstart | hloss
    · exact Or.inl hstart
    · right
      rcases hloss with ⟨t, hst, htp, htz, hpresent, habsent⟩
      have ht : 1 <= t := by omega
      have hclass := gameF_unitDip_prefix_loss_exact_capture_or_left_echo
        hU ht hpresent habsent
      have hnotRowStart : Not (S gameF (gameF s g)) := by
        intro hrowstart
        exact habsent
          (gameF_unitDip_rowstart_prefix_retention
            hU ht hpresent hrowstart)
      exact ⟨t, hst, htp, htz, hpresent, habsent,
        hnotRowStart, hclass⟩
  · intro hfate
    rcases hfate with hstart | hloss
    · exact Or.inl hstart
    · right
      rcases hloss with
        ⟨t, hst, htp, htz, hpresent, habsent,
          _hnotRowStart, _hclass⟩
      exact ⟨t, hst, htp, htz, hpresent, habsent⟩

/-- Abstract packet consequence for a past owner of a selected Q4 value.
The exact R55 diagonal rows exclude owner indices `s,s+1,s+2,s+3`.
If the owner is earlier than `s`, ECHO-LEFT also orders the packet column. -/
theorem gameF_packet_past_owner_interval
    {s z g t a : Nat}
    (hgs : g < s) (hpz : gameF s g < z)
    (hdiag0 : gameF s s = z + 2)
    (hdiag1 : gameF (s + 1) (s + 1) = z + 1)
    (hdiag2 : gameF (s + 2) (s + 2) = z)
    (hdiag3 : z < gameF (s + 3) (s + 3))
    (hat : a < t - 1)
    (howner : gameF a a = gameF s g) :
    (a < s ∧ g < a) ∨ (s + 4 <= a ∧ a < t - 1) := by
  by_cases has : a < s
  · left
    have hleft : g < a :=
      gameF_past_diagonal_echo_strictly_left
        has (Nat.le_of_lt hgs) howner.symm
    exact ⟨has, hleft⟩
  · right
    have hcases : s <= a := by omega
    have hlate : s + 4 <= a := by
      apply Nat.le_of_not_gt
      intro ha4
      have haCases : a = s ∨ a = s + 1 ∨ a = s + 2 ∨ a = s + 3 := by
        omega
      rcases haCases with ha | ha | ha | ha
      · subst a
        omega
      · subst a
        omega
      · subst a
        omega
      · subst a
        omega
    exact ⟨hlate, hat⟩

/-- Specialization of the owner interval to the actual R55 Q4 packet.
This interval statement retains a late-owner arm beginning at `s+4`
and ending strictly before `t-1`. It does not claim optimality; the later
R59 no-recross argument rules out that arm under the full residual hypotheses. -/
theorem gameF_Q4_past_owner_interval_of_residual
    (hU : UnitDip gameRecurrenceModel)
    {s c b0 g t a : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hstrict : EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hg : g ∈ EventEFourPrefixBandSlots
      s (2 * s - gameF (s + 1) (s + 1)) c b0)
    (hpz : gameF s g < gameF (s + 1) (s + 1) - 1)
    (htp : t <= gameF s g)
    (hat : a < t - 1)
    (howner : gameF a a = gameF s g) :
    (a < s ∧ g < a) ∨
      (s + 4 <= a ∧ a + 2 <= t ∧ t <= gameF s g) := by
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipStrictSharedOwnerCertificate
    s delta z c b0 at hstrict
  change g ∈ EventEFourPrefixBandSlots s delta c b0 at hg
  change gameF s g < z at hpz
  have hresData := hres
  change MarginEventECounterexample s ∧
      EventEDefectPacketInvariant s d delta z ∧
      delta + 5 <= s ∧
      exists ce be, EventECrossEdgeSurvivorCertificate
        s delta z ce be at hresData
  rcases hresData with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨hdip0, _hmargin, hdip1⟩
  have hzDiag1 : gameF (s + 1) (s + 1) = z + 1 := by
    have hz := hInv.2.2.2.1
    change z + 1 = d at hz
    omega
  have hunit0 := hU s hdip0
  change gameF (s + 1) (s + 1) + 1 = gameF s s at hunit0
  have hdiag0 : gameF s s = z + 2 := by omega
  have hunit1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hunit1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by omega
  have hnondip3 : Not
      (gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2)) :=
    hstrict.1.1.1
  have hdiag3Ne :
      gameF (s + 3) (s + 3) ≠ gameF (s + 2) (s + 2) := by
    intro hEq
    have hidx := diagonal_injective gameRecurrenceModel hEq
    omega
  have hdiag3 : z < gameF (s + 3) (s + 3) := by
    omega
  have hgTriple :
      g ∈ EventETriplePrefixBandSlots s delta c b0 :=
    (List.mem_filter.mp hg).1
  have hgSurvivor :
      g ∈ EventESurvivingBandSlots s delta c b0 :=
    (List.mem_filter.mp hgTriple).1
  have hgBand : g ∈ EventEDefectBandSlots s delta c b0 :=
    (List.mem_filter.mp hgSurvivor).1
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      _hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hgs : g < s := (hslotsProps g hgBand).1
  rcases gameF_packet_past_owner_interval
      hgs hpz hdiag0 hzDiag1 hdiag2 hdiag3 hat howner with
    hearly | hlate
  · exact Or.inl hearly
  · exact Or.inr ⟨hlate.1, add_two_le_of_lt_sub_one hlate.2, htp⟩

#print axioms gameF_unitDip_prefix_loss_exact_capture_or_left_echo
#print axioms gameF_unitDip_rowstart_prefix_retention
#print axioms eventE_four_prefix_finite_fate_iff_R58
#print axioms gameF_packet_past_owner_interval
#print axioms gameF_Q4_past_owner_interval_of_residual

end ChompLean
