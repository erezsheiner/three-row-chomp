import R56Integration

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
R57 audit of the four R55 exact geometric terminals.

The first three branches are retained verbatim.  The fourth-prefix branch
receives one exact extra classification at its first strict-prefix loss:
the lost value is either at or above the new diagonal, or it is a past
diagonal whose previous-row host lies strictly left of its diagonal owner.

The final equivalence proves that this is a structural sharpening, not an
elimination of any R55 branch.  A separate theorem records why the R56
window-local path theorem cannot be applied to an R55 residual: every such
residual already contains two adjacent diagonal dips.
-/

/-- Exact classification of a value which is present in the strict prefix
of row `t-1` and absent from the strict prefix of row `t`.

If the value is below the new diagonal, NEVER-VANISH forces a past diagonal
owner.  ECHO-LEFT then places the previous-row host strictly left of that
owner. -/
theorem gameF_strict_prefix_loss_above_or_left_echo
    {t p : Nat} (ht : 1 <= t)
    (hpresent : p ∈ StrictRowPrefixValues gameF (t - 1))
    (habsent : p ∉ StrictRowPrefixValues gameF t) :
    gameF t t <= p ∨
      exists a b,
        b < a ∧ a < t - 1 ∧ b < t - 1 ∧
        gameF a a = p ∧ gameF (t - 1) b = p := by
  rcases mem_strictRowPrefixValues_iff_C.mp hpresent with
    ⟨b, hbt, hhost⟩
  have hpPos : 0 < p := by
    have hvalueGt := encoded_gt game_encodes (Nat.le_of_lt hbt)
    rw [hhost] at hvalueGt
    omega
  have hnotC : Not (C gameF t t p) := by
    intro hC
    exact habsent (mem_strictRowPrefixValues_iff_C.mpr hC)
  by_cases hdiagLe : gameF t t <= p
  · exact Or.inl hdiagLe
  · right
    have hpBelow : p < gameF t t := by omega
    have hpast : exists a, a < t ∧ gameF a a = p := by
      by_cases hpast : exists a, a < t ∧ gameF a a = p
      · exact hpast
      · exfalso
        apply hnotC
        apply recurrence_nonpast_below_diagonal_strict_prefix
          gameRecurrenceModel hpPos hpBelow
        simpa [PastDiagonalValueBefore, gameRecurrenceModel] using hpast
    rcases hpast with ⟨a, hat, howner⟩
    have haBefore : a < t - 1 := by
      have haLe : a <= t - 1 := by omega
      apply Nat.lt_of_le_of_ne haLe
      intro haEq
      have haEq' : a = t - 1 := by omega
      subst a
      have hcols : b = t - 1 :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hbt) (Nat.le_refl _)
          (hhost.trans howner.symm)
      omega
    have hleft : b < a :=
      gameF_past_diagonal_echo_strictly_left
        haBefore (Nat.le_of_lt hbt) (hhost.trans howner.symm)
    exact ⟨a, b, hleft, haBefore, hbt, howner, hhost⟩

/-- R57 finite fate: the permanent-row-start arm is unchanged; the
loss-edge arm carries the exact above-diagonal/left-echo classification. -/
def EventEFourPrefixFiniteFateR57
    (s z g : Nat) : Prop :=
  (exists p r,
    p = gameF s g ∧ r < p ∧ gameF p r = p ∧
    forall t, p < t -> C gameF t t p) ∨
  (exists t,
    s + 4 <= t ∧ t <= gameF s g ∧ t < z ∧
    gameF s g ∈ StrictRowPrefixValues gameF (t - 1) ∧
    gameF s g ∉ StrictRowPrefixValues gameF t ∧
    (gameF t t <= gameF s g ∨
      exists a b,
        b < a ∧ a < t - 1 ∧ b < t - 1 ∧
        gameF a a = gameF s g ∧
        gameF (t - 1) b = gameF s g))

/-- The R57 fate is equivalent to the R55 fate for the actual game; its
extra geometry is forced rather than assumed. -/
theorem eventE_four_prefix_finite_fate_iff_R57
    {s z g : Nat} :
    EventEFourPrefixFiniteFate s z g <->
      EventEFourPrefixFiniteFateR57 s z g := by
  constructor
  · intro hfate
    rcases hfate with hstart | hloss
    · exact Or.inl hstart
    · right
      rcases hloss with ⟨t, hst, htp, htz, hpresent, habsent⟩
      have ht : 1 <= t := by omega
      have hclass := gameF_strict_prefix_loss_above_or_left_echo
        ht hpresent habsent
      exact ⟨t, hst, htp, htz, hpresent, habsent, hclass⟩
  · intro hfate
    rcases hfate with hstart | hloss
    · exact Or.inl hstart
    · right
      rcases hloss with
        ⟨t, hst, htp, htz, hpresent, habsent, _hclass⟩
      exact ⟨t, hst, htp, htz, hpresent, habsent⟩

/-- Fourth R57 branch: identical to the R55 branch, with the selected
value's fate replaced by its classified equivalent. -/
def EventEFourPrefixFiniteFateGeometryCertificateR57
    (s delta z c b0 : Nat) : Prop :=
  EventENonDipStrictSharedOwnerCertificate s delta z c b0 ∧
  exists g,
    g ∈ EventEFourPrefixBandSlots s delta c b0 ∧
    EventEFourPrefixFiniteFateR57 s z g

theorem eventE_four_prefix_geometry_iff_R57
    {s delta z c b0 : Nat} :
    EventEFourPrefixFiniteFateGeometryCertificate s delta z c b0 <->
      EventEFourPrefixFiniteFateGeometryCertificateR57
        s delta z c b0 := by
  constructor
  · rintro ⟨hstrict, g, hg, hfate⟩
    exact ⟨hstrict, g, hg,
      eventE_four_prefix_finite_fate_iff_R57.mp hfate⟩
  · rintro ⟨hstrict, g, hg, hfate⟩
    exact ⟨hstrict, g, hg,
      eventE_four_prefix_finite_fate_iff_R57.mpr hfate⟩

/-- R57 four-way menu.  Branches one through three are literally the R55
branches; only branch four carries the derived loss-edge classification. -/
def EventER57ExactGeometricTerminal
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBandHitLeftHistoryCertificate s delta z c b0 ∨
  EventEThirdDipBoundaryEchoLedgerTerminal s delta z c b0 ∨
  EventEDeepQuietExactGeometryCertificate s delta z c b0 ∨
  EventEFourPrefixFiniteFateGeometryCertificateR57 s delta z c b0

/-- No R55 branch is eliminated by the R56 imports.  The exact terminal
menu is equivalent after annotating the fourth branch. -/
theorem eventE_R55_exact_terminal_iff_R57
    {s delta z c b0 : Nat} :
    EventER55ExactGeometricTerminal s delta z c b0 <->
      EventER57ExactGeometricTerminal s delta z c b0 := by
  constructor
  · intro hterm
    rcases hterm with hhit | hboundary | hdeep | hfour
    · exact Or.inl hhit
    · exact Or.inr (Or.inl hboundary)
    · exact Or.inr (Or.inr (Or.inl hdeep))
    · exact Or.inr (Or.inr (Or.inr
        (eventE_four_prefix_geometry_iff_R57.mp hfour)))
  · intro hterm
    rcases hterm with hhit | hboundary | hdeep | hfour
    · exact Or.inl hhit
    · exact Or.inr (Or.inl hboundary)
    · exact Or.inr (Or.inr (Or.inl hdeep))
    · exact Or.inr (Or.inr (Or.inr
        (eventE_four_prefix_geometry_iff_R57.mpr hfour)))

def NonmaxMarginEventER57ExactGeometricResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  NonmaxMarginEventECrossEdgeResidual s ∧
  2 * delta + 10 <= s ∧
  exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 ∧
    EventER57ExactGeometricTerminal s delta z c b0

theorem R55_exact_residual_iff_R57 {s : Nat} :
    NonmaxMarginEventER55ExactGeometricResidual s <->
      NonmaxMarginEventER57ExactGeometricResidual s := by
  dsimp [NonmaxMarginEventER55ExactGeometricResidual,
    NonmaxMarginEventER57ExactGeometricResidual]
  constructor
  · rintro ⟨hres, henv, c, b0, hcross, hterm⟩
    exact ⟨hres, henv, c, b0, hcross,
      eventE_R55_exact_terminal_iff_R57.mp hterm⟩
  · rintro ⟨hres, henv, c, b0, hcross, hterm⟩
    exact ⟨hres, henv, c, b0, hcross,
      eventE_R55_exact_terminal_iff_R57.mpr hterm⟩

/-- Exact obstruction to using the R56 window-local path theorem inside
any R55 residual: Event E already has adjacent dips at `s` and `s+1`. -/
theorem R55_exact_residual_refutes_noAdjacentDiagonalDips
    {s : Nat} (hres : NonmaxMarginEventER55ExactGeometricResidual s) :
    Not (NoAdjacentDiagonalDips gameRecurrenceModel) := by
  intro hNoAdjacent
  have hEvent : MarginEventECounterexample s := hres.1.1
  exact (hNoAdjacent s hEvent.1) hEvent.2.2

#print axioms gameF_strict_prefix_loss_above_or_left_echo
#print axioms eventE_four_prefix_finite_fate_iff_R57
#print axioms eventE_R55_exact_terminal_iff_R57
#print axioms R55_exact_residual_iff_R57
#print axioms R55_exact_residual_refutes_noAdjacentDiagonalDips

end ChompLean
