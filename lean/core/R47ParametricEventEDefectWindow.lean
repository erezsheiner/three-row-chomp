import R45DefectOnePacketPairAttack

set_option autoImplicit false

namespace ChompLean

/-!
R47: a defect-parameter invariant for every genuine margin event E.

Put

* `d = gameF (s+1) (s+1)`,
* `delta = 2*s-d`, and
* `z = d-1`.

Source capacity bounds the depths, measured from the right edge, of the
three packet hosts by `delta`, `delta+1`, and `delta+3`.  Thus the defect-zero
and defect-one menus are only the first two instances of one finite family.

Moreover every other column in the old packet row carries a value below
`z`, and hence has the carry / ordered-echo / next-row-rehost transition
proved in R45.
-/

/-- Defect-independent name for the lower transition extracted in R45. -/
def EventELowerTransition (s z g : Nat) : Prop :=
  let q := gameF s g
  0 < q ∧ q < z ∧
    ((q < s ∧ gameF (s - 1) g = q) ∨
      (∃ a, g < a ∧ a < s ∧ gameF a a = q) ∨
      C gameF (s + 1) (s + 1) q)

/-- The full reusable invariant.  The offset witnesses `dc,d0,d1`
determine the three host columns uniquely and range over intervals of sizes
at most `delta+1`, `delta+2`, and `delta+4`, respectively. -/
def EventEDefectPacketInvariant
    (s d delta z : Nat) : Prop :=
  1 ≤ delta ∧ delta + 4 ≤ s ∧ d + delta = 2 * s ∧ z + 1 = d ∧
    ∃ c b0 b1 dc d0 d1,
      c < s ∧ b0 < s ∧ b1 < s + 1 ∧
      c ≠ b0 ∧ b0 ≠ b1 ∧
      gameF s c = z + 1 ∧ gameF s b0 = z ∧
      gameF (s + 1) b1 = z ∧
      s - delta - 1 ≤ c ∧
      s - delta - 2 ≤ b0 ∧
      s - delta - 3 ≤ b1 ∧
      dc ≤ delta ∧ d0 ≤ delta + 1 ∧ d1 ≤ delta + 3 ∧
      c + dc + 1 = s ∧ b0 + d0 + 1 = s ∧ b1 + d1 = s ∧
      ∀ g, g < s → g ≠ c → g ≠ b0 →
        EventELowerTransition s z g

/-- Pure arithmetic conversion from per-cell source capacities to defect
depths and exact right-edge offsets.  This lemma is independent of the game
recurrence. -/
theorem packet_capacity_defect_depth_bounds
    {s d z c b0 b1 : Nat}
    (hz : z + 1 = d)
    (hc : c < s) (hb0 : b0 < s) (hb1 : b1 < s + 1)
    (hcapSucc : z ≤ s + c)
    (hcapBase : z - 1 ≤ s + b0)
    (hcapNext : z - 1 ≤ (s + 1) + b1)
    (htotal : d ≤ 2 * s) :
    let delta := 2 * s - d
    d + delta = 2 * s ∧
      s - delta - 1 ≤ c ∧
      s - delta - 2 ≤ b0 ∧
      s - delta - 3 ≤ b1 ∧
      s - 1 - c ≤ delta ∧
      s - 1 - b0 ≤ delta + 1 ∧
      s - b1 ≤ delta + 3 ∧
      ∃ dc d0 d1,
        dc ≤ delta ∧ d0 ≤ delta + 1 ∧ d1 ≤ delta + 3 ∧
        c + dc + 1 = s ∧ b0 + d0 + 1 = s ∧ b1 + d1 = s := by
  dsimp only
  refine ⟨by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_⟩
  exact ⟨s - 1 - c, s - 1 - b0, s - b1,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Defect-independent wrapper around the R45 unused-column transition. -/
theorem gameF_lower_unused_column_eventE_transition
    {s z g : Nat}
    (hg : g < s)
    (hDiag : gameF s s = z + 2)
    (hNextDiag : gameF (s + 1) (s + 1) = z + 1)
    (hLower : gameF s g < z) :
    EventELowerTransition s z g := by
  change DefectOneLowerTransition s z g
  exact gameF_lower_unused_column_transition hg hDiag hNextDiag hLower

/-- Parametric event-E theorem.  It simultaneously gives:

* the intrinsic defect range `1 <= delta <= s-4`;
* finite right-edge windows for all three packet hosts;
* exact bounded offset coordinates for those hosts; and
* a lower transition at every unused old-row column.
-/
theorem gameF_margin_eventE_parametric_defect_invariant
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    EventEDefectPacketInvariant s d delta z := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change EventEDefectPacketInvariant s d delta z

  have hwindow := gameF_margin_eventE_strict_window
    hU hdip hmargin hnextDip
  change 5 ≤ s ∧ s + 3 < d ∧ d < 2 * s at hwindow
  have hzDiag : z + 1 = d := by
    dsimp [z, d]
    have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
    change s + 1 < gameF (s + 1) (s + 1) at hgt
    omega
  have hdeltaSum : d + delta = 2 * s := by
    dsimp [delta]
    omega
  have hdeltaPos : 1 ≤ delta := by
    dsimp [delta]
    omega
  have hdeltaUpper : delta + 4 ≤ s := by
    omega

  rcases gameF_margin_eventE_packet_source_capacity
      hU hdip hmargin hnextDip with
    ⟨c, b0, b1, hc, hb0, hb1, hcNe, hbNe,
      hSucc, hBase, hHost1, hcapSucc, hcapBase, hcapNext, htotal⟩
  have htotalD : d ≤ 2 * s := by omega
  have hdepth := packet_capacity_defect_depth_bounds
    hzDiag hc hb0 hb1 hcapSucc hcapBase hcapNext htotalD
  change d + delta = 2 * s ∧
      s - delta - 1 ≤ c ∧
      s - delta - 2 ≤ b0 ∧
      s - delta - 3 ≤ b1 ∧
      s - 1 - c ≤ delta ∧
      s - 1 - b0 ≤ delta + 1 ∧
      s - b1 ≤ delta + 3 ∧
      ∃ dc d0 d1,
        dc ≤ delta ∧ d0 ≤ delta + 1 ∧ d1 ≤ delta + 3 ∧
        c + dc + 1 = s ∧ b0 + d0 + 1 = s ∧ b1 + d1 = s
    at hdepth
  rcases hdepth with
    ⟨_hdeltaSum', hcWindow, hb0Window, hb1Window,
      _hcDepth, _hb0Depth, _hb1Depth,
      dc, d0, d1, hdc, hd0, hd1, hcOffset, hb0Offset, hb1Offset⟩

  have hunit := hU s hdip
  change d + 1 = gameF s s at hunit
  have hDiag : gameF s s = z + 2 := by omega
  have hTransitions : ∀ g, g < s → g ≠ c → g ≠ b0 →
      EventELowerTransition s z g := by
    intro g hg hgc hgb0
    have hLower : gameF s g < z :=
      unused_column_below_consecutive_row_top gameRecurrenceModel
        (s := s) (z := z) (g := g) (b := b0) (c := c)
        hg hb0 hc hgb0 hgc hBase hSucc hDiag
    exact gameF_lower_unused_column_eventE_transition
      hg hDiag (by omega) hLower

  exact ⟨hdeltaPos, hdeltaUpper, hdeltaSum, hzDiag,
    c, b0, b1, dc, d0, d1,
    hc, hb0, hb1, hcNe, hbNe, hSucc, hBase, hHost1,
    hcWindow, hb0Window, hb1Window,
    hdc, hd0, hd1, hcOffset, hb0Offset, hb1Offset,
    hTransitions⟩

/-- Lightweight projection exposing just the requested parametric column
windows and the packet values. -/
theorem gameF_margin_eventE_parametric_column_windows
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    ∃ c b0 b1,
      c < s ∧ b0 < s ∧ b1 < s + 1 ∧
      gameF s c = z + 1 ∧ gameF s b0 = z ∧
      gameF (s + 1) b1 = z ∧
      s - delta - 1 ≤ c ∧
      s - delta - 2 ≤ b0 ∧
      s - delta - 3 ≤ b1 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  rcases hInv with
    ⟨_hdeltaPos, _hdeltaUpper, _hdeltaSum, _hzDiag,
      c, b0, b1, _dc, _d0, _d1,
      hc, hb0, hb1, _hcNe, _hbNe, hSucc, hBase, hHost1,
      hcWindow, hb0Window, hb1Window, _rest⟩
  exact ⟨c, b0, b1, hc, hb0, hb1,
    hSucc, hBase, hHost1, hcWindow, hb0Window, hb1Window⟩

#print axioms packet_capacity_defect_depth_bounds
#print axioms gameF_lower_unused_column_eventE_transition
#print axioms gameF_margin_eventE_parametric_defect_invariant
#print axioms gameF_margin_eventE_parametric_column_windows

end ChompLean
