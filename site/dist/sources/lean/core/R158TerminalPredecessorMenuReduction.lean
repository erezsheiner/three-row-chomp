import R157TerminalTargetHistoryDepth8Reduction
import R155TerminalSingletonSourceExchange

set_option autoImplicit false

namespace ChompLean

/-!
# Direct terminal predecessor menu

The F8000 audit suggests a sharper target than two unrelated global atoms.
For a blocker freeze at `(v,r)`, a target host in the terminal predecessor
column `c=r-1>2` has one of two biographies:

* it is the ordinary lag-three preview host; or
* it is a lag-eight host, and by row `v-3` the same column has become the
  freeze column of the lower blocker `v-3`.

The second clause contains its own owner-cutoff certificate.  Consequently
this one menu closes the upper rail directly.  As before, the empirical menu
is named as an explicit input rather than asserted as a theorem of `gameF`.
-/

/-- The direct `{3,8}` terminal host menu, strengthened in the lag-eight arm
by the lower-blocker cell observed at the same column. -/
def TerminalPredecessorHostMenu38 : Prop :=
  forall {v r a : Nat},
    r < v ->
    gameF v r = v ->
    2 < r - 1 ->
    r <= a ->
    a < v ->
    gameF a (r - 1) = v ->
    Or (a + 3 = v)
      (a + 8 = v /\ gameF (v - 3) (r - 1) = v - 3)

/-- The strictly weaker theorem target actually needed by the upper-rail
argument: any genuinely old terminal history has already turned into the
lag-three blocker's freeze at that column. -/
def TerminalOldHistoryForcesLag3Freeze : Prop :=
  forall {v r : Nat},
    r < v ->
    gameF v r = v ->
    2 < r - 1 ->
    ColHistPred gameF (v - 3) (r - 1) v ->
    gameF (v - 3) (r - 1) = v - 3

/-- A known lower-blocker freeze column is at most every lower-owner cutoff.
The diagonal-owner arm is impossible by D/S disjointness, while row
injectivity identifies the row-start owner supplied by coverage. -/
theorem lowerOwnerCoveredBy_pins_known_blocker_column
    {v g k c : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (hkpos : 0 < k)
    (hkv : k < v)
    (hck : c < k)
    (hstart : gameF k c = k) :
    c <= g := by
  rcases howners k hkpos hkv with
      ⟨a, _hag, hdiag⟩ | ⟨rk, hrkg, hrkk, hstartk⟩
  · exact False.elim
      (disjoint_D_S gameRecurrenceModel
        ⟨a, hdiag⟩ ⟨c, hck, hstart⟩)
  · have hcol : c = rk :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hck) (Nat.le_of_lt hrkk)
        (hstart.trans hstartk.symm)
    omega

/-- The direct menu contains the weaker old-history-to-lower-freeze atom.
No midpoint or owner-coverage assumption is used in this implication. -/
theorem terminalOldHistoryForcesLag3Freeze_of_menu38
    (hmenu : TerminalPredecessorHostMenu38) :
    TerminalOldHistoryForcesLag3Freeze := by
  intro v r hrv hstart hc hhist
  rcases hhist with ⟨a, hca, hav3, hhost⟩
  have hrpos : 0 < r := by omega
  have hra : r <= a := by
    by_cases har : a = r - 1
    · subst a
      have hdiag : gameF (r - 1) (r - 1) = v := hhost
      exact False.elim
        (disjoint_D_S gameRecurrenceModel
          ⟨r - 1, hdiag⟩ ⟨r, hrv, hstart⟩)
    · omega
  rcases hmenu hrv hstart hc hra (by omega) hhost with hlag3 | hlag8
  · omega
  · exact hlag8.2

/-- The old-history-to-lower-freeze atom alone closes the upper rail.  In a
strict failure R137 supplies old terminal history; the atom turns it into a
freeze of `q=v-3` at column `r-1`; lower-owner coverage then puts that
column at or left of `g`, contradicting `g<r-1`. -/
theorem gameF_upperRail_of_terminalOldHistoryForcesLag3Freeze
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hOldFreeze : TerminalOldHistoryForcesLag3Freeze) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  have hold : ColHistPred gameF q (r - 1) (q + 3) :=
    (gameF_firstFailure_terminal_predecessor_old_packet
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview).1
  have hc : 2 < r - 1 := by omega
  have hold' :
      ColHistPred gameF ((q + 3) - 3) (r - 1) (q + 3) := by
    simpa [show (q + 3) - 3 = q by omega] using hold
  have hlower : gameF q (r - 1) = q := by
    have h := hOldFreeze hrv hstart hc hold'
    simpa [show (q + 3) - 3 = q by omega] using h
  rcases hold with ⟨a, hca, haq, _hhost⟩
  have hcolLe : r - 1 <= g :=
    lowerOwnerCoveredBy_pins_known_blocker_column
      howners (by omega) (by omega) (by omega) hlower
  omega

/-- The full `{3,8}` menu therefore closes the upper rail as a corollary. -/
theorem gameF_upperRail_of_terminalPredecessorHostMenu38
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hmenu : TerminalPredecessorHostMenu38) :
    r <= g + 1 := by
  exact gameF_upperRail_of_terminalOldHistoryForcesLag3Freeze
    hq hrv hstart howners hinterior hpreviewLe hpreviewLeft hpreview
      (terminalOldHistoryForcesLag3Freeze_of_menu38 hmenu)

#print axioms lowerOwnerCoveredBy_pins_known_blocker_column
#print axioms terminalOldHistoryForcesLag3Freeze_of_menu38
#print axioms gameF_upperRail_of_terminalOldHistoryForcesLag3Freeze
#print axioms gameF_upperRail_of_terminalPredecessorHostMenu38

end ChompLean
