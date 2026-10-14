import R158TerminalPredecessorMenuReduction

set_option autoImplicit false

namespace ChompLean

/-!
# Live terminal predecessor reduction

The lag-eight F8000 event is not a counterexample to a live-column theorem:
its terminal predecessor column freezes at the lower blocker `v-3`.  This
suggests the weaker and more structural atom below.  If the terminal column
has no lower blocker freeze before `v`, then its target host is the ordinary
lag-three host.
-/

/-- Column `c` has not become the freeze column of any blocker below `v`. -/
def ColumnLiveBelow (v c : Nat) : Prop :=
  forall z, c < z -> z < v -> gameF z c ≠ z

/-- The live-column terminal predecessor atom.  The threshold `v>=7` is the
smallest range relevant to the audited `c=r-1>2` terminal menu. -/
def LiveTerminalPredecessorLag3 : Prop :=
  forall {v r a : Nat},
    7 <= v ->
    r < v ->
    gameF v r = v ->
    2 < r - 1 ->
    r <= a ->
    a < v ->
    gameF a (r - 1) = v ->
    ColumnLiveBelow v (r - 1) ->
    a + 3 = v

/-- Every column strictly to the right of a lower-owner cutoff is live up to
the target.  A lower freeze there would be pinned back to the cutoff. -/
theorem lowerOwnerCoveredBy_columnLive_right_of_cutoff
    {v g c : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (hgc : g < c) :
    ColumnLiveBelow v c := by
  intro z hcz hzv hfreeze
  have hcg : c <= g :=
    lowerOwnerCoveredBy_pins_known_blocker_column
      howners (by omega) hzv hcz hfreeze
  omega

/-- The stronger `{3,8}` menu proves the live-column atom: its lag-eight arm
exhibits exactly the lower freeze forbidden by liveness. -/
theorem liveTerminalPredecessorLag3_of_menu38
    (hmenu : TerminalPredecessorHostMenu38) :
    LiveTerminalPredecessorLag3 := by
  intro v r a _hv hrv hstart hc hra hav hhost hlive
  rcases hmenu hrv hstart hc hra hav hhost with hlag3 | hlag8
  · exact hlag3
  · have hca : r - 1 < v - 3 := by omega
    exact False.elim
      (hlive (v - 3) hca (by omega) hlag8.2)

/-- `LiveTerminalPredecessorLag3` alone closes the upper rail.  At a strict
failure, R137 supplies an old host `a<q=v-3`; owner coverage makes its column
live; the atom then says `a=v-3`, an immediate contradiction. -/
theorem gameF_upperRail_of_liveTerminalPredecessorLag3
    {q r g H : Nat}
    (hq : 4 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hliveLag3 : LiveTerminalPredecessorLag3) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  rcases gameF_firstFailure_forces_early_terminal_sighting
      (by omega) hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hhost⟩
  have hc : 2 < r - 1 := by omega
  have hcolLive : ColumnLiveBelow (q + 3) (r - 1) :=
    lowerOwnerCoveredBy_columnLive_right_of_cutoff
      howners (by omega)
  have hlag3 : a + 3 = q + 3 :=
    hliveLag3 (by omega) hrv hstart hc hra (by omega) hhost hcolLive
  omega

/-- The direct terminal menu closes the upper rail through its conceptually
weaker live-column consequence. -/
theorem gameF_upperRail_of_menu38_via_liveColumn
    {q r g H : Nat}
    (hq : 4 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hmenu : TerminalPredecessorHostMenu38) :
    r <= g + 1 := by
  exact gameF_upperRail_of_liveTerminalPredecessorLag3
    hq hrv hstart howners hinterior hpreviewLe hpreviewLeft hpreview
      (liveTerminalPredecessorLag3_of_menu38 hmenu)

#print axioms lowerOwnerCoveredBy_columnLive_right_of_cutoff
#print axioms liveTerminalPredecessorLag3_of_menu38
#print axioms gameF_upperRail_of_liveTerminalPredecessorLag3
#print axioms gameF_upperRail_of_menu38_via_liveColumn

end ChompLean
