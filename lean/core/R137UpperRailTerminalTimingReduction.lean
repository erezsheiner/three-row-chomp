import R136UpperRailLoadedInterval

set_option autoImplicit false

namespace ChompLean

/-!
R137: a first upper-rail failure is not merely a dirty midpoint column.
It forces old history at the terminal predecessor `r-1`.

Write the blocker as `v=q+3`.  Owner coverage loads every column between
the midpoint cutoff `g` and the freeze `r`.  At `r-1`, the exact causal
depth-three theorem says that this load is either already present below
row `q`, or comes from row `q`.  A known lag-three preview host `H<=g`
and fixed-row injectivity exclude the latter alternative because
`r-1>g`.  Thus failure forces a genuinely earlier terminal-predecessor
sighting.
-/

/-- Exact packet forced at the terminal predecessor by an upper-rail
failure.  The first conjunct is the new point: the history already occurs
strictly before the lag-three row `q=v-3`. -/
theorem gameF_firstFailure_terminal_predecessor_old_packet
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    ColHistPred gameF q (r - 1) (q + 3) /\
      ParkedOnly gameF (q + 3) (r - 1) (q + 3) /\
      B gameF (q + 3) (r - 1) (q + 3) /\
      Not (B gameF (q + 3) r (q + 3)) := by
  have hpacket := gameF_firstFailureLoadedInterval_of_ownerCoverage
    (v := q + 3) (r := r) (s := g)
    (by omega) hrv hstart howners hfailure
  have hterminal := hpacket.1 (r - 1) (by omega) (by omega)
  have hold : ColHistPred gameF q (r - 1) (q + 3) := by
    rcases (gameF_colHist_causal_depth_three hq (by omega)).mp
        hterminal.1 with hold | hnew
    · exact hold
    · have hcol : r - 1 = H :=
        gameRecurrenceModel.fixed_q_injective hnew.1 hpreviewLe
          (hnew.2.trans hpreview.symm)
      omega
  exact ⟨hold, hterminal.2.1, hterminal.2.2, hpacket.2.2.1⟩

/-- Witness form of the same obstruction.  A first failure forces a copy
of the blocker in column `r-1` on some row from `r` through `q-1`.
The endpoint `a=r-1` is excluded because it would make the blocker both a
diagonal value and a row-start value. -/
theorem gameF_firstFailure_forces_early_terminal_sighting
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    exists a, r <= a /\ a < q /\ gameF a (r - 1) = q + 3 := by
  have hold :=
    (gameF_firstFailure_terminal_predecessor_old_packet
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview).1
  rcases hold with ⟨a, hca, haq, hvalue⟩
  have hra : r <= a := by
    apply Nat.le_of_not_gt
    intro har
    have hac : a = r - 1 := by omega
    have hdiag : gameF a a = q + 3 := by simpa [hac] using hvalue
    exact disjoint_D_S gameRecurrenceModel
      ⟨a, hdiag⟩ ⟨r, hrv, hstart⟩
  exact ⟨a, hra, haq, hvalue⟩

/-- Clean terminal-predecessor history is the exact extra input needed to
turn owner coverage and the lag-three preview into the upper rail. -/
theorem gameF_upperRail_of_terminal_predecessor_clean
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hterminalClean : Not (ColHistPred gameF q (r - 1) (q + 3))) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  exact hterminalClean
    (gameF_firstFailure_terminal_predecessor_old_packet
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview).1

#print axioms gameF_firstFailure_terminal_predecessor_old_packet
#print axioms gameF_firstFailure_forces_early_terminal_sighting
#print axioms gameF_upperRail_of_terminal_predecessor_clean

end ChompLean
