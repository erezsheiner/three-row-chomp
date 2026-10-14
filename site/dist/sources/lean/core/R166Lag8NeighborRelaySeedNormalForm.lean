import R164Lag8PreviewOwnerTwoArmNormalForm
import LineHolePreservation
import R152LowTailCrossingDemand

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight neighbour relay: the first seeded cell and its exact aftermath

Put `q=v-3` and `c=r-1`.  The three certified lag-eight packets have

```
F(q-3,c-1)=q,   F(q-2,c-1)=q-2,
F(q,c-2)=v,     F(q,c)=q.
```

This file separates the part which is formally forced *after* naming the
first cells from the still-open chronological input.

The first equality alone already implies the owner-order atom used by
`R163`: a diagonal or row-start owner strictly left of `c` would force every
pre-owner reply strictly left of that owner, whereas `c-1` is the last
possible column left of `c`.  Thus the weakest useful neighbour atom is just
the first equality, not the full four-cell packet.

If the second equality is also named, the full recurrence gives an exact
row-source exchange.  The value `q-2` is present in the old row prefix, is
absent from persistent history, disappears from the replacement prefix,
and then carries for the next two rows.  If the observed `v@(q,c-2)` cell is
also named, the generic crossing law produces a saturated pre-freeze
supplier for `q-2` in column `c-2`.  Its exact row (`q-5` in all three
certified packets) is not forced here.
-/

/-- The weakest concrete neighbour-relay atom seen in the census: the
preview value occurs one row/column northwest of its eventual preview
freeze.  This is a proposed chronology statement, not asserted here. -/
def Lag8NeighborQSeed : Prop :=
  forall {v r : Nat},
    11 <= v ->
    r < v ->
    gameF v r = v ->
    r <= v - 8 ->
    gameF (v - 8) (r - 1) = v ->
    gameF (v - 6) (r - 2) = v - 3

/-- Source-native weakening of the first neighbour cell.  It retains only
the missing value which would allow that cell to emit `v-3`; lower-source
saturation and the non-carry guard are deliberately not included. -/
def Lag8NeighborQSourceHole : Prop :=
  forall {v r : Nat},
    11 <= v ->
    r < v ->
    gameF v r = v ->
    r <= v - 8 ->
    gameF (v - 8) (r - 1) = v ->
    Not (B gameF (v - 6) (r - 2) (v - 3))

/-- The first two cells of the observed neighbour relay. -/
def Lag8NeighborTwoCellSeed (v r : Nat) : Prop :=
  gameF (v - 6) (r - 2) = v - 3 /\
    gameF (v - 5) (r - 2) = v - 5

/-- A high neighbour seed is necessarily a MEX cell. -/
theorem gameF_lag8_neighbor_qSeed_isMex
    {v r : Nat}
    (hv : 11 <= v)
    (hra : r <= v - 8)
    (hseed : gameF (v - 6) (r - 2) = v - 3) :
    IsMex (B gameF (v - 6) (r - 2)) (v - 3) := by
  have hnotCarry :
      Not (r - 2 < v - 6 /\
        gameF ((v - 6) - 1) (r - 2) < v - 6) := by
    rintro ⟨hcol, hlow⟩
    have hcopy := gameF_brouwerRecurrence.1 hcol hlow
    rw [hseed] at hcopy
    omega
  have hmex := gameF_brouwerRecurrence.2
    (q := v - 6) (r := r - 2) (by omega) hnotCarry
  simpa [hseed] using hmex

/-- Literal channel decomposition of the first missing chronology bit.  At
the cell `(v-6,r-2)`, the debt is exactly the simultaneous exclusion of a
past diagonal, an old same-column host, and a current-row prefix host. -/
theorem lag8_neighbor_qSourceHole_iff_three_channel_holes
    {v r : Nat} :
    Not (B gameF (v - 6) (r - 2) (v - 3)) <->
      Not (DiagPrefix gameF (v - 6) (r - 2) (v - 3)) /\
      Not (ColTail gameF (v - 6) (r - 2) (v - 3)) /\
      Not (C gameF (v - 6) (r - 2) (v - 3)) := by
  constructor
  · intro hhole
    refine ⟨?_, ?_, ?_⟩
    · intro hD
      exact hhole (Or.inl
        (R_iff_diagPrefix_or_colTail.mpr (Or.inl hD)))
    · intro hCol
      exact hhole (Or.inl
        (R_iff_diagPrefix_or_colTail.mpr (Or.inr hCol)))
    · intro hC
      exact hhole (Or.inr hC)
  · rintro ⟨hD, hCol, hC⟩ (hR | hRow)
    · rcases R_iff_diagPrefix_or_colTail.mp hR with hDiag | hTail
      · exact hD hDiag
      · exact hCol hTail
    · exact hC hRow

/-- With the routine non-carry guard and lower saturation supplied, the
first neighbour equality is equivalent to the single source hole above.
This isolates the first prefix/chronology cell rather than hiding it inside
a four-cell empirical packet. -/
theorem gameF_lag8_neighbor_qSeed_iff_sourceHole_of_saturated
    {v r : Nat}
    (hv : 11 <= v)
    (hra : r <= v - 8)
    (hnotCarry :
      Not (r - 2 < v - 6 /\
        gameF ((v - 6) - 1) (r - 2) < v - 6))
    (hlower : forall k, 0 < k -> k < v - 3 ->
      B gameF (v - 6) (r - 2) k) :
    gameF (v - 6) (r - 2) = v - 3 <->
      Not (B gameF (v - 6) (r - 2) (v - 3)) := by
  constructor
  · intro hseed
    exact (gameF_lag8_neighbor_qSeed_isMex hv hra hseed).2.1
  · intro hhole
    exact gameF_value_of_source_mex
      (q := v - 6) (r := r - 2) (m := v - 3)
      (by omega) hnotCarry (by omega) hhole hlower

/-- The concrete neighbour output contains the source-hole bit. -/
theorem lag8NeighborQSourceHole_of_qSeed
    (hseedAtom : Lag8NeighborQSeed) :
    Lag8NeighborQSourceHole := by
  intro v r hv hrv hstart hra hburn
  have hseed := hseedAtom hv hrv hstart hra hburn
  exact (gameF_lag8_neighbor_qSeed_isMex hv hra hseed).2.1

/-- Even the source-hole weakening already excludes every opening owner
strictly left of `c=r-1`.  A left diagonal owner enters the history source;
a left row-start owner propagates into the strict row prefix. -/
theorem lag8PreviewOwnerNotLeft_of_neighborQSourceHole
    (hholeAtom : Lag8NeighborQSourceHole) :
    Lag8PreviewOwnerNotLeft := by
  intro v r hv hrv hstart hra hburn
  have hhole := hholeAtom hv hrv hstart hra hburn
  constructor
  · intro a hdiag
    apply Nat.le_of_not_gt
    intro hac
    apply hhole
    left
    refine ⟨a, by omega, ?_⟩
    have hmin : min a (r - 2) = a := Nat.min_eq_left (by omega)
    simpa [hmin] using hdiag
  · intro s hs hrow
    apply Nat.le_of_not_gt
    intro hsc
    have hst : s < v - 6 := by omega
    rcases rowStartPropagation gameRecurrenceModel
        hrow hs hst (by omega) with ⟨b, hbs, hvalue⟩
    apply hhole
    right
    exact ⟨b, by omega, hvalue⟩

/-- The first neighbour cell already contains the complete owner-order
content needed in R163.  No second neighbour cell, terminal preview MEX, or
exact freeze at `(v-3,r-1)` is used. -/
theorem lag8PreviewOwnerNotLeft_of_neighborQSeed
    (hseedAtom : Lag8NeighborQSeed) :
    Lag8PreviewOwnerNotLeft := by
  exact lag8PreviewOwnerNotLeft_of_neighborQSourceHole
    (lag8NeighborQSourceHole_of_qSeed hseedAtom)

/-- Consequently the one-cell neighbour atom closes the lag-eight branch
of an owner-covered failed band. -/
theorem gameF_lag8_failed_band_impossible_of_neighborQSeed
    {v r g : Nat}
    (hv : 11 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v)
    (hseedAtom : Lag8NeighborQSeed) :
    False := by
  exact gameF_lag8_failed_band_impossible_of_previewOwnerNotLeft
    hv hrv hstart howners hfailure hra hburn
      (lag8PreviewOwnerNotLeft_of_neighborQSeed hseedAtom)

/-- Scoped contrapositive, requiring no global chronology atom: every
owner-covered failed lag-eight packet must *deviate* from the empirical
neighbour relay at its first cell.  Thus proving this cell from the terminal
packet would immediately be the contradiction, not an additional cleanup
step. -/
theorem gameF_lag8_failed_band_neighborQSeed_ne
    {v r g : Nat}
    (hv : 11 <= v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8) :
    gameF (v - 6) (r - 2) ≠ v - 3 := by
  intro hseed
  have hhole := (gameF_lag8_neighbor_qSeed_isMex hv hra hseed).2.1
  have hqpos : 0 < v - 3 := by omega
  have hqv : v - 3 < v := by omega
  rcases howners (v - 3) hqpos hqv with
      ⟨a, hag, hdiag⟩ | ⟨s, hsg, hs, hrow⟩
  · apply hhole
    left
    refine ⟨a, by omega, ?_⟩
    have hmin : min a (r - 2) = a := Nat.min_eq_left (by omega)
    simpa [hmin] using hdiag
  · have hst : s < v - 6 := by omega
    rcases rowStartPropagation gameRecurrenceModel
        hrow hs hst (by omega) with ⟨b, hbs, hvalue⟩
    apply hhole
    right
    exact ⟨b, by omega, hvalue⟩

/-- Exact source-channel normal form at the first neighbour cell of a
failed owner-covered packet.  The preview value is present through its
left opening owner (diagonal prefix or propagated row prefix), while a
same-column historical tail is impossible in either owner arm. -/
theorem gameF_lag8_failed_band_neighbor_q_exact_owner_channel
    {v r g : Nat}
    (hv : 11 <= v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8) :
    (DiagPrefix gameF (v - 6) (r - 2) (v - 3) \/
      C gameF (v - 6) (r - 2) (v - 3)) /\
      Not (ColTail gameF (v - 6) (r - 2) (v - 3)) := by
  have hqpos : 0 < v - 3 := by omega
  have hqv : v - 3 < v := by omega
  have hopening := howners (v - 3) hqpos hqv
  have hownerChannel :
      DiagPrefix gameF (v - 6) (r - 2) (v - 3) \/
        C gameF (v - 6) (r - 2) (v - 3) := by
    rcases hopening with ⟨a, hag, hdiag⟩ | ⟨s, hsg, hs, hrow⟩
    · left
      exact ⟨a, by omega, by omega, hdiag⟩
    · right
      rcases rowStartPropagation gameRecurrenceModel (q := v - 6)
          hrow hs (by omega) (by omega) with ⟨b, hbs, hvalue⟩
      change gameF (v - 6) b = v - 3 at hvalue
      exact ⟨b, by omega, hvalue⟩
  refine ⟨hownerChannel, ?_⟩
  rintro ⟨w, hwt, hew, hwvalue⟩
  rcases howners (v - 3) hqpos hqv with
      ⟨a, hag, hdiag⟩ | ⟨s, hsg, hs, hrow⟩
  · have hleft := gameF_past_diagonal_echo_strictly_left
      (a := a) (q := w) (r := r - 2)
      (by omega) (by omega) (hwvalue.trans hdiag.symm)
    omega
  · rcases rowStartPropagation gameRecurrenceModel (q := w)
        hrow hs (by omega : s < w) (by omega : w < v - 3) with
        ⟨b, hbs, hbvalue⟩
    change gameF w b = v - 3 at hbvalue
    have heq : b = r - 2 :=
      gameRecurrenceModel.fixed_q_injective
        (by omega) (by omega) (hbvalue.trans hwvalue.symm)
    omega

/-- The second empirical neighbour cell has a weaker unconditional
consequence.  In an owner-covered failed packet, a freeze of `v-5` at
`r-2` forces the failed band to have the atomic width `r=g+2`. -/
theorem gameF_lag8_failed_band_neighborFreeze_pins_atomic_width
    {v r g : Nat}
    (hv : 11 <= v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8)
    (hfreeze : gameF (v - 5) (r - 2) = v - 5) :
    r = g + 2 := by
  have hkpos : 0 < v - 5 := by omega
  have hkv : v - 5 < v := by omega
  have herow : r - 2 < v - 5 := by omega
  rcases howners (v - 5) hkpos hkv with
      ⟨a, _hag, hdiag⟩ | ⟨s, hsg, hs, hrow⟩
  · exact False.elim
      (disjoint_D_S gameRecurrenceModel
        ⟨a, hdiag⟩ ⟨r - 2, herow, hfreeze⟩)
  · have heq : r - 2 = s :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt herow) (Nat.le_of_lt hs)
        (hfreeze.trans hrow.symm)
    omega

/-- Away from the atomic width, the first neighbour cell is not merely
different from `v-3`: owner saturation and the non-carry law force it to at least the terminal target.  Hence any attempt to reproduce the
empirical low neighbour word must first collapse to `r=g+2`. -/
theorem gameF_lag8_failed_band_wide_neighbor_is_high
    {v r g : Nat}
    (hv : 11 <= v)
    (howners : LowerOwnerCoveredBy v g)
    (hwide : g + 2 < r)
    (hra : r <= v - 8) :
    v <= gameF (v - 6) (r - 2) := by
  have htv : v - 6 < v := by omega
  have hge : g < r - 2 := by omega
  have het : r - 2 <= v - 6 := by omega
  have hnotCarry :
      Not (r - 2 < v - 6 /\
        gameF ((v - 6) - 1) (r - 2) < v - 6) :=
    gameF_noCarry_after_lowerOwnerCutoff
      (v := v) (s := g) (q := v - 6) (e := r - 2)
      htv hge howners
  have hmex := gameF_brouwerRecurrence.2
    (q := v - 6) (r := r - 2) het hnotCarry
  have hsat := gameF_ownerCovered_full_saturation
    (v := v) (g := g) (t := v - 6) (e := r - 2)
    howners htv hge het
  apply Nat.le_of_not_gt
  intro hlow
  exact hmex.2.1
    (hsat (gameF (v - 6) (r - 2)) hmex.1 hlow)

/-- Exact one-row chronology forced by the first two neighbour cells.

At row `v-6`, the lower value `v-5` is covered only by the row prefix.  On
the next row it is the MEX, so it is absent from both persistent history and
the replacement prefix.  The new row-start then carries through rows
`v-4` and `v-3` in the same column. -/
theorem gameF_lag8_neighbor_twoCell_exact_row_exchange
    {v r : Nat}
    (hv : 11 <= v)
    (hra : r <= v - 8)
    (hseed : Lag8NeighborTwoCellSeed v r) :
    IsMex (B gameF (v - 6) (r - 2)) (v - 3) /\
      C gameF (v - 6) (r - 2) (v - 5) /\
      Not (R gameF (v - 6) (r - 2) (v - 5)) /\
      IsMex (B gameF (v - 5) (r - 2)) (v - 5) /\
      Not (B gameF (v - 5) (r - 2) (v - 5)) /\
      Not (C gameF (v - 5) (r - 2) (v - 5)) /\
      gameF (v - 4) (r - 2) = v - 5 /\
      gameF (v - 3) (r - 2) = v - 5 := by
  have hmexOld := gameF_lag8_neighbor_qSeed_isMex
    hv hra hseed.1
  have holdCovered : B gameF (v - 6) (r - 2) (v - 5) :=
    hmexOld.2.2 (v - 5) (by omega) (by omega)
  have hnotCarryNew :
      Not (r - 2 < v - 5 /\
        gameF ((v - 5) - 1) (r - 2) < v - 5) := by
    rintro ⟨_hcol, hlow⟩
    have hrow : (v - 5) - 1 = v - 6 := by omega
    rw [hrow, hseed.1] at hlow
    omega
  have hmexNewRaw := gameF_brouwerRecurrence.2
    (q := v - 5) (r := r - 2) (by omega) hnotCarryNew
  have hmexNew : IsMex (B gameF (v - 5) (r - 2)) (v - 5) := by
    simpa [hseed.2] using hmexNewRaw
  have hnewHole : Not (B gameF (v - 5) (r - 2) (v - 5)) :=
    hmexNew.2.1
  have hnewHole' :
      Not (B gameF ((v - 6) + 1) (r - 2) (v - 5)) := by
    have hrow : (v - 6) + 1 = v - 5 := by omega
    rw [hrow]
    exact hnewHole
  have hexclusions :=
    (next_row_hole_iff_three_exclusions
      (f := gameF) (r := v - 6) (c := r - 2) (y := v - 5)
      (by omega)).mp hnewHole'
  have holdPrefix : C gameF (v - 6) (r - 2) (v - 5) := by
    rcases holdCovered with hR | hC
    · exact False.elim (hexclusions.1 hR)
    · exact hC
  have hcarryOneRaw := gameF_brouwerRecurrence.1
    (q := v - 4) (r := r - 2) (by omega) (by
      have hrow : (v - 4) - 1 = v - 5 := by omega
      rw [hrow, hseed.2]
      omega)
  have hcarryOne : gameF (v - 4) (r - 2) = v - 5 := by
    have hrow : (v - 4) - 1 = v - 5 := by omega
    rw [hrow, hseed.2] at hcarryOneRaw
    exact hcarryOneRaw
  have hcarryTwoRaw := gameF_brouwerRecurrence.1
    (q := v - 3) (r := r - 2) (by omega) (by
      have hrow : (v - 3) - 1 = v - 4 := by omega
      rw [hrow, hcarryOne]
      omega)
  have hcarryTwo : gameF (v - 3) (r - 2) = v - 5 := by
    have hrow : (v - 3) - 1 = v - 4 := by omega
    rw [hrow, hcarryOne] at hcarryTwoRaw
    exact hcarryTwoRaw
  have hreplacementHole :
      Not (C gameF (v - 5) (r - 2) (v - 5)) := by
    have hrow : (v - 6) + 1 = v - 5 := by omega
    simpa only [hrow] using hexclusions.2.2
  exact ⟨hmexOld, holdPrefix, hexclusions.1, hmexNew, hnewHole,
    hreplacementHole, hcarryOne, hcarryTwo⟩

/-- If the final observed preview freeze is also named, the old `v-3`
neighbour is an exact parked-only source loss on the horizontal edge
`r-2 -> r-1`.  This is the literal `B_successor_exact` debt: no new
diagonal, no replacement column tail, and no fresh current-row occurrence
rescues the value. -/
theorem gameF_lag8_neighbor_final_horizontal_source_loss
    {v r : Nat}
    (hv : 11 <= v)
    (hr2 : 2 <= r)
    (hra : r <= v - 8)
    (hseed : Lag8NeighborTwoCellSeed v r)
    (hfinal : gameF (v - 3) (r - 1) = v - 3) :
    B gameF (v - 3) (r - 2) (v - 3) /\
      Not (B gameF (v - 3) (r - 1) (v - 3)) /\
      ParkedOnly gameF (v - 3) (r - 2) (v - 3) /\
      Not (r - 1 < v - 3 /\ gameF (r - 1) (r - 1) = v - 3) /\
      Not (ColTail gameF (v - 3) (r - 1) (v - 3)) /\
      gameF (v - 3) (r - 2) ≠ v - 3 := by
  have hcurrent : B gameF (v - 3) (r - 2) (v - 3) := by
    left
    refine ⟨v - 6, by omega, ?_⟩
    have hmin : min (v - 6) (r - 2) = r - 2 :=
      Nat.min_eq_right (by omega)
    simpa [hmin] using hseed.1
  have hnotCarry :
      Not (r - 1 < v - 3 /\
        gameF ((v - 3) - 1) (r - 1) < v - 3) := by
    rintro ⟨hcol, hlow⟩
    have hcopy := gameF_brouwerRecurrence.1 hcol hlow
    rw [hfinal] at hcopy
    omega
  have hmexRaw := gameF_brouwerRecurrence.2
    (q := v - 3) (r := r - 1) (by omega) hnotCarry
  have hmex : IsMex (B gameF (v - 3) (r - 1)) (v - 3) := by
    simpa [hfinal] using hmexRaw
  have hnext : Not (B gameF (v - 3) (r - 1) (v - 3)) := hmex.2.1
  have hsucc : (r - 2) + 1 = r - 1 := by omega
  have hloss :
      B gameF (v - 3) (r - 2) (v - 3) /\
        Not (B gameF (v - 3) ((r - 2) + 1) (v - 3)) := by
    refine ⟨hcurrent, ?_⟩
    simpa [hsucc] using hnext
  have hnormal :=
    (source_loss_iff_parked_and_no_replacement
      (f := gameF) (t := v - 3) (e := r - 2) (z := v - 3)).mp hloss
  exact ⟨hcurrent, hnext, hnormal.1, by simpa [hsucc] using hnormal.2.1,
    by simpa [hsucc] using hnormal.2.2.1, hnormal.2.2.2⟩

/-- Adding the observed preview host `v@(v-3,r-3)` to the two-cell seed
forces a genuine saturated crossing supplier for the new blocker `v-5`.
The recurrence does not, with the present interfaces, pin its row to the
empirical value `v-8`. -/
theorem gameF_lag8_neighbor_preview_forces_crossing_supplier
    {v r : Nat}
    (hv : 11 <= v)
    (hr3 : 3 <= r)
    (hra : r <= v - 8)
    (hseed : Lag8NeighborTwoCellSeed v r)
    (hpreview : gameF (v - 3) (r - 3) = v) :
    exists a,
      r - 3 < a /\ a < v - 5 /\
      gameF a (r - 3) = v - 5 /\
      forall j, 0 < j -> j < v - 5 -> B gameF a (r - 3) j := by
  exact gameF_high_host_crossing_supplier_is_saturated
    (t := v - 3) (H := r - 3) (v := v)
    (k := v - 5) (rk := r - 2)
    hpreview (by omega) (by omega) (by omega) (by omega)
      (by omega) hseed.2

#print axioms gameF_lag8_neighbor_qSeed_isMex
#print axioms lag8_neighbor_qSourceHole_iff_three_channel_holes
#print axioms gameF_lag8_neighbor_qSeed_iff_sourceHole_of_saturated
#print axioms lag8NeighborQSourceHole_of_qSeed
#print axioms lag8PreviewOwnerNotLeft_of_neighborQSourceHole
#print axioms lag8PreviewOwnerNotLeft_of_neighborQSeed
#print axioms gameF_lag8_failed_band_impossible_of_neighborQSeed
#print axioms gameF_lag8_failed_band_neighborQSeed_ne
#print axioms gameF_lag8_failed_band_neighbor_q_exact_owner_channel
#print axioms gameF_lag8_failed_band_neighborFreeze_pins_atomic_width
#print axioms gameF_lag8_failed_band_wide_neighbor_is_high
#print axioms gameF_lag8_neighbor_twoCell_exact_row_exchange
#print axioms gameF_lag8_neighbor_final_horizontal_source_loss
#print axioms gameF_lag8_neighbor_preview_forces_crossing_supplier

end ChompLean
