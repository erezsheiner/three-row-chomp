import R177Lag8DiagonalOwnerEarlyDescent
import R174TerminalRelayHallSaturation

set_option autoImplicit false

namespace ChompLean

/-- The genuine replacement-opening packet left by a south-west source
hole.  Both opening kinds obey the same sharp `2*seat+1` capacity law. -/
def Lag8StrictLateOpening (g k : Nat) : Prop :=
  (exists d,
    g < d /\ d < k /\ gameF d d = k /\ k <= d + d + 1) \/
  (exists s,
    g < s /\ s < k /\ gameF k s = k /\ k <= s + s + 1)

/-!
# R183: a lost dynamic high value has a genuinely late opening

The south-west exchange in R177 left one apparently large obligation: every
dynamic value below `X = F(q-3,g)` should survive when the source moves from
`(q-3,g)` to `(q-2,g-1)`.  The theorem below gives the unconditional
contrapositive supplied by the actual recurrence.

If such a value is lost, its opening cannot lie at or to the left of the
cutoff `g`.  A diagonal opening left of `g` is already in the new diagonal
prefix.  A row-start opening left of `g` propagates to the new current-row
prefix; an opening exactly at `g` is excluded by the named freeze
`F(q-2,g)=q-2`.  Apart from the single boundary diagonal value `F(g,g)`, a
lost dynamic value therefore consumes a strict late opening seat `>g`.

This is an actual `gameF` theorem, with no chronology atom.  In the
diagonal arm we also retain the unconditional diagonal source-capacity
bound.
-/

/-- A dynamic value lost by the lag-eight south-west source shift must have
an opening strictly to the right of `g`.  The only diagonal boundary
exception is stated explicitly as `k != F(g,g)`. -/
theorem gameF_lag8_high_source_hole_forces_strict_late_opening
    {q r g k : Nat}
    (hq : 26 <= q)
    (hra : r <= q - 5)
    (hatomic : r = g + 2)
    (hsecond : gameF (q - 2) g = q - 2)
    (hkHigh : q + 3 <= k)
    (hkBoundary : Not (k = gameF g g))
    (hLost : Not (B gameF (q - 2) (g - 1) k)) :
    (exists d,
      g < d /\ d < k /\ gameF d d = k /\ k <= d + d + 1) \/
    (exists s,
      g < s /\ s < k /\ gameF k s = k /\ k <= s + s + 1) := by
  have hkPos : 0 < k := by omega
  have hgq : g < q - 2 := by omega
  rcases gameRecurrenceModel.opening_cover hkPos with
      hDiagonal | hRowstart
  · rcases hDiagonal with ⟨d, hdk, hdd⟩
    have hgd : g < d := by
      by_cases hgd : g < d
      · exact hgd
      · have hdg : d <= g := Nat.le_of_not_gt hgd
        by_cases hdEq : d = g
        · subst d
          exact False.elim (hkBoundary hdd.symm)
        · have hdPred : d <= g - 1 := by omega
          exact False.elim (hLost (Or.inl
            (R_iff_diagPrefix_or_colTail.mpr (Or.inl
              ⟨d, by omega, hdPred, hdd⟩))))
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel d
    exact Or.inl ⟨d, hgd, hdk, hdd, by omega⟩
  · rcases hRowstart with ⟨s, hsk, hstart⟩
    have hgs : g < s := by
      by_cases hgs : g < s
      · exact hgs
      · have hsg : s <= g := Nat.le_of_not_gt hgs
        by_cases hsEq : s = g
        · subst s
          exact False.elim
            (gameF_freeze_column_unique
              (r := g) (k₁ := q - 2) (k₂ := k)
              hgq hsecond (by omega) hstart)
        · have hsStrict : s < g := by omega
          rcases rowStartPropagation gameRecurrenceModel
              (p := k) (r := s) hstart hsk
              (q := q - 2) (by omega) (by omega) with
              ⟨b, hbs, hbhost⟩
          exact False.elim (hLost (Or.inr ⟨b, by omega, hbhost⟩))
    have hcap := gameF_terminal_freeze_value_le_twice_column_plus_one
      hsk hstart
    exact Or.inr ⟨s, hgs, hsk, hstart, hcap⟩

/-- Tail values admit the same strict-late conclusion without excluding the
boundary diagonal value and without using the named neighbour freeze.  In
the diagonal case ECHO-LEFT orders the old tail column before its owner; in
the row-start case `rowstart_host_order_exact` gives the identical order. -/
theorem gameF_lag8_oldTail_opening_strictly_right
    {q g k : Nat}
    (hgq : g < q - 3)
    (hkHigh : q - 3 < k)
    (hTail : ColTail gameF (q - 3) g k) :
    (exists d,
      g < d /\ d < k /\ gameF d d = k /\ k <= d + d + 1) \/
    (exists s,
      g < s /\ s < k /\ gameF k s = k /\ k <= s + s + 1) := by
  have hkPos : 0 < k := by omega
  rcases hTail with ⟨t, httop, hgt, hhost⟩
  rcases gameRecurrenceModel.opening_cover hkPos with
      hDiagonal | hRowstart
  · rcases hDiagonal with ⟨d, hdk, hdd⟩
    have hgd : g < d := by
      by_cases hdt : d < t
      · exact gameF_past_diagonal_echo_strictly_left
          (a := d) (q := t) (r := g)
          hdt (by omega) (hhost.trans hdd.symm)
      · by_cases htd : t < d
        · omega
        · have htdEq : t = d := by omega
          subst t
          have hcols : g = d :=
            gameRecurrenceModel.fixed_q_injective
              (Nat.le_of_lt hgt) (Nat.le_refl d)
              (hhost.trans hdd.symm)
          omega
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel d
    exact Or.inl ⟨d, hgd, hdk, hdd, by omega⟩
  · rcases hRowstart with ⟨s, hsk, hstart⟩
    have htlt : t < k := by omega
    have horder := rowstart_host_order_exact
      gameRecurrenceModel hsk hstart hgt (Nat.le_of_lt htlt) hhost
    rcases horder with ⟨_htk, hgs⟩ | ⟨htk, _hgs⟩
    · have hcap := gameF_terminal_freeze_value_le_twice_column_plus_one
        hsk hstart
      exact Or.inr ⟨s, hgs, hsk, hstart, hcap⟩
    · omega

/-- A useful exact split: any lost high dynamic value is either the single
boundary diagonal value, or it consumes a strict late opening seat. -/
theorem gameF_lag8_dynamic_high_transfer_or_boundaryPrefix_or_lateOpening
    {q r g k : Nat}
    (hq : 26 <= q)
    (hra : r <= q - 5)
    (hatomic : r = g + 2)
    (hsecond : gameF (q - 2) g = q - 2)
    (hkHigh : q + 3 <= k)
    (hDynamic :
      ColTail gameF (q - 3) g k \/ C gameF (q - 3) g k)
    :
    B gameF (q - 2) (g - 1) k \/
    (C gameF (q - 3) g k /\ k = gameF g g) \/
      (exists d,
        g < d /\ d < k /\ gameF d d = k /\ k <= d + d + 1) \/
      (exists s,
        g < s /\ s < k /\ gameF k s = k /\ k <= s + s + 1) := by
  by_cases hmem : B gameF (q - 2) (g - 1) k
  · exact Or.inl hmem
  · right
    by_cases hkBoundary : k = gameF g g
    · have hPrefix : C gameF (q - 3) g k := by
        rcases hDynamic with hTail | hPrefix
        · rcases hTail with ⟨t, httop, hgt, hhost⟩
          have hforbid :=
            encoding_diagonal_value_not_reemitted_in_owner_column
              game_encodes hgt
          exact False.elim (hforbid (by simpa only [hkBoundary] using hhost))
        · exact hPrefix
      exact Or.inl ⟨hPrefix, hkBoundary⟩
    · exact Or.inr
        (gameF_lag8_high_source_hole_forces_strict_late_opening
          hq hra hatomic hsecond hkHigh hkBoundary hmem)

/-!
The seeded replay has one extra prefix-only value: the diagonal value which
was deleted by the artificial seed replacement.  The next theorem explains
exactly why that is not a legal global exception.  In an actual game, every
dynamic value which is prefix-only at the receiver must still have one of
four genuine opening packets: the boundary diagonal, an early row-start
whose propagated copies are prefix-only on both rows, a strict late
diagonal, or a strict late row-start.  A deleted diagonal with no replacement
opening satisfies none of them.
-/

/-- Exact global-opening classification of a dynamic value which reaches
the south-west receiver only through its current prefix. -/
theorem gameF_lag8_dynamic_high_prefixOnly_opening_normalForm
    {q r g k : Nat}
    (hq : 26 <= q)
    (hra : r <= q - 5)
    (hatomic : r = g + 2)
    (hsecond : gameF (q - 2) g = q - 2)
    (hkHigh : q + 3 <= k)
    (hDynamic :
      ColTail gameF (q - 3) g k \/ C gameF (q - 3) g k)
    (hNewPrefix : C gameF (q - 2) (g - 1) k)
    (hNoNewR : Not (R gameF (q - 2) (g - 1) k)) :
    (C gameF (q - 3) g k /\
      C gameF (q - 2) (g - 1) k /\ k = gameF g g) \/
    (exists s,
      s < g /\ s < k /\ gameF k s = k /\ k <= s + s + 1 /\
      C gameF (q - 3) g k /\ C gameF (q - 2) (g - 1) k) \/
    (exists d,
      g < d /\ d < k /\ gameF d d = k /\ k <= d + d + 1) \/
    (exists s,
      g < s /\ s < k /\ gameF k s = k /\ k <= s + s + 1) := by
  have hkPos : 0 < k := by omega
  have hgq : g < q - 2 := by omega
  rcases gameRecurrenceModel.opening_cover hkPos with
      hDiagonal | hRowstart
  · rcases hDiagonal with ⟨d, hdk, hdd⟩
    have hgd : g <= d := by
      apply Nat.le_of_not_gt
      intro hdg
      have hdPred : d <= g - 1 := by omega
      apply hNoNewR
      apply R_iff_diagPrefix_or_colTail.mpr
      left
      exact ⟨d, by omega, hdPred, hdd⟩
    by_cases hdEq : d = g
    · subst d
      have hOldPrefix : C gameF (q - 3) g k := by
        rcases hDynamic with hTail | hPrefix
        · rcases hTail with ⟨t, httop, hgt, hhost⟩
          have hforbid :=
            encoding_diagonal_value_not_reemitted_in_owner_column
              game_encodes hgt
          exact False.elim (hforbid (hhost.trans hdd.symm))
        · exact hPrefix
      exact Or.inl ⟨hOldPrefix, hNewPrefix, hdd.symm⟩
    · have hcap := recurrence_diagonal_source_capacity
        gameRecurrenceModel d
      exact Or.inr (Or.inr (Or.inl
        ⟨d, by omega, hdk, hdd, by omega⟩))
  · rcases hRowstart with ⟨s, hsk, hstart⟩
    by_cases hsg : s < g
    · have hOldPrefix : C gameF (q - 3) g k := by
        rcases hDynamic with hTail | hPrefix
        · rcases hTail with ⟨t, httop, hgt, hhost⟩
          have htlt : t < k := by omega
          have horder := rowstart_host_order_exact
            gameRecurrenceModel hsk hstart hgt
              (Nat.le_of_lt htlt) hhost
          rcases horder with ⟨_htk, hgs⟩ | ⟨htk, _⟩ <;> omega
        · exact hPrefix
      have hcap := gameF_terminal_freeze_value_le_twice_column_plus_one
        hsk hstart
      exact Or.inr (Or.inl
        ⟨s, hsg, hsk, hstart, hcap, hOldPrefix, hNewPrefix⟩)
    · have hgs : g < s := by
        have hle : g <= s := Nat.le_of_not_gt hsg
        by_cases hsEq : s = g
        · subst s
          exact False.elim
            (gameF_freeze_column_unique
              (r := g) (k₁ := q - 2) (k₂ := k)
              hgq hsecond (by omega) hstart)
        · omega
      have hcap := gameF_terminal_freeze_value_le_twice_column_plus_one
        hsk hstart
      exact Or.inr (Or.inr (Or.inr ⟨s, hgs, hsk, hstart, hcap⟩))

/-!
## Exact replacement-opening reduction

R177 phrased the last high-interval debt in terms of arbitrary dynamic
source channels.  The opening classification above removes the replay
artifact from that debt.  It is enough, and also necessary, to cover only
values which have a genuine strict late opening.  Early row-start values
are automatically propagated into the receiver prefix; a deleted diagonal
with no replacement opening is therefore not among the legal residuals.
-/

/-- Exact source-exchange criterion expressed purely through genuine late
openings.  This is equivalent to R177's dynamic-channel packet, but its last
line cannot be satisfied by the replay's deleted diagonal artifact. -/
theorem gameF_lag8_atomic_strictHigh_southwest_iff_lateOpening_packet
    {q r g : Nat}
    (hq : 26 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : r <= q - 5)
    (hatomic : r = g + 2)
    (hsecond : gameF (q - 2) g = q - 2)
    (hhigh : q + 3 < gameF (q - 3) g) :
    gameF (q - 2) (g - 1) = gameF (q - 3) g <->
      q - 2 <= gameF (q - 3) (g - 1) /\
      Not (ColTail gameF (q - 2) (g - 1) (gameF (q - 3) g)) /\
      Not (C gameF (q - 2) (g - 1) (gameF (q - 3) g)) /\
      (gameF g g < gameF (q - 3) g ->
        B gameF (q - 2) (g - 1) (gameF g g)) /\
      (forall k, q + 3 <= k -> k < gameF (q - 3) g ->
        (ColTail gameF (q - 3) g k \/ C gameF (q - 3) g k) ->
        Lag8StrictLateOpening g k ->
        B gameF (q - 2) (g - 1) k) := by
  have hiff :=
    gameF_lag8_atomic_strictHigh_southwest_iff_minimal_dynamic_packet
      hq howners hra hatomic hsecond hhigh
  constructor
  · intro hreceiver
    rcases hiff.mp hreceiver with
      ⟨hnoCarry, hnoTail, hnoPrefix, hBoundary, hDynamic⟩
    exact ⟨hnoCarry, hnoTail, hnoPrefix, hBoundary,
      fun k hkHigh hkX hkDynamic _hLate =>
        hDynamic k hkHigh hkX hkDynamic⟩
  · rintro ⟨hnoCarry, hnoTail, hnoPrefix, hBoundary, hLateCovered⟩
    apply hiff.mpr
    refine ⟨hnoCarry, hnoTail, hnoPrefix, hBoundary, ?_⟩
    intro k hkHigh hkX hkDynamic
    have hopening :=
      gameF_lag8_dynamic_high_transfer_or_boundaryPrefix_or_lateOpening
        hq hra hatomic hsecond hkHigh hkDynamic
    rcases hopening with hmem | hboundary | hdiag | hrow
    · exact hmem
    · have hkEq : k = gameF g g := hboundary.2
      rw [hkEq]
      exact hBoundary (by simpa only [hkEq] using hkX)
    · exact hLateCovered k hkHigh hkX hkDynamic (Or.inl hdiag)
    · exact hLateCovered k hkHigh hkX hkDynamic (Or.inr hrow)

/-- Failure of the south-west transport does not leave an amorphous
universal debt.  Under the four non-opening side conditions, the actual
receiver output is a strictly smaller high MEX, is dynamic in the old
source, and itself carries a genuine strict late opening.  Thus every
failure exposes one concrete replacement opener. -/
theorem gameF_lag8_southwest_failure_exposes_strict_late_opening_mex
    {q r g : Nat}
    (hq : 26 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : r <= q - 5)
    (hatomic : r = g + 2)
    (hsecond : gameF (q - 2) g = q - 2)
    (hhigh : q + 3 < gameF (q - 3) g)
    (hnoCarry : q - 2 <= gameF (q - 3) (g - 1))
    (hnoTail :
      Not (ColTail gameF (q - 2) (g - 1) (gameF (q - 3) g)))
    (hnoPrefix :
      Not (C gameF (q - 2) (g - 1) (gameF (q - 3) g)))
    (hBoundary : gameF g g < gameF (q - 3) g ->
      B gameF (q - 2) (g - 1) (gameF g g)) :
    let X := gameF (q - 3) g
    let Y := gameF (q - 2) (g - 1)
    Y = X \/
      (q + 3 <= Y /\ Y < X /\
        IsMex (B gameF (q - 2) (g - 1)) Y /\
        (ColTail gameF (q - 3) g Y \/ C gameF (q - 3) g Y) /\
        Not (B gameF (q - 2) (g - 1) Y) /\
        Lag8StrictLateOpening g Y) := by
  let X := gameF (q - 3) g
  let Y := gameF (q - 2) (g - 1)
  have hnotCarry :
      Not (g - 1 < q - 2 /\
        gameF ((q - 2) - 1) (g - 1) < q - 2) := by
    rintro ⟨_hcol, hlow⟩
    have hrow : (q - 2) - 1 = q - 3 := by omega
    rw [hrow] at hlow
    omega
  have hmexY : IsMex (B gameF (q - 2) (g - 1)) Y := by
    dsimp only [Y]
    exact gameF_brouwerRecurrence.2 (by omega) hnotCarry
  have hXpos : 0 < X := by dsimp only [X]; omega
  have hsourceNF :=
    gameF_lag8_strictHigh_neighbor_southwest_source_normalForm
      hq hra hatomic hhigh
  have hXhole : Not (B gameF (q - 2) (g - 1) X) := by
    apply hsourceNF.2.2.mpr
    exact ⟨by simpa only [X] using hnoTail,
      by simpa only [X] using hnoPrefix⟩
  have hYleX : Y <= X := by
    apply Nat.le_of_not_gt
    intro hXY
    exact hXhole (hmexY.2.2 X hXpos hXY)
  by_cases hYX : Y = X
  · exact Or.inl hYX
  · right
    have hYLtX : Y < X := by omega
    have hSecond : B gameF (q - 2) (g - 1) (q - 2) :=
      gameF_lag8_atomic_southwest_qminus2_mem_of_diagonal_boundary
        hq howners hra hatomic hsecond hhigh hnoCarry hBoundary
    have hLowSaturated : forall k, 0 < k -> k < q + 3 ->
        B gameF (q - 2) (g - 1) k := by
      intro k hkpos hkLow
      by_cases hkSecond : k = q - 2
      · simpa only [hkSecond] using hSecond
      · by_cases hkBoundary : k = gameF g g
        · subst k
          exact hBoundary (by omega)
        · exact gameF_lag8_atomic_southwest_low_saturation_except_two
            hq howners hra hatomic hsecond k hkpos hkLow
              hkSecond hkBoundary
    have hYHigh : q + 3 <= Y := by
      apply Nat.le_of_not_gt
      intro hYLow
      exact hmexY.2.1 (hLowSaturated Y hmexY.1 hYLow)
    have hmexOld : IsMex (B gameF (q - 3) g) X := by
      dsimp only [X]
      exact gameF_high_host_isMex (by omega) (by omega) rfl
    have hYOld : B gameF (q - 3) g Y :=
      hmexOld.2.2 Y hmexY.1 hYLtX
    have hYBoundaryNe : Not (Y = gameF g g) := by
      intro hEq
      apply hmexY.2.1
      rw [hEq]
      exact hBoundary (by simpa only [hEq] using hYLtX)
    have hYDynamic :
        ColTail gameF (q - 3) g Y \/ C gameF (q - 3) g Y := by
      rcases hYOld with hR | hC
      · rcases R_iff_diagPrefix_or_colTail.mp hR with hD | hTail
        · rcases hD with ⟨d, hdrow, hdg, hdd⟩
          by_cases hdPred : d <= g - 1
          · exact False.elim (hmexY.2.1 (Or.inl
              (R_iff_diagPrefix_or_colTail.mpr (Or.inl
                ⟨d, by omega, hdPred, hdd⟩))))
          · have hdEq : d = g := by omega
            subst d
            exact False.elim (hYBoundaryNe hdd.symm)
        · exact Or.inl hTail
      · exact Or.inr hC
    have hLate : Lag8StrictLateOpening g Y := by
      exact gameF_lag8_high_source_hole_forces_strict_late_opening
        hq hra hatomic hsecond hYHigh hYBoundaryNe hmexY.2.1
    exact ⟨hYHigh, hYLtX, hmexY, hYDynamic, hmexY.2.1, hLate⟩

/-! ## Can the descent be iterated at the exposed opener? -/

/-- A terminal freeze at column `r` permanently blocks owner coverage for
every larger target at every stricter cutoff `cutoff < r`.  Indeed,
coverage of `v` below the larger target would have to give it either a
diagonal opening (forbidden by D/S disjointness) or a second row-start
column at most `cutoff` (forbidden by fixed-row injectivity). -/
theorem gameF_terminal_freeze_blocks_higher_ownerCoverage_left
    {v w r cutoff : Nat}
    (hvpos : 0 < v)
    (hvw : v < w)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hcut : cutoff < r) :
    Not (LowerOwnerCoveredBy w cutoff) := by
  intro hownersNext
  rcases hownersNext v hvpos hvw with
      hDiagonal | hRowstart
  · rcases hDiagonal with ⟨d, _hdcut, hdd⟩
    exact disjoint_D_S gameRecurrenceModel
      ⟨d, hdd⟩ ⟨r, hrv, hstart⟩
  · rcases hRowstart with ⟨s, hscut, hsV, hsstart⟩
    have hsr : s = r :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hsV) (Nat.le_of_lt hrv)
        (hsstart.trans hstart.symm)
    omega

/-- Successor-target specialization of the preceding permanent barrier. -/
theorem gameF_terminal_freeze_blocks_next_ownerCoverage_left
    {v r cutoff : Nat}
    (hvpos : 0 < v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hcut : cutoff < r) :
    Not (LowerOwnerCoveredBy (v + 1) cutoff) := by
  exact gameF_terminal_freeze_blocks_higher_ownerCoverage_left
    hvpos (by omega) hrv hstart hcut

/-- The natural geometric recentering of a south-west step would use
`q' = q+1` and `g' = g-1`; its owner hypothesis is therefore
`LowerOwnerCoveredBy (q+4) (g-1)`.  The old terminal freeze
`F(q+3,r)=q+3`, with `r=g+2`, makes that hypothesis impossible.  Hence the
lag-eight failure theorem cannot be iterated by a self-similar one-row,
one-column shift. -/
theorem gameF_lag8_southwest_recenter_ownerCoverage_impossible
    {q r g : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (hatomic : r = g + 2) :
    Not (LowerOwnerCoveredBy (q + 4) (g - 1)) := by
  have hblock := gameF_terminal_freeze_blocks_next_ownerCoverage_left
    (v := q + 3) (r := r) (cutoff := g - 1)
    (by omega) hrv hstart (by omega)
  simpa only [show q + 3 + 1 = q + 4 by omega] using hblock

/-- The empirical A7 adjacent-freeze word cannot itself supply `hsecond`
inside the diagonal-owner arm.  Its left freeze `F(q,c)=q` is a row-start
opening of `q`, and is disjoint from any diagonal opening `F(d,d)=q`.
Thus importing A7 into the diagonal replay would be circularly mixing the
two mutually exclusive opening branches. -/
theorem gameF_diagonalOwner_excludes_A7_leftFreeze
    {q c d : Nat}
    (hcq : c < q)
    (hfreeze : gameF q c = q)
    (hdiag : gameF d d = q) :
    False := by
  exact disjoint_D_S gameRecurrenceModel
    ⟨d, hdiag⟩ ⟨c, hcq, hfreeze⟩

/-- Chronology trichotomy for a high host carrying a strict late opening.
A diagonal opener is either already past (hence the cell is an ordinary
strict-left echo) or genuinely future, in which case the host is an actual
`FutureDiagonalPrehostLoss`.  A row-start opener instead carries the full
all-depth terminal relay certificate.  These are three different global
species; none is another lag-eight atomic neighbour packet. -/
theorem gameF_strictLateOpening_highHost_chronology
    {t g Y : Nat}
    (hgpos : 0 < g)
    (hgt : g < t)
    (hhost : gameF t (g - 1) = Y)
    (hLate : Lag8StrictLateOpening g Y) :
    (exists d,
      g < d /\ d < t /\ gameF d d = Y /\
      gameF t (g - 1) = Y /\ Y <= d + d + 1) \/
    (exists d,
      t < d /\ d < Y /\ gameF d d = Y /\
      FutureDiagonalPrehostLoss gameRecurrenceModel t d Y /\
      Y <= d + d + 1) \/
    (exists s host,
      g < s /\ s < Y /\ gameF Y s = Y /\
      gameF t (g - 1) = Y /\ Y <= s + s + 1 /\
      TerminalRelayHallCertificate Y s host) := by
  rcases hLate with hDiagonal | hRowstart
  · rcases hDiagonal with ⟨d, hgd, hdY, hdd, hcap⟩
    by_cases hdt : d < t
    · exact Or.inl ⟨d, hgd, hdt, hdd, hhost, hcap⟩
    · by_cases htd : t < d
      · have hC : C gameF t t Y := by
          exact ⟨g - 1, by omega, hhost⟩
        have hAbsent : Not (B gameF d d Y) := by
          intro hB
          have hmexD : IsMex (B gameF d d) (gameF d d) :=
            recurrence_diagonal_exact_mex gameRecurrenceModel d
          rw [hdd] at hmexD
          exact hmexD.2.1 hB
        have hPrehost :
            FutureDiagonalPrehostLoss gameRecurrenceModel t d Y :=
          ⟨htd, hdd, hC, hAbsent⟩
        exact Or.inr (Or.inl
          ⟨d, htd, hdY, hdd, hPrehost, hcap⟩)
      · have hdtEq : d = t := by omega
        subst d
        have hcols : g - 1 = t :=
          gameRecurrenceModel.fixed_q_injective
            (by omega) (Nat.le_refl t) (hhost.trans hdd.symm)
        omega
  · rcases hRowstart with ⟨s, hgs, hsY, hstart, hcap⟩
    rcases gameF_terminal_freeze_relay_hall_certificate
        hsY hstart with ⟨host, hcert⟩
    exact Or.inr (Or.inr
      ⟨s, host, hgs, hsY, hstart, hhost, hcap, hcert⟩)

/-- Specialization of the chronology trichotomy to the concrete smaller
MEX exposed by a failed lag-eight south-west step.  This is the sharp
iteration obstruction: the next object is a past echo, a future-diagonal
prehost loss, or a row-start relay.  Reapplying the lag-eight theorem would
instead require a new terminal target and a new named neighbour freeze. -/
theorem gameF_lag8_southwest_failure_opening_chronology
    {q r g : Nat}
    (hq : 26 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : r <= q - 5)
    (hatomic : r = g + 2)
    (hsecond : gameF (q - 2) g = q - 2)
    (hhigh : q + 3 < gameF (q - 3) g)
    (hnoCarry : q - 2 <= gameF (q - 3) (g - 1))
    (hnoTail :
      Not (ColTail gameF (q - 2) (g - 1) (gameF (q - 3) g)))
    (hnoPrefix :
      Not (C gameF (q - 2) (g - 1) (gameF (q - 3) g)))
    (hBoundary : gameF g g < gameF (q - 3) g ->
      B gameF (q - 2) (g - 1) (gameF g g))
    (hfailure :
      Not (gameF (q - 2) (g - 1) = gameF (q - 3) g)) :
    let Y := gameF (q - 2) (g - 1)
    (exists d,
      g < d /\ d < q - 2 /\ gameF d d = Y /\
      gameF (q - 2) (g - 1) = Y /\ Y <= d + d + 1) \/
    (exists d,
      q - 2 < d /\ d < Y /\ gameF d d = Y /\
      FutureDiagonalPrehostLoss gameRecurrenceModel (q - 2) d Y /\
      Y <= d + d + 1) \/
    (exists s host,
      g < s /\ s < Y /\ gameF Y s = Y /\
      gameF (q - 2) (g - 1) = Y /\ Y <= s + s + 1 /\
      TerminalRelayHallCertificate Y s host) := by
  let Y := gameF (q - 2) (g - 1)
  have hwitness :=
    gameF_lag8_southwest_failure_exposes_strict_late_opening_mex
      hq howners hra hatomic hsecond hhigh hnoCarry
        hnoTail hnoPrefix hBoundary
  rcases hwitness with hsuccess | hfail
  · exact False.elim (hfailure (by simpa only [Y] using hsuccess))
  · have hgpos : 0 < g := by
      apply Nat.pos_of_ne_zero
      intro hgzero
      have hcol0 := gameF_col0 (q - 2)
      rw [hgzero] at hsecond
      omega
    have hchron := gameF_strictLateOpening_highHost_chronology
      (t := q - 2) (g := g) (Y := Y)
      hgpos (by omega) (by rfl) hfail.2.2.2.2.2
    simpa only [Y] using hchron

#print axioms gameF_lag8_high_source_hole_forces_strict_late_opening
#print axioms gameF_lag8_oldTail_opening_strictly_right
#print axioms gameF_lag8_dynamic_high_transfer_or_boundaryPrefix_or_lateOpening
#print axioms gameF_lag8_dynamic_high_prefixOnly_opening_normalForm
#print axioms gameF_lag8_atomic_strictHigh_southwest_iff_lateOpening_packet
#print axioms gameF_lag8_southwest_failure_exposes_strict_late_opening_mex
#print axioms gameF_terminal_freeze_blocks_higher_ownerCoverage_left
#print axioms gameF_terminal_freeze_blocks_next_ownerCoverage_left
#print axioms gameF_lag8_southwest_recenter_ownerCoverage_impossible
#print axioms gameF_diagonalOwner_excludes_A7_leftFreeze
#print axioms gameF_strictLateOpening_highHost_chronology
#print axioms gameF_lag8_southwest_failure_opening_chronology

end ChompLean
