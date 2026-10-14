import R42FutureDiagonalGapGeneration

set_option autoImplicit false

namespace ChompLean

/-!
R43: source-capacity collapse of the future-diagonal first-gap branch.

At a cell `(q,r)`, exact MEX has only `q+r` source slots with which to
cover all positive values below the output.  On the diagonal this gives the
unconditional bound `d(q) <= 2*q+1`.  A future-diagonal prehost/loss has the
strict chronology

`q < a < x < d(q)`.

Consequently `x <= 2*q` and `a < 2*q`.  For the R33 future-first-gap
episode (`q=s` and `s+2<=a`) this does more than refine the three branches
of R42: it makes the far-owner premise impossible.  Thus neither a tail
downcross nor a shifted host is needed to discharge that trichotomy; its
near-owner branch always holds, in the sharper form `a < 2*s`.

No RM2 or UnitDip assumption is used.
-/

/-- Every diagonal output fits in its `2*q` positive source slots. -/
theorem recurrence_diagonal_source_capacity
    (M : RecurrenceModel) (q : Nat) :
    M.f q q <= q + q + 1 := by
  have hsat : LowerSaturated M.f q q (M.f q q) := by
    intro k hkpos hklt
    exact M.mex_no_skip (Nat.le_refl q) (M.diagonal_gt q)
      hkpos hklt
  have hcard := lowerSaturated_card_bound hsat
  omega

/-- A future diagonal prehost/loss lies in the strict source-capacity band:
both its value and its eventual owner are below the doubled old row. -/
theorem futureDiagonalPrehost_source_capacity_band
    (M : RecurrenceModel) {q a x : Nat}
    (hloss : FutureDiagonalPrehostLoss M q a x) :
    q < a /\
      a < x /\
      x <= q + q /\
      a + 1 <= q + q /\
      M.f q q <= q + q + 1 := by
  have hband := futureDiagonalPrehost_owner_band M hloss
  have hcap := recurrence_diagonal_source_capacity M q
  omega

/-- A delayed (`q+2<=a`) future-diagonal episode cannot start before row
three.  This combines the four units of forced diagonal slack with the
absolute diagonal source-capacity bound. -/
theorem delayed_futureDiagonalPrehost_requires_row_three
    (M : RecurrenceModel) {q a x : Nat}
    (hloss : FutureDiagonalPrehostLoss M q a x)
    (hdelay : q + 2 <= a) :
    3 <= q := by
  have hfour := delayed_futureDiagonalPrehost_forces_slack_four
    M hloss hdelay
  have hcap := recurrence_diagonal_source_capacity M q
  omega

/-- The future-first-gap branch is always sharply near-owner.  Its first
gap is at most `2*s`, and the owner is strictly below `2*s`. -/
theorem future_first_gap_source_capacity_collapse
    (M : RecurrenceModel) {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s) :
    3 <= s /\
      DipFirstGap M s <= s + s /\
      exists a,
        s + 2 <= a /\
        a + 1 <= s + s /\
        a <= M.f (s + 1) (s + 1) /\
        M.f a a = DipFirstGap M s := by
  rcases future_first_gap_is_future_prehost_loss M hFuture with
    ⟨a, ha, hloss⟩
  have hcapBand := futureDiagonalPrehost_source_capacity_band M hloss
  have hsThree := delayed_futureDiagonalPrehost_requires_row_three
    M hloss (by omega)
  refine ⟨hsThree, hcapBand.2.2.1, a, by omega,
    hcapBand.2.2.2.1, ?_, hloss.2.1⟩
  dsimp [DipFirstGap] at hcapBand
  omega

/-- The sharp band is independent of which diagonal-owner witness is
presented: diagonal injectivity identifies every such witness with the
future owner in `hFuture`. -/
theorem future_first_gap_every_owner_is_sharply_near
    (M : RecurrenceModel) {s a : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s)
    (haOwner : M.f a a = DipFirstGap M s) :
    s + 2 <= a /\ a + 1 <= s + s := by
  rcases future_first_gap_source_capacity_collapse M hFuture with
    ⟨_hs, _hgap, a₀, ha₀Lower, ha₀Sharp, _ha₀Next, ha₀Owner⟩
  have haa₀ : a = a₀ :=
    diagonal_injective M (haOwner.trans ha₀Owner.symm)
  subst a
  exact ⟨ha₀Lower, ha₀Sharp⟩

/-- No future-diagonal first-gap episode exists on rows `0,1,2`. -/
theorem no_future_first_gap_before_row_three
    (M : RecurrenceModel) {s : Nat}
    (hs : s < 3) :
    Not (DipFirstGapFutureDiagonalLoss M s) := by
  intro hFuture
  have hthree := (future_first_gap_source_capacity_collapse
    M hFuture).1
  omega

/-- Game-native replacement for the R42 trichotomy: the near-owner branch
always holds, and in fact has the strict bound `a<2*s`. -/
theorem game_future_first_gap_sharply_near_owner
    {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    exists a,
      s + 2 <= a /\
      a <= gameF (s + 1) (s + 1) /\
      gameF a a = DipFirstGap gameRecurrenceModel s /\
      a + 1 <= s + s /\
      a <= s + s + 1 := by
  rcases future_first_gap_source_capacity_collapse
      gameRecurrenceModel hFuture with
    ⟨_hs, _hgap, a, haLower, haSharp, haNext, haOwner⟩
  exact ⟨a, haLower, haNext, haOwner, haSharp, by omega⟩

/-- At the first row where such an episode is numerically possible, its
entire diagonal pattern is forced: `7,5,6` on rows `3,4,5`. -/
theorem future_first_gap_at_row_three_is_extremal
    (M : RecurrenceModel)
    (hFuture : DipFirstGapFutureDiagonalLoss M 3) :
    M.f 3 3 = 7 /\
      M.f 4 4 = 5 /\
      DipFirstGap M 3 = 6 /\
      M.f 5 5 = 6 := by
  rcases future_first_gap_source_capacity_collapse M hFuture with
    ⟨_hs, hgapCap, a, haLower, haSharp, _haNext, haOwner⟩
  have hd4gt := M.diagonal_gt 4
  have hgapDef : DipFirstGap M 3 = M.f 4 4 + 1 := rfl
  have hd4 : M.f 4 4 = 5 := by omega
  have hgap : DipFirstGap M 3 = 6 := by omega
  have hOld := hFuture.1
  have hOldCap := recurrence_diagonal_source_capacity M 3
  have hd3 : M.f 3 3 = 7 := by omega
  have haEq : a = 5 := by omega
  subst a
  exact ⟨hd3, hd4, hgap, by simpa [hgap] using haOwner⟩

#print axioms recurrence_diagonal_source_capacity
#print axioms futureDiagonalPrehost_source_capacity_band
#print axioms delayed_futureDiagonalPrehost_requires_row_three
#print axioms future_first_gap_source_capacity_collapse
#print axioms future_first_gap_every_owner_is_sharply_near
#print axioms no_future_first_gap_before_row_three
#print axioms game_future_first_gap_sharply_near_owner
#print axioms future_first_gap_at_row_three_is_extremal

end ChompLean
