import R159LiveTerminalPredecessorLag3Reduction

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight to lower freeze: the exact missing source set

Let `c=r-1`, `a=v-8`, and `t=v-3`.  From a lag-eight host at `(a,c)`
the existing recurrence API can follow the five transitions through row
`t`.  On a live column all six cells are genuine MEX cells, every output
is above its row, and every earlier same-column output belongs to every
later source.  Those facts still do not identify the MEX at row `t`.

The minimal remaining source assertion is simply that `t` itself is the
positive MEX of the one source `B gameF t c`.  The carry/MEX split then
shows that a lag-eight terminal host forces *some* lower freeze in column
`c`: a carry already exposes its carried value's freeze, while the MEX arm
freezes exactly at `t`.  This weaker conclusion is all owner coverage needs.
-/

/-- Abstract five-transition packet exported by the present local API.
It records MEX status, high/live outputs, and complete persistence of all
earlier same-column outputs into later sources. -/
def Lag8FiveStepMexPacket
    (v a t : Nat)
    (out : Nat -> Nat)
    (source : Nat -> Nat -> Prop) : Prop :=
  a + 8 = v /\
  t + 3 = v /\
  out a = v /\
  (forall s, a <= s -> s <= t -> IsMex (source s) (out s)) /\
  (forall s, a <= s -> s <= t -> s < out s) /\
  (forall u s, a <= u -> u < s -> s <= t -> source s (out u))

/-- On a column with no lower freeze, every cell below `v` is on the MEX
branch.  A hypothetical carry exposes a lower row-start at the same column,
contradicting liveness. -/
theorem gameF_cell_isMex_of_columnLiveBelow
    {v q c : Nat}
    (hlive : ColumnLiveBelow v c)
    (hcq : c <= q)
    (hqv : q < v) :
    IsMex (B gameF q c) (gameF q c) := by
  apply gameF_brouwerRecurrence.2 hcq
  rintro ⟨hcqStrict, hprevLow⟩
  have hcPrev : c <= q - 1 := by omega
  have hlow : gameF (q - 1) c <= q - 1 := by omega
  have hfreeze := gameF_low_cell_has_rowstart hcPrev hlow
  exact hlive (gameF (q - 1) c) hfreeze.1 (by omega) hfreeze.2

/-- Liveness also makes every such cell high relative to its own row. -/
theorem gameF_cell_above_row_of_columnLiveBelow
    {v q c : Nat}
    (hlive : ColumnLiveBelow v c)
    (hcq : c <= q)
    (hqv : q < v) :
    q < gameF q c := by
  apply Nat.lt_of_not_ge
  intro hlow
  have hfreeze := gameF_low_cell_has_rowstart hcq hlow
  exact hlive (gameF q c) hfreeze.1 (by omega) hfreeze.2

/-- Exact theorem-grade output of the current five-step API.  Notice that
it names the actual MEX on each row but does not say that the preview-row
MEX equals `v-3`. -/
theorem gameF_lag8_live_fiveStepMexPacket
    {v r : Nat}
    (hv : 11 <= v)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v)
    (hlive : ColumnLiveBelow v (r - 1)) :
    Lag8FiveStepMexPacket v (v - 8) (v - 3)
      (fun s => gameF s (r - 1))
      (fun s => B gameF s (r - 1)) := by
  refine ⟨by omega, by omega, hburn, ?_, ?_, ?_⟩
  · intro s has hst
    exact gameF_cell_isMex_of_columnLiveBelow hlive (by omega) (by omega)
  · intro s has hst
    exact gameF_cell_above_row_of_columnLiveBelow hlive (by omega) (by omega)
  · intro u s hau hus hst
    left
    refine ⟨u, hus, ?_⟩
    have hcu : r - 1 <= u := by omega
    simp [Nat.min_eq_right hcu]

/-- Positive MEX uniqueness, kept local so the reduction has no hidden
dependency on a separate transition package. -/
theorem r160_isMex_unique
    {S : Nat -> Prop} {x y : Nat}
    (hx : IsMex S x) (hy : IsMex S y) :
    x = y := by
  by_cases hxy : x < y
  · exact False.elim (hx.2.1 (hy.2.2 x hx.1 hxy))
  by_cases hyx : y < x
  · exact False.elim (hy.2.1 (hx.2.2 y hy.1 hyx))
  omega

/-- The one-source atom isolated by the carry/MEX audit.  Expanded, it says
that `v-3` is absent from `B gameF (v-3) (r-1)` and every positive smaller
value is present.  The atom is only defined here, not asserted for `gameF`.
-/
def Lag8PreviewSourceMex : Prop :=
  forall {v r : Nat},
    11 <= v ->
    r < v ->
    gameF v r = v ->
    r <= v - 8 ->
    gameF (v - 8) (r - 1) = v ->
    IsMex (B gameF (v - 3) (r - 1)) (v - 3)

/-- On a live column, the desired exact lag-three freeze is equivalent to
the single preview-source MEX assertion.  This is the sharp source-set
reduction of `F(v-3,r-1)=v-3`. -/
theorem gameF_lag8_preview_freeze_iff_sourceMex_of_live
    {v r : Nat}
    (hv : 11 <= v)
    (hra : r <= v - 8)
    (hlive : ColumnLiveBelow v (r - 1)) :
    gameF (v - 3) (r - 1) = v - 3 <->
      IsMex (B gameF (v - 3) (r - 1)) (v - 3) := by
  have hactual :
      IsMex (B gameF (v - 3) (r - 1))
        (gameF (v - 3) (r - 1)) :=
    gameF_cell_isMex_of_columnLiveBelow hlive (by omega) (by omega)
  constructor
  · intro hfreeze
    simpa [hfreeze] using hactual
  · intro hsource
    exact r160_isMex_unique hactual hsource

/-- The exact freeze follows from the one-source atom whenever the terminal
predecessor column is live. -/
theorem gameF_lag8_preview_freeze_of_sourceMex_and_live
    {v r : Nat}
    (hv : 11 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v)
    (hlive : ColumnLiveBelow v (r - 1))
    (hsource : Lag8PreviewSourceMex) :
    gameF (v - 3) (r - 1) = v - 3 := by
  apply (gameF_lag8_preview_freeze_iff_sourceMex_of_live hv hra hlive).2
  exact hsource hv hrv hstart hra hburn

/-- The stronger useful conclusion does not need liveness as a premise.
At row `v-3`, either the recurrence carries a low value, whose own row is
already a freeze at the terminal column, or it takes the MEX branch and the
source atom makes `v-3` that freeze. -/
theorem gameF_lag8_forces_some_lower_terminal_freeze_of_sourceMex
    {v r : Nat}
    (hv : 11 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v)
    (hsource : Lag8PreviewSourceMex) :
    exists z,
      r - 1 < z /\ z < v /\ gameF z (r - 1) = z := by
  let t := v - 3
  have hct : r - 1 < t := by dsimp [t]; omega
  by_cases hcarry :
      r - 1 < t /\ gameF (t - 1) (r - 1) < t
  · have hcPrev : r - 1 <= t - 1 := by omega
    have hlow : gameF (t - 1) (r - 1) <= t - 1 := by omega
    have hfreeze := gameF_low_cell_has_rowstart hcPrev hlow
    exact ⟨gameF (t - 1) (r - 1), hfreeze.1, by omega, hfreeze.2⟩
  · have hactual :
        IsMex (B gameF t (r - 1)) (gameF t (r - 1)) :=
      gameF_brouwerRecurrence.2 (Nat.le_of_lt hct) hcarry
    have htarget : IsMex (B gameF t (r - 1)) t := by
      dsimp [t]
      exact hsource hv hrv hstart hra hburn
    have heq : gameF t (r - 1) = t :=
      r160_isMex_unique hactual htarget
    exact ⟨t, hct, by dsimp [t]; omega, heq⟩

/-- Therefore the one-source atom removes the lag-eight terminal host from
an owner-covered failed band: every lower freeze column is pinned at or
left of the owner cutoff. -/
theorem gameF_lag8_failed_band_impossible_of_previewSourceMex
    {v r g : Nat}
    (hv : 11 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v)
    (hsource : Lag8PreviewSourceMex) :
    False := by
  rcases gameF_lag8_forces_some_lower_terminal_freeze_of_sourceMex
      hv hrv hstart hra hburn hsource with ⟨z, hcz, hzv, hfreeze⟩
  have hcg : r - 1 <= g :=
    lowerOwnerCoveredBy_pins_known_blocker_column
      howners (by omega) hzv hcz hfreeze
  omega

/-- Substituting the one-source atom for fixed-lag HOST-OLD removes the
`a=q-5` endpoint from the proved rail normal form and pushes the burn to
strictly before lag eight. -/
theorem gameF_firstFailure_burn_ladder_pre_lag9_of_previewSourceMex
    {q r g H : Nat}
    (hq : 23 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hsource : Lag8PreviewSourceMex) :
    exists a, r <= a /\ a < q - 5 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_pre_lag8_actual
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 5
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have ha : a = q - 5 := by omega
    subst a
    have hburn' : gameF ((q + 3) - 8) (r - 1) = q + 3 := by
      have hidx : (q + 3) - 8 = q - 5 := by omega
      rw [hidx]
      exact hburn
    exact False.elim
      (gameF_lag8_failed_band_impossible_of_previewSourceMex
        (v := q + 3) (r := r) (g := g)
        (by omega) hrv hstart howners hfailure (by omega) hburn' hsource)

/-! ## Exact local-interface separation

The following packet has six high MEX cells, preserves every earlier
same-column output in every later source, and starts with the lag-eight
target.  Nevertheless its preview source already contains `t=17`, so its
preview MEX is 25 rather than 17.  Thus the five-step exports above do not
imply `Lag8PreviewSourceMex`; a new source-hole/saturation theorem is needed.
-/

def r160CounterOut (s : Nat) : Nat := 20 + (s - 12)

def r160CounterSource (s k : Nat) : Prop :=
  0 < k /\ k < r160CounterOut s

theorem r160_fiveStep_packet_counterframe :
    Lag8FiveStepMexPacket 20 12 17
      r160CounterOut r160CounterSource /\
    r160CounterOut 17 != 17 /\
    r160CounterSource 17 17 /\
    Not (IsMex (r160CounterSource 17) 17) := by
  constructor
  · refine ⟨by omega, by omega, by simp [r160CounterOut], ?_, ?_, ?_⟩
    · intro s has hst
      refine ⟨by simp [r160CounterOut]; omega, ?_, ?_⟩
      · intro hmem
        exact (Nat.lt_irrefl (r160CounterOut s)) hmem.2
      · intro k hkpos hklt
        exact ⟨hkpos, hklt⟩
    · intro s has hst
      simp [r160CounterOut]
      omega
    · intro u s hau hus hst
      constructor
      · simp [r160CounterOut]
        omega
      · simp [r160CounterOut]
        omega
  · refine ⟨by simp [r160CounterOut], ?_, ?_⟩
    · exact ⟨by omega, by simp [r160CounterOut]⟩
    · intro hmex
      exact hmex.2.1 ⟨by omega, by simp [r160CounterOut]⟩

#print axioms gameF_cell_isMex_of_columnLiveBelow
#print axioms gameF_lag8_live_fiveStepMexPacket
#print axioms gameF_lag8_preview_freeze_iff_sourceMex_of_live
#print axioms gameF_lag8_forces_some_lower_terminal_freeze_of_sourceMex
#print axioms gameF_lag8_failed_band_impossible_of_previewSourceMex
#print axioms gameF_firstFailure_burn_ladder_pre_lag9_of_previewSourceMex
#print axioms r160_fiveStep_packet_counterframe

end ChompLean
