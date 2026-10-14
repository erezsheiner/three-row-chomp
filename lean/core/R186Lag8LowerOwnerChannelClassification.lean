import R185GreedyTargetSeatLedger

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight W4: exact lower-owner channel classification

Put `p = u-5` and `t = u-8`.  At the old lag-eight target seat
`(t,c)`, lower-owner coverage has only two genuinely different ways to
make `p` available.

* If `p` has a diagonal owner at or before `g<c`, that owner is literally
  visible in the fixed `R` channel of `(t,c)`.
* If that `R` channel is clean, the diagonal arm is impossible.  Owner
  coverage therefore makes `p` a row-start value.  Row-start propagation
  then supplies a genuine lag-three host on row `t`, strictly before its
  freeze column.

Thus the empirical cell `F(u-5,g)=u-5` is not used as a premise.  The only
remaining discriminator is the concrete source bit `R gameF t c p`.

The last packet explains why the six fixed target rails do not decide this
bit: at every one of those six MEX cells, `p` is already preloaded by its
own affine history in the same column.
-/

/-- The fixed source channel at the old lag-eight seat sees `u-5` exactly
when owner coverage assigns `u-5` a diagonal owner. -/
theorem gameF_lag8_lowerOwner_R_iff_diagonal
    {u g c : Nat}
    (hu : 8 <= u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) :
    R gameF (u - 8) c (u - 5) <->
      exists d, d <= g /\ gameF d d = u - 5 := by
  constructor
  · intro hR
    rcases howners (u - 5) (by omega) (by omega) with
        hDiagonal | hRowstart
    · exact hDiagonal
    · rcases hRowstart with ⟨s, hsg, hsp, hfreeze⟩
      have hclean : Not (R gameF (u - 8) c (u - 5)) :=
        gameF_rowstart_R_clean_at_or_right_of_freeze_before_start
          hsp hfreeze (by omega) (by omega)
      exact False.elim (hclean hR)
  · rintro ⟨d, hdg, hdiag⟩
    refine ⟨d, by omega, ?_⟩
    have hdc : d <= c := by omega
    simpa [Nat.min_eq_left hdc] using hdiag

/-- Exact blocker arm.  Cleaning the old fixed-history channel is
equivalent to obtaining a covered row-start owner together with its genuine
lag-three host.  The final clause records fixed-row uniqueness of that
host. -/
theorem gameF_lag8_lowerOwner_R_clean_iff_blocker_with_lag3_host
    {u g c : Nat}
    (hu : 8 <= u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) :
    Not (R gameF (u - 8) c (u - 5)) <->
      exists s h,
        s <= g /\ s < u - 5 /\ gameF (u - 5) s = u - 5 /\
        h < s /\ gameF (u - 8) h = u - 5 /\
        C gameF (u - 8) c (u - 5) /\
        (forall h', h' <= u - 8 ->
          gameF (u - 8) h' = u - 5 -> h' = h) := by
  constructor
  · intro hclean
    rcases howners (u - 5) (by omega) (by omega) with
        hDiagonal | hRowstart
    · exact False.elim
        (hclean ((gameF_lag8_lowerOwner_R_iff_diagonal
          hu howners hgc hct).2 hDiagonal))
    · rcases hRowstart with ⟨s, hsg, hsp, hfreeze⟩
      have hst : s < u - 8 := by omega
      rcases rowStartPropagation gameRecurrenceModel
          hfreeze hsp hst (by omega) with ⟨h, hhs, hhost⟩
      have hC : C gameF (u - 8) c (u - 5) := by
        exact ⟨h, by omega, hhost⟩
      have hunique : forall h', h' <= u - 8 ->
          gameF (u - 8) h' = u - 5 -> h' = h := by
        intro h' hh't hh'value
        exact gameRecurrenceModel.fixed_q_injective
          hh't (by omega) (hh'value.trans hhost.symm)
      exact ⟨s, h, hsg, hsp, hfreeze, hhs, hhost, hC, hunique⟩
  · rintro ⟨s, _h, hsg, hsp, hfreeze, _hhs, _hhost, _hC, _hunique⟩
    exact gameF_rowstart_R_clean_at_or_right_of_freeze_before_start
      hsp hfreeze (by omega) (by omega)

/-- Exclusive W4 split at the old lag-eight seat.  The blocker arm contains
the lag-three host rather than assuming the empirical second freeze. -/
theorem gameF_lag8_lowerOwner_exact_source_split
    {u g c : Nat}
    (hu : 8 <= u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) :
    (exists d,
      d <= g /\ gameF d d = u - 5 /\
        R gameF (u - 8) c (u - 5)) \/
    (exists s h,
      s <= g /\ s < u - 5 /\ gameF (u - 5) s = u - 5 /\
        h < s /\ gameF (u - 8) h = u - 5 /\
        C gameF (u - 8) c (u - 5) /\
        Not (R gameF (u - 8) c (u - 5)) /\
        (forall h', h' <= u - 8 ->
          gameF (u - 8) h' = u - 5 -> h' = h)) := by
  by_cases hR : R gameF (u - 8) c (u - 5)
  · rcases (gameF_lag8_lowerOwner_R_iff_diagonal
      hu howners hgc hct).1 hR with ⟨d, hdg, hdiag⟩
    exact Or.inl ⟨d, hdg, hdiag, hR⟩
  · rcases (gameF_lag8_lowerOwner_R_clean_iff_blocker_with_lag3_host
      hu howners hgc hct).1 hR with
      ⟨s, h, hsg, hsp, hfreeze, hhs, hhost, hC, hunique⟩
    exact Or.inr
      ⟨s, h, hsg, hsp, hfreeze, hhs, hhost, hC, hR, hunique⟩

/-- Failed-band specialization in the coordinates `u=q+3`, `t=q-5` and
`c=r-1=g+1`.  Besides the exact owner split, the old target seat is a
genuine high MEX and is lower-saturated. -/
theorem gameF_lag8_atomic_burn_lowerOwner_exact_W4_split
    {q r g : Nat}
    (hq : 26 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hburn : gameF (q - 5) (r - 1) = q + 3) :
    IsMex (B gameF (q - 5) (r - 1)) (q + 3) /\
      LowerSaturated gameF (q - 5) (r - 1) (q + 3) /\
      ((exists d,
          d <= g /\ gameF d d = q - 2 /\
            R gameF (q - 5) (r - 1) (q - 2)) \/
        (exists s h,
          s <= g /\ s < q - 2 /\ gameF (q - 2) s = q - 2 /\
            h < s /\ gameF (q - 5) h = q - 2 /\
            C gameF (q - 5) (r - 1) (q - 2) /\
            Not (R gameF (q - 5) (r - 1) (q - 2)) /\
            (forall h', h' <= q - 5 ->
              gameF (q - 5) h' = q - 2 -> h' = h))) := by
  have hct : r - 1 <= q - 5 := by omega
  have hseat := gameF_high_target_exact_greedy_seat
    hct (by omega) hburn
  have hgc : g < r - 1 := by omega
  have hu8 : q + 3 - 8 = q - 5 := by omega
  have hu5 : q + 3 - 5 = q - 2 := by omega
  have hsplit := gameF_lag8_lowerOwner_exact_source_split
    (u := q + 3) (g := g) (c := r - 1)
    (by omega) howners hgc (by omega)
  rw [hu8, hu5] at hsplit
  exact And.intro hseat.1 (And.intro hseat.2.2.2 hsplit)

/-- The terminal freeze and a named lower diagonal owner are not competing
facts.  The diagonal owner is still seen in the old `R` channel; the
terminal barrier acts one target later, by blocking the recentered owner
coverage for `q+4`.  This records the precise quantifier mismatch which
prevents the R183 barrier from deciding the W4 arm. -/
theorem gameF_lag8_terminal_barrier_with_named_lower_diagonal
    {q r g : Nat}
    (hq : 26 <= q)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hatomic : r = g + 2)
    (hra : r <= q - 5)
    (hterminal : gameF (q + 3) r = q + 3)
    (hdiag : exists d, d <= g /\ gameF d d = q - 2) :
    R gameF (q - 5) (r - 1) (q - 2) /\
      Not (LowerOwnerCoveredBy (q + 4) (g - 1)) := by
  have hgc : g < r - 1 := by omega
  have hct : r - 1 <= q + 3 - 8 := by omega
  have hdiagRaw : exists d, d <= g /\ gameF d d = q + 3 - 5 := by
    simpa only [show q + 3 - 5 = q - 2 by omega] using hdiag
  have hRRaw := (gameF_lag8_lowerOwner_R_iff_diagonal
    (u := q + 3) (g := g) (c := r - 1)
    (by omega) howners hgc hct).2 hdiagRaw
  have hR : R gameF (q - 5) (r - 1) (q - 2) := by
    simpa only [show q + 3 - 8 = q - 5 by omega,
      show q + 3 - 5 = q - 2 by omega] using hRRaw
  have hfuture : Not (LowerOwnerCoveredBy (q + 4) (g - 1)) := by
    intro hownersNext
    rcases hownersNext (q + 3) (by omega) (by omega) with
        hDiagonal | hRowstart
    · rcases hDiagonal with ⟨d, _hdcut, hdd⟩
      exact disjoint_D_S gameRecurrenceModel
        ⟨d, hdd⟩ ⟨r, by omega, hterminal⟩
    · rcases hRowstart with ⟨s, hscut, hsV, hsstart⟩
      have hsr : s = r :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hsV) (by omega)
          (hsstart.trans hterminal.symm)
      omega
  exact ⟨hR, hfuture⟩

/-! ## Why the six fixed target rails cannot select the owner arm -/

/-- At each of the six fixed target rails, the lower W4 value `q-2` is
already in the old same-column history, independently of whether its
opening owner is diagonal or row-start. -/
def Lag8LowerValueSixRailPreloadPacket (q : Nat) : Prop :=
  ColTail gameF (q - 4) 11 (q - 2) /\
    ColTail gameF (q - 3) 9 (q - 2) /\
    ColTail gameF (q - 2) 7 (q - 2) /\
    ColTail gameF (q - 1) 5 (q - 2) /\
    ColTail gameF (q + 1) 2 (q - 2) /\
    ColTail gameF (q + 2) 0 (q - 2)

theorem gameF_lag8_lowerValue_sixRail_preloaded
    {q : Nat} (hq : 28 <= q) :
    Lag8LowerValueSixRailPreloadPacket q := by
  have h11raw := gameF_col11_rail (q := q - 9) (by omega)
  have h9raw := gameF_col9_rail (q := q - 8) (by omega)
  have h7raw := gameF_col7_rail (q := q - 7) (by omega)
  have h5raw := gameF_col5_rail (q := q - 6) (by omega)
  have h2raw := gameF_col2_rail (q := q - 4) (by omega)
  have h0raw := gameF_col0 (q - 3)
  refine ⟨⟨q - 9, by omega, by omega, by omega⟩,
    ⟨q - 8, by omega, by omega, by omega⟩,
    ⟨q - 7, by omega, by omega, by omega⟩,
    ⟨q - 6, by omega, by omega, by omega⟩,
    ⟨q - 4, by omega, by omega, by omega⟩,
    ⟨q - 3, by omega, by omega, by omega⟩⟩

/-- The target rail and the lower-value preload coexist at all six fixed
cells.  Consequently their exact high-MEX sources cannot distinguish the
two possible opening species of `q-2`; only a dynamic source can do so. -/
theorem gameF_lag8_targetSixRail_with_lowerValue_preload
    {q : Nat} (hq : 28 <= q) :
    Lag8TargetSixRailPacket q /\
      Lag8LowerValueSixRailPreloadPacket q := by
  exact ⟨gameF_lag8_target_sixRailPacket (by omega),
    gameF_lag8_lowerValue_sixRail_preloaded hq⟩

#print axioms gameF_lag8_lowerOwner_R_iff_diagonal
#print axioms gameF_lag8_lowerOwner_R_clean_iff_blocker_with_lag3_host
#print axioms gameF_lag8_lowerOwner_exact_source_split
#print axioms gameF_lag8_atomic_burn_lowerOwner_exact_W4_split
#print axioms gameF_lag8_terminal_barrier_with_named_lower_diagonal
#print axioms gameF_lag8_lowerValue_sixRail_preloaded
#print axioms gameF_lag8_targetSixRail_with_lowerValue_preload

end ChompLean
