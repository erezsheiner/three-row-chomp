import R185GreedyTargetSeatLedger

set_option autoImplicit false

namespace ChompLean

/-!
# Greedy-seat density audit

The exact ledger from R185 has one useful strengthening: before a high
row-start target, every column without an old same-column copy of the target
emits a value strictly below the target.  Thus the only high-output escape
from the low-value injection is the literal `ColTail` bank.

This still does not create a fresh-seat gain.  The final source counterframe
shows the sharp obstruction: a source can already contain every value up to
`p + jump - 1` except `p`.  Emitting the single missing value `p` then moves
the positive MEX from `p` to `p + jump`, with all intermediate values fully
preloaded.  In particular the lag-eight comparison `u-5 -> u` does not, by
MEX algebra alone, force four additional seats between the two hosts.
-/

/-- Before a high terminal target host, a column is either a genuinely low
emission or contains an old same-column copy of the target.  Carry cells are
low by definition; non-carry lower-hole cells are low by the MEX law. -/
theorem gameF_before_high_rowstart_low_or_colTail
    {u r t c e : Nat}
    (hru : r < u) (hstart : gameF u r = u)
    (hct : c <= t) (htu : t < u) (hhost : gameF t c = u)
    (hec : e < c) :
    gameF t e < u \/ ColTail gameF t e u := by
  rcases gameF_before_high_rowstart_carry_or_colTail_or_lowerHole
      hru hstart hct htu hhost hec with hcarry | htail | hhole
  · left
    have heq := gameF_brouwerRecurrence.1 hcarry.1 hcarry.2
    omega
  · exact Or.inr htail
  · left
    by_cases hcarry : e < t /\ gameF (t - 1) e < t
    · have heq := gameF_brouwerRecurrence.1 hcarry.1 hcarry.2
      omega
    · exact mex_cell_lt_of_lower_hole
        (gameF_brouwerRecurrence.2 (by omega) hcarry) hhole

/-- In the lag-eight/two-blocker row, every clean column strictly between the
lag-three host and the lag-eight host emits a distinct low value different
from `u-5`.  This is the strongest automatic injection supplied by the R185
ledger; it lands in the large low-value bank, not in a new seat bank. -/
theorem gameF_lag8_between_hosts_clean_emission
    {u r c d e : Nat}
    (hu : 8 <= u)
    (hru : r < u) (hstart : gameF u r = u)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hlower : gameF (u - 8) d = u - 5)
    (hde : d < e) (hec : e < c)
    (hclean : Not (ColTail gameF (u - 8) e u)) :
    gameF (u - 8) e < u /\ gameF (u - 8) e ≠ u - 5 := by
  have hlow : gameF (u - 8) e < u :=
    Or.resolve_right
      (gameF_before_high_rowstart_low_or_colTail
        hru hstart hct (by omega) htarget hec)
      hclean
  refine ⟨hlow, ?_⟩
  intro heq
  have hcol : d = e :=
    gameRecurrenceModel.fixed_q_injective
      hdt (by omega) (hlower.trans heq.symm)
  omega

/-! ## Exact no-density source counterframe -/

/-- All positive values below `p+jump`, except the current hole `p`. -/
def GreedyPreloadedSource (p jump z : Nat) : Prop :=
  0 < z /\ z < p + jump /\ z ≠ p

/-- The source after the row prefix contributes the single value `p`. -/
def GreedyAfterHostSource (p jump z : Nat) : Prop :=
  GreedyPreloadedSource p jump z \/ z = p

/-- A single row-prefix insertion can cause an arbitrarily large MEX jump:
the old MEX is `p`, the source edit is exactly union with `{p}`, and the new
MEX is `p+jump`.  Every intermediate value was already present beforehand. -/
theorem greedy_preloaded_single_host_mex_jump
    (p jump : Nat) (hp : 0 < p) (hjump : 0 < jump) :
    IsMex (GreedyPreloadedSource p jump) p /\
      (forall z, GreedyAfterHostSource p jump z <->
        GreedyPreloadedSource p jump z \/ z = p) /\
      IsMex (GreedyAfterHostSource p jump) (p + jump) /\
      (forall z, p < z -> z < p + jump ->
        GreedyPreloadedSource p jump z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hp, ?_, ?_⟩
    · simp [GreedyPreloadedSource]
    · intro z hz0 hzp
      exact ⟨hz0, by omega, by omega⟩
  · intro z
    rfl
  · refine ⟨by omega, ?_, ?_⟩
    · simp [GreedyAfterHostSource, GreedyPreloadedSource]
      omega
    · intro z hz0 hzlt
      by_cases hzp : z = p
      · exact Or.inr hzp
      · exact Or.inl ⟨hz0, hzlt, hzp⟩
  · intro z hpz hzlt
    exact ⟨by omega, hzlt, by omega⟩

/-- The exact lag-eight numerical specialization: the jump from `u-5` to
`u` can be paid by the one emission `u-5`; the four values in between may
all have been present in the earlier source. -/
theorem greedy_lag8_five_step_jump_has_no_forced_intermediate_freshness
    {u : Nat} (hu : 5 < u) :
    IsMex (GreedyPreloadedSource (u - 5) 5) (u - 5) /\
      IsMex (GreedyAfterHostSource (u - 5) 5) u /\
      (forall z, u - 5 < z -> z < u ->
        GreedyPreloadedSource (u - 5) 5 z) := by
  have hpacket := greedy_preloaded_single_host_mex_jump
    (u - 5) 5 (by omega) (by omega)
  have hsum : u - 5 + 5 = u := by omega
  refine ⟨hpacket.1, ?_, ?_⟩
  · simpa [hsum] using hpacket.2.2.1
  · intro z hzlo hzhi
    exact hpacket.2.2.2 z hzlo (by omega)

/-- Even the strongest clean-column injection has seven spare low values in
the worst possible lag-eight interval.  Hence it cannot close by a direct
pigeonhole argument. -/
theorem lag8_between_host_low_value_bank_has_seven_slack
    {u c d : Nat} (hu : 8 <= u) (hdc : d < c) (hct : c <= u - 8) :
    c - d - 1 + 7 <= u - 2 := by
  omega

#print axioms gameF_before_high_rowstart_low_or_colTail
#print axioms gameF_lag8_between_hosts_clean_emission
#print axioms greedy_preloaded_single_host_mex_jump
#print axioms greedy_lag8_five_step_jump_has_no_forced_intermediate_freshness
#print axioms lag8_between_host_low_value_bank_has_seven_slack

end ChompLean
