import R197B31ReverseInclusion

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R198: a local recurrence frontier for B43

The settled-immortal obstruction of R197 looks infinitary, but a settled
tail through a skipped host forces two concrete successor cells:

`F(u-m+1,x)=u+1` and `F(u-m+2,x)=u+2`.

Consequently B43 follows from a two-cell local law saying that these two
equalities never occur together.  The one-cell strengthening is false in
the cache, so retaining both cells is essential.

This file also gives the exact MEX normal form of the two-cell law.  If the
first successor equality holds, the second cell is necessarily a MEX cell.
It fails to continue the affine chain exactly when `u+2` is already in its
source, or some smaller positive value is absent from that source.
-/

/-- The six exceptional lags used by B30/B31. -/
def B43LocalSkippedLag (m : Nat) : Prop :=
  m = 3 ∨ m = 8 ∨ m = 10 ∨ m = 13 ∨ m = 18 ∨ m = 20

/-- General MEX comparison: a positive target differs from the MEX exactly
when the target is filled or a smaller positive hole occurs first. -/
theorem isMex_ne_target_iff_target_filled_or_lower_hole
    {S : Nat -> Prop} {v z : Nat}
    (hzpos : 0 < z) (hmex : IsMex S v) :
    v ≠ z ↔
      S z ∨ exists k, 0 < k ∧ k < z ∧ Not (S k) := by
  constructor
  · intro hvz
    by_cases hzFilled : S z
    · exact Or.inl hzFilled
    · right
      have hvle : v <= z := by
        apply Nat.le_of_not_gt
        intro hzv
        exact hzFilled (hmex.2.2 z hzpos hzv)
      exact ⟨v, hmex.1, by omega, hmex.2.1⟩
  · rintro (hzFilled | ⟨k, hkpos, hkz, hkHole⟩) hvz
    · exact hmex.2.1 (by simpa [hvz] using hzFilled)
    · apply hkHole
      exact hmex.2.2 k hkpos (by omega)

/-- Once the first affine successor is present, the second successor cell
cannot be a carry cell and is therefore governed by MEX. -/
theorem gameF_second_successor_is_mex_of_first_affine_successor
    {t x u : Nat}
    (hxt : x <= t)
    (htwo : t + 2 < u)
    (hfirst : gameF (t + 1) x = u + 1) :
    IsMex (B gameF (t + 2) x) (gameF (t + 2) x) := by
  apply gameF_brouwerRecurrence.2 (by omega)
  rintro ⟨_hxlt, hcarry⟩
  have hrow : t + 2 - 1 = t + 1 := by omega
  rw [hrow, hfirst] at hcarry
  omega

/-- Exact recurrence/MEX spelling of the two-cell break.

If the first cell already breaks, nothing more is needed.  Otherwise the
second cell is a MEX cell, and its failure to equal `u+2` is precisely the
filled-target/lower-hole dichotomy. -/
theorem gameF_two_step_affine_break_iff_mex_source_break
    {t x u : Nat}
    (hxt : x <= t)
    (htwo : t + 2 < u) :
    (gameF (t + 1) x ≠ u + 1 ∨
      gameF (t + 2) x ≠ u + 2) ↔
    (gameF (t + 1) x ≠ u + 1 ∨
      B gameF (t + 2) x (u + 2) ∨
      exists k, 0 < k ∧ k < u + 2 ∧
        Not (B gameF (t + 2) x k)) := by
  constructor
  · rintro (hfirstBreak | hsecondBreak)
    · exact Or.inl hfirstBreak
    · by_cases hfirstBreak : gameF (t + 1) x ≠ u + 1
      · exact Or.inl hfirstBreak
      · right
        have hfirst : gameF (t + 1) x = u + 1 := by
          omega
        have hmex :=
          gameF_second_successor_is_mex_of_first_affine_successor
            hxt htwo hfirst
        exact (isMex_ne_target_iff_target_filled_or_lower_hole
          (by omega) hmex).mp hsecondBreak
  · rintro (hfirstBreak | hsourceBreak)
    · exact Or.inl hfirstBreak
    · by_cases hfirstBreak : gameF (t + 1) x ≠ u + 1
      · exact Or.inl hfirstBreak
      · right
        have hfirst : gameF (t + 1) x = u + 1 := by
          omega
        have hmex :=
          gameF_second_successor_is_mex_of_first_affine_successor
            hxt htwo hfirst
        exact (isMex_ne_target_iff_target_filled_or_lower_hole
          (by omega) hmex).mpr hsourceBreak

/-- Why the existing local recurrence lemmas do not close the pair by
themselves: under a two-step chain, the second cell is a valid MEX cell and
its two largest preceding values are explicitly paid for by the two earlier
same-column hosts in the `R` channel. -/
theorem gameF_two_step_affine_chain_has_self_financing_top_sources
    {t x u : Nat}
    (hxt : x <= t)
    (htwo : t + 2 < u)
    (hbase : gameF t x = u)
    (hfirst : gameF (t + 1) x = u + 1)
    (hsecond : gameF (t + 2) x = u + 2) :
    IsMex (B gameF (t + 2) x) (u + 2) ∧
      R gameF (t + 2) x u ∧
      R gameF (t + 2) x (u + 1) := by
  have hmex0 := gameF_second_successor_is_mex_of_first_affine_successor
    hxt htwo hfirst
  have hmex : IsMex (B gameF (t + 2) x) (u + 2) := by
    simpa [hsecond] using hmex0
  refine ⟨hmex, ?_, ?_⟩
  · refine ⟨t, by omega, ?_⟩
    rw [Nat.min_eq_right hxt, hbase]
  · refine ⟨t + 1, by omega, ?_⟩
    rw [Nat.min_eq_right (by omega : x <= t + 1), hfirst]

/-- An affine tail is locally self-financing under the recurrence: every
successor is a MEX cell, while the immediately preceding affine value is
already present in its `R` source through the preceding cell.  Thus the
generic no-skip rule alone cannot refute such a tail. -/
theorem gameF_affine_tail_successor_mex_and_predecessor_source
    {r x k q : Nat}
    (hxr : x <= r)
    (hkpos : 0 < k)
    (hrq : r < q)
    (htail : forall s, r <= s -> gameF s x = s + k) :
    IsMex (B gameF q x) (q + k) ∧
      R gameF q x (q - 1 + k) := by
  have hrPrev : r <= q - 1 := by omega
  have hxPrev : x <= q - 1 := by omega
  have hprev := htail (q - 1) hrPrev
  have hcur := htail q (by omega)
  have hnotCarry : Not (x < q ∧ gameF (q - 1) x < q) := by
    rintro ⟨_hxq, hsmall⟩
    rw [hprev] at hsmall
    omega
  have hmex0 := gameF_brouwerRecurrence.2 (by omega : x <= q) hnotCarry
  have hmex : IsMex (B gameF q x) (q + k) := by
    simpa [hcur] using hmex0
  refine ⟨hmex, q - 1, by omega, ?_⟩
  rw [Nat.min_eq_right hxPrev, hprev]

/-- The skipped-lag/target context is indispensable.  A bare high host does
not forbid a two-step affine continuation: column zero supplies a concrete
counterexample inside the actual game. -/
theorem gameF_generic_two_step_affine_break_counterexample :
    exists q x u,
      x <= q ∧ q < u ∧
      gameF q x = u ∧
      gameF (q + 1) x = u + 1 ∧
      gameF (q + 2) x = u + 2 := by
  refine ⟨64, 0, 65, by omega, by omega, ?_, ?_, ?_⟩
  · simpa using gameF_col0 64
  · simpa using gameF_col0 65
  · simpa using gameF_col0 66

/-- The finite local atom sufficient for B43.  It asserts only that the two
successor equalities after a physical skipped host cannot both hold. -/
def B43SkippedTwoStepChainBreak : Prop :=
  forall {u L c x m : Nat},
    64 <= u ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    x <= u - L ->
    B43LocalSkippedLag m ->
    m <= L ->
    gameF (u - m) x = u ->
    gameF (u - m + 1) x ≠ u + 1 ∨
      gameF (u - m + 2) x ≠ u + 2

/-- The logically minimal B43 version of the two-cell law.  Only immortal
columns can be settled-immortal obstructions, so mortality need not be
excluded on the much larger set of all skipped seats. -/
def B43ImmortalSkippedTwoStepChainBreak : Prop :=
  forall {u L c x m : Nat},
    64 <= u ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    x <= u - L ->
    Not (B30ColumnMortal x) ->
    B43LocalSkippedLag m ->
    m <= L ->
    gameF (u - m) x = u ->
    gameF (u - m + 1) x ≠ u + 1 ∨
      gameF (u - m + 2) x ≠ u + 2

/-- The all-seat law is a strengthening of the B43-facing immortal
law. -/
theorem b43ImmortalSkippedTwoStepChainBreak_of_allSeats
    (hbreak : B43SkippedTwoStepChainBreak) :
    B43ImmortalSkippedTwoStepChainBreak := by
  intro u L c x m hu hLpos hL20 hcu hfreeze hxHorizon _himmortal
    hmSkipped hmL hhost
  exact hbreak hu hLpos hL20 hcu hfreeze hxHorizon
    hmSkipped hmL hhost

/-- Clean source-facing atom found after isolating the 77 immortal
one-step continuations: whenever the first affine successor survives,
`u+2` already has a diagonal owner inside the second cell's prefix. -/
def B43ImmortalFirstSuccessorDiagonalPrefill : Prop :=
  forall {u L c x m : Nat},
    64 <= u ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    x <= u - L ->
    Not (B30ColumnMortal x) ->
    B43LocalSkippedLag m ->
    m <= L ->
    gameF (u - m) x = u ->
    gameF (u - m + 1) x = u + 1 ->
    DiagPrefix gameF (u - m + 2) x (u + 2)

/-- The diagonal prefill atom kills the second affine successor by MEX,
and therefore proves the minimal immortal two-cell law. -/
theorem b43ImmortalSkippedTwoStepChainBreak_of_diagonalPrefill
    (hprefill : B43ImmortalFirstSuccessorDiagonalPrefill) :
    B43ImmortalSkippedTwoStepChainBreak := by
  intro u L c x m hu hLpos hL20 hcu hfreeze hxHorizon himmortal
    hmSkipped hmL hhost
  by_cases hfirstBreak : gameF (u - m + 1) x ≠ u + 1
  · exact Or.inl hfirstBreak
  · right
    have hfirst : gameF (u - m + 1) x = u + 1 := by omega
    intro hsecond
    have hmLower : 3 <= m := by
      unfold B43LocalSkippedLag at hmSkipped
      rcases hmSkipped with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hmex := gameF_second_successor_is_mex_of_first_affine_successor
      (t := u - m) (x := x) (u := u) (by omega) (by omega) hfirst
    have habsent : Not (B gameF (u - m + 2) x (u + 2)) := by
      simpa [hsecond] using hmex.2.1
    apply habsent
    exact Or.inl (R_iff_diagPrefix_or_colTail.mpr (Or.inl
      (hprefill hu hLpos hL20 hcu hfreeze hxHorizon himmortal
        hmSkipped hmL hhost hfirst)))

/-- The same local atom stated entirely as a recurrence-source obligation.
This is the proof-facing version: either the first successor already
breaks, or the second MEX has a filled target or a lower positive hole. -/
def B43SkippedTwoStepMexSourceBreak : Prop :=
  forall {u L c x m : Nat},
    64 <= u ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    x <= u - L ->
    B43LocalSkippedLag m ->
    m <= L ->
    gameF (u - m) x = u ->
    gameF (u - m + 1) x ≠ u + 1 ∨
      B gameF (u - m + 2) x (u + 2) ∨
      exists k, 0 < k ∧ k < u + 2 ∧
        Not (B gameF (u - m + 2) x k)

/-- Sharper cache-facing source split.  In the observed one-step exceptions,
the second MEX breaks either because `u+2` is filled or because the named
value `u-3` is a source hole.  This predicate records that stronger law; it
is not asserted by the recurrence alone. -/
def B43SkippedNamedSecondMexBreak : Prop :=
  forall {u L c x m : Nat},
    64 <= u ->
    0 < L ->
    L <= 20 ->
    c < u ->
    gameF u c = u ->
    x <= u - L ->
    B43LocalSkippedLag m ->
    m <= L ->
    gameF (u - m) x = u ->
    gameF (u - m + 1) x ≠ u + 1 ∨
      B gameF (u - m + 2) x (u + 2) ∨
      Not (B gameF (u - m + 2) x (u - 3))

/-- The named `u-3` split supplies the existential lower-hole arm of the
exact MEX frontier. -/
theorem b43SkippedTwoStepMexSourceBreak_of_namedSecondMexBreak
    (hnamed : B43SkippedNamedSecondMexBreak) :
    B43SkippedTwoStepMexSourceBreak := by
  intro u L c x m hu hLpos hL20 hcu hfreeze hxHorizon
    hmSkipped hmL hhost
  rcases hnamed hu hLpos hL20 hcu hfreeze hxHorizon
      hmSkipped hmL hhost with hfirstBreak | htargetFilled | hlowerHole
  · exact Or.inl hfirstBreak
  · exact Or.inr (Or.inl htargetFilled)
  · exact Or.inr (Or.inr ⟨u - 3, by omega, by omega, hlowerHole⟩)

/-- Exact global reduction: the empirical two-cell law and its local MEX
source formulation are equivalent, not merely sufficient in one direction. -/
theorem b43SkippedTwoStepChainBreak_iff_mexSourceBreak :
    B43SkippedTwoStepChainBreak ↔
      B43SkippedTwoStepMexSourceBreak := by
  constructor
  · intro hbreak u L c x m hu hLpos hL20 hcu hfreeze hxHorizon
      hmSkipped hmL hhost
    apply (gameF_two_step_affine_break_iff_mex_source_break
      (t := u - m) (x := x) (u := u) (by omega) ?_).mp
    · exact hbreak hu hLpos hL20 hcu hfreeze hxHorizon
        hmSkipped hmL hhost
    · unfold B43LocalSkippedLag at hmSkipped
      rcases hmSkipped with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro hsource u L c x m hu hLpos hL20 hcu hfreeze hxHorizon
      hmSkipped hmL hhost
    apply (gameF_two_step_affine_break_iff_mex_source_break
      (t := u - m) (x := x) (u := u) (by omega) ?_).mpr
    · exact hsource hu hLpos hL20 hcu hfreeze hxHorizon
        hmSkipped hmL hhost
    · unfold B43LocalSkippedLag at hmSkipped
      rcases hmSkipped with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- A settled obstruction forces the forbidden two-cell chain.  Notice that
the immortality conjunct is not used after it exposes the settled tail. -/
theorem b31_settledImmortalObstruction_forces_two_step_chain
    {u L x : Nat}
    (hu : 64 <= u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x)
    (hbad : B31SettledImmortalObstruction u L x) :
    exists m,
      B43LocalSkippedLag m ∧
      m <= L ∧
      gameF (u - m) x = u ∧
      gameF (u - m + 1) x = u + 1 ∧
      gameF (u - m + 2) x = u + 2 := by
  rcases hrelevant with
    ⟨⟨m, hmSkipped, hmL, hhost⟩, hxHorizon⟩
  have hrelevant' : B31RelevantSkippedSeatAtDepth u L x :=
    ⟨⟨m, hmSkipped, hmL, hhost⟩, hxHorizon⟩
  rcases b31_settledImmortalObstruction_creates_skipped_affine_rail
      hu hrelevant' hbad with ⟨m', hm'Skipped, hm'L, htail⟩
  have hsame : m' = m := by
    have hatHost := htail (u - m) (by omega)
    rw [hhost] at hatHost
    omega
  subst m'
  have hfirst := htail (u - m + 1) (by omega)
  have hsecond := htail (u - m + 2) (by omega)
  refine ⟨m, hmSkipped, hmL, hhost, ?_, ?_⟩ <;> omega

/-- The local two-cell atom eliminates the exact R197 obstruction. -/
theorem b31_no_settledImmortalObstruction_of_twoStepChainBreak
    (hbreak : B43SkippedTwoStepChainBreak)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    Not (B31SettledImmortalObstruction u L x) := by
  intro hbad
  have hxHorizon : x <= u - L := hrelevant.2
  rcases b31_settledImmortalObstruction_forces_two_step_chain
      hu hrelevant hbad with
      ⟨m, hmSkipped, hmL, hhost, hfirst, hsecond⟩
  rcases hbreak hu hLpos hL20 hcu hfreeze hxHorizon
      hmSkipped hmL hhost with hfirstBreak | hsecondBreak
  · exact hfirstBreak hfirst
  · exact hsecondBreak hsecond

/-- Minimal version: it is enough to prove the two-cell break on immortal
skipped seats only. -/
theorem b31_no_settledImmortalObstruction_of_immortalTwoStepChainBreak
    (hbreak : B43ImmortalSkippedTwoStepChainBreak)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    Not (B31SettledImmortalObstruction u L x) := by
  intro hbad
  have hxHorizon : x <= u - L := hrelevant.2
  have himmortal : Not (B30ColumnMortal x) := hbad.1
  rcases b31_settledImmortalObstruction_forces_two_step_chain
      hu hrelevant hbad with
      ⟨m, hmSkipped, hmL, hhost, hfirst, hsecond⟩
  rcases hbreak hu hLpos hL20 hcu hfreeze hxHorizon himmortal
      hmSkipped hmL hhost with hfirstBreak | hsecondBreak
  · exact hfirstBreak hfirst
  · exact hsecondBreak hsecond

/-- End-to-end B31 reverse inclusion from the local two-cell atom. -/
theorem b31_relevantSkippedSeat_is_candidate_of_twoStepChainBreak
    (hbreak : B43SkippedTwoStepChainBreak)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  apply (b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
    hu hLpos hL20 hcu hfreeze hrelevant).2
  exact b31_no_settledImmortalObstruction_of_twoStepChainBreak
    hbreak hu hLpos hL20 hcu hfreeze hrelevant

/-- End-to-end reverse inclusion from the minimal immortal-only atom. -/
theorem b31_relevantSkippedSeat_is_candidate_of_immortalTwoStepChainBreak
    (hbreak : B43ImmortalSkippedTwoStepChainBreak)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  apply (b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
    hu hLpos hL20 hcu hfreeze hrelevant).2
  exact
    b31_no_settledImmortalObstruction_of_immortalTwoStepChainBreak
      hbreak hu hLpos hL20 hcu hfreeze hrelevant

/-- The clean diagonal-prefill atom is therefore sufficient for full B31
reverse inclusion. -/
theorem b31_relevantSkippedSeat_is_candidate_of_diagonalPrefill
    (hprefill : B43ImmortalFirstSuccessorDiagonalPrefill)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  exact b31_relevantSkippedSeat_is_candidate_of_immortalTwoStepChainBreak
    (b43ImmortalSkippedTwoStepChainBreak_of_diagonalPrefill hprefill)
    hu hLpos hL20 hcu hfreeze hrelevant

#print axioms isMex_ne_target_iff_target_filled_or_lower_hole
#print axioms gameF_two_step_affine_break_iff_mex_source_break
#print axioms gameF_two_step_affine_chain_has_self_financing_top_sources
#print axioms gameF_affine_tail_successor_mex_and_predecessor_source
#print axioms gameF_generic_two_step_affine_break_counterexample
#print axioms b43SkippedTwoStepChainBreak_iff_mexSourceBreak
#print axioms b43SkippedTwoStepMexSourceBreak_of_namedSecondMexBreak
#print axioms b43ImmortalSkippedTwoStepChainBreak_of_diagonalPrefill
#print axioms b31_settledImmortalObstruction_forces_two_step_chain
#print axioms b31_no_settledImmortalObstruction_of_twoStepChainBreak
#print axioms b31_no_settledImmortalObstruction_of_immortalTwoStepChainBreak
#print axioms b31_relevantSkippedSeat_is_candidate_of_twoStepChainBreak
#print axioms b31_relevantSkippedSeat_is_candidate_of_immortalTwoStepChainBreak
#print axioms b31_relevantSkippedSeat_is_candidate_of_diagonalPrefill

end ChompLean
