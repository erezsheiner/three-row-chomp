import R196B30ImpactSeatCollision

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R197: B31 reverse-inclusion frontier

B31 asks for the reverse of B30 on the skipped-seat arm: every relevant
skipped target seat should itself satisfy the full cache-candidate
predicate.  Two details must be kept explicit.

* `B30SkippedSeatAtDepth` is only a scalar equality predicate.  It does not
  include the physical guard `x <= u-L`.
* the skipped equality makes a mortal column live through the horizon, but
  it says nothing by itself about the stabilization time of an immortal
  column.

After adding the physical guard, all *static* candidate clauses follow from
the target blocker and the skipped host: `3 <= x`, `x < c`, and absence of
an older copy of `u` before the horizon.  The exact remaining condition is

`B30ColumnMortal x OR Not (ColumnAffineSettledBy (u-L) x)`.

Equivalently, the only unproved bad mode is an immortal skipped-seat column
which had already entered an affine tail by the comparison row.  No such
mode is ruled out by the finite affine-rail schedule proved in R195: that
schedule constructs fourteen particular rails; it is not a classification
of every eventual affine column.
-/

/-- A skipped seat is relevant to B31 at depth `L` only when it is already
inside the comparison row.  This is the physical guard present in the cache
candidate definition but absent from `B30SkippedSeatAtDepth`. -/
def B31RelevantSkippedSeatAtDepth (u L x : Nat) : Prop :=
  B30SkippedSeatAtDepth u L x /\ x <= u - L

/-- The exact bad mode left by reverse inclusion: the skipped-seat column
is immortal, yet its affine tail already starts by the comparison row. -/
def B31SettledImmortalObstruction (u L x : Nat) : Prop :=
  Not (B30ColumnMortal x) /\
    ColumnAffineSettledBy (u - L) x

/-- A high host at or after a horizon proves that the column is live through
that horizon.  Any earlier row-start freeze would persist to the host row
and contradict the high output. -/
theorem gameF_high_host_columnLive_at_earlier_horizon
    {r t x u : Nat}
    (hrt : r <= t)
    (htu : t < u)
    (hhost : gameF t x = u) :
    ColumnLiveBelow (r + 1) x := by
  intro w hxw hwr hfreeze
  have hpersist : gameF t x = w :=
    gameF_freeze_persists hxw hfreeze (by omega)
  omega

/-- In the presence of a future high host, the semantic fate predicate has
one exact obstruction: the column is both immortal and already affine at
the horizon. -/
theorem b30FateCandidateAt_iff_mortal_or_notSettled_of_future_high_host
    {r t x u : Nat}
    (hrt : r <= t)
    (htu : t < u)
    (hhost : gameF t x = u) :
    B30FateCandidateAt r x <->
      B30ColumnMortal x \/ Not (ColumnAffineSettledBy r x) := by
  have hlive : ColumnLiveBelow (r + 1) x :=
    gameF_high_host_columnLive_at_earlier_horizon hrt htu hhost
  constructor
  · rintro (hmortal | himmortal)
    · exact Or.inl hmortal.1
    · exact Or.inr himmortal.2
  · intro hmode
    by_cases hmortal : B30ColumnMortal x
    · exact Or.inl ⟨hmortal, hlive⟩
    · rcases hmode with hmortal' | hnotSettled
      · exact False.elim (hmortal hmortal')
      · exact Or.inr ⟨hmortal, hnotSettled⟩

/-- Every relevant skipped target seat automatically satisfies the three
static B30 candidate clauses.

The lower bound `3 <= x` comes from the exact columns `0,1,2`: their values
are respectively `q+1`, `2`, and `q+2`, whereas every skipped lag is at
least three.  Target row-start order gives `x<c`, and same-column no-repeat
deletes every purported older target copy before `u-L`. -/
theorem b31_relevantSkippedSeat_static_candidate_guards
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    3 <= x /\ x < c /\ Not (ColTail gameF (u - L) x u) := by
  rcases hrelevant with
    ⟨⟨m, hmSkipped, hmL, hhost⟩, hxHorizon⟩
  have hmLower : 3 <= m := by
    rcases hmSkipped with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hmUpper : m <= 20 := by
    rcases hmSkipped with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hrowOrder : u - L <= u - m := by omega
  have hhostRowLt : u - m < u := by omega
  have hxHostRow : x <= u - m := by omega
  have hxHostRowStrict : x < u - m := by
    by_cases heq : x = u - m
    · have hdiag : gameF (u - m) (u - m) = u := by
        simpa [heq] using hhost
      exact False.elim
        (disjoint_D_S gameRecurrenceModel
          ⟨u - m, hdiag⟩ ⟨c, hcu, hfreeze⟩)
    · omega
  have hx3 : 3 <= x := by
    by_cases hge : 3 <= x
    · exact hge
    have hxCases : x = 0 \/ x = 1 \/ x = 2 := by omega
    rcases hxCases with rfl | rfl | rfl
    · rw [gameF_col0] at hhost
      omega
    · rw [gameF_col1_rail (q := u - m) (by omega)] at hhost
      omega
    · rw [gameF_col2_rail (q := u - m) (by omega)] at hhost
      omega
  have hxc : x < c := by
    have horder := rowstart_host_order_exact gameRecurrenceModel
      hcu hfreeze hxHostRowStrict (by omega : u - m <= u) hhost
    rcases horder with hbefore | hboundary
    · exact hbefore.2
    · omega
  have hclear : Not (ColTail gameF (u - L) x u) := by
    rintro ⟨a, haHorizon, hxa, haHost⟩
    exact encoding_same_lower_no_repeat game_encodes
      hxa (by omega) hhostRowLt haHost hhost
  exact ⟨hx3, hxc, hclear⟩

/-- Sharp B31 reverse-inclusion reduction at every depth `1..20`.

All clauses of the full physical cache candidate are discharged except the
single fate/stabilization disjunction displayed on the right.  Therefore a
proof of reverse inclusion must exclude exactly an immortal column already
settled at `u-L`; the existing rail schedule does not do this. -/
theorem b31_relevantSkippedSeat_reverseInclusion_iff_fate_frontier
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x <->
      B30ColumnMortal x \/
        Not (ColumnAffineSettledBy (u - L) x) := by
  rcases hrelevant with ⟨hseat, hxHorizon⟩
  rcases hseat with ⟨m, hmSkipped, hmL, hhost⟩
  have hmLower : 3 <= m := by
    rcases hmSkipped with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hhostRowLt : u - m < u := by omega
  have hrowOrder : u - L <= u - m := by omega
  have hstatic := b31_relevantSkippedSeat_static_candidate_guards
    hu hLpos hL20 hcu hfreeze
      ⟨⟨m, hmSkipped, hmL, hhost⟩, hxHorizon⟩
  have hfate :=
    b30FateCandidateAt_iff_mortal_or_notSettled_of_future_high_host
      hrowOrder hhostRowLt hhost
  constructor
  · rintro ⟨_hx3, _hxc, hcandidateFate, _hclear, _hxHorizon⟩
    exact hfate.mp hcandidateFate
  · intro hmode
    exact ⟨hstatic.1, hstatic.2.1, hfate.mpr hmode,
      hstatic.2.2, hxHorizon⟩

/-- Equivalent negative form: full reverse inclusion fails exactly at a
settled immortal obstruction. -/
theorem b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x <->
      Not (B31SettledImmortalObstruction u L x) := by
  rw [b31_relevantSkippedSeat_reverseInclusion_iff_fate_frontier
    hu hLpos hL20 hcu hfreeze hrelevant]
  unfold B31SettledImmortalObstruction
  constructor
  · intro hmode hbad
    rcases hmode with hmortal | hnotSettled
    · exact hbad.1 hmortal
    · exact hnotSettled hbad.2
  · intro hnoBad
    by_cases hmortal : B30ColumnMortal x
    · exact Or.inl hmortal
    · exact Or.inr (by
        intro hsettled
        exact hnoBad ⟨hmortal, hsettled⟩)

/-- Full frontier without silently building “relevant” into the premise.
For the scalar skipped-seat predicate, reverse inclusion is equivalent to
two independent facts: the physical horizon guard and exclusion of the
settled-immortal mode. -/
theorem b31_skippedSeatAtDepth_reverseInclusion_iff_physical_and_no_obstruction
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hseat : B30SkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x <->
      x <= u - L /\
        Not (B31SettledImmortalObstruction u L x) := by
  constructor
  · intro hcandidate
    have hxHorizon : x <= u - L := hcandidate.2.2.2.2
    have hnoBad :=
      (b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
        hu hLpos hL20 hcu hfreeze ⟨hseat, hxHorizon⟩).mp hcandidate
    exact ⟨hxHorizon, hnoBad⟩
  · rintro ⟨hxHorizon, hnoBad⟩
    exact (b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
      hu hLpos hL20 hcu hfreeze ⟨hseat, hxHorizon⟩).mpr hnoBad

/-- If the bad mode exists, its affine offset is not arbitrary: the skipped
host pins it to the skipped lag `m`.  Thus the missing B31 theorem is exactly
the exclusion of an additional, already-stabilized affine rail at one of
the six skipped offsets. -/
theorem b31_settled_relevantSkippedSeat_affine_tail_has_skipped_offset
    {u L x : Nat}
    (hu : 64 <= u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x)
    (hsettled : ColumnAffineSettledBy (u - L) x) :
    exists m,
      (m = 3 \/ m = 8 \/ m = 10 \/ m = 13 \/ m = 18 \/ m = 20) /\
      m <= L /\
      forall q, u - L <= q -> gameF q x = q + m := by
  rcases hrelevant with
    ⟨⟨m, hmSkipped, hmL, hhost⟩, _hxHorizon⟩
  rcases hsettled with ⟨k, htail⟩
  have hmUpper : m <= 20 := by
    rcases hmSkipped with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hrowOrder : u - L <= u - m := by omega
  have hatHost := htail (u - m) hrowOrder
  have hkm : k = m := by
    rw [hhost] at hatHost
    omega
  subst k
  exact ⟨m, hmSkipped, hmL, htail⟩

/-- The preceding affine-tail certificate specialized to the exact bad
mode.  Immortality is not needed to identify the offset, but it is what
makes this tail incompatible with `B30FateCandidateAt`. -/
theorem b31_settledImmortalObstruction_creates_skipped_affine_rail
    {u L x : Nat}
    (hu : 64 <= u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x)
    (hbad : B31SettledImmortalObstruction u L x) :
    exists m,
      (m = 3 \/ m = 8 \/ m = 10 \/ m = 13 \/ m = 18 \/ m = 20) /\
      m <= L /\
      forall q, u - L <= q -> gameF q x = q + m := by
  exact b31_settled_relevantSkippedSeat_affine_tail_has_skipped_offset
    hu hrelevant hbad.2

/-- Direct sufficient form: a relevant skipped seat is a full candidate as
soon as the one remaining fate disjunction is supplied. -/
theorem b31_relevantSkippedSeat_is_candidate_of_fate_frontier
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x)
    (hfate : B30ColumnMortal x \/
      Not (ColumnAffineSettledBy (u - L) x)) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  exact (b31_relevantSkippedSeat_reverseInclusion_iff_fate_frontier
    hu hLpos hL20 hcu hfreeze hrelevant).2 hfate

/-- Immortal-only form of the missing hypothesis.  Mortal skipped seats need
no additional assumption: their later high host already proves liveness. -/
theorem b31_relevantSkippedSeat_is_candidate_of_immortal_notSettled
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x)
    (himmortal : Not (B30ColumnMortal x) ->
      Not (ColumnAffineSettledBy (u - L) x)) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  apply b31_relevantSkippedSeat_is_candidate_of_fate_frontier
      hu hLpos hL20 hcu hfreeze hrelevant
  by_cases hmortal : B30ColumnMortal x
  · exact Or.inl hmortal
  · exact Or.inr (himmortal hmortal)

/-! ## Depth-twenty spelling used by B31 -/

/-- The original six-arm predicate is exactly the parametric skipped-seat
predicate at depth twenty. -/
theorem skippedSeat20_iff_b30SkippedSeatAtDepth_twenty
    {u x : Nat} :
    SkippedSeat20 u x <-> B30SkippedSeatAtDepth u 20 x := by
  constructor
  · intro hseat
    rcases hseat with h3 | h8 | h10 | h13 | h18 | h20
    · exact ⟨3, Or.inl rfl, by omega, h3⟩
    · exact ⟨8, Or.inr (Or.inl rfl), by omega, h8⟩
    · exact ⟨10, Or.inr (Or.inr (Or.inl rfl)), by omega, h10⟩
    · exact ⟨13, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by omega, h13⟩
    · exact ⟨18, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        by omega, h18⟩
    · exact ⟨20, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        by omega, h20⟩
  · rintro ⟨m, hm, _hm20, hhost⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hhost
    · exact Or.inr (Or.inl hhost)
    · exact Or.inr (Or.inr (Or.inl hhost))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hhost)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hhost))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hhost))))

/-- Exact depth-twenty B31 frontier.  Besides the explicit physical guard,
reverse inclusion is equivalent to exclusion of the settled-immortal mode. -/
theorem b31_skippedSeat20_reverseInclusion_iff_fate_frontier
    {u c x : Nat}
    (hu : 64 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hx20 : x <= u - 20)
    (hseat : SkippedSeat20 u x) :
    B30PhysicalCacheCandidate20 u c x <->
      B30ColumnMortal x \/
        Not (ColumnAffineSettledBy (u - 20) x) := by
  rw [← b30PhysicalCacheCandidateAtDepth_twenty_iff]
  exact b31_relevantSkippedSeat_reverseInclusion_iff_fate_frontier
    hu (by omega) (by omega) hcu hfreeze
      ⟨skippedSeat20_iff_b30SkippedSeatAtDepth_twenty.mp hseat, hx20⟩

/-- Fully explicit depth-twenty version.  Raw `SkippedSeat20` alone is not
the reverse inclusion: the right-hand side records both missing interfaces. -/
theorem b31_skippedSeat20_reverseInclusion_iff_physical_and_no_obstruction
    {u c x : Nat}
    (hu : 64 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hseat : SkippedSeat20 u x) :
    B30PhysicalCacheCandidate20 u c x <->
      x <= u - 20 /\
        Not (B31SettledImmortalObstruction u 20 x) := by
  rw [← b30PhysicalCacheCandidateAtDepth_twenty_iff]
  exact b31_skippedSeatAtDepth_reverseInclusion_iff_physical_and_no_obstruction
    hu (by omega) (by omega) hcu hfreeze
      (skippedSeat20_iff_b30SkippedSeatAtDepth_twenty.mp hseat)

#print axioms gameF_high_host_columnLive_at_earlier_horizon
#print axioms b30FateCandidateAt_iff_mortal_or_notSettled_of_future_high_host
#print axioms b31_relevantSkippedSeat_static_candidate_guards
#print axioms b31_relevantSkippedSeat_reverseInclusion_iff_fate_frontier
#print axioms b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
#print axioms b31_skippedSeatAtDepth_reverseInclusion_iff_physical_and_no_obstruction
#print axioms b31_settledImmortalObstruction_creates_skipped_affine_rail
#print axioms b31_relevantSkippedSeat_is_candidate_of_immortal_notSettled
#print axioms skippedSeat20_iff_b30SkippedSeatAtDepth_twenty
#print axioms b31_skippedSeat20_reverseInclusion_iff_fate_frontier
#print axioms b31_skippedSeat20_reverseInclusion_iff_physical_and_no_obstruction

end ChompLean
