import R197B31ReverseInclusion

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R198: the exact affine-offset frontier behind B43

R197 left the B31 reverse inclusion at a `settled immortal` obstruction.
For a relevant skipped seat, the adjective `immortal` is redundant.  The
skipped host pins every settled tail to a strictly positive offset, and a
strictly positive affine tail is incompatible with a row-start freeze both
before and after the tail begins.

Consequently B43 is exactly the exclusion of an affine tail at one of the
six missing offsets `3,8,10,13,18,20`.  The final section records two clean
global interfaces for that remaining theorem: direct exclusion of those six
offsets, or classification of every positive affine offset at most twenty
into the fourteen already realized offsets.
-/

/-- A strictly positive affine tail can never belong to a mortal column.

If the freeze precedes the start of the tail, freeze persistence contradicts
the first affine value.  If it follows the start, the affine identity at the
freeze row contradicts the row-start value directly. -/
theorem positive_affine_tail_not_b30ColumnMortal
    {r x k : Nat}
    (hk : 0 < k)
    (htail : forall q, r <= q -> gameF q x = q + k) :
    Not (B30ColumnMortal x) := by
  rintro ⟨w, hxw, hfreeze⟩
  by_cases hwr : w <= r
  · have hpersist : gameF r x = w :=
      gameF_freeze_persists hxw hfreeze hwr
    have haffine : gameF r x = r + k := htail r (Nat.le_refl r)
    omega
  · have hrw : r <= w := by omega
    have haffine : gameF w x = w + k := htail w hrw
    omega

/-- On a relevant skipped seat, settledness already implies immortality.
The skipped host identifies the affine offset with one of the six positive
skipped lags. -/
theorem b31_relevantSkippedSeat_settled_not_b30ColumnMortal
    {u L x : Nat}
    (hu : 64 <= u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x)
    (hsettled : ColumnAffineSettledBy (u - L) x) :
    Not (B30ColumnMortal x) := by
  rcases b31_settled_relevantSkippedSeat_affine_tail_has_skipped_offset
      hu hrelevant hsettled with
      ⟨m, hm, _hmL, htail⟩
  have hmpos : 0 < m := by
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  exact positive_affine_tail_not_b30ColumnMortal hmpos htail

/-- Exact simplification of the R197 obstruction: on a relevant skipped
seat it is equivalent to affine settledness alone. -/
theorem b31_settledImmortalObstruction_iff_settled
    {u L x : Nat}
    (hu : 64 <= u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B31SettledImmortalObstruction u L x <->
      ColumnAffineSettledBy (u - L) x := by
  constructor
  · exact fun hbad => hbad.2
  · intro hsettled
    exact ⟨b31_relevantSkippedSeat_settled_not_b30ColumnMortal
      hu hrelevant hsettled, hsettled⟩

/-- Sharpened B31 reverse-inclusion frontier.  Every static and mortality
clause has disappeared: the skipped seat is a full physical candidate iff
its column had not yet entered an affine tail at the comparison row. -/
theorem b31_relevantSkippedSeat_reverseInclusion_iff_notSettled
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x <->
      Not (ColumnAffineSettledBy (u - L) x) := by
  rw [b31_relevantSkippedSeat_reverseInclusion_iff_no_obstruction
    hu hLpos hL20 hcu hfreeze hrelevant]
  have hbadIff :=
    b31_settledImmortalObstruction_iff_settled hu hrelevant
  constructor
  · intro hnoBad hsettled
    exact hnoBad (hbadIff.mpr hsettled)
  · intro hnotSettled hbad
    exact hnotSettled (hbadIff.mp hbad)

/-- The six affine offsets missing from the proved depth-twenty rail
schedule. -/
def SkippedAffineOffset20 (m : Nat) : Prop :=
  m = 3 \/ m = 8 \/ m = 10 \/ m = 13 \/ m = 18 \/ m = 20

/-- Global offset-gap formulation of the remaining B43 input. -/
def NoSkippedAffineTail20 : Prop :=
  forall r x m,
    SkippedAffineOffset20 m ->
    Not (forall q, r <= q -> gameF q x = q + m)

/-- Stronger but often more natural classification interface: every
positive affine offset at most twenty is one of the fourteen offsets already
realized by the fixed rail schedule. -/
def SmallAffineOffsetSpectrum20 : Prop :=
  forall r x m,
    0 < m -> m <= 20 ->
    (forall q, r <= q -> gameF q x = q + m) ->
    RealizedLag20 m

/-- The fourteen realized offsets and the six skipped offsets partition
`1..20`. -/
theorem realizedLag20_or_skippedAffineOffset20
    {m : Nat}
    (hmpos : 0 < m)
    (hm20 : m <= 20) :
    RealizedLag20 m \/ SkippedAffineOffset20 m := by
  unfold RealizedLag20 SkippedAffineOffset20
  omega

/-- No offset is both realized and skipped. -/
theorem realizedLag20_not_skippedAffineOffset20
    {m : Nat}
    (hm : RealizedLag20 m) :
    Not (SkippedAffineOffset20 m) := by
  unfold RealizedLag20 SkippedAffineOffset20 at *
  omega

/-- Exact equivalence of the two global formulations. -/
theorem smallAffineOffsetSpectrum20_iff_noSkippedAffineTail20 :
    SmallAffineOffsetSpectrum20 <-> NoSkippedAffineTail20 := by
  constructor
  · intro hspectrum r x m hskipped htail
    have hmpos : 0 < m := by
      unfold SkippedAffineOffset20 at hskipped
      omega
    have hm20 : m <= 20 := by
      unfold SkippedAffineOffset20 at hskipped
      omega
    have hrealized : RealizedLag20 m :=
      hspectrum r x m hmpos hm20 htail
    exact realizedLag20_not_skippedAffineOffset20 hrealized hskipped
  · intro hnoSkipped r x m hmpos hm20 htail
    rcases realizedLag20_or_skippedAffineOffset20 hmpos hm20 with
        hrealized | hskipped
    · exact hrealized
    · exact False.elim (hnoSkipped r x m hskipped htail)

/-! ## Finite part of the affine-spectrum classification -/

/-- At rows at least `44`, every proved column through `31` is either one
of the eighteen constant columns (with value at most `43`) or one of the
fourteen affine rails in `RealizedLag20`.

This packages the several thousand lines of exact low-column recurrence
calculations into the one finite interface needed by B43. -/
def SmallColumnFate20At (q x : Nat) : Prop :=
  (exists w, w <= 43 /\ gameF q x = w) \/
  (exists m, RealizedLag20 m /\ gameF q x = q + m)

theorem gameF_smallColumnFate20At_of_le_thirtyOne
    {q x : Nat}
    (hq : 44 <= q)
    (hx : x <= 31) :
    SmallColumnFate20At q x := by
  have hxCases :
      x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/
      x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/
      x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ x = 16 \/ x = 17 \/
      x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/ x = 22 \/ x = 23 \/
      x = 24 \/ x = 25 \/ x = 26 \/ x = 27 \/ x = 28 \/ x = 29 \/
      x = 30 \/ x = 31 := by
    omega
  rcases hxCases with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [SmallColumnFate20At, RealizedLag20,
      gameF_col0,
      gameF_col1_rail (q := q) (by omega),
      gameF_col2_rail (q := q) (by omega),
      gameF_col3_rail (q := q) (by omega),
      gameF_col4_rail (q := q) (by omega),
      gameF_col5_rail (q := q) (by omega),
      gameF_col6_rail (q := q) (by omega),
      gameF_col7_rail (q := q) (by omega),
      gameF_col8_rail (q := q) (by omega),
      gameF_col9_rail (q := q) (by omega),
      gameF_col10_rail (q := q) (by omega),
      gameF_col11_rail (q := q) (by omega),
      gameF_col12_rail (q := q) (by omega),
      gameF_col13_rail (q := q) (by omega),
      gameF_col14_rail (q := q) (by omega),
      gameF_col15_rail (q := q) (by omega),
      gameF_col16_rail (q := q) (by omega),
      gameF_col17_rail (q := q) (by omega),
      gameF_col18_rail (q := q) (by omega),
      gameF_col19_rail (q := q) (by omega),
      gameF_col20_rail (q := q) (by omega),
      gameF_col21_rail (q := q) (by omega),
      gameF_col22_rail (q := q) (by omega),
      gameF_col23_rail (q := q) (by omega),
      gameF_col24_rail (q := q) (by omega),
      gameF_col25_rail (q := q) (by omega),
      gameF_col26_rail (q := q) (by omega),
      gameF_col27_rail (q := q) (by omega),
      gameF_col28_rail (q := q) (by omega),
      gameF_col29_rail (q := q) (by omega),
      gameF_col30_rail (q := q) (by omega),
      gameF_col31_rail (q := q) (by omega)]

/-- The sole infinite-column input still needed after the exact finite
calculation: a positive affine offset at most twenty must occur by column
`31`. -/
def SmallAffineOffsetColumnBound20 : Prop :=
  forall r x m,
    0 < m -> m <= 20 ->
    (forall q, r <= q -> gameF q x = q + m) ->
    x <= 31

/-- Once the column bound is supplied, the proved low-column table gives
the complete small-offset spectrum. -/
theorem smallAffineOffsetSpectrum20_of_columnBound
    (hbound : SmallAffineOffsetColumnBound20) :
    SmallAffineOffsetSpectrum20 := by
  intro r x m hmpos hm20 htail
  have hx31 : x <= 31 := hbound r x m hmpos hm20 htail
  let q := max r 44
  have hrq : r <= q := by
    dsimp [q]
    exact Nat.le_max_left _ _
  have hq44 : 44 <= q := by
    dsimp [q]
    exact Nat.le_max_right _ _
  have haffine : gameF q x = q + m := htail q hrq
  rcases gameF_smallColumnFate20At_of_le_thirtyOne hq44 hx31 with
      hconstant | hrail
  · rcases hconstant with ⟨w, hw43, hw⟩
    rw [hw] at haffine
    omega
  · rcases hrail with ⟨d, hd, hdvalue⟩
    have hdm : d = m := by
      rw [hdvalue] at haffine
      omega
    simpa [hdm] using hd

/-- Thus B43 is reduced further to the single late-column bound above. -/
theorem noSkippedAffineTail20_of_columnBound
    (hbound : SmallAffineOffsetColumnBound20) :
    NoSkippedAffineTail20 :=
  smallAffineOffsetSpectrum20_iff_noSkippedAffineTail20.mp
    (smallAffineOffsetSpectrum20_of_columnBound hbound)

/-- The global six-offset gap closes B43 at every depth `1..20`. -/
theorem b31_relevantSkippedSeat_notSettled_of_noSkippedAffineTail20
    (hgap : NoSkippedAffineTail20)
    {u L x : Nat}
    (hu : 64 <= u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    Not (ColumnAffineSettledBy (u - L) x) := by
  intro hsettled
  rcases b31_settled_relevantSkippedSeat_affine_tail_has_skipped_offset
      hu hrelevant hsettled with
      ⟨m, hm, _hmL, htail⟩
  exact hgap (u - L) x m hm htail

/-- Conditional end-to-end B31 reverse inclusion under the now-minimal
global affine-offset gap. -/
theorem b31_relevantSkippedSeat_reverseInclusion_of_noSkippedAffineTail20
    (hgap : NoSkippedAffineTail20)
    {u L c x : Nat}
    (hu : 64 <= u)
    (hLpos : 0 < L)
    (hL20 : L <= 20)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hrelevant : B31RelevantSkippedSeatAtDepth u L x) :
    B30PhysicalCacheCandidateAtDepth u L c x := by
  exact (b31_relevantSkippedSeat_reverseInclusion_iff_notSettled
    hu hLpos hL20 hcu hfreeze hrelevant).mpr
      (b31_relevantSkippedSeat_notSettled_of_noSkippedAffineTail20
        hgap hu hrelevant)

#print axioms positive_affine_tail_not_b30ColumnMortal
#print axioms b31_settledImmortalObstruction_iff_settled
#print axioms b31_relevantSkippedSeat_reverseInclusion_iff_notSettled
#print axioms smallAffineOffsetSpectrum20_iff_noSkippedAffineTail20
#print axioms gameF_smallColumnFate20At_of_le_thirtyOne
#print axioms smallAffineOffsetSpectrum20_of_columnBound
#print axioms b31_relevantSkippedSeat_reverseInclusion_of_noSkippedAffineTail20

end ChompLean
