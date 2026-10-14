import R189Lag8StrictIntermediateRelayCover

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# Future hosts in the last twenty rows

This is the finite, non-density part of `FutureSeatContainment`.  The list
below is precisely the affine-rail complement of the six skipped lags
`3, 8, 10, 13, 18, 20`.  Keeping the rail schedule as an explicit premise
makes the remaining L1 obligation visible rather than hiding it in the
word "candidate".
-/

def lag20RailPairs : List (Nat × Nat) :=
  [(1, 0), (2, 2), (4, 5), (5, 7), (6, 9), (7, 11), (9, 14),
   (11, 17), (12, 19), (14, 22), (15, 24), (16, 26), (17, 28),
   (19, 31)]

/-- Every listed affine rail hosts `u` at its prescribed lag. -/
def Lag20TargetRailSchedule (u : Nat) : Prop :=
  forall (m c : Nat), (m, c) ∈ lag20RailPairs ->
    c <= u - m /\ gameF (u - m) c = u

/-- The exact finite exclusion supplied by terminal candidacy once the
listed rails are known to have stabilized. -/
def Lag20NonRailColumn (x : Nat) : Prop :=
  forall (m c : Nat), (m, c) ∈ lag20RailPairs -> x ≠ c

def Lag20SkippedLag (m : Nat) : Prop :=
  1 <= m /\ m <= 20 /\ forall (c : Nat), (m, c) ∉ lag20RailPairs

/-- A physical column is a skipped-lag seat at depth at most twenty. -/
def Lag20SkippedHopSeat (u x : Nat) : Prop :=
  exists m, Lag20SkippedLag m /\ gameF (u - m) x = u

/-- The list definition really is the familiar six-lag menu. -/
theorem lag20SkippedLag_iff_six
    {m : Nat} :
    Lag20SkippedLag m <->
      m = 3 \/ m = 8 \/ m = 10 \/ m = 13 \/ m = 18 \/ m = 20 := by
  constructor
  . rintro ⟨hmPos, hmBound, hmNonRail⟩
    have hm1 : m ≠ 1 := by
      intro hm
      subst m
      exact hmNonRail 0 (by simp [lag20RailPairs])
    have hm2 : m ≠ 2 := by
      intro hm
      subst m
      exact hmNonRail 2 (by simp [lag20RailPairs])
    have hm4 : m ≠ 4 := by
      intro hm
      subst m
      exact hmNonRail 5 (by simp [lag20RailPairs])
    have hm5 : m ≠ 5 := by
      intro hm
      subst m
      exact hmNonRail 7 (by simp [lag20RailPairs])
    have hm6 : m ≠ 6 := by
      intro hm
      subst m
      exact hmNonRail 9 (by simp [lag20RailPairs])
    have hm7 : m ≠ 7 := by
      intro hm
      subst m
      exact hmNonRail 11 (by simp [lag20RailPairs])
    have hm9 : m ≠ 9 := by
      intro hm
      subst m
      exact hmNonRail 14 (by simp [lag20RailPairs])
    have hm11 : m ≠ 11 := by
      intro hm
      subst m
      exact hmNonRail 17 (by simp [lag20RailPairs])
    have hm12 : m ≠ 12 := by
      intro hm
      subst m
      exact hmNonRail 19 (by simp [lag20RailPairs])
    have hm14 : m ≠ 14 := by
      intro hm
      subst m
      exact hmNonRail 22 (by simp [lag20RailPairs])
    have hm15 : m ≠ 15 := by
      intro hm
      subst m
      exact hmNonRail 24 (by simp [lag20RailPairs])
    have hm16 : m ≠ 16 := by
      intro hm
      subst m
      exact hmNonRail 26 (by simp [lag20RailPairs])
    have hm17 : m ≠ 17 := by
      intro hm
      subst m
      exact hmNonRail 28 (by simp [lag20RailPairs])
    have hm19 : m ≠ 19 := by
      intro hm
      subst m
      exact hmNonRail 31 (by simp [lag20RailPairs])
    omega
  . intro hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      refine ⟨by omega, by omega, ?_⟩
      intro c
      simp [lag20RailPairs]

/-- Any target host in the inclusive terminal depth-twenty strip is a
skipped-lag seat unless its column is one of the fourteen affine rails.

There is no density, rolling-cover, owner-coverage, or MidpointPin premise.
The only non-recurrence input is the plainly named rail schedule. -/
theorem gameF_future_host_depth20_is_skippedHop_of_nonRail
    {u r a x : Nat}
    (hu : 20 <= u)
    (hdepth : u - 20 <= r)
    (hra : r <= a)
    (hau : a < u)
    (hxa : x <= a)
    (hhost : gameF a x = u)
    (hrails : Lag20TargetRailSchedule u)
    (hnonRail : Lag20NonRailColumn x) :
    Lag20SkippedHopSeat u x := by
  let m := u - a
  have hmPos : 1 <= m := by
    dsimp [m]
    omega
  have hmBound : m <= 20 := by
    dsimp [m]
    omega
  have ham : a = u - m := by
    dsimp [m]
    omega
  have hhost' : gameF (u - m) x = u := by
    rw [← ham]
    exact hhost
  have hmNonRail : forall (c : Nat), (m, c) ∉ lag20RailPairs := by
    intro c hmem
    have hrail := hrails m c hmem
    have hrailHost : gameF (u - m) c = u := hrail.2
    have hxEq : x = c := gameRecurrenceModel.fixed_q_injective
      (by omega) hrail.1 (hhost'.trans hrailHost.symm)
    exact hnonRail m c hmem hxEq
  refine ⟨m, ⟨hmPos, hmBound, hmNonRail⟩, ?_⟩
  exact hhost'

/-- Expanded physical-seat form, including the lag-twenty endpoint. -/
theorem gameF_future_host_depth20_six_seat_menu
    {u r a x : Nat}
    (hu : 20 <= u)
    (hdepth : u - 20 <= r)
    (hra : r <= a)
    (hau : a < u)
    (hxa : x <= a)
    (hhost : gameF a x = u)
    (hrails : Lag20TargetRailSchedule u)
    (hnonRail : Lag20NonRailColumn x) :
    gameF (u - 3) x = u \/
    gameF (u - 8) x = u \/
    gameF (u - 10) x = u \/
    gameF (u - 13) x = u \/
    gameF (u - 18) x = u \/
    gameF (u - 20) x = u := by
  rcases gameF_future_host_depth20_is_skippedHop_of_nonRail
      hu hdepth hra hau hxa hhost hrails hnonRail with
      ⟨m, hm, hmhost⟩
  rcases (lag20SkippedLag_iff_six.mp hm) with
      rfl | rfl | rfl | rfl | rfl | rfl
  . exact Or.inl hmhost
  . exact Or.inr (Or.inl hmhost)
  . exact Or.inr (Or.inr (Or.inl hmhost))
  . exact Or.inr (Or.inr (Or.inr (Or.inl hmhost)))
  . exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmhost))))
  . exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmhost))))

#print axioms lag20SkippedLag_iff_six
#print axioms gameF_future_host_depth20_is_skippedHop_of_nonRail
#print axioms gameF_future_host_depth20_six_seat_menu

end ChompLean
