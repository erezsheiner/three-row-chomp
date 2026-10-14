import R195B30Depth20AffineRails
import R190FutureSeatContainmentCore
import R191FutureSeatLag20RailClassification

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R195 B30: unconditional rail layer and FutureSeat closure

The previous file closes the three formerly missing affine rails.  This file
packages all fourteen rails into the two interfaces used by R190 and R191 and
then removes the abstract rail premise from the depth-twenty FutureSeat
classification.  The only remaining candidate-side input is the explicit
avoidance of those fourteen stabilized columns.
-/

/-- All fourteen realized depth-twenty affine lags are available once
`u >= 63`.  The threshold is forced here by the last rail:
`F(u-19,31)=u`, whose affine tail starts at row 44. -/
theorem gameF_affineRails20At_of_ge_sixtythree
    {u : Nat} (hu : 63 <= u) :
    AffineRails20At u := by
  intro m hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [realizedRailCol20]
  · rw [gameF_col0]
    omega
  · rw [gameF_col2_rail (q := u - 2) (by omega)]
    omega
  · rw [gameF_col5_rail (q := u - 4) (by omega)]
    omega
  · rw [gameF_col7_rail (q := u - 5) (by omega)]
    omega
  · rw [gameF_col9_rail (q := u - 6) (by omega)]
    omega
  · rw [gameF_col11_rail (q := u - 7) (by omega)]
    omega
  · rw [gameF_col14_rail (q := u - 9) (by omega)]
    omega
  · rw [gameF_col17_rail (q := u - 11) (by omega)]
    omega
  · rw [gameF_col19_rail (q := u - 12) (by omega)]
    omega
  · rw [gameF_col22_rail (q := u - 14) (by omega)]
    omega
  · rw [gameF_col24_rail (q := u - 15) (by omega)]
    omega
  · rw [gameF_col26_rail (q := u - 16) (by omega)]
    omega
  · rw [gameF_col28_rail (q := u - 17) (by omega)]
    omega
  · rw [gameF_col31_rail (q := u - 19) (by omega)]
    omega

/-- The list representation used by R191 is exactly R190's realized-lag
representation, including the prescribed column. -/
theorem lag20RailPairs_mem_iff_realized
    {m c : Nat} :
    (m, c) ∈ lag20RailPairs <->
      RealizedLag20 m /\ c = realizedRailCol20 m := by
  constructor
  · intro hmem
    simp [lag20RailPairs] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [RealizedLag20, realizedRailCol20]
  · rintro ⟨hm, rfl⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [lag20RailPairs, realizedRailCol20]

/-- R191's pair-list interface is now unconditional above the same threshold. -/
theorem gameF_lag20TargetRailSchedule_of_ge_sixtythree
    {u : Nat} (hu : 63 <= u) :
    Lag20TargetRailSchedule u := by
  intro m c hmem
  have hpair := lag20RailPairs_mem_iff_realized.mp hmem
  constructor
  · have hc31 := realizedLag20_railCol_le_thirtyOne hpair.1
    have hm19 : m <= 19 := by
      rcases hpair.1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    omega
  · rw [hpair.2]
    exact gameF_affineRails20At_of_ge_sixtythree hu m hpair.1

/-- The two candidate-column exclusion interfaces in R190 and R191 are
definitionally the same finite fourteen-column exclusion. -/
theorem avoidsAffineRail20_iff_lag20NonRailColumn
    {x : Nat} :
    AvoidsAffineRail20 x <-> Lag20NonRailColumn x := by
  constructor
  · intro hAvoid m c hmem
    have hpair := lag20RailPairs_mem_iff_realized.mp hmem
    simpa [hpair.2] using hAvoid m hpair.1
  · intro hNonRail m hm
    exact hNonRail m (realizedRailCol20 m)
      (lag20RailPairs_mem_iff_realized.mpr ⟨hm, rfl⟩)

/-- R191's physical six-seat theorem with its abstract rail schedule removed. -/
theorem gameF_future_host_depth20_six_seat_menu_of_ge_sixtythree
    {u r a x : Nat}
    (hu : 63 <= u)
    (hdepth : u - 20 <= r)
    (hra : r <= a)
    (hau : a < u)
    (hxa : x <= a)
    (hhost : gameF a x = u)
    (hnonRail : Lag20NonRailColumn x) :
    gameF (u - 3) x = u \/
    gameF (u - 8) x = u \/
    gameF (u - 10) x = u \/
    gameF (u - 13) x = u \/
    gameF (u - 18) x = u \/
    gameF (u - 20) x = u := by
  exact gameF_future_host_depth20_six_seat_menu
    (by omega) hdepth hra hau hxa hhost
    (gameF_lag20TargetRailSchedule_of_ge_sixtythree hu) hnonRail

/-- Corrected B30 at depth twenty, now with no rail premise: a live,
target-clear physical candidate avoiding the fourteen fixed rail columns is
either one of the six skipped target seats or freezes inside the terminal
strip. -/
theorem gameF_futureSkippedSeat20_or_nearFreeze_of_avoidsAffineRail20
    {u c x : Nat}
    (hu : 63 <= u)
    (hcu : c < u)
    (hfreeze : gameF u c = u)
    (hxc : x < c)
    (hx20 : x <= u - 20)
    (haliveAt20 : ColumnLiveBelow (u - 20 + 1) x)
    (hclearAt20 : Not (ColTail gameF (u - 20) x u))
    (havoid : AvoidsAffineRail20 x) :
    SkippedSeat20 u x \/ NearFreezeSeatBetween u (u - 20) x := by
  apply gameF_futureSkippedSeat20_or_nearFreeze
      (by omega) hcu hfreeze hxc haliveAt20 hclearAt20
  exact noRealizedLagHost20_of_affineRails
    (by omega) hx20
    (gameF_affineRails20At_of_ge_sixtythree hu) havoid

#print axioms gameF_affineRails20At_of_ge_sixtythree
#print axioms gameF_lag20TargetRailSchedule_of_ge_sixtythree
#print axioms avoidsAffineRail20_iff_lag20NonRailColumn
#print axioms gameF_future_host_depth20_six_seat_menu_of_ge_sixtythree
#print axioms gameF_futureSkippedSeat20_or_nearFreeze_of_avoidsAffineRail20

end ChompLean
