import R141BottomBarrierCrossingAttack

set_option autoImplicit false

namespace ChompLean

/-!
R144: audit of NO-CRITICAL-FINAL-HOLE-LATE-FREEZE.

The global FreezeOrder statement used here is exactly strict monotonicity of
the freeze column on blocker values.  The predecessor map `n |-> n-1`
satisfies this order on every positive blocker set.  It also puts the final
hole of the R141 parametric bad-crossing frame strictly to the right of the
crossing source cutoff.

The geometric part proves that this late placement is precisely what keeps
the freeze position from attacking any earlier staircase host.  Thus
FreezeOrder and no-attack are compatible with, rather than contradictory to,
the R141 interface counterframe.
-/

/-- The exact abstract content of global FreezeOrder. -/
def StrictFreezeOrder (Blocker : Nat -> Prop) (freezeCol : Nat -> Nat) : Prop :=
  forall {u v}, Blocker u -> Blocker v -> u < v -> freezeCol u < freezeCol v

/-- A canonical order-preserving candidate freeze map. -/
def PredFreeze (v : Nat) : Nat := v - 1

theorem predFreeze_valid {v : Nat} (hv : 0 < v) : PredFreeze v < v := by
  simp [PredFreeze]
  omega

theorem predFreeze_strict {u v : Nat} (hu : 0 < u) (huv : u < v) :
    PredFreeze u < PredFreeze v := by
  simp [PredFreeze]
  omega

theorem predFreezeOrder_of_positive
    (Blocker : Nat -> Prop)
    (hpos : forall {v}, Blocker v -> 0 < v) :
    StrictFreezeOrder Blocker PredFreeze := by
  intro u v hu hv huv
  exact predFreeze_strict (hpos hu) huv

/-! ## Direct no-attack geometry -/

/-- The row-start/freeze position for value `v` at column `c`. -/
def FreezePos (v c : Nat) (hcv : c <= v) : Pos where
  p := v
  q := v
  r := c
  hq := Nat.le_refl v
  hr := hcv

/-- The standard strict host position `[v,s,s-1]`. -/
def StairHostPos (v s : Nat) (hsv : s <= v) : Pos where
  p := v
  q := s
  r := s - 1
  hq := hsv
  hr := Nat.sub_le s 1

/-- If the freeze column is at or to the right of the host row, a second-row
cut leaves lower row `s`, not `s-1`; the other two cuts have the wrong top or
middle coordinate.  Hence the freeze position cannot attack the host. -/
theorem move_q_le {x y : Pos} (h : Move x y) : y.q <= x.q := by
  cases h with
  | first a ha0 ha => exact Nat.min_le_right a x.q
  | second a ha => exact Nat.le_of_lt ha
  | third b hb => exact Nat.le_refl x.q

theorem move_same_top_middle_drop_lower_is_min
    {x y : Pos} (h : Move x y) (hp : y.p = x.p) (hq : y.q < x.q) :
    y.r = min y.q x.r := by
  cases h with
  | first a ha0 ha =>
      simp [Pos.firstCut] at hp
      omega
  | second a ha =>
      simp [Pos.secondCut]
  | third b hb =>
      simp [Pos.thirdCut] at hq

/-- Exact crossing rule: `[v,v,c]` attacks the staircase host
`[v,s,s-1]` iff the freeze column is exactly `s-1`. -/
theorem freeze_attacks_stair_host_iff
    {v c s : Nat} (hsv : s < v) (hcv : c < v) (hs : 0 < s) :
    Move (FreezePos v c (Nat.le_of_lt hcv))
      (StairHostPos v s (Nat.le_of_lt hsv)) <-> c = s - 1 := by
  constructor
  · intro hmove
    have hr := move_same_top_middle_drop_lower_is_min hmove (by rfl) (by
      change s < v
      exact hsv)
    change s - 1 = min s c at hr
    by_cases hcs : c < s
    · rw [Nat.min_eq_right (Nat.le_of_lt hcs)] at hr
      omega
    · have hsc : s <= c := Nat.le_of_not_gt hcs
      rw [Nat.min_eq_left hsc] at hr
      omega
  · intro hc
    subst c
    have hm := move_second_to_same_lower
      (p := v) (q := v) (a := s) (r := s - 1)
      (by omega) (Nat.le_refl v) (Nat.sub_le s 1) hsv
    simpa [FreezePos, StairHostPos, mkPos] using hm

theorem late_freeze_does_not_attack_stair_host
    {v c s : Nat} (hsv : s < v) (hsc : s <= c) (hcv : c < v) (hs : 0 < s) :
    Not (Move (FreezePos v c (Nat.le_of_lt hcv))
      (StairHostPos v s (Nat.le_of_lt hsv))) := by
  intro hmove
  have hr := move_same_top_middle_drop_lower_is_min hmove (by rfl) (by
    change s < v
    exact hsv)
  change s - 1 = min s c at hr
  rw [Nat.min_eq_left hsc] at hr
  omega

/-- An earlier host cannot attack its future freeze position because a Chomp
move never increases the middle coordinate. -/
theorem stair_host_does_not_attack_freeze
    {v c s : Nat} (hsv : s < v) (hcv : c < v) :
    Not (Move (StairHostPos v s (Nat.le_of_lt hsv))
      (FreezePos v c (Nat.le_of_lt hcv))) := by
  intro hmove
  have hq := move_q_le hmove
  change v <= s at hq
  omega

theorem late_freeze_and_stair_host_nonattacking
    {v c s : Nat} (hsv : s < v) (hsc : s <= c) (hcv : c < v) (hs : 0 < s) :
    Not (Move (FreezePos v c (Nat.le_of_lt hcv))
      (StairHostPos v s (Nat.le_of_lt hsv))) /\
    Not (Move (StairHostPos v s (Nat.le_of_lt hsv))
      (FreezePos v c (Nat.le_of_lt hcv))) := by
  exact ⟨late_freeze_does_not_attack_stair_host hsv hsc hcv hs,
    stair_host_does_not_attack_freeze hsv hcv⟩

/-- R141's late-freeze inequality rules out attacks on the complete
three-row source staircase `t-2,t-1,t`, not only on the final V1 host. -/
theorem late_freeze_nonattacks_three_row_chain
    {v c t : Nat} (ht : 3 <= t) (htv : t < v) (htc : t <= c) (hcv : c < v) :
    (Not (Move (FreezePos v c (Nat.le_of_lt hcv))
        (StairHostPos v t (Nat.le_of_lt htv))) /\
      Not (Move (StairHostPos v t (Nat.le_of_lt htv))
        (FreezePos v c (Nat.le_of_lt hcv)))) /\
    (Not (Move (FreezePos v c (Nat.le_of_lt hcv))
        (StairHostPos v (t - 1) (by omega))) /\
      Not (Move (StairHostPos v (t - 1) (by omega))
        (FreezePos v c (Nat.le_of_lt hcv)))) /\
    (Not (Move (FreezePos v c (Nat.le_of_lt hcv))
        (StairHostPos v (t - 2) (by omega))) /\
      Not (Move (StairHostPos v (t - 2) (by omega))
        (FreezePos v c (Nat.le_of_lt hcv)))) := by
  exact ⟨late_freeze_and_stair_host_nonattacking htv htc hcv (by omega),
    late_freeze_and_stair_host_nonattacking (by omega) (by omega) hcv (by omega),
    late_freeze_and_stair_host_nonattacking (by omega) (by omega) hcv (by omega)⟩

/-! ## The boundary branch q=t -/

def BoundaryBlocker (t n : Nat) : Prop := n = t - 1 \/ n = t

theorem boundaryBlocker_positive {t n : Nat} (ht : 2 <= t)
    (hn : BoundaryBlocker t n) : 0 < n := by
  rcases hn with rfl | rfl <;> omega

theorem boundary_strict_freeze_order {t : Nat} (ht : 2 <= t) :
    StrictFreezeOrder (BoundaryBlocker t) PredFreeze := by
  exact predFreezeOrder_of_positive (BoundaryBlocker t)
    (fun h => boundaryBlocker_positive ht h)

/-- A source with the unique positive hole `t` below `v`. -/
def BoundaryCore (t v z : Nat) : Prop :=
  0 < z /\ z < v /\ z ≠ t

theorem boundaryCore_v1_mex {t v : Nat} (ht : 0 < t) (htv : t < v) :
    IsMex (BoundaryCore t v) t := by
  refine ⟨ht, ?_, ?_⟩
  · intro h
    exact h.2.2 rfl
  · intro z hz hzt
    exact ⟨hz, Nat.lt_trans hzt htv, by omega⟩

theorem boundaryCore_diagonal_mex {t v : Nat} (ht : 0 < t) (htv : t < v) :
    IsMex (fun z => BoundaryCore t v z \/ z = t) v := by
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    rcases h with h | h
    · exact (Nat.lt_irrefl v h.2.1).elim
    · omega
  · intro z hz hzv
    by_cases hzt : z = t
    · exact Or.inr hzt
    · exact Or.inl ⟨hz, hzv, hzt⟩

/-- The q=t face is compatible with strict FreezeOrder.  Its immediate
predecessor blocker freezes at `t-2`, q freezes at `t-1`, the V1/diagonal
MEX pair is exact, and the predecessor staircase host is nonattacking. -/
theorem boundary_q_eq_t_ordered_packet {t v : Nat} (ht : 2 <= t) (htv : t < v) :
    BoundaryBlocker t (t - 1) /\
    BoundaryBlocker t t /\
    PredFreeze (t - 1) < PredFreeze t /\
    StrictFreezeOrder (BoundaryBlocker t) PredFreeze /\
    IsMex (BoundaryCore t v) t /\
    IsMex (fun z => BoundaryCore t v z \/ z = t) v /\
    (Not (Move (FreezePos t (PredFreeze t) (Nat.le_of_lt (predFreeze_valid (by omega))))
      (StairHostPos t (t - 1) (by omega))) /\
     Not (Move (StairHostPos t (t - 1) (by omega))
      (FreezePos t (PredFreeze t) (Nat.le_of_lt (predFreeze_valid (by omega)))))) := by
  have hpred : 0 < t - 1 := by omega
  have hlate : t - 1 <= PredFreeze t := by simp [PredFreeze]
  have hnon := late_freeze_and_stair_host_nonattacking
    (v := t) (c := PredFreeze t) (s := t - 1)
    (by omega) hlate (predFreeze_valid (by omega)) hpred
  exact ⟨Or.inl rfl, Or.inr rfl,
    predFreeze_strict (by omega) (by omega),
    boundary_strict_freeze_order ht,
    boundaryCore_v1_mex (by omega) htv,
    boundaryCore_diagonal_mex (by omega) htv,
    hnon⟩

/-! ## The q>t all-index R141 frame with a global ordered freeze map -/

theorem frameBlocker_positive {k n : Nat} (h : FrameBlocker k n) : 0 < n := by
  cases n with
  | zero => simp [FrameBlocker, FrameCount] at h
  | succ n => omega

theorem frame_strict_freeze_order (k : Nat) :
    StrictFreezeOrder (FrameBlocker k) PredFreeze := by
  exact predFreezeOrder_of_positive (FrameBlocker k) frameBlocker_positive

theorem frame_q_pred_freeze_late (k : Nat) (hk : 1 <= k) :
    FrameT k <= PredFreeze (FrameQ k) := by
  simp [FrameT, FrameQ, PredFreeze]
  omega

theorem frame_yq_pred_freeze_order (k : Nat) (hk : 2 <= k) :
    PredFreeze (FrameY k) < PredFreeze (FrameQ k) := by
  apply predFreeze_strict
  · simp [FrameY]
    omega
  · simp [FrameY, FrameQ]
    omega

theorem frame_q_freeze_nonattacks_current_host (k : Nat) (hk : 2 <= k) :
    Not (Move
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ]))))
      (StairHostPos (FrameQ k) (FrameT k) (by simp [FrameQ, FrameT]; omega))) /\
    Not (Move
      (StairHostPos (FrameQ k) (FrameT k) (by simp [FrameQ, FrameT]; omega))
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ]))))) := by
  apply late_freeze_and_stair_host_nonattacking
  · simp [FrameQ, FrameT]
    omega
  · exact frame_q_pred_freeze_late k (by omega)
  · apply predFreeze_valid
    simp [FrameQ]
  · simp [FrameT]

theorem frame_q_freeze_nonattacks_previous_host (k : Nat) (hk : 2 <= k) :
    Not (Move
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ]))))
      (StairHostPos (FrameQ k) (FrameT k - 1) (by simp [FrameQ, FrameT]; omega))) /\
    Not (Move
      (StairHostPos (FrameQ k) (FrameT k - 1) (by simp [FrameQ, FrameT]; omega))
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ]))))) := by
  apply late_freeze_and_stair_host_nonattacking
  · simp [FrameQ, FrameT]
    omega
  · have h := frame_q_pred_freeze_late k (by omega)
    omega
  · apply predFreeze_valid
    simp [FrameQ]
  · simp [FrameT]

/-- The strongest R144 counterframe packet.  For every k>=2 it combines:
the all-index first-bad counting word, both named blockers, a globally strict
freeze map, the required late q-freeze, nonattack against both q-hosts, and
the exact owner-t-2 DROP MEX frame from R141. -/
theorem ordered_late_freeze_bad_crossing_frame (k : Nat) (hk : 2 <= k) :
    FrameBlocker k (FrameY k) /\
    FrameBlocker k (FrameQ k) /\
    StrictFreezeOrder (FrameBlocker k) PredFreeze /\
    FrameT k <= PredFreeze (FrameQ k) /\
    PredFreeze (FrameY k) < PredFreeze (FrameQ k) /\
    (Not (Move
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ]))))
      (StairHostPos (FrameQ k) (FrameT k) (by simp [FrameQ, FrameT]; omega))) /\
     Not (Move
      (StairHostPos (FrameQ k) (FrameT k) (by simp [FrameQ, FrameT]; omega))
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ])))))) /\
    (Not (Move
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ]))))
      (StairHostPos (FrameQ k) (FrameT k - 1) (by simp [FrameQ, FrameT]; omega))) /\
     Not (Move
      (StairHostPos (FrameQ k) (FrameT k - 1) (by simp [FrameQ, FrameT]; omega))
      (FreezePos (FrameQ k) (PredFreeze (FrameQ k))
        (Nat.le_of_lt (predFreeze_valid (by simp [FrameQ])))))) /\
    IsMex (PrevSource (FrameQ k) (FrameL k)) (FrameQ k) /\
    IsMex
      (fun z => PrevSource (FrameQ k) (FrameL k) z \/ z = FrameQ k)
      (FrameL k) /\
    CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k) (FrameL k)
      (FrameL k + 1) /\
    IsMex
      (fun z => CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k)
        (FrameL k) z \/ z = FrameQ k)
      (FrameY k) /\
    IsMex
      (fun z => CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k)
        (FrameL k) z \/ z = FrameL k \/ z = FrameY k)
      (FrameQ k) /\
    IsMex
      (fun z => CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k)
        (FrameL k) z \/ z = FrameL k \/ z = FrameY k \/ z = FrameQ k)
      (FrameL k + 2) := by
  have hframe := parametric_owner_two_drop_frame k hk
  exact ⟨frame_y_is_blocker k hk,
    frame_q_is_blocker k (by omega),
    frame_strict_freeze_order k,
    frame_q_pred_freeze_late k (by omega),
    frame_yq_pred_freeze_order k hk,
    frame_q_freeze_nonattacks_current_host k hk,
    frame_q_freeze_nonattacks_previous_host k hk,
    hframe.2.2.2.1,
    hframe.2.2.2.2.1,
    hframe.2.2.2.2.2.1,
    hframe.2.2.2.2.2.2.1,
    hframe.2.2.2.2.2.2.2.1,
    hframe.2.2.2.2.2.2.2.2⟩

#print axioms boundary_q_eq_t_ordered_packet
#print axioms freeze_attacks_stair_host_iff
#print axioms late_freeze_nonattacks_three_row_chain
#print axioms late_freeze_and_stair_host_nonattacking
#print axioms ordered_late_freeze_bad_crossing_frame

end ChompLean
