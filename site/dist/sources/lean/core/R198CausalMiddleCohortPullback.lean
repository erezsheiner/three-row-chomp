import R195ActualBlockerMidpointFiniteCohort
import R132UpperRailOwnerCoverageReduction

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# Causal pullback of the actual middle cohort

The extensional cohort in `R195ActualBlockerMidpointFiniteCohort` asks for
`gameFBlockerCountThrough (v-1)` even when `v` is later than the current row
`r`.  This file isolates the exact condition under which that apparent
future query can be reconstructed from the diagonal prefix through `r`.

The condition is the familiar range-owner margin: a diagonal value owned at
row `a` has midpoint at least `a + margin`, after a finite base.  If the
cohort half-width `K` is at most that margin, every diagonal value below a
cohort candidate has already been emitted on the diagonal by row `r`.
Consequently the blocker count, the midpoint, the cohort membership, and the
blocker/range label are all functions of the diagonal prefix through `r`.
-/

/-- Tail range-owner margin, stated directly in the actual midpoint
coordinate.  `RangeOwnerCutoff16` is the instance `base = 131`,
`margin = 16`. -/
def ActualRangeOwnerMidpointCutoffFrom (base margin : Nat) : Prop :=
  forall {a v : Nat}, base <= v -> gameF a a = v ->
    a + margin <= actualBlockerMidpoint v

/-- The value `v` has a diagonal owner already visible by row `r`. -/
def PastDiagonalThrough (r v : Nat) : Prop :=
  exists a : Fin (r + 1), gameF a.val a.val = v

/-- Values below `v` whose diagonal owners are visible by row `r`.  The
definition queries only the diagonal prefix `gameF a a`, `a <= r`; the
bounded existential is written propositionally to keep the proof interface
independent of a particular data structure. -/
noncomputable def gameFPastDiagonalBelowList (r v : Nat) : List Nat := by
  classical
  exact (List.range' 1 (v - 1)).filter
    (fun k => decide (PastDiagonalThrough r k))

noncomputable def gameFPastDiagonalBelowCount (r v : Nat) : Nat :=
  (gameFPastDiagonalBelowList r v).length

/-- Blocker count reconstructed from the visible diagonal complement. -/
noncomputable def causalBlockerCountAt (r v : Nat) : Nat :=
  (v - 1) - gameFPastDiagonalBelowCount r v

/-- Midpoint reconstructed solely from the row-`r` diagonal prefix. -/
noncomputable def causalBlockerMidpointAt (r v : Nat) : Nat :=
  (v + causalBlockerCountAt r v) / 2

private theorem filter_decide_partition_length
    {alpha : Type} (P : alpha -> Prop) [DecidablePred P]
    (xs : List alpha) :
    (xs.filter (fun x => decide (P x))).length +
      (xs.filter (fun x => decide (Not (P x)))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [decide_not] at ih
      by_cases hx : P x <;> simp [hx] <;> omega

private theorem filter_length_le_filter_of_imp
    {alpha : Type} (P Q : alpha -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (himp : forall x, P x -> Q x)
    (xs : List alpha) :
    (xs.filter (fun x => decide (P x))).length <=
      (xs.filter (fun x => decide (Q x))).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hp : P x
      . have hq : Q x := himp x hp
        simp [hp, hq, ih]
      . by_cases hq : Q x <;> simp [hp, hq] <;> omega

private theorem filter_length_eq_of_iff_on
    {alpha : Type} (P Q : alpha -> Prop)
    [DecidablePred P] [DecidablePred Q]
    (xs : List alpha)
    (hiff : forall x, x ∈ xs -> (P x <-> Q x)) :
    (xs.filter (fun x => decide (P x))).length =
      (xs.filter (fun x => decide (Q x))).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxiff : P x <-> Q x := hiff x (by simp)
      have htail : forall y, y ∈ xs -> (P y <-> Q y) := by
        intro y hy
        exact hiff y (by simp [hy])
      have iht := ih htail
      by_cases hp : P x
      . have hq : Q x := hxiff.mp hp
        simp [hp, hq, iht]
      . have hq : Not (Q x) := by
          intro hqx
          exact hp (hxiff.mpr hqx)
        simp [hp, hq, iht]

/-- Opening completeness plus D/S disjointness: a positive value is a
row-start blocker exactly when it has no diagonal owner. -/
theorem gameF_blocker_iff_no_diagonal_owner
    {v : Nat} (hv : 0 < v) :
    S gameF v <-> Not (exists a, gameF a a = v) := by
  constructor
  . intro hS hD
    rcases hD with ⟨a, ha⟩
    exact disjoint_D_S gameRecurrenceModel ⟨a, ha⟩ hS
  . intro hnoD
    rcases gameRecurrenceModel.opening_cover hv with hD | hS
    . rcases hD with ⟨a, _hav, ha⟩
      exact False.elim (hnoD ⟨a, ha⟩)
    . exact hS

/-! ## The exact fallback packet when no owner cutoff is available -/

/-- The genuinely external A-side packet between a known prefix endpoint
`r` and a later endpoint `n`. -/
noncomputable def gameFFutureBlockersBetweenList (r n : Nat) : List Nat := by
  classical
  exact (List.range' (r + 1) (n - r)).filter
    (fun k => decide (S gameF k))

noncomputable def gameFFutureBlockerCount (r n : Nat) : Nat :=
  (gameFFutureBlockersBetweenList r n).length

/-- Exact all-`N` prefix decomposition.  Thus, absent a diagonal pullback,
the only missing datum is the A-side packet itself; no row-table or host
oracle is hidden in the formula. -/
theorem gameFBlockerCountThrough_eq_past_add_futurePacket
    {r n : Nat} (hrn : r <= n) :
    gameFBlockerCountThrough n =
      gameFBlockerCountThrough r + gameFFutureBlockerCount r n := by
  classical
  have hrange :
      List.range' 1 r ++ List.range' (r + 1) (n - r) =
        List.range' 1 n := by
    have h := List.range'_append
      (s := 1) (m := r) (n := n - r) (step := 1)
    simpa [Nat.add_sub_of_le hrn, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using h
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList,
    gameFFutureBlockerCount, gameFFutureBlockersBetweenList]
  rw [← hrange, List.filter_append, List.length_append]

/-- Every future midpoint is exactly the past count plus the corresponding
initial segment of the A-side packet. -/
theorem actualBlockerMidpoint_eq_past_add_futurePacket
    {r v : Nat} (hrv : r <= v - 1) :
    actualBlockerMidpoint v =
      (v + gameFBlockerCountThrough r +
        gameFFutureBlockerCount r (v - 1)) / 2 := by
  have hcount := gameFBlockerCountThrough_eq_past_add_futurePacket hrv
  unfold actualBlockerMidpoint countMidpoint
  rw [hcount]
  congr 1
  omega

/-- R195's finite cutoff shows the maximal endpoint of the A-side packet
needed by a width-`K` cohort. -/
theorem middle_cohort_futurePacket_horizon
    {r K v : Nat}
    (hcohort : v ∈ actualBlockerMiddleCohortList r K) :
    v - 1 <= 2 * (r + K) := by
  have hband := gameF_mem_actualBlockerMiddleCohortList.mp hcohort
  have hindex := actualBlockerMidpoint_index_lt_of_le hband.2
  omega

theorem pastDiagonalThrough_not_blocker
    {r v : Nat} (hpast : PastDiagonalThrough r v) :
    Not (S gameF v) := by
  rintro hS
  rcases hpast with ⟨a, ha⟩
  exact disjoint_D_S gameRecurrenceModel ⟨a.val, ha⟩ hS

/-- Without any owner-margin assumption, the visible diagonal count is a
sound lower bound for the number of nonblockers below `v`. -/
theorem actualBlockerCount_add_pastDiagonalCount_le
    (r v : Nat) :
    gameFBlockerCountThrough (v - 1) +
      gameFPastDiagonalBelowCount r v <= v - 1 := by
  classical
  let xs := List.range' 1 (v - 1)
  have hpartition := filter_decide_partition_length
    (fun k : Nat => S gameF k) xs
  have hpastLe := filter_length_le_filter_of_imp
    (PastDiagonalThrough r) (fun k : Nat => Not (S gameF k))
    (fun _k hk => pastDiagonalThrough_not_blocker hk) xs
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList,
    gameFPastDiagonalBelowCount, gameFPastDiagonalBelowList] at *
  dsimp [xs] at hpartition hpastLe
  have hlen : (List.range' 1 (v - 1)).length = v - 1 := by simp
  omega

theorem actualBlockerCount_le_causalBlockerCountAt
    (r v : Nat) :
    gameFBlockerCountThrough (v - 1) <= causalBlockerCountAt r v := by
  have h := actualBlockerCount_add_pastDiagonalCount_le r v
  unfold causalBlockerCountAt
  omega

/-- The visible-prefix reconstruction always overestimates the true
midpoint; missing future diagonal owners can only be mistaken for blockers. -/
theorem actualBlockerMidpoint_le_causalBlockerMidpointAt
    (r v : Nat) :
    actualBlockerMidpoint v <= causalBlockerMidpointAt r v := by
  have hcount := actualBlockerCount_le_causalBlockerCountAt r v
  unfold actualBlockerMidpoint countMidpoint causalBlockerMidpointAt
  exact Nat.div_le_div_right (Nat.add_le_add_left hcount v)

/-- Under the owner margin, every nonblocker below a candidate whose actual
midpoint is at most `r+K` already has its diagonal owner at or before `r`.
This is the exact causal localization step. -/
theorem gameF_not_blocker_iff_pastDiagonalThrough_of_sublevel
    {base margin K r v k : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r)
    (hkpos : 0 < k)
    (hkv : k < v)
    (hupper : actualBlockerMidpoint v <= r + K) :
    Not (S gameF k) <-> PastDiagonalThrough r k := by
  constructor
  . intro hnot
    rcases gameRecurrenceModel.opening_cover hkpos with hD | hS
    . rcases hD with ⟨a, _hak, ha⟩
      have har : a <= r := by
        by_cases hkBase : base <= k
        . have hmargin := hcut hkBase ha
          have hmono : actualBlockerMidpoint k <=
              actualBlockerMidpoint v :=
            actualBlockerMidpoint_monotone (Nat.le_of_lt hkv)
          omega
        . have hak : a < k := by
            have hgt := gameRecurrenceModel.diagonal_gt a
            rw [ha] at hgt
            exact hgt
          omega
      exact ⟨⟨a, by omega⟩, ha⟩
    . exact False.elim (hnot hS)
  . exact pastDiagonalThrough_not_blocker

/-- Hence the true blocker count below every sublevel candidate is exactly
the complement of the diagonal values visible by row `r`. -/
theorem actualBlockerCount_eq_causalBlockerCountAt_of_sublevel
    {base margin K r v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r)
    (hupper : actualBlockerMidpoint v <= r + K) :
    gameFBlockerCountThrough (v - 1) = causalBlockerCountAt r v := by
  classical
  let xs := List.range' 1 (v - 1)
  have hpartition := filter_decide_partition_length
    (fun k : Nat => S gameF k) xs
  have hcomplement :
      (xs.filter (fun k => decide (Not (S gameF k)))).length =
        (xs.filter (fun k => decide (PastDiagonalThrough r k))).length := by
    apply filter_length_eq_of_iff_on
    intro k hk
    have hkrange : 1 <= k /\ k < 1 + (v - 1) :=
      List.mem_range'_1.mp hk
    have hkv : k < v := by omega
    exact gameF_not_blocker_iff_pastDiagonalThrough_of_sublevel
      hcut hK hrBase (by omega) hkv hupper
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList] at *
  dsimp [xs] at hpartition hcomplement
  unfold causalBlockerCountAt gameFPastDiagonalBelowCount
    gameFPastDiagonalBelowList
  have hlen : (List.range' 1 (v - 1)).length = v - 1 := by simp
  omega

theorem actualBlockerMidpoint_eq_causalBlockerMidpointAt_of_sublevel
    {base margin K r v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r)
    (hupper : actualBlockerMidpoint v <= r + K) :
    actualBlockerMidpoint v = causalBlockerMidpointAt r v := by
  have hcount := actualBlockerCount_eq_causalBlockerCountAt_of_sublevel
    hcut hK hrBase hupper
  unfold actualBlockerMidpoint countMidpoint causalBlockerMidpointAt
  rw [hcount]

/-- Noncircular sublevel equivalence.  The right side is computed from the
past diagonal prefix.  In the reverse direction its general overestimate
property first implies the actual sublevel bound, after which the owner
margin makes the estimate exact. -/
theorem actualBlockerMidpoint_sublevel_iff_causal
    {base margin K r v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r) :
    actualBlockerMidpoint v <= r + K <->
      causalBlockerMidpointAt r v <= r + K := by
  constructor
  . intro hactual
    rw [← actualBlockerMidpoint_eq_causalBlockerMidpointAt_of_sublevel
      hcut hK hrBase hactual]
    exact hactual
  . intro hcausal
    have hle := actualBlockerMidpoint_le_causalBlockerMidpointAt r v
    omega

/-- Exact causal pullback of the complete middle-band predicate. -/
theorem actualBlockerMidpoint_band_iff_causal
    {base margin K r v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r) :
    (r - K < actualBlockerMidpoint v /\
        actualBlockerMidpoint v <= r + K) <->
      (r - K < causalBlockerMidpointAt r v /\
        causalBlockerMidpointAt r v <= r + K) := by
  constructor
  . intro hband
    have heq := actualBlockerMidpoint_eq_causalBlockerMidpointAt_of_sublevel
      hcut hK hrBase hband.2
    omega
  . intro hband
    have hactualUpper :=
      (actualBlockerMidpoint_sublevel_iff_causal hcut hK hrBase).2 hband.2
    have heq := actualBlockerMidpoint_eq_causalBlockerMidpointAt_of_sublevel
      hcut hK hrBase hactualUpper
    omega

/-- Canonical causal enumeration.  Unlike the R195 definition, its test
contains no future blocker count: it reads only diagonal values owned by
rows at most `r`. -/
noncomputable def causalBlockerMiddleCohortList (r K : Nat) : List Nat := by
  classical
  exact (List.range (2 * (r + K) + 2)).filter (fun v =>
    decide (r - K < causalBlockerMidpointAt r v /\
      causalBlockerMidpointAt r v <= r + K))

/-- The actual and causal canonical cohort lists are literally equal under
the range-owner margin. -/
theorem actualBlockerMiddleCohortList_eq_causal
    {base margin K r : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r) :
    actualBlockerMiddleCohortList r K =
      causalBlockerMiddleCohortList r K := by
  classical
  unfold actualBlockerMiddleCohortList causalBlockerMiddleCohortList
  apply List.filter_congr
  intro v _hv
  exact decide_eq_decide.mpr
    (actualBlockerMidpoint_band_iff_causal hcut hK hrBase)

/-- The causal enumeration inherits R195's sharp cardinal bound. -/
theorem causalBlockerMiddleCohortList_length_le
    {base margin K r : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r) :
    (causalBlockerMiddleCohortList r K).length <= 4 * K + 2 := by
  rw [← actualBlockerMiddleCohortList_eq_causal hcut hK hrBase]
  exact actualBlockerMiddleCohortList_length_le r K

/-! ## General visible horizon

The previous statements use the current row itself as the visible diagonal
horizon.  A forward induction may instead know a slightly later diagonal
prefix `T`.  The exact arithmetic requirement is

`center + K <= T + margin`.

Thus margin zero needs only the prefix through `center+K`, while a positive
owner margin moves the necessary prefix correspondingly to the left.
-/

theorem gameF_not_blocker_iff_pastDiagonalThrough_of_visible_sublevel
    {base margin center K T v k : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hreach : center + K <= T + margin)
    (hTBase : base <= T)
    (hkpos : 0 < k)
    (hkv : k < v)
    (hupper : actualBlockerMidpoint v <= center + K) :
    Not (S gameF k) <-> PastDiagonalThrough T k := by
  constructor
  . intro hnot
    rcases gameRecurrenceModel.opening_cover hkpos with hD | hS
    . rcases hD with ⟨a, _hak, ha⟩
      have haT : a <= T := by
        by_cases hkBase : base <= k
        . have hmargin := hcut hkBase ha
          have hmono : actualBlockerMidpoint k <=
              actualBlockerMidpoint v :=
            actualBlockerMidpoint_monotone (Nat.le_of_lt hkv)
          omega
        . have hak : a < k := by
            have hgt := gameRecurrenceModel.diagonal_gt a
            rw [ha] at hgt
            exact hgt
          omega
      exact ⟨⟨a, by omega⟩, ha⟩
    . exact False.elim (hnot hS)
  . exact pastDiagonalThrough_not_blocker

theorem actualBlockerCount_eq_causalBlockerCountAt_of_visible_sublevel
    {base margin center K T v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hreach : center + K <= T + margin)
    (hTBase : base <= T)
    (hupper : actualBlockerMidpoint v <= center + K) :
    gameFBlockerCountThrough (v - 1) = causalBlockerCountAt T v := by
  classical
  let xs := List.range' 1 (v - 1)
  have hpartition := filter_decide_partition_length
    (fun k : Nat => S gameF k) xs
  have hcomplement :
      (xs.filter (fun k => decide (Not (S gameF k)))).length =
        (xs.filter (fun k => decide (PastDiagonalThrough T k))).length := by
    apply filter_length_eq_of_iff_on
    intro k hk
    have hkrange : 1 <= k /\ k < 1 + (v - 1) :=
      List.mem_range'_1.mp hk
    have hkv : k < v := by omega
    exact gameF_not_blocker_iff_pastDiagonalThrough_of_visible_sublevel
      hcut hreach hTBase (by omega) hkv hupper
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList] at *
  dsimp [xs] at hpartition hcomplement
  unfold causalBlockerCountAt gameFPastDiagonalBelowCount
    gameFPastDiagonalBelowList
  have hlen : (List.range' 1 (v - 1)).length = v - 1 := by simp
  omega

theorem actualBlockerMidpoint_eq_causal_of_visible_sublevel
    {base margin center K T v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hreach : center + K <= T + margin)
    (hTBase : base <= T)
    (hupper : actualBlockerMidpoint v <= center + K) :
    actualBlockerMidpoint v = causalBlockerMidpointAt T v := by
  have hcount :=
    actualBlockerCount_eq_causalBlockerCountAt_of_visible_sublevel
      hcut hreach hTBase hupper
  unfold actualBlockerMidpoint countMidpoint causalBlockerMidpointAt
  rw [hcount]

theorem actualBlockerMidpoint_visible_sublevel_iff_causal
    {base margin center K T v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hreach : center + K <= T + margin)
    (hTBase : base <= T) :
    actualBlockerMidpoint v <= center + K <->
      causalBlockerMidpointAt T v <= center + K := by
  constructor
  . intro hactual
    rw [← actualBlockerMidpoint_eq_causal_of_visible_sublevel
      hcut hreach hTBase hactual]
    exact hactual
  . intro hcausal
    have hle := actualBlockerMidpoint_le_causalBlockerMidpointAt T v
    omega

theorem actualBlockerMidpoint_visible_band_iff_causal
    {base margin center K T v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hreach : center + K <= T + margin)
    (hTBase : base <= T) :
    (center - K < actualBlockerMidpoint v /\
        actualBlockerMidpoint v <= center + K) <->
      (center - K < causalBlockerMidpointAt T v /\
        causalBlockerMidpointAt T v <= center + K) := by
  constructor
  . intro hband
    have heq := actualBlockerMidpoint_eq_causal_of_visible_sublevel
      hcut hreach hTBase hband.2
    omega
  . intro hband
    have hactualUpper :=
      (actualBlockerMidpoint_visible_sublevel_iff_causal
        hcut hreach hTBase).2 hband.2
    have heq := actualBlockerMidpoint_eq_causal_of_visible_sublevel
      hcut hreach hTBase hactualUpper
    omega

/-- Complete cohort centered at `center`, reconstructed from a possibly later
visible diagonal horizon `T`. -/
noncomputable def causalBlockerMiddleCohortListFrom
    (T center K : Nat) : List Nat := by
  classical
  exact (List.range (2 * (center + K) + 2)).filter (fun v =>
    decide (center - K < causalBlockerMidpointAt T v /\
      causalBlockerMidpointAt T v <= center + K))

theorem actualBlockerMiddleCohortList_eq_causalFrom
    {base margin center K T : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hreach : center + K <= T + margin)
    (hTBase : base <= T) :
    actualBlockerMiddleCohortList center K =
      causalBlockerMiddleCohortListFrom T center K := by
  classical
  unfold actualBlockerMiddleCohortList
    causalBlockerMiddleCohortListFrom
  apply List.filter_congr
  intro v _hv
  exact decide_eq_decide.mpr
    (actualBlockerMidpoint_visible_band_iff_causal
      hcut hreach hTBase)

/-- Margin zero is already enough if the diagonal prefix is visible through
the right edge `center+K` of the midpoint window. -/
theorem actualBlockerMiddleCohortList_eq_causalFrom_rightEdge
    {base center K : Nat}
    (hownerLeMidpoint : ActualRangeOwnerMidpointCutoffFrom base 0)
    (hbase : base <= center + K) :
    actualBlockerMiddleCohortList center K =
      causalBlockerMiddleCohortListFrom (center + K) center K := by
  exact actualBlockerMiddleCohortList_eq_causalFrom
    hownerLeMidpoint (by omega) hbase

/-- For the three early lag-eight rows used by the transition, the K=10
right-edge diagonal packet lies strictly before the target value and is
therefore available to strong/simultaneous induction on that target. -/
theorem lag13_18_20_K10_visible_horizon_before_target
    {u L : Nat}
    (hLu : L <= u)
    (hL : L = 13 \/ L = 18 \/ L = 20) :
    u - L + 10 < u := by
  rcases hL with rfl | rfl | rfl <;> omega

/-! ## Visibility supplied directly, without a per-value owner margin -/

/-- Exact interface needed by the causal rank pullback: below every actual
sublevel candidate, each nonblocker is already present in the diagonal
prefix through `T`. -/
def ActualNonblockerSublevelVisible (T R : Nat) : Prop :=
  forall {v k : Nat}, 0 < k -> k < v ->
    actualBlockerMidpoint v <= R -> Not (S gameF k) ->
    PastDiagonalThrough T k

theorem actualBlockerCount_eq_causalBlockerCountAt_of_visibility
    {T R v : Nat}
    (hvisible : ActualNonblockerSublevelVisible T R)
    (hupper : actualBlockerMidpoint v <= R) :
    gameFBlockerCountThrough (v - 1) = causalBlockerCountAt T v := by
  classical
  let xs := List.range' 1 (v - 1)
  have hpartition := filter_decide_partition_length
    (fun k : Nat => S gameF k) xs
  have hcomplement :
      (xs.filter (fun k => decide (Not (S gameF k)))).length =
        (xs.filter (fun k => decide (PastDiagonalThrough T k))).length := by
    apply filter_length_eq_of_iff_on
    intro k hk
    have hkrange : 1 <= k /\ k < 1 + (v - 1) :=
      List.mem_range'_1.mp hk
    have hkv : k < v := by omega
    constructor
    . exact hvisible (by omega) hkv hupper
    . exact pastDiagonalThrough_not_blocker
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList] at *
  dsimp [xs] at hpartition hcomplement
  unfold causalBlockerCountAt gameFPastDiagonalBelowCount
    gameFPastDiagonalBelowList
  have hlen : (List.range' 1 (v - 1)).length = v - 1 := by simp
  omega

theorem actualBlockerMidpoint_eq_causal_of_visibility
    {T R v : Nat}
    (hvisible : ActualNonblockerSublevelVisible T R)
    (hupper : actualBlockerMidpoint v <= R) :
    actualBlockerMidpoint v = causalBlockerMidpointAt T v := by
  have hcount := actualBlockerCount_eq_causalBlockerCountAt_of_visibility
    hvisible hupper
  unfold actualBlockerMidpoint countMidpoint causalBlockerMidpointAt
  rw [hcount]

theorem actualBlockerMidpoint_sublevel_iff_causal_of_visibility
    {T R v : Nat}
    (hvisible : ActualNonblockerSublevelVisible T R) :
    actualBlockerMidpoint v <= R <->
      causalBlockerMidpointAt T v <= R := by
  constructor
  . intro hactual
    rw [← actualBlockerMidpoint_eq_causal_of_visibility
      hvisible hactual]
    exact hactual
  . intro hcausal
    have hle := actualBlockerMidpoint_le_causalBlockerMidpointAt T v
    omega

theorem actualBlockerMidpoint_band_iff_causal_of_visibility
    {T center K v : Nat}
    (hvisible : ActualNonblockerSublevelVisible T (center + K)) :
    (center - K < actualBlockerMidpoint v /\
        actualBlockerMidpoint v <= center + K) <->
      (center - K < causalBlockerMidpointAt T v /\
        causalBlockerMidpointAt T v <= center + K) := by
  constructor
  . intro hband
    have heq := actualBlockerMidpoint_eq_causal_of_visibility
      hvisible hband.2
    omega
  . intro hband
    have hactualUpper :=
      (actualBlockerMidpoint_sublevel_iff_causal_of_visibility
        hvisible).2 hband.2
    have heq := actualBlockerMidpoint_eq_causal_of_visibility
      hvisible hactualUpper
    omega

theorem actualBlockerMiddleCohortList_eq_causalFrom_of_visibility
    {T center K : Nat}
    (hvisible : ActualNonblockerSublevelVisible T (center + K)) :
    actualBlockerMiddleCohortList center K =
      causalBlockerMiddleCohortListFrom T center K := by
  classical
  unfold actualBlockerMiddleCohortList
    causalBlockerMiddleCohortListFrom
  apply List.filter_congr
  intro v _hv
  exact decide_eq_decide.mpr
    (actualBlockerMidpoint_band_iff_causal_of_visibility hvisible)

/-- A complete lower-owner certificate is sufficient, although stronger
than necessary because the causal cohort uses only its diagonal arm. -/
theorem actualNonblockerSublevelVisible_of_lowerOwnerCovered
    {T R : Nat}
    (howners : forall {v}, actualBlockerMidpoint v <= R ->
      LowerOwnerCoveredBy v T) :
    ActualNonblockerSublevelVisible T R := by
  intro v k hkpos hkv hupper hnot
  rcases howners hupper k hkpos hkv with hdiag | hstart
  . rcases hdiag with ⟨a, haT, ha⟩
    exact ⟨⟨a, by omega⟩, ha⟩
  . rcases hstart with ⟨s, _hsT, hsk, hs⟩
    exact False.elim (hnot ⟨s, hsk, hs⟩)

/-- The already isolated Floor+ / AFloor arithmetic is enough for a
margin-zero visible packet.  Unlike `RangeOwnerCutoff16`, this compares a
lower diagonal owner with the midpoint of the *candidate* `v`, which is all
the causal complement count needs.

The hypotheses are exactly the bank-domain forms used by R132: AFloor from
target 26 onward and Floor+ only for owners at least 16.  The finite owner
prefix is absorbed by `25 <= T`. -/
theorem actualNonblockerSublevelVisible_of_floorPlus_AFloor
    {T : Nat}
    (hT : 25 <= T)
    (hAFloor : forall {v}, 26 <= v ->
      v <= 3 * gameFBlockerCountThrough (v - 1) + 2)
    (hFloorPlus : forall {a k}, 16 <= a -> gameF a a = k ->
      3 * a + 5 <= 2 * k) :
    ActualNonblockerSublevelVisible T T := by
  intro v k hkpos hkv hupper hnot
  rcases gameRecurrenceModel.opening_cover hkpos with hD | hS
  . rcases hD with ⟨a, hak, ha⟩
    have haT : a <= T := by
      by_cases hv : 26 <= v
      . have hmidUpper :
            v + gameFBlockerCountThrough (v - 1) <
              2 * actualBlockerMidpoint v + 2 := by
          unfold actualBlockerMidpoint countMidpoint
          omega
        have hag := diagonal_owner_le_target_midpoint_of_tail_floor
          (a := a) (k := k) (v := v)
          (Av := gameFBlockerCountThrough (v - 1))
          (gv := actualBlockerMidpoint v)
          hv (fun ha16 => hFloorPlus ha16 ha) hkv
          (hAFloor hv) hmidUpper
        omega
      . omega
    exact ⟨⟨a, by omega⟩, ha⟩
  . exact False.elim (hnot hS)

/-- Therefore the full cohort is determined by the diagonal prefix through
the right edge `center+K` under Floor+ and AFloor alone. -/
theorem actualBlockerMiddleCohortList_eq_causalFrom_rightEdge_of_floorPlus_AFloor
    {center K : Nat}
    (hRight : 25 <= center + K)
    (hAFloor : forall {v}, 26 <= v ->
      v <= 3 * gameFBlockerCountThrough (v - 1) + 2)
    (hFloorPlus : forall {a k}, 16 <= a -> gameF a a = k ->
      3 * a + 5 <= 2 * k) :
    actualBlockerMiddleCohortList center K =
      causalBlockerMiddleCohortListFrom (center + K) center K := by
  apply actualBlockerMiddleCohortList_eq_causalFrom_of_visibility
  exact actualNonblockerSublevelVisible_of_floorPlus_AFloor
    hRight hAFloor hFloorPlus

/-- Direct early-lag instantiation used by the dual-stream transition.  It
returns both exact causal reconstruction and the strict induction order of
the whole visible diagonal packet. -/
theorem actualBlockerMiddleCohortList_earlyLag_K10_causal_of_floorPlus_AFloor
    {u L : Nat}
    (hLu : L <= u)
    (hL : L = 13 \/ L = 18 \/ L = 20)
    (hRight : 25 <= u - L + 10)
    (hAFloor : forall {v}, 26 <= v ->
      v <= 3 * gameFBlockerCountThrough (v - 1) + 2)
    (hFloorPlus : forall {a k}, 16 <= a -> gameF a a = k ->
      3 * a + 5 <= 2 * k) :
    actualBlockerMiddleCohortList (u - L) 10 =
        causalBlockerMiddleCohortListFrom
          (u - L + 10) (u - L) 10 /\
      u - L + 10 < u := by
  constructor
  . exact
      actualBlockerMiddleCohortList_eq_causalFrom_rightEdge_of_floorPlus_AFloor
        hRight hAFloor hFloorPlus
  . exact lag13_18_20_K10_visible_horizon_before_target hLu hL

/-- A future cohort member's blocker bit is also a past-diagonal-prefix
query: it is a blocker iff it is absent from the diagonal prefix through
`r`. -/
theorem gameF_middle_cohort_blocker_iff_not_pastDiagonal
    {base margin K r v : Nat}
    (hcut : ActualRangeOwnerMidpointCutoffFrom base margin)
    (hK : K <= margin)
    (hrBase : base <= r)
    (hvpos : 0 < v)
    (hcohort : v ∈ actualBlockerMiddleCohortList r K) :
    S gameF v <-> Not (PastDiagonalThrough r v) := by
  have hband := gameF_mem_actualBlockerMiddleCohortList.mp hcohort
  constructor
  . intro hS hpast
    exact pastDiagonalThrough_not_blocker hpast hS
  . intro hnotPast
    apply (gameF_blocker_iff_no_diagonal_owner hvpos).2
    rintro ⟨a, ha⟩
    have hownerLe : a <= r := by
      by_cases hvBase : base <= v
      . have hmargin := hcut hvBase ha
        omega
      . have hav : a < v := by
          have hgt := gameRecurrenceModel.diagonal_gt a
          change a < gameF a a at hgt
          rw [ha] at hgt
          exact hgt
        omega
    exact hnotPast ⟨⟨a, by omega⟩, ha⟩

/-- The open `RangeOwnerCutoff16` interface is more than enough for the
tested `K=10` cohort.  Once that existing owner-margin atom is supplied,
the future-cohort oracle disappears after the finite prefix `r < 131`. -/
theorem actualBlockerMiddleCohortList_eq_causal_of_cutoff16_K10
    {r : Nat}
    (hr : 131 <= r)
    (hcut16 : ActualRangeOwnerMidpointCutoffFrom 131 16) :
    actualBlockerMiddleCohortList r 10 =
      causalBlockerMiddleCohortList r 10 := by
  exact actualBlockerMiddleCohortList_eq_causal hcut16 (by omega) hr

theorem causalBlockerMiddleCohortList_length_le_42_of_cutoff16
    {r : Nat}
    (hr : 131 <= r)
    (hcut16 : ActualRangeOwnerMidpointCutoffFrom 131 16) :
    (causalBlockerMiddleCohortList r 10).length <= 42 := by
  simpa using causalBlockerMiddleCohortList_length_le
    hcut16 (by omega : 10 <= 16) hr

/-! ## Why the packet cannot be erased from the 0/1-count interface alone -/

private def delayedOneCount (r n : Nat) : Nat :=
  if r < n then 1 else 0

private theorem delayedOneCount_unitIncrement01 (r : Nat) :
    UnitIncrement01 (delayedOneCount r) := by
  intro n
  by_cases hn : r < n
  . left
    have hnext : r < n + 1 := by omega
    simp [delayedOneCount, hn, hnext]
  . by_cases hnext : r < n + 1
    . right
      simp [delayedOneCount, hn, hnext]
    . left
      simp [delayedOneCount, hn, hnext]

/-- Exact counterframe for the information content of R195's abstract
interface.  The two legal 0/1 counts agree at every index through `r`, but
at the future index `2r+1` their midpoints differ by one.  Therefore no
function of the count prefix through `r` alone can recover every future
cohort coordinate; one needs either the A-side suffix packet above or an
additional structural theorem such as the owner cutoff used in the causal
pullback. -/
theorem future_midpoint_not_determined_by_unitIncrement_prefix
    {r : Nat} (hr : 0 < r) :
    UnitIncrement01 (fun _ : Nat => 0) /\
      UnitIncrement01 (delayedOneCount r) /\
      (forall n, n <= r -> (fun _ : Nat => 0) n = delayedOneCount r n) /\
      countMidpoint (fun _ : Nat => 0) (2 * r + 1) = r /\
      countMidpoint (delayedOneCount r) (2 * r + 1) = r + 1 := by
  refine ⟨unitIncrement01_zero, delayedOneCount_unitIncrement01 r, ?_, ?_, ?_⟩
  . intro n hnr
    simp [delayedOneCount, show Not (r < n) by omega]
  . simp [countMidpoint]
    omega
  . simp [countMidpoint, delayedOneCount, show r < 2 * r by omega]
    omega

/-- The same counterframe changes literal cohort membership, not merely the
numeric midpoint.  At center `r-1` and width one, the future index `2r+1`
belongs for the zero continuation and does not belong for the delayed-one
continuation, although the two counts agree through `r`. -/
theorem future_band_not_determined_by_unitIncrement_prefix
    {r : Nat} (hr : 2 <= r) :
    let v := 2 * r + 1
    let center := r - 1
    (center - 1 < countMidpoint (fun _ : Nat => 0) v /\
      countMidpoint (fun _ : Nat => 0) v <= center + 1) /\
    Not (center - 1 < countMidpoint (delayedOneCount r) v /\
      countMidpoint (delayedOneCount r) v <= center + 1) := by
  dsimp
  have hdata := future_midpoint_not_determined_by_unitIncrement_prefix
    (r := r) (by omega)
  rcases hdata with ⟨_h0, _h1, _hprefix, hg0, hg1⟩
  constructor
  . omega
  . intro hband
    omega

#print axioms gameF_blocker_iff_no_diagonal_owner
#print axioms gameFBlockerCountThrough_eq_past_add_futurePacket
#print axioms actualBlockerMidpoint_eq_past_add_futurePacket
#print axioms middle_cohort_futurePacket_horizon
#print axioms actualBlockerCount_add_pastDiagonalCount_le
#print axioms actualBlockerMidpoint_le_causalBlockerMidpointAt
#print axioms gameF_not_blocker_iff_pastDiagonalThrough_of_sublevel
#print axioms actualBlockerCount_eq_causalBlockerCountAt_of_sublevel
#print axioms actualBlockerMidpoint_sublevel_iff_causal
#print axioms actualBlockerMidpoint_band_iff_causal
#print axioms actualBlockerMiddleCohortList_eq_causal
#print axioms causalBlockerMiddleCohortList_length_le
#print axioms gameF_not_blocker_iff_pastDiagonalThrough_of_visible_sublevel
#print axioms actualBlockerCount_eq_causalBlockerCountAt_of_visible_sublevel
#print axioms actualBlockerMidpoint_visible_sublevel_iff_causal
#print axioms actualBlockerMidpoint_visible_band_iff_causal
#print axioms actualBlockerMiddleCohortList_eq_causalFrom
#print axioms actualBlockerMiddleCohortList_eq_causalFrom_rightEdge
#print axioms lag13_18_20_K10_visible_horizon_before_target
#print axioms actualBlockerCount_eq_causalBlockerCountAt_of_visibility
#print axioms actualBlockerMidpoint_sublevel_iff_causal_of_visibility
#print axioms actualBlockerMiddleCohortList_eq_causalFrom_of_visibility
#print axioms actualNonblockerSublevelVisible_of_lowerOwnerCovered
#print axioms actualNonblockerSublevelVisible_of_floorPlus_AFloor
#print axioms actualBlockerMiddleCohortList_eq_causalFrom_rightEdge_of_floorPlus_AFloor
#print axioms actualBlockerMiddleCohortList_earlyLag_K10_causal_of_floorPlus_AFloor
#print axioms gameF_middle_cohort_blocker_iff_not_pastDiagonal
#print axioms actualBlockerMiddleCohortList_eq_causal_of_cutoff16_K10
#print axioms causalBlockerMiddleCohortList_length_le_42_of_cutoff16
#print axioms future_midpoint_not_determined_by_unitIncrement_prefix
#print axioms future_band_not_determined_by_unitIncrement_prefix

end ChompLean
