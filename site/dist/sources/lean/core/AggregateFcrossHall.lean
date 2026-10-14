import R148dContentIntervalRoundedCounterframe

set_option autoImplicit false

namespace ChompLean

/-!
Aggregate audit of freeze-cross incidences.

The first theorem is the exact fixed-column capacity that is absent from the
pointwise FCROSS inequality: distinct later blocker loads must occupy
distinct pre-freeze rows. The remaining theorems independently close small
arithmetic gaps in the rounded R148d interface survivor (strictly triangular
hosts, its early prefix, and the final-hole deadline).
-/

/-- If `loads` distinct services in one column occupy rows in `[lo,b)`, then
there are at most `b-lo` services. In the freeze-cross application

`lo = max (c+1) (u-c-1)`

for a blocker-value cutoff `u`. Thus this statement includes both the
triangular row capacity and every high-value suffix capacity. -/
theorem aggregate_fixed_column_high_slot_capacity
    {loads lo b : Nat}
    (row : Fin loads -> Nat)
    (hLower : forall x, lo <= row x)
    (hUpper : forall x, row x < b)
    (hInjective : Function.Injective row) :
    loads <= b - lo := by
  let slot : Fin loads -> Fin (b - lo) := fun x =>
    Fin.mk (row x - lo) (by
      have hlo := hLower x
      have hhi := hUpper x
      omega)
  have hSlot : Function.Injective slot := by
    intro x y hxy
    have hval := congrArg Fin.val hxy
    dsimp [slot] at hval
    have hx := hLower x
    have hy := hLower y
    apply hInjective
    omega
  exact r148b_fin_injective_card_le slot hSlot

/-- The unweighted version used for a whole pre-freeze column. -/
theorem aggregate_fixed_column_full_capacity
    {loads c b : Nat}
    (row : Fin loads -> Nat)
    (hLower : forall x, c < row x)
    (hUpper : forall x, row x < b)
    (hInjective : Function.Injective row) :
    loads <= b - c - 1 := by
  have h := aggregate_fixed_column_high_slot_capacity row
    (lo := c + 1) (fun x => by have := hLower x; omega) hUpper hInjective
  omega

/-! ## Independent strictness and prefix audit for R148d -/

/-- R148d's displayed host is strictly above the diagonal, not merely weakly
above it. Together with `r148d_host_before_freeze`, this puts it in the open
triangular interval `(c_s,b_s)`. -/
theorem r148d_host_strictly_above_diagonal
    {k j s : Nat} (hk : 2 <= k) (hj : 1 <= j)
    (hjk : j <= 2 * k) (hcontent : r148dContent j s) :
    r148dC k s < r148dHostRow k j s := by
  have hratio := r148d_content_implies_ratio hcontent
  have hspos : 1 <= s := by
    have hlow := (r148dR_bounds j).1
    have hrle : r148dR j <= s := hcontent.1
    omega
  have hrs := r148dR_bounds s
  have hrsle := r148dR_le_self hspos
  simp [r148dC, r148dHostRow, r148dB]
  omega

/-- Complete early prefix for the rounded schedule. -/
def aggregateEarlyFreeze (i : Nat) : Nat := 2 * i - 1

theorem aggregate_early_pizero_zero_load
    {i : Nat} (_hi : 1 <= i) :
    aggregateEarlyFreeze i + 0 = 2 * i - 1 := by
  simp [aggregateEarlyFreeze]

/-- Every early column has zero open pre-freeze rows, exactly matching its
zero PiZero load. -/
theorem aggregate_early_zero_prefreeze_capacity
    {i : Nat} (hi : 1 <= i) :
    r146EarlyBlocker i - aggregateEarlyFreeze i - 1 = 0 := by
  simp [r146EarlyBlocker, aggregateEarlyFreeze]
  omega

/-- The last early freeze is strictly before the first rounded late freeze. -/
theorem aggregate_prefix_to_rounded_tail_order
    {k : Nat} (hk : 1 <= k) :
    aggregateEarlyFreeze (2 * k) < r148dC k 1 := by
  simp [aggregateEarlyFreeze, r148dC, r148dR]
  omega

/-- The R148b ordered-HCR endpoint also holds on every early blocker of the
completed schedule. -/
theorem aggregate_early_ordered_hcr_endpoint
    {k i : Nat} (hi : 1 <= i) (hik : i <= 2 * k) :
    r146EarlyBlocker i + FrameCount k (aggregateEarlyFreeze i + 1) <=
      2 * aggregateEarlyFreeze i + 1 := by
  have hn : 2 * i <= 4 * k := by omega
  simp only [r146EarlyBlocker, aggregateEarlyFreeze]
  have hsub : 2 * i - 1 + 1 = 2 * i := by omega
  rw [hsub]
  simp only [FrameCount, if_pos hn]
  rw [show (2 * i) / 2 = i by omega]
  omega

/-- The rounded critical endpoint obeys the special future-V1 deadline while
remaining strictly left of the first R147 target column. -/
theorem r148d_critical_deadline_and_target_gap
    {k : Nat} (hk : 4 <= k) :
    FrameT k <= r148dC k (2 * k) /\
      r148dC k (2 * k) < 7 * k := by
  have hlow := (r148dR_bounds (2 * k)).1
  have hhigh := (r148dR_bounds (2 * k)).2
  constructor
  case left =>
    simp [FrameT, r148dC]
    omega
  case right =>
    exact r148d_critical_freeze_left_of_targets hk

/-! ## A stronger survivor that also tracks the old Phi-R receipt -/

/-- Ceiling of `j/2`. -/
def aggregateHalf (j : Nat) : Nat := (j + 1) / 2

theorem aggregateHalf_bounds (j : Nat) :
    j <= 2 * aggregateHalf j /\
      2 * aggregateHalf j <= j + 1 := by
  simp [aggregateHalf]
  omega

theorem aggregateHalf_le_self {j : Nat} (hj : 1 <= j) :
    aggregateHalf j <= j := by
  have h := (aggregateHalf_bounds j).2
  omega

/-- The late `3/2` freeze schedule. Its offsets from `4k` are
`1,2,4,5,7,8,...`, exactly the positive offsets not divisible by three. -/
def aggregateBandFreeze (k j : Nat) : Nat :=
  4 * k - 1 + j + aggregateHalf j

def aggregateBandKappa (j : Nat) : Nat := j - aggregateHalf j

def aggregateBandContent (j s : Nat) : Prop :=
  aggregateHalf j <= s /\ s < j

def aggregateBandHostRow (k j s : Nat) : Nat :=
  r148dB k s - (j - s)

theorem aggregateBand_pizero
    {k j : Nat} (hk : 1 <= k) (hj : 1 <= j) :
    aggregateBandFreeze k j + aggregateBandKappa j =
      2 * r148dI k j - 1 := by
  have hh := aggregateHalf_le_self hj
  have hsub := Nat.sub_add_cancel hh
  simp only [aggregateBandFreeze, aggregateBandKappa, r148dI]
  omega

theorem aggregateBand_fcross
    {k j : Nat} (hk : 2 <= k) (hj : 1 <= j) (hjk : j <= 2 * k) :
    r148dB k j <=
      r148dB k (aggregateHalf j) +
        aggregateBandFreeze k (aggregateHalf j) := by
  have hb := aggregateHalf_bounds j
  have hh := aggregateHalf_le_self hj
  have hhb := aggregateHalf_bounds (aggregateHalf j)
  simp [r148dB, aggregateBandFreeze]
  omega

def aggregateBandAFreezeSucc (k j : Nat) : Nat :=
  2 * k + (j + aggregateHalf j - 1) / 3

theorem aggregateBand_ordered_hcr_endpoint
    {k j : Nat} (hk : 2 <= k) (hj : 1 <= j) (hjk : j <= 2 * k) :
    r148dB k j + aggregateBandAFreezeSucc k j <=
      2 * aggregateBandFreeze k j + 1 := by
  have hb := aggregateHalf_bounds j
  have hh := aggregateHalf_le_self hj
  simp [r148dB, aggregateBandAFreezeSucc, aggregateBandFreeze]
  omega

theorem aggregateBand_content_implies_ratio
    {j s : Nat} (hcontent : aggregateBandContent j s) :
    j <= 2 * s := by
  have hb := (aggregateHalf_bounds j).1
  have hs := Nat.mul_le_mul_left 2 hcontent.1
  omega

theorem aggregateBand_service_chronology
    {k j s : Nat} (hk : 2 <= k) (hj : 1 <= j)
    (hjk : j <= 2 * k) (hcontent : aggregateBandContent j s) :
    aggregateBandFreeze k s < aggregateBandHostRow k j s /\
      aggregateBandHostRow k j s < r148dB k s /\
      r148dB k s < r148dB k j := by
  have hratio := aggregateBand_content_implies_ratio hcontent
  have hslt := hcontent.2
  have hspos : 1 <= s := by
    have hb := (aggregateHalf_bounds j).1
    omega
  have hhs := aggregateHalf_bounds s
  have hhle := aggregateHalf_le_self hspos
  simp [aggregateBandFreeze, aggregateBandHostRow, r148dB]
  omega

theorem aggregateBand_service_cell_ceiling
    {k j s : Nat} (hk : 2 <= k) (hj : 1 <= j)
    (hjk : j <= 2 * k) (hcontent : aggregateBandContent j s) :
    r148dB k j <=
      aggregateBandHostRow k j s + aggregateBandFreeze k s + 1 := by
  have hratio := aggregateBand_content_implies_ratio hcontent
  have hslt := hcontent.2
  have hspos : 1 <= s := by
    have hb := (aggregateHalf_bounds j).1
    omega
  have hhs := aggregateHalf_bounds s
  have hhle := aggregateHalf_le_self hspos
  simp [aggregateBandFreeze, aggregateBandHostRow, r148dB]
  omega

theorem aggregateBand_target_rows_injective
    {k j s t : Nat} (hk : 2 <= k) (hjk : j <= 2 * k)
    (hsj : s < j) (htj : t < j) (hst : s < t) :
    aggregateBandHostRow k j s < aggregateBandHostRow k j t := by
  simp [aggregateBandHostRow, r148dB]
  omega

theorem aggregateBand_column_rows_injective
    {k i j s : Nat} (hk : 2 <= k) (hjk : j <= 2 * k)
    (his : s < i) (hij : i < j) :
    aggregateBandHostRow k j s < aggregateBandHostRow k i s := by
  simp [aggregateBandHostRow, r148dB]
  omega

theorem aggregateBand_critical_endpoint
    {k : Nat} (hk : 4 <= k) :
    aggregateBandFreeze k (2 * k) = 7 * k - 1 /\
      FrameT k <= aggregateBandFreeze k (2 * k) /\
      aggregateBandFreeze k (2 * k) < 7 * k := by
  simp [aggregateBandFreeze, aggregateHalf, FrameT]
  omega

/-- Late freeze gaps are one or two, so this survivor satisfies the static
NO-THREE-LIVE consequence with room. -/
theorem aggregateBand_freeze_gap_at_most_two (k j : Nat) :
    aggregateBandFreeze k (j + 1) <= aggregateBandFreeze k j + 2 := by
  simp [aggregateBandFreeze, aggregateHalf]
  omega

/-- The equivalent KAPPA-DROP-ONE inequality also holds. -/
theorem aggregateBand_kappa_drop_one (j : Nat) :
    aggregateBandKappa j <= aggregateBandKappa (j + 1) + 1 := by
  simp [aggregateBandKappa, aggregateHalf]
  omega

/-- On the dense early half, the empirical assignment-band displacement is
not bounded: it is exactly `i/2`. -/
theorem aggregate_early_assignment_displacement
    {i : Nat} (hi : 1 <= i) :
    aggregateEarlyFreeze i - (3 * i - 1) / 2 = i / 2 := by
  simp [aggregateEarlyFreeze]
  omega

/-- A single MaxPlus/NoAssignmentGap instance kills the forced early
placement. If both the previous freeze and the lag-three preview are at most
`2i-3`, MaxPlus puts the new freeze at most `2i-2`, whereas aggregate
capacity forces `2i-1`. -/
theorem aggregate_early_one_column_maxplus_kill
    {i previous preview : Nat} (hi : 2 <= i)
    (hPrevious : previous <= 2 * i - 3)
    (hPreview : preview <= 2 * i - 3)
    (hMaxPlus : aggregateEarlyFreeze i = max previous preview + 1) :
    False := by
  by_cases hle : previous <= preview
  case pos =>
    rw [Nat.max_eq_right hle] at hMaxPlus
    simp [aggregateEarlyFreeze] at hMaxPlus
    omega
  case neg =>
    have hge : preview <= previous := by omega
    rw [Nat.max_eq_left hge] at hMaxPlus
    simp [aggregateEarlyFreeze] at hMaxPlus
    omega

/-- Arithmetic core of the old finite `Phi-R` receipt on the late interval.
The `3/2` schedule has `m-m/3` late freezes through offset `m`, while the
R141 word has `m-(m-1)/3` new range values. Their difference is zero or
minus one. -/
theorem aggregateBand_phi_R_trit
    {k m : Nat} (hm : 1 <= m) :
    let phi := 2 * k + m - m / 3
    let range := 2 * k + m - (m - 1) / 3
    phi = range \/ phi + 1 = range := by
  dsimp
  omega

#print axioms aggregate_fixed_column_high_slot_capacity
#print axioms aggregate_fixed_column_full_capacity
#print axioms r148d_host_strictly_above_diagonal
#print axioms aggregate_early_ordered_hcr_endpoint
#print axioms r148d_critical_deadline_and_target_gap
#print axioms aggregateBand_fcross
#print axioms aggregateBand_ordered_hcr_endpoint
#print axioms aggregateBand_service_chronology
#print axioms aggregateBand_service_cell_ceiling
#print axioms aggregateBand_critical_endpoint
#print axioms aggregateBand_phi_R_trit
#print axioms aggregateBand_freeze_gap_at_most_two
#print axioms aggregateBand_kappa_drop_one
#print axioms aggregate_early_assignment_displacement
#print axioms aggregate_early_one_column_maxplus_kill

end ChompLean
