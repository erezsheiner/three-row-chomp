import R148bPersistentHostOrderedHall

set_option autoImplicit false

namespace ChompLean

/-!
R148d: CONTENT-INTERVAL and the rounded 7/5 incidence counterframe.

The finite CONTENT-INTERVAL observation is not assumed as a game theorem
here.  Instead, this file checks an explicit all-index interface family that
satisfies its exact interval shape, PiZero, FCROSS, the ordered-HCR endpoint,
and a collision-free two-dimensional host matching.  Its critical freeze is
still strictly left of the R147 target triple.
-/

/-- `ceil(2*n/5)`, written with natural-number division. -/
def r148dR (n : Nat) : Nat := (2 * n + 4) / 5

theorem r148dR_bounds (n : Nat) :
    2 * n <= 5 * r148dR n /\
    5 * r148dR n <= 2 * n + 4 := by
  simp [r148dR]
  omega

theorem r148dR_le_self {n : Nat} (hn : 1 <= n) :
    r148dR n <= n := by
  have h := (r148dR_bounds n).2
  omega

theorem r148dR_mono {a b : Nat} (hab : a <= b) :
    r148dR a <= r148dR b := by
  simp [r148dR]
  omega

theorem r148dR_step {n : Nat} :
    r148dR (n + 1) <= r148dR n + 1 := by
  simp [r148dR]
  omega

/-- The late `A_k` blocker of late index `j` and its rank. -/
def r148dB (k j : Nat) : Nat := 4 * k + 3 * j + 1
def r148dI (k j : Nat) : Nat := 2 * k + j

/-- Rounded `7/5` freeze schedule:
`c_(2k+j)=4k-1+ceil(7j/5)=4k-1+j+ceil(2j/5)`. -/
def r148dC (k j : Nat) : Nat := 4 * k - 1 + j + r148dR j

/-- The preceding early ranks use the PiZero ceiling and have no
earlier-frozen load. -/
def r148dEarlyC (i : Nat) : Nat := 2 * i - 1

theorem r148d_early_pizero_zero
    {i : Nat} (hi : 1 <= i) :
    r148dEarlyC i + 0 = 2 * i - 1 := by
  simp [r148dEarlyC]

theorem r148d_early_strict
    {i l : Nat} (hi : 1 <= i) (hil : i < l) :
    r148dEarlyC i < r148dEarlyC l := by
  simp [r148dEarlyC]
  omega

/-- The splice from the last early rank to the first late rank is a gap of
two, so the entire displayed prefix has freeze gaps at most two. -/
theorem r148d_early_late_splice (k : Nat) (hk : 1 <= k) :
    r148dC k 1 = r148dEarlyC (2 * k) + 2 := by
  simp [r148dC, r148dEarlyC, r148dR]
  omega

/-- PiZero load and the first rank in the CONTENT suffix. -/
def r148dKappa (j : Nat) : Nat := j - r148dR j
def r148dP (k j : Nat) : Nat := 2 * k + r148dR j

/-- Exact CONTENT-INTERVAL choice: the unshifted suffix `[p_i,i-1]`. -/
def r148dContent (j s : Nat) : Prop :=
  r148dR j <= s /\ s < j

theorem r148d_freeze_strict
    {k j l : Nat} (hjl : j < l) :
    r148dC k j < r148dC k l := by
  have hr := r148dR_mono (Nat.le_of_lt hjl)
  simp [r148dC]
  omega

theorem r148d_freeze_gap_at_most_two (k j : Nat) :
    r148dC k (j + 1) <= r148dC k j + 2 := by
  have hr := r148dR_step (n := j)
  simp [r148dC]
  omega

theorem r148d_freeze_before_blocker
    {k j : Nat} (hj : 1 <= j) :
    r148dC k j < r148dB k j := by
  have hr := r148dR_le_self hj
  simp [r148dC, r148dB]
  omega

theorem r148d_pizero
    {k j : Nat} (hk : 1 <= k) (hj : 1 <= j) :
    r148dC k j + r148dKappa j = 2 * r148dI k j - 1 := by
  have hr := r148dR_le_self hj
  have hsub : j - r148dR j + r148dR j = j :=
    Nat.sub_add_cancel hr
  simp only [r148dC, r148dKappa, r148dI]
  omega

theorem r148d_probe_rank
    {k j : Nat} (hk : 1 <= k) (hj : 1 <= j) :
    r148dC k j - r148dI k j + 1 = r148dP k j := by
  have hr := r148dR_le_self hj
  simp [r148dC, r148dI, r148dP]
  omega

theorem r148d_content_is_exact_form1
    {k j s : Nat} (hk : 1 <= k) (hj : 1 <= j) :
    r148dContent j s <->
      r148dP k j <= 2 * k + s /\
        2 * k + s <= r148dI k j - 1 := by
  simp [r148dContent, r148dP, r148dI]
  omega

/-- The suffix has exactly the PiZero number of ranks. -/
theorem r148d_content_length
    {j : Nat} (hj : 1 <= j) :
    j - r148dR j = r148dKappa j := by
  rfl

/-- FCROSS holds at every late rank of the rounded schedule. -/
theorem r148d_fcross
    {k j : Nat} (hk : 2 <= k) (hj : 1 <= j) (hjk : j <= 2 * k) :
    r148dB k j <=
      r148dB k (r148dR j) + r148dC k (r148dR j) := by
  have hjLower := (r148dR_bounds j).1
  have hjUpper := (r148dR_bounds j).2
  have hrle := r148dR_le_self hj
  have hrr := r148dR_bounds (r148dR j)
  simp [r148dB, r148dC]
  omega

/-- Exact blocker count at the successor of the rounded freeze, in the
uncapped late part of the `A_k` word. -/
def r148dAFreezeSucc (k j : Nat) : Nat :=
  2 * k + (j + r148dR j - 1) / 3

/-- ORDERED-HCR-HALL endpoint for every late blocker. -/
theorem r148d_ordered_hcr_endpoint
    {k j : Nat} (hk : 2 <= k) (hj : 1 <= j) (hjk : j <= 2 * k) :
    r148dB k j + r148dAFreezeSucc k j <= 2 * r148dC k j + 1 := by
  have hrl := (r148dR_bounds j).1
  have hru := (r148dR_bounds j).2
  have hrle := r148dR_le_self hj
  simp [r148dB, r148dAFreezeSucc, r148dC]
  omega

/-! ## A collision-free incidence matching -/

/-- If late column `s` belongs to target `j`'s CONTENT interval, put the
load in the `(j-s)`-th row immediately before blocker `b_s` freezes. -/
def r148dHostRow (k j s : Nat) : Nat :=
  r148dB k s - (j - s)

theorem r148d_content_implies_ratio
    {j s : Nat} (hcontent : r148dContent j s) :
    2 * j <= 5 * s := by
  have h := (r148dR_bounds j).1
  simp [r148dContent] at hcontent
  omega

/-- Every named host is a genuine pre-freeze cell in its column. -/
theorem r148d_host_before_freeze
    {k j s : Nat} (hk : 2 <= k) (hj : 1 <= j)
    (hjk : j <= 2 * k) (hcontent : r148dContent j s) :
    r148dC k s <= r148dHostRow k j s /\
      r148dHostRow k j s < r148dB k s := by
  have hratio := r148d_content_implies_ratio hcontent
  have hslt : s < j := hcontent.2
  have hspos : 1 <= s := by
    have hrpos : 1 <= r148dR j := by
      have hlow := (r148dR_bounds j).1
      omega
    omega
  have hrs := r148dR_bounds s
  have hrsle := r148dR_le_self hspos
  simp [r148dC, r148dHostRow, r148dB]
  omega

/-- CellCeiling has uniform slack at every incidence. -/
theorem r148d_host_cell_ceiling
    {k j s : Nat} (hk : 2 <= k) (hj : 1 <= j)
    (hjk : j <= 2 * k) (hcontent : r148dContent j s) :
    r148dB k j <= r148dHostRow k j s + r148dC k s + 1 := by
  have hratio := r148d_content_implies_ratio hcontent
  have hslt : s < j := hcontent.2
  have hspos : 1 <= s := by
    have hlow := (r148dR_bounds j).1
    have hrle : r148dR j <= s := hcontent.1
    omega
  have hrsle := r148dR_le_self hspos
  simp [r148dB, r148dHostRow, r148dC]
  omega

/-- For a fixed target, increasing the freeze rank increases the assigned
host row by four, so RowInj is automatic. -/
theorem r148d_target_rows_injective
    {k j s t : Nat} (hk : 2 <= k) (hj : 1 <= j) (hjk : j <= 2 * k)
    (hsContent : r148dContent j s)
    (htContent : r148dContent j t) (hst : s < t) :
    r148dHostRow k j s < r148dHostRow k j t := by
  have hsValid := r148d_host_before_freeze hk hj hjk hsContent
  have htValid := r148d_host_before_freeze hk hj hjk htContent
  simp [r148dHostRow, r148dB] at hsValid htValid ⊢
  omega

/-- In a fixed column, successive target ranks use successive earlier rows;
the column never repeats a blocker value. -/
theorem r148d_column_rows_injective
    {k i j s : Nat} (hk : 2 <= k) (hi : 1 <= i) (hij : i < j)
    (hjk : j <= 2 * k)
    (hiContent : r148dContent i s)
    (hjContent : r148dContent j s) :
    r148dHostRow k j s < r148dHostRow k i s := by
  have hjpos : 1 <= j := by omega
  have hik : i <= 2 * k := by omega
  have hiValid := r148d_host_before_freeze hk hi hik hiContent
  have hjValid := r148d_host_before_freeze hk hjpos hjk hjContent
  simp [r148dHostRow, r148dB] at hiValid hjValid ⊢
  omega

/-- The critical freeze remains strictly left of the first R147 target
column `7k`; hence future ordered freezes may occupy the target triple. -/
theorem r148d_critical_freeze_left_of_targets
    {k : Nat} (hk : 4 <= k) :
    r148dC k (2 * k) < 7 * k := by
  have hr := (r148dR_bounds (2 * k)).2
  simp [r148dC]
  omega

/-! The earlier all-live kinks also satisfy CONTENT-INTERVAL locally.  They
therefore separate CONTENT from any freeze-gap-at-most-three theorem. -/

theorem r148d_even_kink_content_form1
    (m : Nat) (hm : 2 <= m) :
    let i := 7 * m + 1
    let cA := 14 * m - 1
    let cB := 14 * m + 3
    cA - i + 1 = i - 2 /\
    cA + 2 = 2 * i - 1 /\
    cB - (i + 1) + 1 = i + 1 /\
    cB + 0 = 2 * (i + 1) - 1 /\
    cB - cA = 4 := by
  dsimp
  omega

theorem r148d_odd_kink_content_form1
    (m : Nat) (hm : 2 <= m) :
    let i := 7 * m + 5
    let cA := 14 * m + 5
    let cB := 14 * m + 6
    cA - (i - 1) + 1 = (i - 1) - 2 /\
    cA + 2 = 2 * (i - 1) - 1 /\
    cB - i + 1 = i - 3 /\
    cB + 3 = 2 * i - 1 /\
    R148HighFreeze (i + 1) - cB = 4 := by
  dsimp [R148HighFreeze]
  omega

/-! ## Exact conditional role of NO-THREE-LIVE -/

/-- At least one of three consecutive columns has already frozen by `row`. -/
def ThreeColumnsHavePastFreeze
    (M : RecurrenceModel) (row e : Nat) : Prop :=
  exists j, j <= 2 /\ exists w,
    e + j < w /\ w <= row /\ M.f w (e + j) = w

/-- A proved NO-THREE-LIVE statement at the target row would immediately
force TRIPLE-CAP: the frozen target is a carry of a value at most `v`. -/
theorem pastFreeze_in_target_triple_forces_cap
    (M : RecurrenceModel) {row e v : Nat}
    (hrowv : row <= v)
    (hPast : ThreeColumnsHavePastFreeze M row e) :
    exists j, j <= 2 /\ M.f row (e + j) <= v := by
  let j := Classical.choose hPast
  have hjData := Classical.choose_spec hPast
  let w := Classical.choose hjData.2
  have hwData := Classical.choose_spec hjData.2
  have hj : j <= 2 := hjData.1
  have hew : e + j < w := hwData.1
  have hwr : w <= row := hwData.2.1
  have hfreeze : M.f w (e + j) = w := hwData.2.2
  have hconst := constant_from M hew (by rw [hfreeze]; omega)
      (row - w)
  have hidx : w + (row - w) = row := by omega
  rw [hidx, hfreeze] at hconst
  exact Exists.intro j (And.intro hj (by omega))

/-! ## Arithmetic reduction of CONTENT-INTERVAL -/

/-- Once PiZero fixes interval length `kappa`, CONTENT-INTERVAL reduces to
two genuinely game-specific facts: rank-convexity and the lower cutoff
`start >= c-i`.  The arithmetic then leaves only the two observed starts. -/
theorem tight_convex_start_pin
    {i c kappa start : Nat}
    (hic : i <= c)
    (hPiZero : c + kappa = 2 * i - 1)
    (hOldCutoff : c - i <= start)
    (hFits : start + kappa <= i) :
    start = c - i \/ start = c - i + 1 := by
  omega

#print axioms r148d_fcross
#print axioms r148d_ordered_hcr_endpoint
#print axioms r148d_host_before_freeze
#print axioms r148d_host_cell_ceiling
#print axioms r148d_target_rows_injective
#print axioms r148d_critical_freeze_left_of_targets
#print axioms r148d_even_kink_content_form1
#print axioms r148d_odd_kink_content_form1
#print axioms pastFreeze_in_target_triple_forces_cap
#print axioms tight_convex_start_pin

end ChompLean
