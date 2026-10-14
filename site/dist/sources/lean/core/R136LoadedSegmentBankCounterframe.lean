import R132UpperRailOwnerCoverageReduction

set_option autoImplicit false

namespace ChompLean

/-!
An abstract counterframe for the R02 loaded-column interfaces.

This is deliberately not claimed to be a second Chomp game.  It shows that
the information exported by R02/NEWBORN/FCHP about a single blocker does not
itself contradict a consecutive live loaded segment.  For every `k >= 2` we
use

  v = 10k,  A(v-1) = 4k,  g = 7k,  c_v = 8k.

The high rows are the interval `[6k-1,10k)`, hence have the advertised R02
cardinality `A+1`.  The map below assigns them injectively to columns below
`c_v`, respects the newborn host, the two floor hosts, and the cell-ceiling
host pin.  Every column in `[g+1,c_v)` occurs in its image.  The segment has
length `k-1`, so these interfaces permit segments of unbounded length.
-/

def r136V (k : Nat) : Nat := 10 * k
def r136A (k : Nat) : Nat := 4 * k
def r136G (k : Nat) : Nat := 7 * k
def r136C (k : Nat) : Nat := 8 * k
def r136Birth (k : Nat) : Nat := 6 * k - 1

/-- Explicit host-column assignment on the high-row interval. -/
def r136Host (k x : Nat) : Nat :=
  if x = 6 * k - 1 then 6 * k - 2
  else if x = 10 * k - 2 then 2
  else if x = 10 * k - 1 then 0
  else if x <= 8 * k - 4 then x - 2 * k + 1
  else x - 2 * k + 2

/-- A left inverse on the advertised host image. -/
def r136Unhost (k e : Nat) : Nat :=
  if e = 6 * k - 2 then 6 * k - 1
  else if e = 2 then 10 * k - 2
  else if e = 0 then 10 * k - 1
  else if e <= 6 * k - 3 then e + 2 * k - 1
  else e + 2 * k - 2

def r136HighRow (k x : Nat) : Prop :=
  r136Birth k <= x /\ x < r136V k

def r136Loaded (k e : Nat) : Prop :=
  exists x, r136HighRow k x /\ r136Host k x = e

/-- The midpoint arithmetic is exact, not an asymptotic convention. -/
theorem r136_midpoint_exact (k : Nat) :
    2 * r136G k = r136V k + r136A k := by
  unfold r136G r136V r136A
  omega

/-- The proposed upper rail fails by a segment of length `k-1`. -/
theorem r136_segment_length (k : Nat) (hk : 2 <= k) :
    r136C k - (r136G k + 1) = k - 1 := by
  simp [r136C, r136G]
  omega

/-- The R02 exact freeze-column ledger can absorb this frame with
`L=0`, `kappa=1`, `pi=0`. -/
theorem r136_freeze_ledger (k : Nat) :
    r136C k = 2 * r136A k + 1 - 0 - 1 - 0 := by
  unfold r136C r136A
  omega

/-- The high-row interval has exactly the banked BIJ length `A(v-1)+1`. -/
theorem r136_high_row_count (k : Nat) (hk : 1 <= k) :
    r136V k - r136Birth k = r136A k + 1 := by
  unfold r136Birth r136V r136A
  omega

/-- Every host lies strictly below its row, as an off-diagonal occurrence
must. -/
theorem r136_host_lt_row {k x : Nat} (hk : 2 <= k)
    (hx : r136HighRow k x) :
    r136Host k x < x := by
  rcases hx with ⟨hx0, hx1⟩
  change 6 * k - 1 <= x at hx0
  change x < 10 * k at hx1
  by_cases h0 : x = 6 * k - 1
  · simp only [r136Host, if_pos h0]
    omega
  by_cases h1 : x = 10 * k - 2
  · simp only [r136Host, if_neg h0, if_pos h1]
    omega
  by_cases h2 : x = 10 * k - 1
  · simp only [r136Host, if_neg h0, if_neg h1, if_pos h2]
    omega
  by_cases h3 : x <= 8 * k - 4
  · simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
    omega
  · simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
    omega

/-- PiZero/freeze exclusion: every occurrence column is strictly left of
`c_v`. -/
theorem r136_host_lt_freeze {k x : Nat} (hk : 2 <= k)
    (hx : r136HighRow k x) :
    r136Host k x < r136C k := by
  rcases hx with ⟨hx0, hx1⟩
  change 6 * k - 1 <= x at hx0
  change x < 10 * k at hx1
  change r136Host k x < 8 * k
  by_cases h0 : x = 6 * k - 1
  · simp only [r136Host, if_pos h0]
    omega
  by_cases h1 : x = 10 * k - 2
  · simp only [r136Host, if_neg h0, if_pos h1]
    omega
  by_cases h2 : x = 10 * k - 1
  · simp only [r136Host, if_neg h0, if_neg h1, if_pos h2]
    omega
  by_cases h3 : x <= 8 * k - 4
  · simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
    omega
  · simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
    omega

/-- The cell-ceiling consequence `e >= v-x-1`, written without truncated
subtraction. -/
theorem r136_host_pin {k x : Nat} (hk : 2 <= k)
    (hx : r136HighRow k x) :
    r136V k <= x + r136Host k x + 1 := by
  rcases hx with ⟨hx0, hx1⟩
  change 6 * k - 1 <= x at hx0
  change x < 10 * k at hx1
  change 10 * k <= x + r136Host k x + 1
  by_cases h0 : x = 6 * k - 1
  · simp only [r136Host, if_pos h0]
    omega
  by_cases h1 : x = 10 * k - 2
  · simp only [r136Host, if_neg h0, if_pos h1]
    omega
  by_cases h2 : x = 10 * k - 1
  · simp only [r136Host, if_neg h0, if_neg h1, if_pos h2]
    omega
  by_cases h3 : x <= 8 * k - 4
  · simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
    omega
  · simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
    omega

/-- The displayed inverse recovers every high row. -/
theorem r136_unhost_host {k x : Nat} (hk : 2 <= k)
    (hx : r136HighRow k x) :
    r136Unhost k (r136Host k x) = x := by
  rcases hx with ⟨hx0, hx1⟩
  change 6 * k - 1 <= x at hx0
  change x < 10 * k at hx1
  by_cases h0 : x = 6 * k - 1
  · have hh : r136Host k x = 6 * k - 2 := by
      simp only [r136Host, if_pos h0]
    rw [hh]
    unfold r136Unhost
    rw [if_pos (by rfl)]
    omega
  by_cases h1 : x = 10 * k - 2
  · have hh : r136Host k x = 2 := by
      simp only [r136Host, if_neg h0, if_pos h1]
    have he0 : (2 : Nat) ≠ 6 * k - 2 := by omega
    rw [hh]
    unfold r136Unhost
    rw [if_neg he0, if_pos (by rfl)]
    omega
  by_cases h2 : x = 10 * k - 1
  · have hh : r136Host k x = 0 := by
      simp only [r136Host, if_neg h0, if_neg h1, if_pos h2]
    have he0 : (0 : Nat) ≠ 6 * k - 2 := by omega
    have he2 : (0 : Nat) ≠ 2 := by omega
    rw [hh]
    unfold r136Unhost
    rw [if_neg he0, if_neg he2, if_pos (by rfl)]
    omega
  by_cases h3 : x <= 8 * k - 4
  · have he0 : x - 2 * k + 1 ≠ 6 * k - 2 := by omega
    have he2 : x - 2 * k + 1 ≠ 2 := by omega
    have hez : x - 2 * k + 1 ≠ 0 := by omega
    have hele : x - 2 * k + 1 <= 6 * k - 3 := by omega
    have hh : r136Host k x = x - 2 * k + 1 := by
      simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
    rw [hh]
    unfold r136Unhost
    rw [if_neg he0, if_neg he2, if_neg hez, if_pos hele]
    omega
  · have he0 : x - 2 * k + 2 ≠ 6 * k - 2 := by omega
    have he2 : x - 2 * k + 2 ≠ 2 := by omega
    have hez : x - 2 * k + 2 ≠ 0 := by omega
    have hele : Not (x - 2 * k + 2 <= 6 * k - 3) := by omega
    have hh : r136Host k x = x - 2 * k + 2 := by
      simp only [r136Host, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
    rw [hh]
    unfold r136Unhost
    rw [if_neg he0, if_neg he2, if_neg hez, if_neg hele]
    omega

/-- The assignment has the row/column uniqueness required by the R02 BIJ. -/
theorem r136_host_injective {k x y : Nat} (hk : 2 <= k)
    (hx : r136HighRow k x) (hy : r136HighRow k y)
    (hxy : r136Host k x = r136Host k y) :
    x = y := by
  have h := congrArg (r136Unhost k) hxy
  rw [r136_unhost_host hk hx, r136_unhost_host hk hy] at h
  exact h

/-- NEWBORN: the first high row is hosted in its penultimate column. -/
theorem r136_newborn_host (k : Nat) (hk : 1 <= k) :
    r136Host k (r136Birth k) = r136Birth k - 1 := by
  simp [r136Host, r136Birth]
  omega

/-- The two universal floor hosts from D-infinity are also present. -/
theorem r136_floor_hosts (k : Nat) (hk : 2 <= k) :
    r136Host k (r136V k - 2) = 2 /\
      r136Host k (r136V k - 1) = 0 := by
  constructor
  · change r136Host k (10 * k - 2) = 2
    have h0 : 10 * k - 2 ≠ 6 * k - 1 := by omega
    unfold r136Host
    rw [if_neg h0, if_pos (by rfl)]
  · change r136Host k (10 * k - 1) = 0
    have h0 : 10 * k - 1 ≠ 6 * k - 1 := by omega
    have h1 : 10 * k - 1 ≠ 10 * k - 2 := by omega
    unfold r136Host
    rw [if_neg h0, if_neg h1, if_pos (by rfl)]

/-- Every row strictly between the freeze column and the blocker belongs to
`H(v)`, matching HostCensusRigidity/Theorem A. -/
theorem r136_gap_rows_are_high {k x : Nat} (hk : 1 <= k)
    (hcx : r136C k < x) (hxv : x < r136V k) :
    r136HighRow k x := by
  simp [r136HighRow, r136Birth, r136C, r136V] at *
  omega

/-- The whole upper-rail failure segment is loaded.  Its witnesses are
in-gap rows, so the segment can be paid entirely by the already mandatory
HostCensusRigidity rows. -/
theorem r136_consecutive_segment_loaded {k e : Nat} (hk : 2 <= k)
    (hlo : r136G k + 1 <= e) (hhi : e < r136C k) :
    r136Loaded k e := by
  let x := e + 2 * k - 2
  have hlo' : 7 * k + 1 <= e := by
    simpa [r136G] using hlo
  have hhi' : e < 8 * k := by
    simpa [r136C] using hhi
  refine ⟨x, ?_, ?_⟩
  · constructor
    · simp [x, r136Birth]
      omega
    · simp [x, r136V]
      omega
  · simp only [x, r136Host]
    have h0 : e + 2 * k - 2 ≠ 6 * k - 1 := by omega
    have h1 : e + 2 * k - 2 ≠ 10 * k - 2 := by omega
    have h2 : e + 2 * k - 2 ≠ 10 * k - 1 := by omega
    have h3 : Not (e + 2 * k - 2 <= 8 * k - 4) := by
      omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3]
    omega

/-- The witnesses selected for the consecutive segment really lie after
the freeze row-coordinate and before `v`; thus no deep-host census is forced
by the segment. -/
theorem r136_segment_witness_is_ingap {k e : Nat} (hk : 2 <= k)
    (hlo : r136G k + 1 <= e) (hhi : e < r136C k) :
    r136C k < e + 2 * k - 2 /\ e + 2 * k - 2 < r136V k := by
  simp [r136G, r136C, r136V] at *
  omega

/-- The freeze column itself is not loaded. -/
theorem r136_freeze_not_loaded (k : Nat) (hk : 2 <= k) :
    Not (r136Loaded k (r136C k)) := by
  rintro ⟨x, hx, hxe⟩
  have hlt := r136_host_lt_freeze hk hx
  omega

#print axioms r136_midpoint_exact
#print axioms r136_freeze_ledger
#print axioms r136_high_row_count
#print axioms r136_host_injective
#print axioms r136_consecutive_segment_loaded
#print axioms r136_segment_witness_is_ingap
#print axioms r136_freeze_not_loaded

end ChompLean
