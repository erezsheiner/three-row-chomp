import R136UpperRailLoadedInterval
import R136LoadedSegmentBankCounterframe

set_option autoImplicit false

namespace ChompLean

/-!
R136 scalar audit for the preview-row high run.

The first theorem is an actual-game consequence of `opening_cover`.  It
records the chronology which is easy to lose when one merely labels a high
output RANGE or BLOCKER.

The second part is an arithmetic/interface counterframe.  It is not claimed
to be a second Chomp recurrence.  It shows that row injectivity, the full
J1--J9 cell ceiling, E9, Floor+, opening classification, NoTriple, and even
nested exact-MEX sources permit preview segments of unbounded length.
-/

/-! ## Actual-game opening classification -/

/-- A strict high off-diagonal cell has exactly three opening chronologies.

* a past diagonal owner must lie strictly to the right of the cell, since an
  owner at or to its left would already occur in the cell's MEX source;
* a diagonal owner may instead be genuinely future;
* a row-start owner freezes strictly to the right of the observed host, by
  R30's exact host/freeze order.
-/
theorem gameF_high_cell_opening_trichotomy
    {q e w : Nat}
    (heq : e < q)
    (hvalue : gameF q e = w)
    (hqw : q < w) :
    (exists a, e < a /\ a < q /\ gameF a a = w) \/
      (exists a, q < a /\ a < w /\ gameF a a = w) \/
      (exists c, e < c /\ c < w /\ gameF w c = w) := by
  have hwpos : 0 < w := by omega
  have hnotCarry : Not (e < q /\ gameF (q - 1) e < q) := by
    rintro ⟨heq', hlow⟩
    have hcarry := gameF_brouwerRecurrence.1 heq' hlow
    rw [hvalue] at hcarry
    omega
  have hmex0 := gameF_brouwerRecurrence.2
    (Nat.le_of_lt heq) hnotCarry
  have hmex : IsMex (B gameF q e) w := by
    rw [hvalue] at hmex0
    exact hmex0
  rcases gameRecurrenceModel.opening_cover hwpos with
      ⟨a, haw, hdiag⟩ | ⟨c, hcw, hstart⟩
  · by_cases haq : a < q
    · left
      refine ⟨a, ?_, haq, hdiag⟩
      apply Nat.lt_of_not_ge
      intro hae
      apply hmex.2.1
      left
      refine ⟨a, haq, ?_⟩
      have hmin : min a e = a := Nat.min_eq_left hae
      simpa [hmin] using hdiag
    · by_cases haqeq : a = q
      · subst a
        have heqq : e = q :=
          gameRecurrenceModel.fixed_q_injective
            (Nat.le_of_lt heq) (Nat.le_refl q)
            (hvalue.trans hdiag.symm)
        omega
      · right
        left
        exact ⟨a, by omega, haw, hdiag⟩
  · right
    right
    rcases rowstart_host_order_exact gameRecurrenceModel
        hcw hstart heq (Nat.le_of_lt hqw) hvalue with
        ⟨_qw, hec⟩ | ⟨hEq, _⟩
    · exact ⟨c, hec, hcw, hstart⟩
    · omega

/-! ## Unbounded nested all-RANGE counterframe -/

def r136PreviewQ (k : Nat) : Nat := 10 * k - 3
def r136PreviewE (k i : Nat) : Nat := 7 * k + i
def r136PreviewOwner (k i : Nat) : Nat := 8 * k + i + 5
def r136PreviewW (k i : Nat) : Nat := 16 * k + i
def r136PreviewDiagonal (k : Nat) : Nat := 20 * k - 15

/-- The synthetic exact-MEX source for the `i`th preview cell. -/
def r136PreviewSource (k i p : Nat) : Prop :=
  0 < p /\ p < r136PreviewW k i

/-- RANGE openings in the counterframe are precisely the displayed owner
rows and values. -/
def r136PreviewRangeOpening (k a w : Nat) : Prop :=
  exists i, 1 <= i /\ i < k /\
    a = r136PreviewOwner k i /\ w = r136PreviewW k i

/-- We may classify every displayed output as RANGE; the BLOCKER class is
empty on this packet. -/
def r136PreviewIsRange (k w : Nat) : Prop :=
  exists a, a < w /\ r136PreviewRangeOpening k a w

def r136PreviewIsBlocker (_k _w : Nat) : Prop := False

/-- The indices `1,...,k-1` are exactly the upper-rail failure segment
`[g+1,r)`, with `g=7k` and `r=8k`. -/
theorem r136_preview_index_is_segment
    {k i : Nat} (hi0 : 1 <= i) (hik : i < k) :
    r136G k + 1 <= r136PreviewE k i /\
      r136PreviewE k i < r136C k := by
  simp [r136G, r136C, r136PreviewE]
  omega

/-- The packet length is `k-1`, and hence is unbounded. -/
theorem r136_preview_segment_length (k : Nat) (hk : 2 <= k) :
    r136C k - (r136G k + 1) = k - 1 :=
  r136_segment_length k hk

/-- Every displayed output has a genuine past RANGE owner strictly between
its cell column and the preview row. -/
theorem r136_preview_owner_chronology
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    r136PreviewE k i < r136PreviewOwner k i /\
      r136PreviewOwner k i < r136PreviewQ k /\
      r136PreviewOwner k i < r136PreviewW k i := by
  simp [r136PreviewE, r136PreviewOwner, r136PreviewQ, r136PreviewW]
  omega

/-- Strict highness and the E9 row-maximum ceiling leave ample room for the
entire packet. -/
theorem r136_preview_high_below_row_max
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    r136V k < r136PreviewW k i /\
      r136PreviewW k i < r136PreviewDiagonal k /\
      r136PreviewDiagonal k = 2 * r136PreviewQ k - 9 := by
  simp [r136V, r136PreviewW, r136PreviewDiagonal, r136PreviewQ]
  omega

/-- The full J1--J9 pointwise ceiling is satisfied, not just the coarse cell
capacity bound. -/
theorem r136_preview_J9_cell_ceiling
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    r136PreviewW k i <=
      r136PreviewQ k + r136PreviewE k i - 9 := by
  simp [r136PreviewW, r136PreviewQ, r136PreviewE]
  omega

/-- Floor+ holds at every RANGE owner. -/
theorem r136_preview_owner_floor_plus
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    3 * r136PreviewOwner k i + 5 <=
      2 * r136PreviewW k i := by
  simp [r136PreviewOwner, r136PreviewW]
  omega

/-- E9 holds at every displayed RANGE owner. -/
theorem r136_preview_owner_E9
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    r136PreviewW k i <= 2 * r136PreviewOwner k i - 9 := by
  simp [r136PreviewW, r136PreviewOwner]
  omega

/-- The elementary value/owner slack is constant across the packet.  This
is deliberately not called the global numerical RANGE rank: diagonal
owners need not enumerate RANGE values monotonically. -/
theorem r136_preview_constant_owner_slack
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    r136PreviewW k i - r136PreviewOwner k i - 1 = 8 * k - 6 := by
  simp [r136PreviewW, r136PreviewOwner]
  omega

/-- Consecutive columns produce consecutive, and therefore distinct,
outputs. -/
theorem r136_preview_successor_output
    (k i : Nat) :
    r136PreviewW k (i + 1) = r136PreviewW k i + 1 := by
  unfold r136PreviewW
  omega

theorem r136_preview_output_injective
    {k i j : Nat}
    (hij : r136PreviewW k i = r136PreviewW k j) : i = j := by
  simp [r136PreviewW] at hij
  omega

theorem r136_preview_owner_injective
    {k i j : Nat}
    (hij : r136PreviewOwner k i = r136PreviewOwner k j) : i = j := by
  simp [r136PreviewOwner] at hij
  omega

/-- Every packet value has its advertised opening-cover RANGE witness. -/
theorem r136_preview_all_range
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    r136PreviewIsRange k (r136PreviewW k i) := by
  refine ⟨r136PreviewOwner k i, ?_, i, hi0, hik, rfl, rfl⟩
  exact (r136_preview_owner_chronology hk hi0 hik).2.2

/-- NoTriple is vacuous on this all-RANGE packet. -/
theorem r136_preview_noTriple_blockers (k z : Nat) :
    Not (r136PreviewIsBlocker k z /\
      r136PreviewIsBlocker k (z + 1) /\
      r136PreviewIsBlocker k (z + 2)) := by
  simp [r136PreviewIsBlocker]

/-- The synthetic source has the displayed value as its exact positive MEX. -/
theorem r136_preview_source_exact_mex
    {k i : Nat} (hk : 12 <= k) (hi0 : 1 <= i) (hik : i < k) :
    IsMex (r136PreviewSource k i) (r136PreviewW k i) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [r136PreviewW]
    omega
  · simp [r136PreviewSource]
  · intro p hp0 hpw
    exact ⟨hp0, hpw⟩

/-- Adjacent sources are perfectly nested: the next source adds exactly the
previous MEX and loses nothing.  Thus a source-loss count cannot charge this
packet either. -/
theorem r136_preview_source_successor_nesting
    (k i p : Nat) (hk : 1 <= k) :
    r136PreviewSource k (i + 1) p <->
      r136PreviewSource k i p \/ p = r136PreviewW k i := by
  simp only [r136PreviewSource, r136_preview_successor_output]
  constructor
  · rintro ⟨hp0, hp⟩
    by_cases hlt : p < r136PreviewW k i
    · exact Or.inl ⟨hp0, hlt⟩
    · exact Or.inr (by omega)
  · rintro (⟨hp0, hp⟩ | rfl)
    · exact ⟨hp0, by omega⟩
    · constructor
      · unfold r136PreviewW
        omega
      · omega

#print axioms gameF_high_cell_opening_trichotomy
#print axioms r136_preview_J9_cell_ceiling
#print axioms r136_preview_owner_floor_plus
#print axioms r136_preview_owner_E9
#print axioms r136_preview_all_range
#print axioms r136_preview_source_exact_mex
#print axioms r136_preview_source_successor_nesting

end ChompLean
