import R144NoCriticalFinalHoleLateFreeze
import R56TopTwoHoles

set_option autoImplicit false

namespace ChompLean

/-!
R147: exact backward-graft audit for the R144 XOR-rook packet.

There are two literal failures.  First, the proposed rank-minus-one freeze
schedule puts the final blocker three columns before the exact V1 deadline.
Second, after repairing that endpoint, the first XOR value `v+1` is already
present in the source as the next diagonal seed.

Neither failure proves the desired cap.  A diagonal-seeded additive packet
has an exact MEX realization at every depth.  Its source consists of the
diagonal/blocker base interval, earlier rows in the same column, and earlier
columns in the current row.
-/

def r147LateFreeze (k j : Nat) : Nat := 2 * k + 2 * j
def r147C0 (k : Nat) : Nat := 7 * k
def r147R0 (k : Nat) : Nat := FrameV k - 4

theorem r147_proposed_final_freeze_is_three_early (k : Nat) :
    r147LateFreeze k (2 * k) + 3 = FrameT k := by
  simp [r147LateFreeze, FrameT]
  omega

/-- The exact first obstruction to the proposed saturated-prefix graft.
The final blocker is the V1 hole at row `t`; every genuine row-start freeze
of it is at or to the right of `t`, while the proposal puts it at `t-3`. -/
theorem r147_final_hole_rejects_proposed_freeze
    (k : Nat) (hk : 1 <= k)
    (hstart :
      gameF (FrameQ k) (r147LateFreeze k (2 * k)) = FrameQ k)
    (hV1 : IsMex
      (B gameF (FrameT k) (FrameT k - 1)) (FrameQ k)) :
    False := by
  have hlate := future_v1_hole_forces_late_freeze gameRecurrenceModel
    (t := FrameT k) (q := FrameQ k)
    (r := r147LateFreeze k (2 * k))
    (by simp [FrameT])
    (by simp [FrameT, FrameQ]; omega)
    (by simp [r147LateFreeze, FrameQ]; omega)
    hstart hV1
  have hearly := r147_proposed_final_freeze_is_three_early k
  omega

/-- A diagonal seed at an owner to the left of a later cutoff belongs to
the later cell's literal Brouwer source. -/
theorem r147_diagonal_seed_in_later_source
    (M : RecurrenceModel) {a r c x : Nat}
    (har : a < r) (hac : a <= c) (hdiag : M.f a a = x) :
    B M.f r c x := by
  left
  refine ⟨a, har, ?_⟩
  simpa [Nat.min_eq_left hac] using hdiag

/-- Hence a live MEX cell cannot emit that seeded value. -/
theorem r147_diagonal_seed_forbids_later_mex
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f)
    {a r c x : Nat}
    (har : a < r) (hac : a <= c) (hcr : c < r) (hrx : r < x)
    (hdiag : M.f a a = x) :
    M.f r c ≠ x := by
  intro hout
  have hB := r147_diagonal_seed_in_later_source M har hac hdiag
  have habs : Not (B M.f r c (M.f r c)) :=
    recurrence_mex_absent hrec (Nat.le_of_lt hcr)
      (by simpa [hout] using hrx)
  exact habs (by simpa [hout] using hB)

/-- In the monotone `A_k` range enumeration the next value after the bad
diagonal is `v+1`.  It already lies in the first target source, so the
literal XOR start `F(v-4,7k)=v+1` is impossible. -/
theorem r147_Ak_next_diagonal_seed_kills_xor_start
    (k : Nat) (hk : 4 <= k)
    (hnext :
      gameF (FrameT k + 1) (FrameT k + 1) = FrameV k + 1) :
    gameF (r147R0 k) (r147C0 k) ≠ FrameV k + 1 := by
  apply r147_diagonal_seed_forbids_later_mex
    gameRecurrenceModel gameF_brouwerRecurrence
    (a := FrameT k + 1) (r := r147R0 k)
    (c := r147C0 k) (x := FrameV k + 1)
  · simp [FrameT, FrameV, r147R0]
    omega
  · simp [FrameT, r147C0]
    omega
  · simp [FrameV, r147R0, r147C0]
    omega
  · simp [FrameV, r147R0]
    omega
  · exact hnext

/-! ## The surviving diagonal-seeded additive packet -/

/-- Values already supplied before a target cell: the complete seeded base
through `M+j`, all earlier target rows in column `j`, and all earlier target
columns in row `n`. -/
def R147AddSource (M n j z : Nat) : Prop :=
  (0 < z /\ z <= M + j) \/
  (exists i, i < n /\ z = M + i + j + 1) \/
  (exists e, e < j /\ z = M + n + e + 1)

def r147AddValue (M n j : Nat) : Nat := M + n + j + 1

/-- Exact all-depth MEX identity for the additive replacement of XOR. -/
theorem r147_additive_exact_mex (M n j : Nat) :
    IsMex (R147AddSource M n j) (r147AddValue M n j) := by
  refine ⟨by simp [r147AddValue], ?_, ?_⟩
  · intro hs
    rcases hs with hbase | hvertical | hprefix
    · simp [r147AddValue] at hbase
      omega
    · rcases hvertical with ⟨i, hin, hi⟩
      simp [r147AddValue] at hi
      omega
    · rcases hprefix with ⟨e, hej, he⟩
      simp [r147AddValue] at he
      omega
  · intro z hz hzx
    by_cases hbase : z <= M + j
    · exact Or.inl ⟨hz, hbase⟩
    · right; left
      let i := z - (M + j + 1)
      refine ⟨i, ?_, ?_⟩
      · dsimp [i]
        simp [r147AddValue] at hzx
        omega
      · dsimp [i]
        omega

theorem r147_additive_row_injective (M n : Nat) :
    Function.Injective (fun j => r147AddValue M n j) := by
  intro i j hij
  simp [r147AddValue] at hij
  omega

theorem r147_additive_column_injective (M j : Nat) :
    Function.Injective (fun n => r147AddValue M n j) := by
  intro i n hin
  simp [r147AddValue] at hin
  omega

def r147SeedM (k : Nat) : Nat := 11 * k + 1
def r147AddOwner (k n j : Nat) : Nat := r147C0 k + n + j + 1

/-- If the range diagonal continues consecutively after the critical value,
the additive output is owned at this index.  For the three target columns
that owner is strictly between the target column and the target row, exactly
the chronology required of a legal past-diagonal echo. -/
theorem r147_additive_echo_geometry
    (k n j : Nat) (hk : 4 <= k) (hj : j <= 2) :
    r147C0 k + j < r147AddOwner k n j /\
    r147AddOwner k n j < r147R0 k + n /\
    r147R0 k + n < r147AddValue (r147SeedM k) n j := by
  simp [r147AddOwner, r147C0, r147R0, FrameV,
    r147AddValue, r147SeedM]
  omega

/-- In the `A_k` coordinates the additive packet stays strictly above the
critical value and satisfies the defect-nine cell ceiling at every depth. -/
theorem r147_additive_frame_bounds
    (k n j : Nat) (hk : 4 <= k) :
    FrameV k < r147AddValue (r147SeedM k) n j /\
    r147AddValue (r147SeedM k) n j <=
      (r147R0 k + n) + (r147C0 k + j) - 9 := by
  simp [FrameV, r147AddValue, r147SeedM, r147R0, r147C0]
  omega

/-- The additive values are high relative to their rows, so the low-value
constant-step premise never fires on the packet. -/
theorem r147_additive_is_noncarry_high
    (k n j : Nat) (hk : 4 <= k) :
    r147R0 k + n < r147AddValue (r147SeedM k) n j := by
  simp [FrameV, r147R0, r147AddValue, r147SeedM]
  omega

#print axioms r147_final_hole_rejects_proposed_freeze
#print axioms r147_Ak_next_diagonal_seed_kills_xor_start
#print axioms r147_additive_exact_mex
#print axioms r147_additive_row_injective
#print axioms r147_additive_column_injective
#print axioms r147_additive_echo_geometry
#print axioms r147_additive_frame_bounds

end ChompLean
