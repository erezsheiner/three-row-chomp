import R136LoadedSegmentBankCounterframe
import R16LanePersistence
import R17HandoffSink

set_option autoImplicit false

namespace ChompLean

/-!
An unbounded source-interface counterframe for the R136 loaded suffix.

This is not claimed to satisfy the Brouwer/MEX recurrence.  It does satisfy
the exact R15 source definitions, realizes the strongest adjacent R16 lane
handoff at every interior edge, and realizes the R17 fresh-sink branch at
the terminal edge.  Hence those interfaces alone cannot contradict an
arbitrarily long `ParkedOnly` suffix.

We reuse `v=10k`, `g=7k`, `r=8k` from the R136 bank frame.  Each loaded
column `e` hosts the target on row `e+1`; the terminal freeze cell is
`(v,r)`.  It also includes the parallel R137 lag-three preview at
`(v-3,g)`.  All other outputs are odd, while the target is even.
-/

def r137LaneCell (k a b : Nat) : Prop :=
  a = b + 1 /\ r136G k + 1 <= b /\ b < r136C k

def r137FreezeCell (k a b : Nat) : Prop :=
  a = r136V k /\ b = r136C k

def r137PreviewCell (k a b : Nat) : Prop :=
  a + 3 = r136V k /\ b = r136G k

noncomputable def r137SourceFrame (k a b : Nat) : Nat :=
  by
    classical
    exact if r137LaneCell k a b then r136V k
      else if r137FreezeCell k a b then r136V k
      else if r137PreviewCell k a b then r136V k
      else 2 * b + 1

/-- Exact target fibre of the frame. -/
theorem r137_sourceFrame_eq_target_iff
    {k a b : Nat} (hk : 1 <= k) :
    r137SourceFrame k a b = r136V k <->
      r137LaneCell k a b \/ r137FreezeCell k a b \/
        r137PreviewCell k a b := by
  by_cases hlane : r137LaneCell k a b
  · simp [r137SourceFrame, hlane]
  by_cases hfreeze : r137FreezeCell k a b
  · simp [r137SourceFrame, hlane, hfreeze]
  by_cases hpreview : r137PreviewCell k a b
  · simp [r137SourceFrame, hlane, hfreeze, hpreview]
  · simp only [r137SourceFrame, if_neg hlane, if_neg hfreeze,
      if_neg hpreview]
    constructor
    · intro hodd
      simp [r136V] at hodd
      omega
    · intro h
      rcases h with h | h | h
      · exact False.elim (hlane h)
      · exact False.elim (hfreeze h)
      · exact False.elim (hpreview h)

/-- The target occurs at most once on any fixed row.  This is the exact
piece of fixed-row injectivity used by the parked-suffix boundary audit. -/
theorem r137_target_fibre_fixed_row_unique
    {k a b c : Nat} (hk : 1 <= k)
    (hb : r137SourceFrame k a b = r136V k)
    (hc : r137SourceFrame k a c = r136V k) :
    b = c := by
  have hb' := (r137_sourceFrame_eq_target_iff hk).mp hb
  have hc' := (r137_sourceFrame_eq_target_iff hk).mp hc
  rcases hb' with hbL | hbF | hbP <;>
    rcases hc' with hcL | hcF | hcP
  all_goals
    simp [r137LaneCell, r137FreezeCell, r137PreviewCell,
      r136V, r136G, r136C] at * <;> omega

theorem r137_sourceFrame_non_target_is_odd
    {k a b : Nat} (hk : 1 <= k)
    (hnot : r137SourceFrame k a b ≠ r136V k) :
    r137SourceFrame k a b = 2 * b + 1 := by
  have hnone : Not (r137LaneCell k a b \/
      r137FreezeCell k a b \/ r137PreviewCell k a b) := by
    intro hcell
    exact hnot ((r137_sourceFrame_eq_target_iff hk).2 hcell)
  have hlane : Not (r137LaneCell k a b) := by
    intro h
    exact hnone (Or.inl h)
  have hfreeze : Not (r137FreezeCell k a b) := by
    intro h
    exact hnone (Or.inr (Or.inl h))
  have hpreview : Not (r137PreviewCell k a b) := by
    intro h
    exact hnone (Or.inr (Or.inr h))
  simp [r137SourceFrame, hlane, hfreeze, hpreview]

/-- Unlike the older bank-only frame, the source frame also satisfies full
fixed-row injectivity: special cells all carry the even target and are
row-unique; every other cell carries the distinct odd code `2b+1`. -/
theorem r137_sourceFrame_fixed_row_injective
    {k a b c : Nat} (hk : 1 <= k)
    (heq : r137SourceFrame k a b = r137SourceFrame k a c) :
    b = c := by
  by_cases hb : r137SourceFrame k a b = r136V k
  · have hc : r137SourceFrame k a c = r136V k :=
      heq.symm.trans hb
    exact r137_target_fibre_fixed_row_unique hk hb hc
  · have hc : r137SourceFrame k a c ≠ r136V k := by
      intro hc
      exact hb (heq.trans hc)
    rw [r137_sourceFrame_non_target_is_odd hk hb,
      r137_sourceFrame_non_target_is_odd hk hc] at heq
    omega

/-- The frame also respects the strict cell-code inequality used throughout
the real encoding interface. -/
theorem r137_sourceFrame_encoded_gt
    {k a b : Nat} (hk : 1 <= k) (_hba : b <= a) :
    b < r137SourceFrame k a b := by
  by_cases htarget : r137SourceFrame k a b = r136V k
  · rw [htarget]
    rcases (r137_sourceFrame_eq_target_iff hk).mp htarget with
        hlane | hfreeze | hpreview
    all_goals
      simp [r137LaneCell, r137FreezeCell, r137PreviewCell,
        r136V, r136G, r136C] at * <;> omega
  · rw [r137_sourceFrame_non_target_is_odd hk htarget]
    omega

theorem r137_sourceFrame_diagonal_value
    {k a : Nat} (hk : 2 <= k) :
    r137SourceFrame k a a = 2 * a + 1 := by
  apply r137_sourceFrame_non_target_is_odd (by omega)
  intro htarget
  rcases (r137_sourceFrame_eq_target_iff (by omega)).mp htarget with
      hlane | hfreeze | hpreview
  · simp [r137LaneCell] at hlane
  · simp [r137FreezeCell, r136V, r136C] at hfreeze
    omega
  · simp [r137PreviewCell, r136V, r136G] at hpreview
    omega

/-- Even strict diagonal maximality leaves the unbounded parked suffix
untouched; the missing ingredient is the MEX/host-path schedule itself. -/
theorem r137_sourceFrame_strict_row_diagonal_maximal
    {k a b : Nat} (hk : 2 <= k) (hba : b < a) :
    r137SourceFrame k a b < r137SourceFrame k a a := by
  rw [r137_sourceFrame_diagonal_value hk]
  by_cases htarget : r137SourceFrame k a b = r136V k
  · rw [htarget]
    rcases (r137_sourceFrame_eq_target_iff (by omega)).mp htarget with
        hlane | hfreeze | hpreview
    all_goals
      simp [r137LaneCell, r137FreezeCell, r137PreviewCell,
        r136V, r136G, r136C] at * <;> omega
  · rw [r137_sourceFrame_non_target_is_odd (by omega) htarget]
    omega

theorem r137_lane_value
    {k e : Nat} (hlo : r136G k + 1 <= e)
    (hhi : e < r136C k) :
    r137SourceFrame k (e + 1) e = r136V k := by
  apply (r137_sourceFrame_eq_target_iff (by
    simp [r136G, r136C] at hlo hhi
    omega)).2
  left
  exact ⟨rfl, hlo, hhi⟩

theorem r137_freeze_value (k : Nat) (hk : 1 <= k) :
    r137SourceFrame k (r136V k) (r136C k) = r136V k := by
  apply (r137_sourceFrame_eq_target_iff hk).2
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- The frame also carries the exact lag-three preview assumed by the
parallel R137 timing reduction, at a column strictly left of the suffix. -/
theorem r137_preview_value (k : Nat) (hk : 1 <= k) :
    r137SourceFrame k (r136V k - 3) (r136G k) = r136V k := by
  apply (r137_sourceFrame_eq_target_iff hk).2
  right
  right
  refine ⟨?_, rfl⟩
  simp [r136V]
  omega

/-- Every column in the whole upper-rail failure interval is genuinely
`ParkedOnly` in the R15 sense. -/
theorem r137_whole_segment_parkedOnly
    {k e : Nat} (hk : 2 <= k)
    (hlo : r136G k + 1 <= e)
    (hhi : e < r136C k) :
    ParkedOnly (r137SourceFrame k) (r136V k) e (r136V k) := by
  have hkv : 1 <= k := by omega
  have hrv : r136C k < r136V k := by
    simp [r136C, r136V]
    omega
  have hcol : ColTail (r137SourceFrame k) (r136V k) e (r136V k) :=
    ⟨e + 1, by omega, by omega, r137_lane_value hlo hhi⟩
  refine ⟨hcol, ?_, ?_⟩
  · rintro ⟨a, hav, hae, hvalue⟩
    rcases (r137_sourceFrame_eq_target_iff hkv).mp hvalue with
        hlane | hfreeze | hpreview
    · simp [r137LaneCell] at hlane
    · simp [r137FreezeCell] at hfreeze
      omega
    · simp [r137PreviewCell, r136V, r136G] at hpreview
      omega
  · rintro ⟨b, hbe, hvalue⟩
    rcases (r137_sourceFrame_eq_target_iff hkv).mp hvalue with
        hlane | hfreeze | hpreview
    · simp [r137LaneCell, r136V, r136C] at hlane
      omega
    · simp [r137FreezeCell] at hfreeze
      omega
    · simp [r137PreviewCell] at hpreview

/-- Every interior edge realizes the strongest R16 adjacent-lane packet,
not merely an unrelated successor-column witness. -/
theorem r137_every_interior_edge_is_adjacent_handoff
    {k e : Nat} (hk : 2 <= k)
    (hlo : r136G k + 1 <= e)
    (hhi : e + 1 < r136C k) :
    r137SourceFrame k (e + 1) e = r136V k /\
      r137SourceFrame k (e + 2) (e + 1) = r136V k /\
      ColTail (r137SourceFrame k) (r136V k) (e + 1) (r136V k) := by
  have hold := r137_lane_value hlo (by omega : e < r136C k)
  have hnext := r137_lane_value (by omega : r136G k + 1 <= e + 1) hhi
  have ht : e + 2 < r136V k := by
    simp [r136C, r136V] at hhi ⊢
    omega
  exact ⟨hold, hnext,
    adjacent_lane_handoff_enters_colTail
      (t := r136V k) (r := e + 1) hold hnext (by omega) ht⟩

/-- The freeze source itself omits the target. -/
theorem r137_target_absent_at_freeze_source
    {k : Nat} (hk : 2 <= k) :
    Not (B (r137SourceFrame k) (r136V k) (r136C k) (r136V k)) := by
  have hkv : 1 <= k := by omega
  intro hB
  rcases hB with hR | hC
  · rcases R_iff_diagPrefix_or_colTail.mp hR with hdiag | hcol
    · rcases hdiag with ⟨a, hav, hac, hvalue⟩
      rcases (r137_sourceFrame_eq_target_iff hkv).mp hvalue with
          hlane | hfreeze | hpreview
      · simp [r137LaneCell] at hlane
      · simp [r137FreezeCell, r136V, r136C] at hfreeze
        omega
      · simp [r137PreviewCell, r136V, r136G] at hpreview
        omega
    · rcases hcol with ⟨a, hav, hca, hvalue⟩
      rcases (r137_sourceFrame_eq_target_iff hkv).mp hvalue with
          hlane | hfreeze | hpreview
      · simp [r137LaneCell] at hlane
      · simp [r137FreezeCell] at hfreeze
        omega
      · simp [r137PreviewCell, r136G, r136C] at hpreview
        omega
  · rcases hC with ⟨b, hbc, hvalue⟩
    rcases (r137_sourceFrame_eq_target_iff hkv).mp hvalue with
        hlane | hfreeze | hpreview
    · simp [r137LaneCell, r136V, r136C] at hlane
      omega
    · simp [r137FreezeCell] at hfreeze
      omega
    · simp [r137PreviewCell] at hpreview

/-- Exact R15/R17 terminal packet: the terminal host is row `r`, the value
is lost at the freeze source, and the freeze output restores it immediately.
-/
theorem r137_terminal_source_word
    {k : Nat} (hk : 2 <= k) :
    ParkedOnly (r137SourceFrame k) (r136V k) (r136C k - 1) (r136V k) /\
      B (r137SourceFrame k) (r136V k) (r136C k - 1) (r136V k) /\
      Not (B (r137SourceFrame k) (r136V k) (r136C k) (r136V k)) /\
      B (r137SourceFrame k) (r136V k) (r136C k + 1) (r136V k) /\
      r137SourceFrame k (r136C k) (r136C k - 1) = r136V k /\
      r137SourceFrame k (r136V k) (r136C k) = r136V k := by
  have hleft : r136G k + 1 <= r136C k - 1 := by
    simp [r136G, r136C]
    omega
  have hright : r136C k - 1 < r136C k := by
    simp [r136C]
    omega
  have hpark := r137_whole_segment_parkedOnly hk hleft hright
  have hfreeze := r137_freeze_value k (by omega)
  have hrestored :
      B (r137SourceFrame k) (r136V k) (r136C k + 1) (r136V k) :=
    fresh_emission_closes_next hfreeze
  have hterminalHost :
      r137SourceFrame k (r136C k) (r136C k - 1) = r136V k := by
    have hs : r136C k - 1 + 1 = r136C k := by
      simp [r136C]
      omega
    simpa [hs] using r137_lane_value hleft hright
  exact ⟨hpark, parkedOnly_mem_current_source hpark,
    r137_target_absent_at_freeze_source hk, hrestored,
    hterminalHost, hfreeze⟩

/-- The permitted parked suffix has unbounded length `k-1`. -/
theorem r137_parked_suffix_unbounded_length
    (k : Nat) (hk : 2 <= k) :
    r136C k - (r136G k + 1) = k - 1 /\
      forall e, r136G k + 1 <= e -> e < r136C k ->
        ParkedOnly (r137SourceFrame k) (r136V k) e (r136V k) := by
  exact ⟨r136_segment_length k hk,
    fun _ hlo hhi => r137_whole_segment_parkedOnly hk hlo hhi⟩

#print axioms r137_sourceFrame_eq_target_iff
#print axioms r137_target_fibre_fixed_row_unique
#print axioms r137_sourceFrame_fixed_row_injective
#print axioms r137_sourceFrame_encoded_gt
#print axioms r137_sourceFrame_strict_row_diagonal_maximal
#print axioms r137_preview_value
#print axioms r137_whole_segment_parkedOnly
#print axioms r137_every_interior_edge_is_adjacent_handoff
#print axioms r137_target_absent_at_freeze_source
#print axioms r137_terminal_source_word
#print axioms r137_parked_suffix_unbounded_length

end ChompLean
