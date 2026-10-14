import R159LiveTerminalPredecessorLag3Reduction
import R137ParkedSuffixSourceCounterframe

set_option autoImplicit false

namespace ChompLean

/-!
# Source-interface separation for the live terminal atom

The R137 source frame already shows that the exact target word and the
standard encoding-order interfaces do not imply
`LiveTerminalPredecessorLag3`.  Its terminal predecessor column is live,
yet its target host can be arbitrarily old.  The frame is intentionally not
a Brouwer recurrence table, so this identifies the missing content as
cross-row MEX chronology rather than source membership alone.
-/

def ColumnLiveBelowFor
    (f : Nat -> Nat -> Nat) (v c : Nat) : Prop :=
  forall z, c < z -> z < v -> f z c ≠ z

/-- The terminal column of the R137 source frame has no lower row-start
fixed point below its target. -/
theorem r137_terminal_column_is_live
    {k : Nat} (hk : 2 <= k) :
    ColumnLiveBelowFor (r137SourceFrame k)
      (r136V k) (r136C k - 1) := by
  intro z hcz hzv hfreeze
  by_cases htarget :
      r137SourceFrame k z (r136C k - 1) = r136V k
  · rw [hfreeze] at htarget
    omega
  · have hodd := r137_sourceFrame_non_target_is_odd
      (k := k) (a := z) (b := r136C k - 1) (by omega) htarget
    rw [hfreeze] at hodd
    simp [r136C, r136V] at hcz hzv hodd
    omega

/-- Concrete live terminal geometry with a depth-eight host, an exact
lag-three preview elsewhere, and the genuine terminal source word.  The
host is not the lag-three host. -/
theorem r137_k4_live_terminal_lag3_countergeometry :
    let f := r137SourceFrame 4
    let v := r136V 4
    let r := r136C 4
    let c := r - 1
    let a := r
    r < v /\
      f v r = v /\
      2 < c /\
      r <= a /\
      a < v /\
      f a c = v /\
      ColumnLiveBelowFor f v c /\
      a + 3 ≠ v /\
      f (v - 3) (r136G 4) = v /\
      (B f v c v /\ Not (B f v r v) /\ B f v (r + 1) v) := by
  dsimp only
  have hword := r137_terminal_source_word (k := 4) (by omega)
  refine ⟨by simp [r136C, r136V], r137_freeze_value 4 (by omega),
    by simp [r136C], by omega, by simp [r136C, r136V], ?_,
    r137_terminal_column_is_live (k := 4) (by omega),
    by simp [r136C, r136V], r137_preview_value 4 (by omega),
    hword.2.1, hword.2.2.1, ?_⟩
  · exact r137_lane_value (k := 4) (e := r136C 4 - 1)
      (by simp [r136G, r136C]) (by simp [r136C])
  · simpa using hword.2.2.2.1

/-- The same separation has unbounded host age `2k`; all target-source and
live-column facts survive for every `k>=2`. -/
theorem r137_live_terminal_host_age_unbounded
    {k : Nat} (hk : 2 <= k) :
    let f := r137SourceFrame k
    let v := r136V k
    let r := r136C k
    let c := r - 1
    let a := r
    f v r = v /\
      f a c = v /\
      ColumnLiveBelowFor f v c /\
      v - a = 2 * k /\
      ParkedOnly f v c v /\
      B f v c v /\
      Not (B f v r v) := by
  dsimp only
  have hword := r137_terminal_source_word (k := k) hk
  have hCpos : 0 < r136C k := by simp [r136C]; omega
  refine ⟨r137_freeze_value k (by omega), ?_,
    r137_terminal_column_is_live hk, (by simp [r136V, r136C]; omega),
    hword.1, hword.2.1, hword.2.2.1⟩
  have hlane := r137_lane_value (k := k) (e := r136C k - 1)
    (by simp [r136G, r136C]; omega) (by simp [r136C]; omega)
  simpa [Nat.sub_add_cancel hCpos] using hlane

#print axioms r137_terminal_column_is_live
#print axioms r137_k4_live_terminal_lag3_countergeometry
#print axioms r137_live_terminal_host_age_unbounded

end ChompLean
