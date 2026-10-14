import R125AssignmentStripBridge
import R54WideBoundaryChronologyExclusion

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
The theorem-grade reduction behind the assignment max-plus experiment.

`LowerOwnerCoveredBy v s` says that every positive value below the blocker
`v` has its actual opening owner at a column at most `s`: a diagonal owner
for a range value, or a row-start freeze for a blocker.  The second input to
the main theorem is the one remaining cleanliness bit: the target `v` has
not already appeared in the old history of the candidate column `s+1`.

Neither input is asserted here for the actual max-plus frontier.  In
particular, the row-start half of `LowerOwnerCoveredBy` contains the global
freeze-order debt and must not be inferred from finite data.
-/

def LowerOwnerCoveredBy (v s : Nat) : Prop :=
  forall k, 0 < k -> k < v ->
    (exists a, a <= s /\ gameF a a = k) \/
    (exists r, r <= s /\ r < k /\ gameF k r = k)

/-- A low actual-game cell is already on the constant row-start branch at
its own value row.  This is the exact fact needed to show that a candidate
column beyond every lower row-start owner cannot be a carry cell. -/
theorem gameF_low_cell_has_rowstart
    {q c : Nat} (hcq : c <= q) (hlow : gameF q c <= q) :
    c < gameF q c /\ gameF (gameF q c) c = gameF q c := by
  have hcvalue : c < gameF q c := encoded_gt game_encodes hcq
  refine ⟨hcvalue, ?_⟩
  by_cases heq : gameF q c = q
  · simpa [heq] using heq.symm
  · have hlt : gameF q c < q := by omega
    have hP := encoded_isP_of_lt game_encodes hcq hlt
    have hP' :
        IsP (mkPos (gameF q c) (gameF q c) c
          (Nat.le_refl (gameF q c)) (Nat.le_of_lt hcvalue)) := by
      simpa [rowStartPos] using hP
    exact game_complete.2 (Nat.le_refl (gameF q c))
      (Nat.le_of_lt hcvalue) hP'

/-- Separate diagonal/freeze bounds imply the combined lower-owner
certificate.  `opening_cover` supplies the exhaustive range/blocker split;
the two hypotheses only localize the corresponding owner columns. -/
theorem lowerOwnerCoveredBy_of_owner_bounds
    {v s : Nat}
    (hdiag : forall {k a}, 0 < k -> k < v -> a < k ->
      gameF a a = k -> a <= s)
    (hfreeze : forall {k r}, 0 < k -> k < v -> r < k ->
      gameF k r = k -> r <= s) :
    LowerOwnerCoveredBy v s := by
  intro k hkpos hkv
  rcases gameRecurrenceModel.opening_cover hkpos with
      ⟨a, hak, hdiagOwner⟩ | ⟨r, hrk, hfreezeOwner⟩
  · exact Or.inl ⟨a, hdiag hkpos hkv hak hdiagOwner, hdiagOwner⟩
  · exact Or.inr
      ⟨r, hfreeze hkpos hkv hrk hfreezeOwner, hrk, hfreezeOwner⟩

/-- Owner coverage alone transports every lower value into the literal
source at the frontier successor.  Diagonal owners enter `R`; row-start
owners persist to row `v` and enter the current-row prefix `C`. -/
theorem lowerOwnerCoveredBy_source_saturation
    {v s : Nat} (hsv : s < v) (howners : LowerOwnerCoveredBy v s) :
    forall k, 0 < k -> k < v -> B gameF v (s + 1) k := by
  intro k hkpos hkv
  rcases howners k hkpos hkv with
      ⟨a, has, hdiag⟩ | ⟨r, hrs, hrk, hstart⟩
  · left
    refine ⟨a, by omega, ?_⟩
    have hmin : min a (s + 1) = a := Nat.min_eq_left (by omega)
    simpa [hmin] using hdiag
  · right
    refine ⟨r, by omega, ?_⟩
    have hsmall : gameRecurrenceModel.f k r < k + 1 := by
      change gameF k r < k + 1
      rw [hstart]
      omega
    have hpersist := constant_from gameRecurrenceModel hrk
      hsmall (v - k)
    have hsum : k + (v - k) = v := by omega
    change gameF (k + (v - k)) r = gameF k r at hpersist
    rw [hsum, hstart] at hpersist
    exact hpersist

/-- Exact NoAssignmentGap reduction.  Suppose `v` really freezes at `r`.
If the proposed frontier `s` lies before `r`, covers all lower owners, and
the candidate column `s+1` has no old occurrence of `v`, then that candidate
is a live MEX cell with value `v`; row injectivity forces `r=s+1`.

The proof derives non-carry internally: a low predecessor at `s+1` would,
by `gameF_low_cell_has_rowstart`, be a lower row start owned strictly beyond
the certified frontier. -/
theorem gameF_freeze_eq_frontier_succ
    {v r s : Nat}
    (hvpos : 0 < v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hsr : s < r)
    (howners : LowerOwnerCoveredBy v s)
    (hclean : Not (ColHistPred gameF v (s + 1) v)) :
    r = s + 1 := by
  let c := s + 1
  have hcv : c <= v := by dsimp [c]; omega
  have hcr : c <= r := by dsimp [c]; omega

  have hnotCarry : Not (c < v /\ gameF (v - 1) c < v) := by
    rintro ⟨hcvlt, hprevLow⟩
    have hcprev : c <= v - 1 := by omega
    have hrow := gameF_low_cell_has_rowstart hcprev (by omega)
    let k := gameF (v - 1) c
    have hkpos : 0 < k := by dsimp [k]; omega
    have hkv : k < v := by exact hprevLow
    rcases howners k hkpos hkv with
        ⟨a, _has, hdiag⟩ | ⟨r', hr's, hr'k, hstart'⟩
    · exact disjoint_D_S gameRecurrenceModel
        ⟨a, hdiag⟩ ⟨c, hrow.1, hrow.2⟩
    · have hcc' : c = r' :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hrow.1) (Nat.le_of_lt hr'k)
          (hrow.2.trans hstart'.symm)
      dsimp [c] at hcc'
      omega

  have habsent : Not (B gameF v c v) := by
    intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, hav, hvalue⟩
      by_cases hac : a < c
      · have hmin : min a c = a := Nat.min_eq_left (Nat.le_of_lt hac)
        have hdiag : gameF a a = v := by simpa [hmin] using hvalue
        exact disjoint_D_S gameRecurrenceModel
          ⟨a, hdiag⟩ ⟨r, hrv, hstart⟩
      · have hca : c <= a := Nat.le_of_not_gt hac
        have hmin : min a c = c := Nat.min_eq_right hca
        apply hclean
        exact ⟨a, hca, hav, by simpa [hmin] using hvalue⟩
    · rcases hC with ⟨b, hbc, hvalue⟩
      have hbr : b = r :=
        gameRecurrenceModel.fixed_q_injective
          (by omega) (Nat.le_of_lt hrv) (hvalue.trans hstart.symm)
      omega

  have hlower : forall k, 0 < k -> k < v -> B gameF v c k := by
    simpa [c] using lowerOwnerCoveredBy_source_saturation
      (by omega : s < v) howners

  have hcandidate : gameF v c = v :=
    gameF_value_of_source_mex hcv hnotCarry hvpos habsent hlower

  have hcol : c = r :=
    gameRecurrenceModel.fixed_q_injective hcv (Nat.le_of_lt hrv)
      (hcandidate.trans hstart.symm)
  exact hcol.symm

/-- Max-plus-facing specialization.  The easy strict inequalities put the
two observed inputs before the true freeze.  All remaining game content is
now exactly `LowerOwnerCoveredBy` plus one clean-history bit. -/
theorem gameF_freeze_eq_preview_maxPlus
    {v r previousFreeze previewHost : Nat}
    (hvpos : 0 < v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hprevious : previousFreeze < r)
    (hpreview : previewHost < r)
    (howners :
      LowerOwnerCoveredBy v (max previousFreeze previewHost))
    (hclean : Not (ColHistPred gameF v
      (max previousFreeze previewHost + 1) v)) :
    r = max previousFreeze previewHost + 1 := by
  apply gameF_freeze_eq_frontier_succ hvpos hrv hstart
  · omega
  · exact howners
  · exact hclean

/-- Causal-depth-three turns cleanliness at the final selector row into one
old-history exclusion plus exclusion of the single preview-row cell. -/
theorem gameF_candidate_clean_of_causal_depth_three
    {q c : Nat}
    (hq : 1 <= q)
    (hc : 2 < c)
    (hold : Not (ColHistPred gameF q c (q + 3)))
    (hpreview : gameF q c ≠ q + 3) :
    Not (ColHistPred gameF (q + 3) c (q + 3)) := by
  intro hfull
  rcases (gameF_colHist_causal_depth_three hq hc).mp hfull with
      hOld | hNew
  · exact hold hOld
  · exact hpreview hNew.2

/-- If the preview host is known, fixed-row injectivity deletes the new-row
arm at every distinct candidate column.  This leaves precisely the old
`ColHist` atom at cutoff `v-3`. -/
theorem gameF_candidate_clean_of_old_history_and_distinct_preview
    {q previewHost c : Nat}
    (hq : 1 <= q)
    (hpreviewLe : previewHost <= q)
    (hc : 2 < c)
    (hhost : gameF q previewHost = q + 3)
    (hne : c ≠ previewHost)
    (hold : Not (ColHistPred gameF q c (q + 3))) :
    Not (ColHistPred gameF (q + 3) c (q + 3)) := by
  intro hfull
  rcases (gameF_colHist_causal_depth_three hq hc).mp hfull with
      hOld | hNew
  · exact hold hOld
  · have hcol : c = previewHost :=
      gameRecurrenceModel.fixed_q_injective hNew.1 hpreviewLe
        (hNew.2.trans hhost.symm)
    exact hne hcol

#print axioms gameF_low_cell_has_rowstart
#print axioms lowerOwnerCoveredBy_source_saturation
#print axioms gameF_freeze_eq_frontier_succ
#print axioms gameF_freeze_eq_preview_maxPlus
#print axioms gameF_candidate_clean_of_causal_depth_three
#print axioms gameF_candidate_clean_of_old_history_and_distinct_preview

end ChompLean
