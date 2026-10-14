import R156FixedLag8HostOldReduction

set_option autoImplicit false

namespace ChompLean

/-!
# Terminal target-history depth eight

For a target freeze `gameF v r = v`, the terminal predecessor column is
`r-1`.  The new recurrence atom isolated here says that any old copy of the
target in that column occurs within the last eight rows before `v`.

The statement is deliberately kept as an explicit input: the existing
`ColHistPred` causal-depth-three theorem removes only the newest two rows and
splits off row `v-3`; it gives no lower bound on a witness in its old-history
arm.  The reductions below record exactly what depth eight would buy, without
assuming that empirical observation as a theorem.
-/

/-- Global terminal-history recency atom.  The subtraction-free conclusion
`v <= a+8` is the robust Nat form of `v-8 <= a`. -/
def TerminalTargetHistoryDepth8 : Prop :=
  forall {v r a : Nat},
    r < v ->
    gameF v r = v ->
    r <= a ->
    a < v ->
    gameF a (r - 1) = v ->
    v <= a + 8

/-! ## What the existing history theorem does and does not say -/

/-- Any host below the lag-three preview cutoff enters the unrestricted old
arm of `gameF_colHist_causal_depth_three`, regardless of how old it is. -/
theorem gameF_old_host_is_accepted_by_causal_depth_three
    {q c a : Nat}
    (hq : 1 <= q)
    (hc : 2 < c)
    (hca : c <= a)
    (haq : a < q)
    (hhost : gameF a c = q + 3) :
    ColHistPred gameF q c (q + 3) /\
      ColHistPred gameF (q + 3) c (q + 3) := by
  have hold : ColHistPred gameF q c (q + 3) :=
    ⟨a, hca, haq, hhost⟩
  exact ⟨hold,
    (gameF_colHist_causal_depth_three hq hc).2 (Or.inl hold)⟩

/-- A terminal-predecessor target host is unique.  This is a chronology fact,
not a recency fact: same-lower no-repeat forbids two distinct host rows but
does not bound the age of the one remaining row. -/
theorem gameF_terminal_predecessor_host_unique
    {v r a1 a2 : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hra1 : r <= a1)
    (ha1v : a1 < v)
    (hhost1 : gameF a1 (r - 1) = v)
    (hra2 : r <= a2)
    (ha2v : a2 < v)
    (hhost2 : gameF a2 (r - 1) = v) :
    a1 = a2 := by
  have hrpos : 0 < r := by
    by_cases hr0 : r = 0
    · subst r
      rw [gameF_col0] at hstart
      omega
    · omega
  by_cases h12 : a1 < a2
  · exact False.elim
      (encoding_same_lower_no_repeat game_encodes
        (s := r - 1) (t₁ := a1) (t₂ := a2) (p := v)
        (by omega) h12 ha2v hhost1 hhost2)
  · by_cases h21 : a2 < a1
    · exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          (s := r - 1) (t₁ := a2) (t₂ := a1) (p := v)
          (by omega) h21 ha1v hhost2 hhost1)
    · omega

/-! ## Exact first-failure reduction -/

/-- After the compiled lag-four through lag-seven rail exclusions, depth
eight pins the adaptive terminal burn to the single row `v-8 = q-5`. -/
theorem gameF_firstFailure_terminal_burn_exact_lag8_of_historyDepth8
    {q r g H : Nat}
    (hq : 23 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hdepth8 : TerminalTargetHistoryDepth8) :
    exists a, a = q - 5 /\
      r <= a /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_pre_lag8_actual
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  have harecent : q + 3 <= a + 8 :=
    hdepth8 hrv hstart hra (by omega) hburn
  have ha : a = q - 5 := by omega
  exact ⟨a, ha, hra, hburn, hband, htail⟩

/-- The two empirical atoms are complementary and sufficient: depth eight
pins the terminal burn to lag eight, and fixed-lag HOST-OLD puts its column
strictly left of `g`, contradicting a first failure. -/
theorem gameF_upperRail_of_historyDepth8_and_fixedLag8HostCeiling
    {q r g H : Nat}
    (hq : 23 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hdepth8 : TerminalTargetHistoryDepth8)
    (hlag8 : FixedLag8HostCeiling (q + 3) g) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  rcases gameF_firstFailure_terminal_burn_exact_lag8_of_historyDepth8
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview hdepth8 with
    ⟨a, ha, hra, hburn, _hband, _htail⟩
  have hrow : (q + 3) - 8 = a := by omega
  have hburn8 : gameF ((q + 3) - 8) (r - 1) = q + 3 := by
    rw [hrow]
    exact hburn
  have hleft : r - 1 < g := hlag8 (r - 1) (by omega) hburn8
  omega

/-! ## Existing-interface separation -/

/-- At `k=8`, the R151F order/scalar counterframe has an otherwise legal
terminal witness at depth nine.  Thus the exported interface cannot imply
the depth-eight atom. -/
theorem r151f_k8_terminal_history_depth8_countergeometry :
    r151fV 8 = 80 /\
    r151fQ 8 = 77 /\
    r151fR 8 = 64 /\
    r151fA 8 = 71 /\
    r151fR 8 <= r151fA 8 /\
    r151fA 8 < r151fQ 8 /\
    r151fV 8 > r151fA 8 + 8 /\
    r151fBurnRow 8 (r151fR 8 - 1) = r151fA 8 := by
  simp [r151fV, r151fQ, r151fR, r151fA, r151fBurnRow]

/-- The same depth-nine geometry satisfies all packaged first-failure and
scalar constraints of R151F. -/
theorem r151f_k8_terminal_history_interface_survives :
    (1 <= r151fQ 8 /\
      r151fR 8 < r151fQ 8 + 3 /\
      r151fV 8 = r151fQ 8 + 3 /\
      r151fG 8 + 1 < r151fR 8 /\
      2 < r151fG 8 + 1 /\
      r151fH 8 <= r151fQ 8 /\
      r151fH 8 <= r151fG 8 /\
      r151fR 8 - (r151fG 8 + 1) = 8 - 1) /\
    (r151fV 8 + 4 * 8 = 2 * r151fG 8 /\
      r151fR 8 + 1 = 2 * (4 * 8 + 1) - 1 /\
      r151fV 8 = 6 * 8 + 4 * 8 /\
      r151fV 8 + 4 * 8 <= 2 * r151fR 8 + 1 /\
      (r151fV 8 - r151fR 8 - 1) + 4 * 8 <= r151fR 8) := by
  exact ⟨r151f_first_failure_frame (by omega),
    r151f_scalar_interfaces (by omega)⟩

#print axioms gameF_old_host_is_accepted_by_causal_depth_three
#print axioms gameF_terminal_predecessor_host_unique
#print axioms gameF_firstFailure_terminal_burn_exact_lag8_of_historyDepth8
#print axioms gameF_upperRail_of_historyDepth8_and_fixedLag8HostCeiling
#print axioms r151f_k8_terminal_history_depth8_countergeometry
#print axioms r151f_k8_terminal_history_interface_survives

end ChompLean
