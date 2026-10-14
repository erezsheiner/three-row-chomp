import R148dContentIntervalRoundedCounterframe

set_option autoImplicit false

namespace ChompLean

/-!
R149d: backward prefix forcing for reverse-ordered services.

If a column emits a high value `v` by MEX and later emits a smaller value
`w` by MEX, then the earlier MEX source must obtain `w` from its strict
row prefix.  It cannot obtain `w` from the historical arm: that history is
monotone in the row coordinate, while the later MEX source excludes `w`.

This is the first game-source constraint not present in the scalar/2D
interface audit of R148d--R148e.  In the rounded service packet the rows in
one fixed column are reverse-ordered by target rank, so the theorem forces
the whole intervening lower-blocker packet into one earlier row prefix.
-/

/-- Historical-source membership persists when only the row cutoff grows. -/
theorem R_mono_row
    {f : Nat -> Nat -> Nat} {q q' c v : Nat}
    (hqq' : q < q') (hR : R f q c v) :
    R f q' c v := by
  rcases hR with ⟨a, haq, ha⟩
  exact ⟨a, Nat.lt_trans haq hqq', ha⟩

/-- A smaller value emitted later by MEX in the same column must be supplied
by the strict row prefix of an earlier larger MEX in that column. -/
theorem reverse_mex_service_forces_earlier_prefix
    {f : Nat -> Nat -> Nat} {q q' c v w : Nat}
    (hqq' : q < q')
    (hmexV : IsMex (B f q c) v)
    (hmexW : IsMex (B f q' c) w)
    (hwPos : 0 < w) (hwv : w < v) :
    C f q c w := by
  have hcovered : B f q c w := hmexV.2.2 w hwPos hwv
  rcases hcovered with hHistory | hPrefix
  · exfalso
    exact hmexW.2.1 (Or.inl (R_mono_row hqq' hHistory))
  · exact hPrefix

/-- Any recurrence output strictly above its row is on the MEX branch. -/
theorem recurrence_high_output_exact_mex
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {q c v : Nat}
    (hcq : c <= q) (hqv : q < v) (hvalue : f q c = v) :
    IsMex (B f q c) v := by
  have hnotCarry : Not (c < q /\ f (q - 1) c < q) := by
    rintro ⟨hcqStrict, hsmall⟩
    have hcopy := hrec.1 hcqStrict hsmall
    rw [hvalue] at hcopy
    omega
  have hmex := hrec.2 hcq hnotCarry
  simpa [hvalue] using hmex

/-- Recurrence-level service form.  Two reverse-ordered high occurrences in
one column force the lower future target into the earlier strict prefix. -/
theorem recurrence_reverse_high_services_force_prefix
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {q q' c v w : Nat}
    (hcq : c <= q) (hqq' : q < q')
    (hqv : q < v) (hq'w : q' < w)
    (hvalueV : f q c = v) (hvalueW : f q' c = w)
    (hwv : w < v) :
    C f q c w := by
  have hmexV : IsMex (B f q c) v :=
    recurrence_high_output_exact_mex hrec hcq hqv hvalueV
  have hcq' : c <= q' := Nat.le_trans hcq (Nat.le_of_lt hqq')
  have hmexW : IsMex (B f q' c) w :=
    recurrence_high_output_exact_mex hrec hcq' hq'w hvalueW
  exact reverse_mex_service_forces_earlier_prefix
    hqq' hmexV hmexW hmexW.1 hwv

/-! ## Rounded-family arithmetic -/

/-- In one rounded service column, larger blocker targets occur earlier in
time.  This is the chronology that activates the backward-prefix theorem. -/
theorem r149d_rounded_service_rows_reverse
    {k h j s : Nat} (hsh : s < h)
    (hhj : h < j) (hjk : j <= 2 * k) :
    r148dHostRow k j s < r148dHostRow k h s := by
  simp [r148dHostRow, r148dB]
  omega

/-- Exact number of prefix columns left after the `2k+j-1` lower blockers
have been forced into a rounded service prefix. -/
theorem r149d_rounded_prefix_slack_identity
    {k j s : Nat} (hjk : j <= 2 * k) :
    r148dC k s =
      (2 * k + j - 1) + (2 * k + s + r148dR s - j) := by
  simp [r148dC]
  omega

/-- At the critical target `j=2k`, the remaining prefix budget is exactly
`s+R(s)`.  A closure must force more than this many non-blocker labels into
the same prefix (or force one duplicate/wasted chair). -/
theorem r149d_critical_prefix_slack_identity
    {k s : Nat} :
    r148dC k s =
      (4 * k - 1) + (s + r148dR s) := by
  simp [r148dC]
  omega

#print axioms R_mono_row
#print axioms reverse_mex_service_forces_earlier_prefix
#print axioms recurrence_high_output_exact_mex
#print axioms recurrence_reverse_high_services_force_prefix
#print axioms r149d_rounded_service_rows_reverse
#print axioms r149d_rounded_prefix_slack_identity
#print axioms r149d_critical_prefix_slack_identity

end ChompLean
