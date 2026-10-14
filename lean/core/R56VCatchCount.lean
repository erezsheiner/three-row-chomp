import R56VCatchGate
import R56TopTwoHoles

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
R56: finite V-catch count, including currently hosted diagonal echoes.

At row `t+1`, let `u` be hosted in the V1 column `t`.  The list
`VCatchHigherColumns M t u` contains precisely the columns strictly left
of V1 whose current values lie in the open interval `(u,d(t+1))`.
`vCatch_gate_at_V1_host` sends every such column to the *same* column in
`VCatchPastHostColumns M t u`.  Since columns are already distinct, this
is an honest finite injection; fixed-row injectivity also says that their
current values are distinct.

This formulation automatically includes both classes from the proposed
count:

* a non-past-diagonal interval value is forced into the current prefix by
  exact diagonal MEX;
* a past diagonal which is currently echo-hosted lies in the same column
  list and receives exactly the same gate witness.

For the advertised flicker correction, `VCatchMissingGapValues` is the
open-interval list of values absent from the prefix strictly left of V1.
Under the exact first-two-hole hypothesis, every member of this list is a
past diagonal.  Thus this list is precisely the theorem-grade version of
`F`: past diagonals in `(u,d)` not currently echo-hosted.  The final bound
is

  d - u - 1 - F.length <= PastHostColumns.length.

Without the first-two-hole hypothesis the finite injection remains true,
but calling every missing interval value a diagonal flicker would not be
justified; the file keeps that bridge explicit.
-/

/-- Columns left of V1 whose current values lie strictly between the
caught value and the diagonal. -/
def VCatchHigherColumns
    (M : RecurrenceModel) (t u : Nat) : List Nat :=
  (List.range t).filter (fun b =>
    decide (u < M.f (t + 1) b /\
      M.f (t + 1) b < M.f (t + 1) (t + 1)))

/-- All strict prior-host columns of `u` before row `t+1`.

Every `PastHostColumn M (t+1) u b` automatically has `b<t`, so filtering
`range t` loses no possible witness column. -/
noncomputable def VCatchPastHostColumns
    (M : RecurrenceModel) (t u : Nat) : List Nat := by
  classical
  exact (List.range t).filter (fun b =>
    decide (PastHostColumn M (t + 1) u b))

/-- Current interval values, listed via their unique current columns. -/
def VCatchHigherValues
    (M : RecurrenceModel) (t u : Nat) : List Nat :=
  (VCatchHigherColumns M t u).map (fun b => M.f (t + 1) b)

/-- The column-level witness relation used by the value injection. -/
def VCatchPastHostWitness
    (M : RecurrenceModel) (t u v b : Nat) : Prop :=
  b < t /\ M.f (t + 1) b = v /\
    PastHostColumn M (t + 1) u b

/-- The complete open numerical interval `(u,d(t+1))`. -/
def VCatchGapValues
    (M : RecurrenceModel) (t u : Nat) : List Nat :=
  List.range' (u + 1) (M.f (t + 1) (t + 1) - u - 1)

/-- Gap values currently hosted strictly left of V1. -/
noncomputable def VCatchHostedGapValues
    (M : RecurrenceModel) (t u : Nat) : List Nat := by
  classical
  exact (VCatchGapValues M t u).filter (fun v =>
    decide (C M.f (t + 1) t v))

/-- Gap values not currently hosted strictly left of V1.

Only after the first-two-hole theorem is supplied do these become exactly
the flickering past diagonals. -/
noncomputable def VCatchMissingGapValues
    (M : RecurrenceModel) (t u : Nat) : List Nat := by
  classical
  exact (VCatchGapValues M t u).filter (fun v =>
    !(decide (C M.f (t + 1) t v)))

theorem mem_vCatchHigherColumns_iff
    {M : RecurrenceModel} {t u b : Nat} :
    b ∈ VCatchHigherColumns M t u <->
      b < t /\ u < M.f (t + 1) b /\
        M.f (t + 1) b < M.f (t + 1) (t + 1) := by
  simp [VCatchHigherColumns]

theorem mem_vCatchPastHostColumns_iff
    {M : RecurrenceModel} {t u b : Nat} :
    b ∈ VCatchPastHostColumns M t u <->
      b < t /\ PastHostColumn M (t + 1) u b := by
  classical
  simp [VCatchPastHostColumns]

theorem mem_vCatchHostedGapValues_iff
    {M : RecurrenceModel} {t u v : Nat} :
    v ∈ VCatchHostedGapValues M t u <->
      v ∈ VCatchGapValues M t u /\ C M.f (t + 1) t v := by
  classical
  simp [VCatchHostedGapValues]

theorem mem_vCatchMissingGapValues_iff
    {M : RecurrenceModel} {t u v : Nat} :
    v ∈ VCatchMissingGapValues M t u <->
      v ∈ VCatchGapValues M t u /\ Not (C M.f (t + 1) t v) := by
  classical
  simp [VCatchMissingGapValues]

/-- Exact membership description of the open interval. -/
theorem mem_vCatchGapValues_iff
    {M : RecurrenceModel} {t u v : Nat}
    (huDiag : u < M.f (t + 1) (t + 1)) :
    v ∈ VCatchGapValues M t u <->
      u < v /\ v < M.f (t + 1) (t + 1) := by
  constructor
  · intro hv
    have hrange := List.mem_range'_1.mp hv
    change u + 1 <= v /\
      v < u + 1 + (M.f (t + 1) (t + 1) - u - 1) at hrange
    omega
  · rintro ⟨huv, hvd⟩
    apply List.mem_range'_1.mpr
    change u + 1 <= v /\
      v < u + 1 + (M.f (t + 1) (t + 1) - u - 1)
    omega

theorem vCatchHigherColumns_nodup
    (M : RecurrenceModel) (t u : Nat) :
    (VCatchHigherColumns M t u).Nodup := by
  exact List.filter_sublist.nodup List.nodup_range

theorem vCatchPastHostColumns_nodup
    (M : RecurrenceModel) (t u : Nat) :
    (VCatchPastHostColumns M t u).Nodup := by
  classical
  exact List.filter_sublist.nodup List.nodup_range

private theorem r56_vcatch_nodup_map_of_injective_on
    {alpha beta : Type} (f : alpha -> beta) (xs : List alpha)
    (hxs : xs.Nodup)
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
      f x = f y -> x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      change (f a :: as.map f).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hay⟩
        have hay' : a = y :=
          hinj a (by simp) y (by simp [hy]) hay.symm
        subst y
        exact hxs.1 hy
      · apply ih hxs.2
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

/-- Fixed-row injectivity makes the currently hosted interval values
pairwise distinct. -/
theorem vCatchHigherValues_nodup
    (M : RecurrenceModel) (t u : Nat) :
    (VCatchHigherValues M t u).Nodup := by
  apply r56_vcatch_nodup_map_of_injective_on
      (fun b => M.f (t + 1) b)
      (VCatchHigherColumns M t u)
      (vCatchHigherColumns_nodup M t u)
  intro b hb c hc hvalue
  have hbt := (mem_vCatchHigherColumns_iff.mp hb).1
  have hct := (mem_vCatchHigherColumns_iff.mp hc).1
  exact M.fixed_q_injective (by omega) (by omega) hvalue

/-- The V-catch gate is literally the identity injection on current
higher columns.  The upper interval cutoff is not needed by the gate, but
records exactly the family used in the count. -/
theorem vCatchHigherColumns_subset_pastHostColumns
    (M : RecurrenceModel) {t u : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u) :
    VCatchHigherColumns M t u ⊆ VCatchPastHostColumns M t u := by
  intro b hb
  have hdata := mem_vCatchHigherColumns_iff.mp hb
  apply mem_vCatchPastHostColumns_iff.mpr
  refine ⟨hdata.1, ?_⟩
  exact vCatch_gate_at_V1_host M hhost hnotPast
    b hdata.1 hdata.2.1

/-- Finite cardinality form of the clean column injection. -/
theorem vCatchHigherColumns_card_le_pastHostColumns
    (M : RecurrenceModel) {t u : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u) :
    (VCatchHigherColumns M t u).length <=
      (VCatchPastHostColumns M t u).length := by
  exact nodup_subset_length_le
    (vCatchHigherColumns_nodup M t u)
    (vCatchHigherColumns_subset_pastHostColumns M hhost hnotPast)

/-- Every currently hosted interval value has one unique current column,
and that same column is a strict prior host column of `u`.  This theorem
does not distinguish non-past values from echoed past diagonals: both are
covered, exactly as required by the higher-cell argument. -/
theorem vCatch_current_interval_value_unique_pastHostColumn
    (M : RecurrenceModel) {t u v : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u)
    (huv : u < v)
    (hvd : v < M.f (t + 1) (t + 1))
    (hcurrent : C M.f (t + 1) t v) :
    exists b, VCatchPastHostWitness M t u v b /\
      forall c, VCatchPastHostWitness M t u v c -> c = b := by
  rcases hcurrent with ⟨b, hbt, hvalue⟩
  have hbHigher : b ∈ VCatchHigherColumns M t u := by
    apply mem_vCatchHigherColumns_iff.mpr
    constructor
    · exact hbt
    constructor
    · simpa [hvalue] using huv
    · simpa [hvalue] using hvd
  have hbPastMem :=
    vCatchHigherColumns_subset_pastHostColumns M hhost hnotPast hbHigher
  have hbPast := (mem_vCatchPastHostColumns_iff.mp hbPastMem).2
  refine ⟨b, ⟨hbt, hvalue, hbPast⟩, ?_⟩
  intro c hc
  have hct : c < t := hc.1
  exact M.fixed_q_injective (by omega) (by omega)
    (hc.2.1.trans hvalue.symm)

/-- A non-past-diagonal interval value is automatically currently hosted,
by exact diagonal MEX, and therefore enters the same unique-column
injection. -/
theorem vCatch_nonpast_interval_value_unique_pastHostColumn
    (M : RecurrenceModel) {t u v : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPastU : forall a, a < t + 1 -> M.f a a ≠ u)
    (huv : u < v)
    (hvd : v < M.f (t + 1) (t + 1))
    (hnotPastV : forall a, a < t + 1 -> M.f a a ≠ v) :
    exists b, VCatchPastHostWitness M t u v b /\
      forall c, VCatchPastHostWitness M t u v c -> c = b := by
  have huPos : 0 < u := by
    have hindex := M.value_gt_index (q := t + 1) (r := t) (by omega)
    rw [hhost] at hindex
    omega
  have hMex : IsMex
      (B M.f (t + 1) (t + 1)) (M.f (t + 1) (t + 1)) :=
    recurrence_diagonal_exact_mex M (t + 1)
  have hB : B M.f (t + 1) (t + 1) v :=
    hMex.2.2 v (by omega) hvd
  have hcurrentFull : C M.f (t + 1) (t + 1) v := by
    rcases hB with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hdiag : M.f a a = v := by
        simpa [Nat.min_eq_left (Nat.le_of_lt ha)] using hvalue
      exact False.elim ((hnotPastV a ha) hdiag)
    · exact hC
  have hcurrent : C M.f (t + 1) t v := by
    rcases hcurrentFull with ⟨b, hbq, hvalue⟩
    have hbt : b < t := by
      by_cases hbeq : b = t
      · subst b
        rw [hhost] at hvalue
        omega
      · omega
    exact ⟨b, hbt, hvalue⟩
  exact vCatch_current_interval_value_unique_pastHostColumn
    M hhost hnotPastU huv hvd hcurrent

/-- Explicit echoed-past-diagonal corollary.  The past-diagonal witness is
recorded for classification; current echo-hosting is the hypothesis used
by the common higher-cell injection. -/
theorem vCatch_echoed_past_diagonal_unique_pastHostColumn
    (M : RecurrenceModel) {t u v : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPastU : forall a, a < t + 1 -> M.f a a ≠ u)
    (huv : u < v)
    (hvd : v < M.f (t + 1) (t + 1))
    (_hPastV : exists a, a < t + 1 /\ M.f a a = v)
    (hEcho : C M.f (t + 1) t v) :
    exists b, VCatchPastHostWitness M t u v b /\
      forall c, VCatchPastHostWitness M t u v c -> c = b :=
  vCatch_current_interval_value_unique_pastHostColumn
    M hhost hnotPastU huv hvd hEcho

/-- Hosted and missing gap values partition the complete numerical gap. -/
theorem vCatch_gap_partition_length
    (M : RecurrenceModel) (t u : Nat) :
    (VCatchGapValues M t u).length =
      (VCatchHostedGapValues M t u).length +
      (VCatchMissingGapValues M t u).length := by
  classical
  have hraw := List.length_eq_countP_add_countP
    (fun v => decide (C M.f (t + 1) t v))
    (l := VCatchGapValues M t u)
  simp only [List.countP_eq_length_filter] at hraw
  simpa [VCatchHostedGapValues, VCatchMissingGapValues] using hraw

theorem vCatchGapValues_length
    (M : RecurrenceModel) (t u : Nat) :
    (VCatchGapValues M t u).length =
      M.f (t + 1) (t + 1) - u - 1 := by
  simp [VCatchGapValues]

theorem vCatchHostedGapValues_nodup
    (M : RecurrenceModel) (t u : Nat) :
    (VCatchHostedGapValues M t u).Nodup := by
  classical
  exact List.filter_sublist.nodup (List.nodup_range' _)

/-- The value-list and column-list descriptions of the currently hosted
gap have identical membership. -/
theorem mem_vCatchHostedGapValues_iff_mem_vCatchHigherValues
    (M : RecurrenceModel) {t u v : Nat}
    (huDiag : u < M.f (t + 1) (t + 1)) :
    v ∈ VCatchHostedGapValues M t u <->
      v ∈ VCatchHigherValues M t u := by
  constructor
  · intro hv
    rcases mem_vCatchHostedGapValues_iff.mp hv with ⟨hvGap, hC⟩
    have hvBounds := (mem_vCatchGapValues_iff huDiag).mp hvGap
    rcases hC with ⟨b, hbt, hvalue⟩
    apply List.mem_map.mpr
    refine ⟨b, ?_, hvalue⟩
    apply mem_vCatchHigherColumns_iff.mpr
    exact ⟨hbt, by simpa [hvalue] using hvBounds.1,
      by simpa [hvalue] using hvBounds.2⟩
  · intro hv
    rcases List.mem_map.mp hv with ⟨b, hb, hvalue⟩
    have hbData := mem_vCatchHigherColumns_iff.mp hb
    apply mem_vCatchHostedGapValues_iff.mpr
    constructor
    · apply (mem_vCatchGapValues_iff huDiag).mpr
      exact ⟨by simpa [hvalue] using hbData.2.1,
        by simpa [hvalue] using hbData.2.2⟩
    · exact ⟨b, hbData.1, hvalue⟩

/-- Current hosted gap values and their current columns have equal finite
cardinality. -/
theorem vCatchHostedGapValues_length_eq_higherColumns
    (M : RecurrenceModel) {t u : Nat}
    (huDiag : u < M.f (t + 1) (t + 1)) :
    (VCatchHostedGapValues M t u).length =
      (VCatchHigherColumns M t u).length := by
  have hmem : forall v,
      v ∈ VCatchHostedGapValues M t u <->
        v ∈ VCatchHigherValues M t u := by
    intro v
    exact mem_vCatchHostedGapValues_iff_mem_vCatchHigherValues
      M (t := t) (u := u) (v := v) huDiag
  have hleForward := nodup_subset_length_le
    (vCatchHostedGapValues_nodup M t u)
    (fun v hv => (hmem v).mp hv)
  have hleBackward := nodup_subset_length_le
    (vCatchHigherValues_nodup M t u)
    (fun v hv => (hmem v).mpr hv)
  simp [VCatchHigherValues] at hleForward hleBackward
  omega

/-- Clean gap-minus-missing bound.  It needs only the V-catch hypotheses;
the first-two-hole theorem is used below to identify the missing list with
past-diagonal flickers. -/
theorem vCatch_gap_minus_missing_le_pastHostColumns
    (M : RecurrenceModel) {t u : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u)
    (huDiag : u < M.f (t + 1) (t + 1)) :
    M.f (t + 1) (t + 1) - u - 1 -
        (VCatchMissingGapValues M t u).length <=
      (VCatchPastHostColumns M t u).length := by
  have hpartition := vCatch_gap_partition_length M t u
  have hgapLength := vCatchGapValues_length M t u
  have hhostedLength :=
    vCatchHostedGapValues_length_eq_higherColumns M huDiag
  have hcolumnBound :=
    vCatchHigherColumns_card_le_pastHostColumns M hhost hnotPast
  omega

/-- Pure MEX fact: the first positive hole precedes the second one. -/
theorem firstTwoPositiveHoles_strict_order
    {S : Nat -> Prop} {u d : Nat}
    (hholes : IsFirstTwoPositiveHoles S u d) :
    u < d := by
  have huMex := hholes.1
  have hdMex := hholes.2
  by_cases hdu : d = u
  · subst d
    exact False.elim (hdMex.2.1 (Or.inr rfl))
  · by_cases hud : u < d
    · exact hud
    · have hduLt : d < u := by omega
      have hSd : S d := huMex.2.2 d hdMex.1 hduLt
      exact False.elim (hdMex.2.1 (Or.inl hSd))

/-- With the exact top-two-hole input, every currently missing gap value
is a past diagonal.  This is the missing semantic bridge which turns the
raw missing list into the flicker list `F`. -/
theorem vCatch_missingGap_is_past_diagonal
    (M : RecurrenceModel) {t u v : Nat}
    (hholes : IsFirstTwoPositiveHoles
      (TwoEdgeSigma M.f (t + 1)) u (M.f (t + 1) (t + 1)))
    (hvMissing : v ∈ VCatchMissingGapValues M t u) :
    exists a, a < t + 1 /\ M.f a a = v := by
  have huDiag := firstTwoPositiveHoles_strict_order hholes
  rcases mem_vCatchMissingGapValues_iff.mp hvMissing with
    ⟨hvGap, hvNotCurrent⟩
  have hvBounds := (mem_vCatchGapValues_iff huDiag).mp hvGap
  have hsource :
      TwoEdgeSigma M.f (t + 1) v \/ v = u :=
    hholes.2.2.2 v (by omega) hvBounds.2
  have hsigma : TwoEdgeSigma M.f (t + 1) v := by
    rcases hsource with hsigma | hEq
    · exact hsigma
    · omega
  rcases hsigma with hPast | hCurrent
  · exact hPast
  · exfalso
    apply hvNotCurrent
    rcases hCurrent with ⟨b, hbq, hvalue⟩
    exact ⟨b, by omega, hvalue⟩

/-- Exact semantic identification of the correction list: membership is
equivalent to being an interval past diagonal with no current echo strictly
left of V1. -/
theorem mem_vCatchMissingGapValues_iff_flickering_past_diagonal
    (M : RecurrenceModel) {t u v : Nat}
    (hholes : IsFirstTwoPositiveHoles
      (TwoEdgeSigma M.f (t + 1)) u (M.f (t + 1) (t + 1))) :
    v ∈ VCatchMissingGapValues M t u <->
      u < v /\ v < M.f (t + 1) (t + 1) /\
      (exists a, a < t + 1 /\ M.f a a = v) /\
      Not (C M.f (t + 1) t v) := by
  have huDiag := firstTwoPositiveHoles_strict_order hholes
  constructor
  · intro hv
    rcases mem_vCatchMissingGapValues_iff.mp hv with
      ⟨hvGap, hvNotCurrent⟩
    have hvBounds := (mem_vCatchGapValues_iff huDiag).mp hvGap
    exact ⟨hvBounds.1, hvBounds.2,
      vCatch_missingGap_is_past_diagonal M hholes hv,
      hvNotCurrent⟩
  · rintro ⟨huv, hvd, _hvPast, hvNotCurrent⟩
    apply mem_vCatchMissingGapValues_iff.mpr
    exact ⟨(mem_vCatchGapValues_iff huDiag).mpr ⟨huv, hvd⟩,
      hvNotCurrent⟩

/-- The advertised count, with `F` represented by
`VCatchMissingGapValues`.  The first conjunct certifies that this list
really consists of past diagonals rather than arbitrary missing values. -/
theorem vCatch_gap_minus_flicker_count
    (M : RecurrenceModel) {t u : Nat}
    (hhost : M.f (t + 1) t = u)
    (hnotPast : forall a, a < t + 1 -> M.f a a ≠ u)
    (hholes : IsFirstTwoPositiveHoles
      (TwoEdgeSigma M.f (t + 1)) u (M.f (t + 1) (t + 1))) :
    (forall v, v ∈ VCatchMissingGapValues M t u ->
      exists a, a < t + 1 /\ M.f a a = v) /\
    M.f (t + 1) (t + 1) - u - 1 -
        (VCatchMissingGapValues M t u).length <=
      (VCatchPastHostColumns M t u).length := by
  have huDiag := firstTwoPositiveHoles_strict_order hholes
  constructor
  · intro v hv
    exact vCatch_missingGap_is_past_diagonal M hholes hv
  · exact vCatch_gap_minus_missing_le_pastHostColumns
      M hhost hnotPast huDiag

/-- Unconditional actual-game specialization: `F` is now an exact finite
list, and every non-flickering interval value contributes a distinct prior
host column of the first hole. -/
theorem gameF_first_hole_gap_minus_flicker_count (t : Nat) :
    (forall v,
      v ∈ VCatchMissingGapValues gameRecurrenceModel t (gameF (t + 1) t) ->
      exists a, a < t + 1 /\ gameF a a = v) /\
    gameF (t + 1) (t + 1) - gameF (t + 1) t - 1 -
        (VCatchMissingGapValues
          gameRecurrenceModel t (gameF (t + 1) t)).length <=
      (VCatchPastHostColumns
        gameRecurrenceModel t (gameF (t + 1) t)).length := by
  have hholes := gameF_nextRow_top_two_positive_holes t
  have hnotPast : forall a, a < t + 1 ->
      gameF a a ≠ gameF (t + 1) t := by
    intro a ha hEq
    exact hholes.1.2.1 (Or.inl ⟨a, ha, hEq⟩)
  exact vCatch_gap_minus_flicker_count
    gameRecurrenceModel rfl hnotPast hholes

#print axioms vCatchHigherColumns_card_le_pastHostColumns
#print axioms vCatch_nonpast_interval_value_unique_pastHostColumn
#print axioms vCatch_echoed_past_diagonal_unique_pastHostColumn
#print axioms mem_vCatchMissingGapValues_iff_flickering_past_diagonal
#print axioms vCatch_gap_minus_flicker_count
#print axioms gameF_first_hole_gap_minus_flicker_count

end ChompLean
