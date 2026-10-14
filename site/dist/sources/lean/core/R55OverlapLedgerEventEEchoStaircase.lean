import R54EventEThirdDipBoundarySaturation

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R55: the exact overlap ledger, its echo band and the resulting lower
envelope, followed by the exact echo staircase at a margin event E.

Everything is phrased with duplicate-free lists because the present Chomp
development deliberately has no `Finset` dependency.  The lists below are
finite sets: nodup is proved before every cardinality argument.
-/

/-- Indices of past diagonals which lie below the current diagonal. -/
noncomputable def PastLowerDiagonalIndices (t : Nat) : List Nat :=
  (List.range t).filter
    (fun i => decide (gameF i i < gameF t t))

/-- Values of the past lower diagonals. -/
noncomputable def PastLowerDiagonalValues (t : Nat) : List Nat :=
  (PastLowerDiagonalIndices t).map (fun i => gameF i i)

/-- Past diagonals already at or below the current row index. -/
noncomputable def PastAtMostRowDiagonalIndices (t : Nat) : List Nat :=
  (List.range t).filter
    (fun i => decide (gameF i i <= t))

noncomputable def PastAtMostRowDiagonalValues (t : Nat) : List Nat :=
  (PastAtMostRowDiagonalIndices t).map (fun i => gameF i i)

/-- Strict-prefix cells which duplicate a past lower diagonal. -/
noncomputable def PastDiagonalEchoValues (t : Nat) : List Nat :=
  (StrictRowPrefixValues gameF t).filter
    (fun v => decide (v ∈ PastLowerDiagonalValues t))

/-- The complementary fresh part of the strict row prefix. -/
noncomputable def FreshStrictRowPrefixValues (t : Nat) : List Nat :=
  (StrictRowPrefixValues gameF t).filter
    (fun v => !(decide (v ∈ PastLowerDiagonalValues t)))

/-- The positive interval strictly below the current diagonal. -/
noncomputable def PositiveBelowDiagonalValues (t : Nat) : List Nat :=
  (List.range (gameF t t - 1)).map (fun k => k + 1)

/-- The three ledger cardinalities `P,L,W`. -/
noncomputable def PastLowerDiagonalCount (t : Nat) : Nat :=
  (PastLowerDiagonalIndices t).length

noncomputable def PastAtMostRowDiagonalCount (t : Nat) : Nat :=
  (PastAtMostRowDiagonalIndices t).length

noncomputable def StrictRowEchoCount (t : Nat) : Nat :=
  (PastDiagonalEchoValues t).length

private theorem r55_nodup_map_of_injective_on
    (f : Nat -> Nat) (xs : List Nat)
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

theorem mem_pastLowerDiagonalIndices_iff {t i : Nat} :
    i ∈ PastLowerDiagonalIndices t <->
      i < t ∧ gameF i i < gameF t t := by
  simp [PastLowerDiagonalIndices]

theorem mem_pastAtMostRowDiagonalIndices_iff {t i : Nat} :
    i ∈ PastAtMostRowDiagonalIndices t <->
      i < t ∧ gameF i i <= t := by
  simp [PastAtMostRowDiagonalIndices]

theorem mem_pastLowerDiagonalValues_iff {t v : Nat} :
    v ∈ PastLowerDiagonalValues t <->
      exists i, i < t ∧ gameF i i = v ∧ v < gameF t t := by
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨i, hi, hiv⟩
    have hi' := mem_pastLowerDiagonalIndices_iff.mp hi
    exact ⟨i, hi'.1, hiv, by simpa [hiv] using hi'.2⟩
  · rintro ⟨i, hit, hiv, hvlt⟩
    apply List.mem_map.mpr
    refine ⟨i, mem_pastLowerDiagonalIndices_iff.mpr ?_, hiv⟩
    exact ⟨hit, by simpa [hiv] using hvlt⟩

theorem mem_pastAtMostRowDiagonalValues_iff {t v : Nat} :
    v ∈ PastAtMostRowDiagonalValues t <->
      exists i, i < t ∧ gameF i i = v ∧ v <= t := by
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨i, hi, hiv⟩
    have hi' := mem_pastAtMostRowDiagonalIndices_iff.mp hi
    exact ⟨i, hi'.1, hiv, by simpa [hiv] using hi'.2⟩
  · rintro ⟨i, hit, hiv, hvle⟩
    apply List.mem_map.mpr
    refine ⟨i, mem_pastAtMostRowDiagonalIndices_iff.mpr ?_, hiv⟩
    exact ⟨hit, by simpa [hiv] using hvle⟩

theorem mem_positiveBelowDiagonalValues_iff {t v : Nat} :
    v ∈ PositiveBelowDiagonalValues t <->
      0 < v ∧ v < gameF t t := by
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨k, hk, rfl⟩
    have hk' := List.mem_range.mp hk
    have hgt := gameRecurrenceModel.diagonal_gt t
    omega
  · rintro ⟨hvpos, hvlt⟩
    apply List.mem_map.mpr
    refine ⟨v - 1, List.mem_range.mpr ?_, by omega⟩
    omega

theorem pastLowerDiagonalIndices_nodup (t : Nat) :
    (PastLowerDiagonalIndices t).Nodup := by
  exact List.filter_sublist.nodup List.nodup_range

theorem pastAtMostRowDiagonalIndices_nodup (t : Nat) :
    (PastAtMostRowDiagonalIndices t).Nodup := by
  exact List.filter_sublist.nodup List.nodup_range

theorem pastLowerDiagonalValues_nodup (t : Nat) :
    (PastLowerDiagonalValues t).Nodup := by
  apply r55_nodup_map_of_injective_on
    (fun i => gameF i i) (PastLowerDiagonalIndices t)
    (pastLowerDiagonalIndices_nodup t)
  intro i _hi j _hj hEq
  exact diagonal_injective gameRecurrenceModel hEq

theorem pastAtMostRowDiagonalValues_nodup (t : Nat) :
    (PastAtMostRowDiagonalValues t).Nodup := by
  apply r55_nodup_map_of_injective_on
    (fun i => gameF i i) (PastAtMostRowDiagonalIndices t)
    (pastAtMostRowDiagonalIndices_nodup t)
  intro i _hi j _hj hEq
  exact diagonal_injective gameRecurrenceModel hEq

theorem positiveBelowDiagonalValues_nodup (t : Nat) :
    (PositiveBelowDiagonalValues t).Nodup := by
  apply r55_nodup_map_of_injective_on
    (fun k => k + 1) (List.range (gameF t t - 1)) List.nodup_range
  intro i _hi j _hj hEq
  omega

/-- Strict row maximality plus fixed-row injectivity makes every strict
prefix value positive and strictly below the diagonal. -/
theorem gameF_strict_prefix_value_band {t v : Nat}
    (hv : v ∈ StrictRowPrefixValues gameF t) :
    0 < v ∧ v < gameF t t := by
  rcases mem_strictRowPrefixValues_iff_C.mp hv with ⟨b, hbt, hbval⟩
  have hpos0 := gameRecurrenceModel.value_gt_index
    (q := t) (r := b) (Nat.le_of_lt hbt)
  change b < gameF t b at hpos0
  have hmax0 := game_diagonal_maximal
    (q := t) (s := b) (Nat.le_of_lt hbt)
  have hne : gameF t b ≠ gameF t t := by
    intro hEq
    have := gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hbt) (Nat.le_refl t) hEq
    omega
  rw [hbval] at hpos0 hmax0 hne
  omega

/-- Exact partition of the strict prefix into echoes and fresh values. -/
theorem strict_prefix_echo_fresh_length (t : Nat) :
    t = StrictRowEchoCount t + (FreshStrictRowPrefixValues t).length := by
  have hraw := List.length_eq_countP_add_countP
    (fun v => decide (v ∈ PastLowerDiagonalValues t))
    (l := StrictRowPrefixValues gameF t)
  simp only [List.countP_eq_length_filter] at hraw
  simpa [StrictRowPrefixValues, StrictRowEchoCount,
    PastDiagonalEchoValues, FreshStrictRowPrefixValues] using hraw

/-- Exact MEX coverage: past-lower diagonal values together with fresh
strict-prefix values are precisely the positive interval below `d(t)`.
Only cardinal equality is exposed, which is all the ledger needs. -/
theorem past_lower_append_fresh_exact_cardinality (t : Nat) :
    (PastLowerDiagonalValues t ++
      FreshStrictRowPrefixValues t).length = gameF t t - 1 := by
  let past := PastLowerDiagonalValues t
  let fresh := FreshStrictRowPrefixValues t
  let below := PositiveBelowDiagonalValues t
  have hpastNodup : past.Nodup := pastLowerDiagonalValues_nodup t
  have hprefNodup := strictRowPrefixValues_nodup gameRecurrenceModel t
  have hfreshNodup : fresh.Nodup := by
    exact List.filter_sublist.nodup hprefNodup
  have hcross : forall a, a ∈ past -> forall b, b ∈ fresh -> a ≠ b := by
    intro a ha b hb hEq
    have hbFilter := (List.mem_filter.mp hb).2
    have hbNot : b ∉ past := by
      simpa [fresh, FreshStrictRowPrefixValues, past] using hbFilter
    subst b
    exact hbNot ha
  have happNodup : (past ++ fresh).Nodup :=
    List.nodup_append.mpr ⟨hpastNodup, hfreshNodup, hcross⟩
  have hbelowNodup : below.Nodup := positiveBelowDiagonalValues_nodup t
  have happSub : past ++ fresh ⊆ below := by
    intro v hv
    apply mem_positiveBelowDiagonalValues_iff.mpr
    rcases List.mem_append.mp hv with hvPast | hvFresh
    · rcases mem_pastLowerDiagonalValues_iff.mp hvPast with
        ⟨i, _hit, hiv, hvlt⟩
      have hpos := gameRecurrenceModel.diagonal_gt i
      change i < gameF i i at hpos
      rw [hiv] at hpos
      exact ⟨by omega, hvlt⟩
    · have hvPrefix := (List.mem_filter.mp hvFresh).1
      exact gameF_strict_prefix_value_band hvPrefix
  have hbelowSub : below ⊆ past ++ fresh := by
    intro v hv
    have hvBand := mem_positiveBelowDiagonalValues_iff.mp hv
    have hvB : B gameF t t v :=
      gameRecurrenceModel.mex_no_skip (Nat.le_refl t)
        (gameRecurrenceModel.diagonal_gt t) hvBand.1 hvBand.2
    rcases hvB with hvR | hvC
    · rcases hvR with ⟨i, hit, hvalue⟩
      have hmin : min i t = i := Nat.min_eq_left (Nat.le_of_lt hit)
      rw [hmin] at hvalue
      apply List.mem_append.mpr
      left
      apply mem_pastLowerDiagonalValues_iff.mpr
      exact ⟨i, hit, hvalue, hvBand.2⟩
    · have hvPrefix := mem_strictRowPrefixValues_iff_C.mpr hvC
      by_cases hvPast : v ∈ past
      · exact List.mem_append.mpr (Or.inl hvPast)
      · apply List.mem_append.mpr
        right
        apply List.mem_filter.mpr
        refine ⟨hvPrefix, ?_⟩
        simp [past, hvPast]
  have happLe := nodup_subset_length_le happNodup happSub
  have hbelowLe := nodup_subset_length_le hbelowNodup hbelowSub
  have hbelowLen : below.length = gameF t t - 1 := by
    simp [below, PositiveBelowDiagonalValues]
  change (past ++ fresh).length = gameF t t - 1
  omega

/-- L1, in subtraction-safe form:
`d(t)-1 + W(t) = t + P(t)`. -/
theorem gameF_overlap_ledger (t : Nat) :
    gameF t t - 1 + StrictRowEchoCount t =
      t + PastLowerDiagonalCount t := by
  have hpartition := strict_prefix_echo_fresh_length t
  have hcover := past_lower_append_fresh_exact_cardinality t
  simp only [List.length_append] at hcover
  have hpastLen : (PastLowerDiagonalValues t).length =
      PastLowerDiagonalCount t := by
    simp [PastLowerDiagonalValues, PastLowerDiagonalCount]
  omega

/-- L2 pointwise: an echoed past diagonal lies in the open band
`(t,d(t))`. -/
theorem gameF_overlap_echo_band {t v : Nat}
    (hv : v ∈ PastDiagonalEchoValues t) :
    t < v ∧ v < gameF t t := by
  have hvFilter := List.mem_filter.mp hv
  have hvPrefix : v ∈ StrictRowPrefixValues gameF t := hvFilter.1
  have hvPast : v ∈ PastLowerDiagonalValues t := by
    simpa [PastDiagonalEchoValues] using hvFilter.2
  rcases mem_pastLowerDiagonalValues_iff.mp hvPast with
    ⟨i, _hit, hiv, hvlt⟩
  rcases mem_strictRowPrefixValues_iff_C.mp hvPrefix with
    ⟨b, hbt, hbval⟩
  have hhigh := game_past_diagonal_reemission_is_high
    (i := i) (t := t) (b := b) (Nat.le_of_lt hbt)
      (hiv.trans hbval.symm)
  exact ⟨by simpa [hiv] using hhigh, hvlt⟩

/-- Cardinal form of `W(t) <= P(t)-L(t)`, avoiding truncated
subtraction: `W(t)+L(t) <= P(t)`. -/
theorem gameF_echo_plus_low_le_past_lower (t : Nat) :
    StrictRowEchoCount t + PastAtMostRowDiagonalCount t <=
      PastLowerDiagonalCount t := by
  let echo := PastDiagonalEchoValues t
  let low := PastAtMostRowDiagonalValues t
  let past := PastLowerDiagonalValues t
  have hechoNodup : echo.Nodup := by
    exact List.filter_sublist.nodup
      (strictRowPrefixValues_nodup gameRecurrenceModel t)
  have hlowNodup : low.Nodup := pastAtMostRowDiagonalValues_nodup t
  have hcross : forall a, a ∈ echo -> forall b, b ∈ low -> a ≠ b := by
    intro a ha b hb hEq
    have haHigh := gameF_overlap_echo_band ha
    rcases mem_pastAtMostRowDiagonalValues_iff.mp hb with
      ⟨_i, _hit, _hiv, hble⟩
    omega
  have happNodup : (echo ++ low).Nodup :=
    List.nodup_append.mpr ⟨hechoNodup, hlowNodup, hcross⟩
  have happSub : echo ++ low ⊆ past := by
    intro v hv
    rcases List.mem_append.mp hv with hvEcho | hvLow
    · have hvFilter := (List.mem_filter.mp hvEcho).2
      simpa [echo, PastDiagonalEchoValues, past] using hvFilter
    · rcases mem_pastAtMostRowDiagonalValues_iff.mp hvLow with
        ⟨i, hit, hiv, hvle⟩
      apply mem_pastLowerDiagonalValues_iff.mpr
      have hdiag := gameRecurrenceModel.diagonal_gt t
      change t < gameF t t at hdiag
      exact ⟨i, hit, hiv, by omega⟩
  have hcap := nodup_subset_length_le happNodup happSub
  change echo.length +
      (PastAtMostRowDiagonalIndices t).length <=
      (PastLowerDiagonalIndices t).length
  simpa [low, past, PastAtMostRowDiagonalValues,
    PastLowerDiagonalValues] using hcap

/-- The first envelope consequence of L1+L2. -/
theorem gameF_ledger_lower_envelope_with_L (t : Nat) :
    t + 1 + PastAtMostRowDiagonalCount t <= gameF t t := by
  have hledger := gameF_overlap_ledger t
  have hecho := gameF_echo_plus_low_le_past_lower t
  have hgt := gameRecurrenceModel.diagonal_gt t
  change t < gameF t t at hgt
  omega

/-- Source capacity supplies at least `floor((t+1)/2)` old diagonals at or
below row `t`. -/
theorem gameF_past_at_most_row_count_lower_bound (t : Nat) :
    (t + 1) / 2 <= PastAtMostRowDiagonalCount t := by
  have hsub : List.range ((t + 1) / 2) ⊆
      PastAtMostRowDiagonalIndices t := by
    intro i hi
    have hiHalf := List.mem_range.mp hi
    have hiTwice : i * 2 < t := by
      have hraw := (Nat.lt_div_iff_mul_lt (k := 2) (x := i)
        (y := t + 1) (by omega)).mp hiHalf
      omega
    have hit : i < t := by omega
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel i
    change gameF i i <= i + i + 1 at hcap
    apply mem_pastAtMostRowDiagonalIndices_iff.mpr
    exact ⟨hit, by omega⟩
  have hlen := nodup_subset_length_le List.nodup_range hsub
  simpa [PastAtMostRowDiagonalCount] using hlen

/-- L3: the unconditional `3/2` lower envelope. -/
theorem gameF_overlap_env_lower_bound (t : Nat) :
    t + 1 + (t + 1) / 2 <= gameF t t := by
  have hL := gameF_past_at_most_row_count_lower_bound t
  have henv := gameF_ledger_lower_envelope_with_L t
  omega

private theorem r55_margin_past_below
    {s z : Nat}
    (hmargin : s = 0 ∨
      exists j, s = j + 1 ∧
        RMax gameRecurrenceModel j < z) :
    forall i, i < s -> gameF i i < z := by
  intro i hi
  rcases hmargin with hs0 | ⟨j, hsj, hmarg⟩
  · omega
  · have hij : i <= j := by omega
    have hle := rmax_ge gameRecurrenceModel j i hij
    change gameF i i <= RMax gameRecurrenceModel j at hle
    omega

private theorem r55_count_eq_of_mutual_subset
    {xs ys : List Nat} (hxs : xs.Nodup) (hys : ys.Nodup)
    (hxy : xs ⊆ ys) (hyx : ys ⊆ xs) :
    xs.length = ys.length := by
  have h1 := nodup_subset_length_le hxs hxy
  have h2 := nodup_subset_length_le hys hyx
  omega

/-- At the three rows of event E, exactly the first `s` diagonal indices
are lower than the current diagonal. -/
theorem gameF_margin_eventE_past_lower_count_staircase
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip0 : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      exists j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hdip1 : gameF (s + 2) (s + 2) <
      gameF (s + 1) (s + 1)) :
    PastLowerDiagonalCount s = s ∧
    PastLowerDiagonalCount (s + 1) = s ∧
    PastLowerDiagonalCount (s + 2) = s := by
  let d := gameF (s + 1) (s + 1)
  let z := d - 1
  have hdgt := gameRecurrenceModel.diagonal_gt (s + 1)
  have hz : z + 1 = d := by
    dsimp [z, d]
    omega
  have hdiag1 : gameF (s + 1) (s + 1) = z + 1 := by
    omega
  have hu0 := hU s hdip0
  have hdiag0 : gameF s s = z + 2 := by
    change d + 1 = gameF s s at hu0
    omega
  have hu1 := hU (s + 1) hdip1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by
    change gameF (s + 2) (s + 2) + 1 = d at hu1
    omega
  have hold : forall i, i < s -> gameF i i < z := by
    apply r55_margin_past_below
    simpa [d, z] using hmargin
  have countAt : forall t,
      (t = s ∨ t = s + 1 ∨ t = s + 2) ->
      PastLowerDiagonalCount t = s := by
    intro t ht
    have hrangeSub : List.range s ⊆ PastLowerDiagonalIndices t := by
      intro i hi
      have his := List.mem_range.mp hi
      apply mem_pastLowerDiagonalIndices_iff.mpr
      rcases ht with rfl | rfl | rfl
      · exact ⟨his, by have := hold i his; omega⟩
      · exact ⟨by omega, by have := hold i his; omega⟩
      · exact ⟨by omega, by have := hold i his; omega⟩
    have hindexSub : PastLowerDiagonalIndices t ⊆ List.range s := by
      intro i hi
      have hiData := mem_pastLowerDiagonalIndices_iff.mp hi
      apply List.mem_range.mpr
      rcases ht with rfl | rfl | rfl
      · exact hiData.1
      · apply Nat.lt_of_not_ge
        intro hnot
        have hiEq : i = s := by omega
        subst i
        omega
      · apply Nat.lt_of_not_ge
        intro hnot
        have hiCases : i = s ∨ i = s + 1 := by omega
        rcases hiCases with rfl | rfl <;> omega
    have hEq := r55_count_eq_of_mutual_subset
      List.nodup_range (pastLowerDiagonalIndices_nodup t)
      hrangeSub hindexSub
    change (PastLowerDiagonalIndices t).length = s
    simpa using hEq.symm
  refine ⟨?_, ?_, ?_⟩
  · exact countAt s (Or.inl rfl)
  · exact countAt (s + 1) (Or.inr (Or.inl rfl))
  · exact countAt (s + 2) (Or.inr (Or.inr rfl))

/-- The exact event-E echo staircase promised by the overlap ledger:
`W(s),W(s+1),W(s+2) = delta,delta+2,delta+4`. -/
theorem gameF_margin_eventE_overlap_echo_staircase
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip0 : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      exists j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hdip1 : gameF (s + 2) (s + 2) <
      gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    StrictRowEchoCount s = delta ∧
    StrictRowEchoCount (s + 1) = delta + 2 ∧
    StrictRowEchoCount (s + 2) = delta + 4 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip0 hmargin hdip1
  change EventEDefectPacketInvariant s d delta z at hInv
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hz : z + 1 = d := hInv.2.2.2.1
  have hu0 := hU s hdip0
  change d + 1 = gameF s s at hu0
  have hu1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hu1
  have hcounts := gameF_margin_eventE_past_lower_count_staircase
    hU hdip0 hmargin hdip1
  have hledger0 := gameF_overlap_ledger s
  have hledger1 := gameF_overlap_ledger (s + 1)
  have hledger2 := gameF_overlap_ledger (s + 2)
  omega

/-- Importing the unconditional envelope at the *second dipped row* gives
the sharp half-window bound.  The division-free consequence is especially
useful for the R53/R54 atom menu: every event E satisfies
`2*delta+10 <= s`. -/
theorem gameF_margin_eventE_second_dip_env_defect_bound
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip0 : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      exists j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hdip1 : gameF (s + 2) (s + 2) <
      gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    delta + (s + 3) / 2 + 4 <= s ∧
      2 * delta + 10 <= s := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip0 hmargin hdip1
  change EventEDefectPacketInvariant s d delta z at hInv
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hu1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hu1
  have henv := gameF_overlap_env_lower_bound (s + 2)
  constructor <;> omega

/-- After the envelope import, the former four-way R53 proof split has only
three top-level branches.  The separate `four-prefix` alternative was
selected only under `s < 2*delta+7`, whereas every event E now has
`2*delta+10 <= s`.  This removes that selector, not the possibility that
the four-prefix packet is nonempty inside the no-third-dip branch. -/
def EventER55EnvThreeAtom
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipPenultimateHitCertificate s delta z c b0 ∨
  EventEThirdDipExtraForbiddenCertificate s delta z c b0 ∨
  (EventENonDipSharedOwnerSaturationCertificate s delta z c b0 ∧
    2 * delta + 10 <= s)

theorem gameF_nonmax_eventE_R55_env_three_atoms
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 ∧
      EventER55EnvThreeAtom s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have htri := gameF_nonmax_eventE_R53_shared_owner_trichotomy
    hU hres
  change exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 ∧
    (EventEThirdDipPenultimateHitCertificate s delta z c b0 ∨
     EventEThirdDipExtraForbiddenCertificate s delta z c b0 ∨
     EventENonDipSharedOwnerSaturationCertificate s delta z c b0)
    at htri
  have hresData := hres
  change MarginEventECounterexample s ∧
      EventEDefectPacketInvariant s d delta z ∧ _ at hresData
  rcases hresData.1 with ⟨hdip0, hmargin, hdip1⟩
  have henv := gameF_margin_eventE_second_dip_env_defect_bound
    hU hdip0 hmargin hdip1
  change delta + (s + 3) / 2 + 4 <= s ∧
      2 * delta + 10 <= s at henv
  rcases htri with ⟨c, b0, hcross, hcase⟩
  refine ⟨c, b0, hcross, ?_⟩
  rcases hcase with hHit | hExtra | hNoDip
  · exact Or.inl hHit
  · exact Or.inr (Or.inl hExtra)
  · exact Or.inr (Or.inr ⟨hNoDip, henv.2⟩)

/-- If event E continues with a third dip, the next ledger step is exact as
well: `W(s+3)=delta+6`. -/
theorem gameF_margin_eventE_third_dip_overlap_echo
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip0 : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      exists j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hdip1 : gameF (s + 2) (s + 2) <
      gameF (s + 1) (s + 1))
    (hdip2 : gameF (s + 3) (s + 3) <
      gameF (s + 2) (s + 2)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    StrictRowEchoCount (s + 3) = delta + 6 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip0 hmargin hdip1
  change EventEDefectPacketInvariant s d delta z at hInv
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hz : z + 1 = d := hInv.2.2.2.1
  have hu1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hu1
  have hu2 := hU (s + 2) hdip2
  have hdiag3 : gameF (s + 3) (s + 3) = z - 1 := by
    change gameF (s + 3) (s + 3) + 1 =
      gameF (s + 2) (s + 2) at hu2
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    omega
  have hold : forall i, i < s -> gameF i i < z := by
    apply r55_margin_past_below
    simpa [d, z] using hmargin
  have hrangeSub : List.range s ⊆
      PastLowerDiagonalIndices (s + 3) := by
    intro i hi
    have his := List.mem_range.mp hi
    apply mem_pastLowerDiagonalIndices_iff.mpr
    constructor
    · omega
    · have hiz := hold i his
      apply Nat.lt_of_not_ge
      intro hnot
      have hEq : gameF i i = gameF (s + 3) (s + 3) := by
        omega
      have hiEq := diagonal_injective gameRecurrenceModel hEq
      omega
  have hindexSub : PastLowerDiagonalIndices (s + 3) ⊆
      List.range s := by
    intro i hi
    have hiData := mem_pastLowerDiagonalIndices_iff.mp hi
    apply List.mem_range.mpr
    apply Nat.lt_of_not_ge
    intro hnot
    have hiCases : i = s ∨ i = s + 1 ∨ i = s + 2 := by omega
    rcases hiCases with hiS | hiS1 | hiS2
    · subst i
      have hu0 := hU s hdip0
      change d + 1 = gameF s s at hu0
      omega
    · subst i
      omega
    · subst i
      omega
  have hcountEq := r55_count_eq_of_mutual_subset
    List.nodup_range
    (pastLowerDiagonalIndices_nodup (s + 3))
    hrangeSub hindexSub
  have hcount : PastLowerDiagonalCount (s + 3) = s := by
    simpa [PastLowerDiagonalCount] using hcountEq.symm
  have hledger := gameF_overlap_ledger (s + 3)
  have hgt3 := gameRecurrenceModel.diagonal_gt (s + 3)
  change s + 3 < gameF (s + 3) (s + 3) at hgt3
  omega

/-- A third consecutive dip imports one more envelope step.  Its
division-free form, `2*delta+15 <= s`, is the strong global budget attached
to both remaining third-dip atoms. -/
theorem gameF_margin_eventE_third_dip_env_defect_bound
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip0 : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      exists j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hdip1 : gameF (s + 2) (s + 2) <
      gameF (s + 1) (s + 1))
    (hdip2 : gameF (s + 3) (s + 3) <
      gameF (s + 2) (s + 2)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    delta + (s + 4) / 2 + 6 <= s ∧
      2 * delta + 15 <= s := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip0 hmargin hdip1
  change EventEDefectPacketInvariant s d delta z at hInv
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hu1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hu1
  have hu2 := hU (s + 2) hdip2
  change gameF (s + 3) (s + 3) + 1 =
    gameF (s + 2) (s + 2) at hu2
  have henv := gameF_overlap_env_lower_bound (s + 3)
  constructor <;> omega

#print axioms gameF_overlap_ledger
#print axioms gameF_overlap_echo_band
#print axioms gameF_echo_plus_low_le_past_lower
#print axioms gameF_overlap_env_lower_bound
#print axioms gameF_margin_eventE_overlap_echo_staircase
#print axioms gameF_margin_eventE_third_dip_overlap_echo
#print axioms gameF_margin_eventE_second_dip_env_defect_bound
#print axioms gameF_margin_eventE_third_dip_env_defect_bound
#print axioms gameF_nonmax_eventE_R55_env_three_atoms

end ChompLean
