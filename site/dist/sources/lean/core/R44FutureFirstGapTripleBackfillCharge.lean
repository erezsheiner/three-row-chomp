import R43FutureDiagonalSourceCapacityCollapse

set_option autoImplicit false

namespace ChompLean

/-!
R44: a genuine three-slot backfill charge for the sharply near
future-first-gap window left by R43.

Write `x=d(s+1)+1`.  The old row `s` hosts both adjacent values `x-1` and
`x`: the latter is part of the future-loss certificate, while exact MEX
forces the former and diagonal injectivity rules out an old diagonal
source.  Neither value occurs in the strict prefix of row `s+1`.

The new prefix has `s+1` pairwise-distinct cells and the old prefix only
`s`.  Since two old slots are unusable, at most `s-2` new cells can be
carried from the old prefix.  Hence at least three new cells are genuine
backfills.  Exact MEX at the old diagonal identifies every backfill with a
past diagonal value `d(i)`, and diagonal/general no-attack localizes its
column to `b<=i<s`.

For the actual game, encoding geometry sharpens this to `b<i`.  Moreover a
past diagonal value re-emitted on row `s+1` must exceed `s+1`; otherwise it
would simultaneously be a row-start value.  R43 source capacity then puts
each of the three distinct owners in the strict upper half `s<2*i`.  Three
such owners below `s` exist only when `7<=s`.

No RM2 or UnitDip assumption is used.
-/

private theorem r44_nodup_map_of_injective_on
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) (xs : List alpha)
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

/-- In a genuine encoding, a diagonal value can never be re-emitted later
in its owner's own lower column.  Depending on whether the value is below
or above the later row, the later P-position is a row start or a general
position; in both cases it moves directly to the diagonal P-position. -/
theorem encoding_diagonal_value_not_reemitted_in_owner_column
    {f : Nat -> Nat -> Nat} (hf : Encodes f) {i t : Nat}
    (hit : i < t) :
    f t i ≠ f i i := by
  intro hEq
  let p := f i i
  have hip : i < p := by
    dsimp [p]
    exact encoded_gt hf (Nat.le_refl i)
  have hDiagP : IsP (lowerSquarePos p i (Nat.le_of_lt hip)) := by
    dsimp [p]
    simpa [lowerSquarePos] using
      (encoded_isP_of_ge hf (Nat.le_refl i) (Nat.le_of_lt hip))
  by_cases hpt : p < t
  · have hLaterP : IsP (rowStartPos p i (Nat.le_of_lt hip)) := by
      have hsmall : f t i < t := by simpa [p, hEq] using hpt
      simpa [p, hEq] using
        (encoded_isP_of_lt hf (Nat.le_of_lt hit) hsmall)
    have hmove :
        Move (rowStartPos p i (Nat.le_of_lt hip))
          (lowerSquarePos p i (Nat.le_of_lt hip)) := by
      simpa [rowStartPos, lowerSquarePos] using
        (move_second_to_min
          (p := p) (q := p) (a := i) (r := i)
          (Nat.le_of_lt hip) (Nat.le_refl p) hip)
    exact (isP_no_move_to_P hLaterP hmove) hDiagP
  · have htp : t <= p := Nat.le_of_not_gt hpt
    have hLaterP : IsP (mkPos p t i htp (Nat.le_of_lt hit)) := by
      have hlarge : t <= f t i := by simpa [p, hEq] using htp
      simpa [p, hEq] using
        (encoded_isP_of_ge hf (Nat.le_of_lt hit) hlarge)
    have hmove :
        Move (mkPos p t i htp (Nat.le_of_lt hit))
          (lowerSquarePos p i (Nat.le_of_lt hip)) := by
      simpa [lowerSquarePos] using
        (move_second_to_min
          (p := p) (q := t) (a := i) (r := i)
          (Nat.le_of_lt hit) htp hit)
    exact (isP_no_move_to_P hLaterP hmove) hDiagP

/-- A past diagonal value re-emitted on a later row of the actual game must
lie strictly above that later row.  Otherwise the later encoding is a row
start for the same value (directly at equality, or via completeness below
the row), contradicting diagonal/row-start disjointness. -/
theorem game_past_diagonal_reemission_is_high
    {i t b : Nat}
    (hbt : b <= t)
    (hvalue : gameF i i = gameF t b) :
    t < gameF i i := by
  let p := gameF i i
  have hbp : b < p := by
    have hgt := gameRecurrenceModel.value_gt_index hbt
    change b < gameF t b at hgt
    simpa [p, hvalue] using hgt
  apply Nat.lt_of_not_ge
  intro hle
  have hpt : p <= t := by simpa [p] using hle
  have hstart : gameF p b = p := by
    by_cases hstrict : p < t
    · have hsmall : gameF t b < t := by
        rw [← hvalue]
        exact hstrict
      have hP : IsP (rowStartPos p b (Nat.le_of_lt hbp)) := by
        simpa [p, hvalue] using
          (encoded_isP_of_lt game_encodes hbt hsmall)
      exact game_complete.2
        (p := p) (q := p) (r := b)
        (Nat.le_refl p) (Nat.le_of_lt hbp)
        (by simpa [rowStartPos] using hP)
    · have hEq : p = t := by omega
      have : gameF t b = p := by simpa [p] using hvalue.symm
      simpa [hEq] using this
  exact disjoint_D_S gameRecurrenceModel
    ⟨i, by rfl⟩ ⟨b, hbp, hstart⟩

/-- Besides the future first gap itself, the old row already hosts the new
diagonal value immediately below it. -/
theorem future_first_gap_old_row_hosts_adjacent_pair
    (M : RecurrenceModel) {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s) :
    exists cPrev cGap,
      cPrev < s /\ cGap < s /\ cPrev ≠ cGap /\
      M.f s cPrev = M.f (s + 1) (s + 1) /\
      M.f s cGap = DipFirstGap M s := by
  let x := DipFirstGap M s
  let y := M.f (s + 1) (s + 1)
  have hyPos : 0 < y := by
    dsimp [y]
    have hgt := M.diagonal_gt (s + 1)
    omega
  have hyOld : y < M.f s s := by
    have hxOld := hFuture.1
    dsimp [x, y, DipFirstGap] at hxOld ⊢
    omega
  have hyB : B M.f s s y :=
    M.mex_no_skip (Nat.le_refl s) (M.diagonal_gt s)
      hyPos hyOld
  have hyC : C M.f s s y := by
    rcases hyB with hR | hC
    · rcases hR with ⟨i, his, hvalue⟩
      have hmin : min i s = i := Nat.min_eq_left (Nat.le_of_lt his)
      rw [hmin] at hvalue
      have hidx := diagonal_injective M hvalue
      omega
    · exact hC
  rcases hyC with ⟨cPrev, hcPrev, hPrev⟩
  rcases hFuture.2 with
    ⟨a, _ha, _haOwner, hOldGap, _hNewGap⟩
  rcases hOldGap with ⟨cGap, hcGap, hGap⟩
  have hcNe : cPrev ≠ cGap := by
    intro hEq
    subst cGap
    rw [hPrev] at hGap
    dsimp [x, y, DipFirstGap] at hGap
    omega
  exact ⟨cPrev, cGap, hcPrev, hcGap, hcNe, hPrev, hGap⟩

/-- The terminal new-prefix cell cannot be a past-diagonal backfill, so it
must carry a value already present in the old prefix. -/
theorem future_first_gap_terminal_column_is_old_prefix_carry
    (M : RecurrenceModel) {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s) :
    exists c,
      c < s /\
      M.f s c = M.f (s + 1) s /\
      M.f (s + 1) s < M.f (s + 1) (s + 1) := by
  let v := M.f (s + 1) s
  have hvLe : v <= M.f (s + 1) (s + 1) :=
    diagonalMaximal M (by omega)
  have hvNe : v ≠ M.f (s + 1) (s + 1) := by
    intro hEq
    have hcol := M.fixed_q_injective
      (q := s + 1) (b₁ := s) (b₂ := s + 1)
      (by omega) (Nat.le_refl _) hEq
    omega
  have hvNext : v < M.f (s + 1) (s + 1) := by omega
  have hvPos : 0 < v := by
    dsimp [v]
    have hgt := M.value_gt_index (q := s + 1) (r := s) (by omega)
    omega
  have hvOld : v < M.f s s := by
    have hxOld := hFuture.1
    dsimp [DipFirstGap] at hxOld
    omega
  have hvB : B M.f s s v :=
    M.mex_no_skip (Nat.le_refl s) (M.diagonal_gt s)
      hvPos hvOld
  have hvC : C M.f s s v := by
    rcases hvB with hR | hC
    · rcases hR with ⟨i, his, hvalue⟩
      have hmin : min i s = i := Nat.min_eq_left (Nat.le_of_lt his)
      rw [hmin] at hvalue
      exact False.elim
        (M.diagonal_general_no_attack his (by omega) hvalue)
    · exact hC
  rcases hvC with ⟨c, hc, hcarry⟩
  exact ⟨c, hc, hcarry, hvNext⟩

/-- At least three columns of the new prefix are not carries from the old
prefix.  Each is a localized past-diagonal backfill. -/
theorem future_first_gap_forces_three_past_diagonal_backfills
    (M : RecurrenceModel) {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s) :
    exists bs : List Nat,
      bs.Nodup /\
      3 <= bs.length /\
      forall b, b ∈ bs ->
        b < s + 1 /\
        Not (C M.f s s (M.f (s + 1) b)) /\
        exists i,
          b <= i /\ i < s /\
          M.f i i = M.f (s + 1) b := by
  classical
  rcases future_first_gap_old_row_hosts_adjacent_pair M hFuture with
    ⟨cPrev, cGap, hcPrev, hcGap, hcNe, hPrev, hGap⟩
  let isCarry : Nat -> Bool := fun b =>
    decide (C M.f s s (M.f (s + 1) b))
  let carryCols := (List.range (s + 1)).filter isCarry
  let backfillCols := (List.range (s + 1)).filter
    (fun b => decide (Not (isCarry b = true)))
  have hcarryRows : forall b, b ∈ carryCols ->
      exists c, c < s /\ M.f s c = M.f (s + 1) b := by
    intro b hb
    have hbFilter := List.mem_filter.mp hb
    have hC : C M.f s s (M.f (s + 1) b) := by
      simpa [isCarry] using hbFilter.2
    exact hC
  let oldHost : Nat -> Nat := fun b =>
    if hb : b ∈ carryCols then Classical.choose (hcarryRows b hb) else 0
  have hhost : forall b, b ∈ carryCols ->
      oldHost b < s /\ M.f s (oldHost b) = M.f (s + 1) b := by
    intro b hb
    dsimp [oldHost]
    rw [dif_pos hb]
    exact Classical.choose_spec (hcarryRows b hb)
  have hcarryNodup : carryCols.Nodup := by
    exact List.filter_sublist.nodup List.nodup_range
  have hhostInj : forall b₁, b₁ ∈ carryCols ->
      forall b₂, b₂ ∈ carryCols ->
      oldHost b₁ = oldHost b₂ -> b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ hEq
    have hb₁Range := (List.mem_filter.mp hb₁).1
    have hb₂Range := (List.mem_filter.mp hb₂).1
    have hvalue : M.f (s + 1) b₁ = M.f (s + 1) b₂ := by
      rw [← (hhost b₁ hb₁).2, ← (hhost b₂ hb₂).2, hEq]
    exact M.fixed_q_injective
      (Nat.le_of_lt (List.mem_range.mp hb₁Range))
      (Nat.le_of_lt (List.mem_range.mp hb₂Range)) hvalue
  have hmapNodup : (carryCols.map oldHost).Nodup :=
    r44_nodup_map_of_injective_on oldHost carryCols
      hcarryNodup hhostInj
  have hnewPrevAbsent :
      Not (B M.f (s + 1) (s + 1) (M.f (s + 1) (s + 1))) :=
    (recurrence_diagonal_exact_mex M (s + 1)).2.1
  have hnewGapAbsent :
      Not (B M.f (s + 1) (s + 1) (DipFirstGap M s)) :=
    hFuture.2.choose_spec.2.2.2
  have hcPrevNotMap : cPrev ∉ carryCols.map oldHost := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, hbEq⟩
    have hbRange := List.mem_range.mp (List.mem_filter.mp hb).1
    have hnewEq : M.f (s + 1) b = M.f (s + 1) (s + 1) := by
      rw [← (hhost b hb).2, hbEq, hPrev]
    exact hnewPrevAbsent (Or.inr ⟨b, hbRange, hnewEq⟩)
  have hcGapNotMap : cGap ∉ carryCols.map oldHost := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, hbEq⟩
    have hbRange := List.mem_range.mp (List.mem_filter.mp hb).1
    have hnewEq : M.f (s + 1) b = DipFirstGap M s := by
      rw [← (hhost b hb).2, hbEq, hGap]
    exact hnewGapAbsent (Or.inr ⟨b, hbRange, hnewEq⟩)
  have hreservedNodup :
      (cPrev :: cGap :: carryCols.map oldHost).Nodup := by
    rw [List.nodup_cons, List.nodup_cons]
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with hEq | hMap
      · exact hcNe hEq
      · exact hcPrevNotMap hMap
    · exact ⟨hcGapNotMap, hmapNodup⟩
  have hreservedSubset :
      cPrev :: cGap :: carryCols.map oldHost ⊆ List.range s := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.mem_range.mpr hcPrev
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.mem_range.mpr hcGap
    rcases List.mem_map.mp hc with ⟨b, hb, rfl⟩
    exact List.mem_range.mpr (hhost b hb).1
  have hcarryCap := nodup_subset_length_le
    hreservedNodup hreservedSubset
  have hcarryLen : carryCols.length + 2 <= s := by
    simp only [List.length_cons, List.length_map, List.length_range] at hcarryCap
    omega
  have hpartition :
      (List.range (s + 1)).length =
        carryCols.length + backfillCols.length := by
    have hraw := List.length_eq_countP_add_countP isCarry
      (l := List.range (s + 1))
    simp only [List.countP_eq_length_filter] at hraw
    simpa [carryCols, backfillCols] using hraw
  have hbackfillLen : 3 <= backfillCols.length := by
    simp only [List.length_range] at hpartition
    omega
  have hbackfillNodup : backfillCols.Nodup := by
    exact List.filter_sublist.nodup List.nodup_range
  refine ⟨backfillCols, hbackfillNodup, hbackfillLen, ?_⟩
  intro b hb
  have hbFilter := List.mem_filter.mp hb
  have hbRange : b < s + 1 := List.mem_range.mp hbFilter.1
  have hnotCarry : Not (C M.f s s (M.f (s + 1) b)) := by
    simpa [isCarry] using hbFilter.2
  let v := M.f (s + 1) b
  have hvLe : v <= M.f (s + 1) (s + 1) :=
    diagonalMaximal M (Nat.le_of_lt hbRange)
  have hvNe : v ≠ M.f (s + 1) (s + 1) := by
    intro hEq
    have hcol := M.fixed_q_injective
      (Nat.le_of_lt hbRange) (Nat.le_refl _) hEq
    omega
  have hvNext : v < M.f (s + 1) (s + 1) := by omega
  have hvPos : 0 < v := by
    dsimp [v]
    have hgt := M.value_gt_index (Nat.le_of_lt hbRange)
    omega
  have hvOld : v < M.f s s := by
    have hxOld := hFuture.1
    dsimp [v, DipFirstGap] at hxOld ⊢
    omega
  have hvB : B M.f s s v :=
    M.mex_no_skip (Nat.le_refl s) (M.diagonal_gt s)
      hvPos hvOld
  have hvR : R M.f s s v := by
    rcases hvB with hR | hC
    · exact hR
    · exact False.elim (hnotCarry hC)
  rcases hvR with ⟨i, his, hvalue⟩
  have hmin : min i s = i := Nat.min_eq_left (Nat.le_of_lt his)
  rw [hmin] at hvalue
  have hbi : b <= i := by
    apply Nat.le_of_not_gt
    intro hib
    exact M.diagonal_general_no_attack hib
      (Nat.le_of_lt hbRange) hvalue
  exact ⟨hbRange, hnotCarry, i, hbi, his, hvalue⟩

/-- In the actual game the localization is strict and high: a backfilled
diagonal value cannot use its owner's own column, cannot lie at or below the
new row, and therefore its owner lies in the strict upper half of `[0,s)`. -/
theorem game_future_first_gap_forces_three_strict_diagonal_backfills
    {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    exists bs : List Nat,
      bs.Nodup /\
      3 <= bs.length /\
      forall b, b ∈ bs ->
        b < s + 1 /\
        Not (C gameF s s (gameF (s + 1) b)) /\
        exists i,
          b < i /\ i < s /\
          s + 1 < gameF i i /\
          s < i + i /\
          gameF i i = gameF (s + 1) b := by
  rcases future_first_gap_forces_three_past_diagonal_backfills
      gameRecurrenceModel hFuture with
    ⟨bs, hbsNodup, hbsLen, hbs⟩
  refine ⟨bs, hbsNodup, hbsLen, ?_⟩
  intro b hb
  rcases hbs b hb with
    ⟨hbRange, hnotCarry, i, hbi, his, hvalue⟩
  have hbiStrict : b < i := by
    have hne : b ≠ i := by
      intro hEq
      subst i
      exact
        (encoding_diagonal_value_not_reemitted_in_owner_column
          game_encodes (i := b) (t := s + 1) (by omega)) hvalue.symm
    exact Nat.lt_of_le_of_ne hbi hne
  have hhigh : s + 1 < gameF i i :=
    game_past_diagonal_reemission_is_high
      (i := i) (t := s + 1) (b := b)
      (Nat.le_of_lt hbRange) hvalue
  have hcap := recurrence_diagonal_source_capacity
    gameRecurrenceModel i
  have hupperHalf : s < i + i := by
    change gameF i i <= i + i + 1 at hcap
    omega
  exact ⟨hbRange, hnotCarry, i, hbiStrict, his,
    hhigh, hupperHalf, hvalue⟩

private theorem r44_nodup_length_three_extract
    {xs : List Nat} (hxs : xs.Nodup) (hlen : 3 <= xs.length) :
    exists x y z,
      x ∈ xs /\ y ∈ xs /\ z ∈ xs /\
      x ≠ y /\ x ≠ z /\ y ≠ z := by
  cases xs with
  | nil => simp at hlen
  | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y xs =>
          cases xs with
          | nil => simp at hlen
          | cons z tail =>
              have hxNot : x ∉ y :: z :: tail :=
                (List.nodup_cons.mp hxs).1
              have hyNot : y ∉ z :: tail :=
                (List.nodup_cons.mp
                  (List.nodup_cons.mp hxs).2).1
              have hxy : x ≠ y := by
                intro hEq
                apply hxNot
                simp [hEq]
              have hxz : x ≠ z := by
                intro hEq
                apply hxNot
                simp [hEq]
              have hyz : y ≠ z := by
                intro hEq
                apply hyNot
                simp [hEq]
              exact ⟨x, y, z, by simp, by simp, by simp,
                hxy, hxz, hyz⟩

/-- The three high backfill owners are distinct strict-upper-half indices.
There are fewer than three such indices below any `s<7`; hence the actual
future-first-gap branch cannot begin before row seven. -/
theorem game_future_first_gap_requires_row_seven
    {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    7 <= s := by
  rcases game_future_first_gap_forces_three_strict_diagonal_backfills
      hFuture with ⟨bs, hbsNodup, hbsLen, hbs⟩
  rcases r44_nodup_length_three_extract hbsNodup hbsLen with
    ⟨b₀, b₁, b₂, hb₀Mem, hb₁Mem, hb₂Mem,
      hb₀₁, hb₀₂, hb₁₂⟩
  rcases hbs b₀ hb₀Mem with
    ⟨hb₀Range, _hb₀NotCarry, i₀, _hb₀i, hi₀s,
      _hi₀High, hi₀Half, hvalue₀⟩
  rcases hbs b₁ hb₁Mem with
    ⟨hb₁Range, _hb₁NotCarry, i₁, _hb₁i, hi₁s,
      _hi₁High, hi₁Half, hvalue₁⟩
  rcases hbs b₂ hb₂Mem with
    ⟨hb₂Range, _hb₂NotCarry, i₂, _hb₂i, hi₂s,
      _hi₂High, hi₂Half, hvalue₂⟩
  have hi₀₁ : i₀ ≠ i₁ := by
    intro hEq
    subst i₁
    have hnewEq : gameF (s + 1) b₀ = gameF (s + 1) b₁ :=
      hvalue₀.symm.trans hvalue₁
    have hbEq := gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hb₀Range) (Nat.le_of_lt hb₁Range) hnewEq
    exact hb₀₁ hbEq
  have hi₀₂ : i₀ ≠ i₂ := by
    intro hEq
    subst i₂
    have hnewEq : gameF (s + 1) b₀ = gameF (s + 1) b₂ :=
      hvalue₀.symm.trans hvalue₂
    have hbEq := gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hb₀Range) (Nat.le_of_lt hb₂Range) hnewEq
    exact hb₀₂ hbEq
  have hi₁₂ : i₁ ≠ i₂ := by
    intro hEq
    subst i₂
    have hnewEq : gameF (s + 1) b₁ = gameF (s + 1) b₂ :=
      hvalue₁.symm.trans hvalue₂
    have hbEq := gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hb₁Range) (Nat.le_of_lt hb₂Range) hnewEq
    exact hb₁₂ hbEq
  omega

/-- The triple strict-backfill charge removes the extremal `s=3` pattern
left open by R43.  A future-first-gap episode in the actual game can start
only at row four or later. -/
theorem game_future_first_gap_requires_row_four
    {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    4 <= s := by
  rcases game_future_first_gap_forces_three_strict_diagonal_backfills
      hFuture with ⟨bs, hbsNodup, hbsLen, hbs⟩
  have hsubset : bs ⊆ List.range (s - 1) := by
    intro b hb
    rcases hbs b hb with
      ⟨_hbRange, _hnotCarry, i, hbi, his,
        _hhigh, _hhalf, _hvalue⟩
    exact List.mem_range.mpr (by omega)
  have hcap := nodup_subset_length_le hbsNodup hsubset
  simp only [List.length_range] at hcap
  omega

/-- Complementary exclusion form for base-case use. -/
theorem game_no_future_first_gap_before_row_four
    {s : Nat} (hs : s < 4) :
    Not (DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) := by
  intro hFuture
  have hfour := game_future_first_gap_requires_row_four hFuture
  omega

/-- Strong exclusion form supplied by the high-owner refinement. -/
theorem game_no_future_first_gap_before_row_seven
    {s : Nat} (hs : s < 7) :
    Not (DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) := by
  intro hFuture
  have hseven := game_future_first_gap_requires_row_seven hFuture
  omega

/-- Consolidated R43--R44 window: any surviving actual-game future first
gap starts at row at least seven and has an owner in `s+2 <= a < 2*s`. -/
theorem game_future_first_gap_R44_reduced_window
    {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    7 <= s /\
      DipFirstGap gameRecurrenceModel s <= s + s /\
      exists a,
        s + 2 <= a /\
        a + 1 <= s + s /\
        a <= gameF (s + 1) (s + 1) /\
        gameF a a = DipFirstGap gameRecurrenceModel s := by
  rcases future_first_gap_source_capacity_collapse
      gameRecurrenceModel hFuture with
    ⟨_hthree, hgap, a, haLower, haUpper, haNext, haOwner⟩
  exact ⟨game_future_first_gap_requires_row_seven hFuture,
    hgap, a, haLower, haUpper, haNext, haOwner⟩

#print axioms encoding_diagonal_value_not_reemitted_in_owner_column
#print axioms game_past_diagonal_reemission_is_high
#print axioms future_first_gap_old_row_hosts_adjacent_pair
#print axioms future_first_gap_terminal_column_is_old_prefix_carry
#print axioms future_first_gap_forces_three_past_diagonal_backfills
#print axioms game_future_first_gap_forces_three_strict_diagonal_backfills
#print axioms game_future_first_gap_requires_row_seven
#print axioms game_future_first_gap_requires_row_four
#print axioms game_no_future_first_gap_before_row_four
#print axioms game_no_future_first_gap_before_row_seven
#print axioms game_future_first_gap_R44_reduced_window

end ChompLean
