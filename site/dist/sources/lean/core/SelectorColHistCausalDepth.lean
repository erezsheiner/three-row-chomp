import R66CeilingBase
import ColHistSlantedDeltaCore

set_option autoImplicit false

namespace ChompLean

/-!
Exact causal-depth core for the three-column midpoint selector.

For `q >= 2`, the two newest possible owner rows of a value `v=q+2` are rigid:

* row `v-1=q+1` hosts `v` at column `0` (`gameF_col0`);
* row `v-2=q` hosts `v` at column `2` (the column-2 rail proved below).

Fixed-row injectivity therefore excludes both rows from every column `c>2`.
This yields an exact truncation of `ColHistPred` and isolates row `v-3` as
the first row which can change the selector bit.  No midpoint theorem and no
finite receipt is used as a premise.
-/

/-- First nontrivial diagonal base: `d(1)=3`. -/
theorem gameF_one_one : gameF 1 1 = 3 := by
  apply gameF_value_of_source_mex (by omega)
  · omega
  · omega
  · intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have ha0 : a = 0 := by omega
      subst a
      simp [gameF_col0] at hvalue
    · rcases hC with ⟨b, hb, hvalue⟩
      have hb0 : b = 0 := by omega
      subst b
      rw [gameF_col0] at hvalue
      omega
  · intro k hkpos hklt
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · exact Or.inl ⟨0, by omega, by simp [gameF_col0]⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 1⟩

/-- Base of the constant column-1 rail. -/
theorem gameF_two_one : gameF 2 1 = 2 := by
  apply gameF_value_of_source_mex (by omega)
  · rw [gameF_one_one]
    omega
  · omega
  · intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hcases : a = 0 ∨ a = 1 := by omega
      rcases hcases with rfl | rfl
      · simp [gameF_col0] at hvalue
      · simp [gameF_one_one] at hvalue
    · rcases hC with ⟨b, hb, hvalue⟩
      have hb0 : b = 0 := by omega
      subst b
      rw [gameF_col0] at hvalue
      omega
  · intro k hkpos hklt
    have hk : k = 1 := by omega
    subst k
    exact Or.inl ⟨0, by omega, by simp [gameF_col0]⟩

/-- Constant column-1 rail: `F(q,1)=2` for every `q>=2`. -/
theorem gameF_col1_rail {q : Nat} (hq : 2 <= q) :
    gameF q 1 = 2 := by
  have hsmall : gameRecurrenceModel.f 2 1 < 2 + 1 := by
    change gameF 2 1 < 2 + 1
    rw [gameF_two_one]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 2) (r := 1) (by omega)
    hsmall (q - 2)
  change gameF (2 + (q - 2)) 1 = gameF 2 1 at hconst
  have hsum : 2 + (q - 2) = q := by omega
  rw [hsum, gameF_two_one] at hconst
  exact hconst

/-- Linear column-2 rail: `F(q,2)=q+2` for every `q>=2`.

The source at `(q,2)` contains `1` from row 0, `3` from the row-1
diagonal, `2` from the current column-1 rail, and `4,...,q+1` from earlier
column-2 rail entries.  The next value `q+2` is absent, so it is the MEX. -/
theorem gameF_col2_rail {q : Nat} (hq : 2 <= q) :
    gameF q 2 = q + 2 := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
      apply gameF_value_of_source_mex (by omega)
      · rintro ⟨h2q, hcarry⟩
        have hprev := ih (q - 1) (by omega) (by omega)
        rw [hprev] at hcarry
        omega
      · omega
      · intro hsource
        rcases hsource with hR | hC
        · rcases hR with ⟨a, haq, hvalue⟩
          by_cases ha0 : a = 0
          · subst a
            simp [gameF_col0] at hvalue
          · by_cases ha1 : a = 1
            · subst a
              simp [gameF_one_one] at hvalue
              omega
            · have ha2 : 2 <= a := by omega
              have hmin : min a 2 = 2 := Nat.min_eq_right ha2
              rw [hmin, ih a haq ha2] at hvalue
              omega
        · rcases hC with ⟨b, hb2, hvalue⟩
          have hcases : b = 0 ∨ b = 1 := by omega
          rcases hcases with rfl | rfl
          · rw [gameF_col0] at hvalue
            omega
          · rw [gameF_col1_rail hq] at hvalue
            omega
      · intro k hkpos hklt
        by_cases hk1 : k = 1
        · subst k
          exact Or.inl ⟨0, by omega, by simp [gameF_col0]⟩
        · by_cases hk2 : k = 2
          · subst k
            exact Or.inr ⟨1, by omega, gameF_col1_rail hq⟩
          · by_cases hk3 : k = 3
            · subst k
              exact Or.inl ⟨1, by omega, by simp [gameF_one_one]⟩
            · have hk4 : 4 <= k := by omega
              let a := k - 2
              have ha2 : 2 <= a := by omega
              have haq : a < q := by omega
              refine Or.inl ⟨a, haq, ?_⟩
              have hmin : min a 2 = 2 := Nat.min_eq_right ha2
              rw [hmin, ih a haq ha2]
              dsimp [a]
              omega

/-! ## Abstract history truncation -/

/-- Adding one owner row to `ColHistPred` is exactly an old-history/new-row
disjunction. -/
theorem colHistPred_succ_iff
    {f : Nat -> Nat -> Nat} {top c z : Nat} :
    ColHistPred f (top + 1) c z <->
      ColHistPred f top c z \/ (c <= top /\ f top c = z) := by
  constructor
  · rintro ⟨a, hca, hatop, hvalue⟩
    by_cases haold : a < top
    · exact Or.inl ⟨a, hca, haold, hvalue⟩
    · have hatopEq : a = top := by omega
      subst a
      exact Or.inr ⟨hca, hvalue⟩
  · intro h
    rcases h with hold | hnew
    · rcases hold with ⟨a, hca, hatop, hvalue⟩
      exact ⟨a, hca, by omega, hvalue⟩
    · exact ⟨top, hnew.1, by omega, hnew.2⟩

/-- If the two newly admitted rows cannot host `z` at admissible column
`c`, extending the history cutoff by two changes no membership bit. -/
theorem colHistPred_add_two_iff_of_new_rows_absent
    {f : Nat -> Nat -> Nat} {top c z : Nat}
    (hrow0 : c <= top -> f top c ≠ z)
    (hrow1 : c <= top + 1 -> f (top + 1) c ≠ z) :
    ColHistPred f (top + 2) c z <-> ColHistPred f top c z := by
  have hn0 : Not (c <= top /\ f top c = z) := by
    rintro ⟨hctop, hvalue⟩
    exact hrow0 hctop hvalue
  have hn1 : Not (c <= top + 1 /\ f (top + 1) c = z) := by
    rintro ⟨hctop, hvalue⟩
    exact hrow1 hctop hvalue
  rw [show top + 2 = (top + 1) + 1 by omega,
    colHistPred_succ_iff, colHistPred_succ_iff]
  simp [hn0, hn1]

/-! ## Exact game-level causal depth -/

/-- On row `q+1=v-1`, value `v=q+2` has its unique host at column 0. -/
theorem gameF_lag_one_host_only_col0
    {q c : Nat} (hcq : c <= q + 1)
    (hhost : gameF (q + 1) c = q + 2) :
    c = 0 := by
  have hzero : gameF (q + 1) 0 = q + 2 := by
    rw [gameF_col0]
  exact gameRecurrenceModel.fixed_q_injective hcq (by omega)
    (hhost.trans hzero.symm)

/-- On row `q=v-2`, value `v=q+2` has its unique host at column 2. -/
theorem gameF_lag_two_host_only_col2
    {q c : Nat} (hq : 2 <= q) (hcq : c <= q)
    (hhost : gameF q c = q + 2) :
    c = 2 := by
  exact gameRecurrenceModel.fixed_q_injective hcq hq
    (hhost.trans (gameF_col2_rail hq).symm)

/-- Exact two-row causal cutoff.  For every `c>2`, the two newest rows in
`ColHist_{c}(<v)` cannot be owners of `v`; hence the cutoff may move from
`v` to `v-2`. -/
theorem gameF_colHist_drop_newest_two
    {q c : Nat} (hq : 2 <= q) (hc : 2 < c) :
    ColHistPred gameF (q + 2) c (q + 2) <->
      ColHistPred gameF q c (q + 2) := by
  apply colHistPred_add_two_iff_of_new_rows_absent
  · intro hcq hhost
    have hcol := gameF_lag_two_host_only_col2 hq hcq hhost
    omega
  · intro hcq hhost
    have hcol := gameF_lag_one_host_only_col0 hcq hhost
    omega

/-- Strongest exact causal form: for `v=q+3` and `c>2`, full history below
`v` is old history below `v-3`, plus exactly the possible owner cell on row
`v-3`.  Rows `v-2` and `v-1` have disappeared by theorem, not assumption. -/
theorem gameF_colHist_causal_depth_three
    {q c : Nat} (hq : 1 <= q) (hc : 2 < c) :
    ColHistPred gameF (q + 3) c (q + 3) <->
      ColHistPred gameF q c (q + 3) \/
        (c <= q /\ gameF q c = q + 3) := by
  calc
    ColHistPred gameF (q + 3) c (q + 3) <->
        ColHistPred gameF (q + 1) c (q + 3) := by
          simpa [show q + 3 = (q + 1) + 2 by omega] using
            (gameF_colHist_drop_newest_two
              (q := q + 1) (c := c) (by omega) hc)
    _ <-> ColHistPred gameF q c (q + 3) \/
        (c <= q /\ gameF q c = q + 3) :=
      colHistPred_succ_iff

/-- Three adjacent selector tracks inherit the same exact causal depth as
soon as the leftmost column is greater than 2.  No definition or theorem
about the midpoint `g(v)` is needed. -/
theorem gameF_three_adjacent_colHist_causal_depth_three
    {q left : Nat} (hq : 1 <= q) (hleft : 2 < left) :
    (ColHistPred gameF (q + 3) left (q + 3) <->
      ColHistPred gameF q left (q + 3) \/
        (left <= q /\ gameF q left = q + 3)) /\
    (ColHistPred gameF (q + 3) (left + 1) (q + 3) <->
      ColHistPred gameF q (left + 1) (q + 3) \/
        (left + 1 <= q /\ gameF q (left + 1) = q + 3)) /\
    (ColHistPred gameF (q + 3) (left + 2) (q + 3) <->
      ColHistPred gameF q (left + 2) (q + 3) \/
        (left + 2 <= q /\ gameF q (left + 2) = q + 3)) := by
  exact ⟨gameF_colHist_causal_depth_three hq hleft,
    gameF_colHist_causal_depth_three hq (by omega),
    gameF_colHist_causal_depth_three hq (by omega)⟩

/-- Selector notation matching the finite audit.  The only geometric input
about the midpoint window is the elementary bound `2 < g-1`; no selector
correctness or midpoint-uniqueness theorem is assumed. -/
theorem gameF_selector_window_drop_newest_two
    {v g : Nat} (hv : 4 <= v) (hg : 2 < g - 1) :
    (ColHistPred gameF v (g - 1) v <->
      ColHistPred gameF (v - 2) (g - 1) v) /\
    (ColHistPred gameF v g v <->
      ColHistPred gameF (v - 2) g v) /\
    (ColHistPred gameF v (g + 1) v <->
      ColHistPred gameF (v - 2) (g + 1) v) := by
  have hq : 2 <= v - 2 := by omega
  have hsum : v - 2 + 2 = v := by omega
  constructor
  · simpa [hsum] using
      (gameF_colHist_drop_newest_two
        (q := v - 2) (c := g - 1) hq hg)
  constructor
  · simpa [hsum] using
      (gameF_colHist_drop_newest_two
        (q := v - 2) (c := g) hq (by omega))
  · simpa [hsum] using
      (gameF_colHist_drop_newest_two
        (q := v - 2) (c := g + 1) hq (by omega))

#print axioms gameF_col1_rail
#print axioms gameF_col2_rail
#print axioms colHistPred_add_two_iff_of_new_rows_absent
#print axioms gameF_colHist_drop_newest_two
#print axioms gameF_colHist_causal_depth_three
#print axioms gameF_three_adjacent_colHist_causal_depth_three
#print axioms gameF_selector_window_drop_newest_two

end ChompLean
