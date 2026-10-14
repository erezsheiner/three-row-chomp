import R66StageA
import EventEPacketSourceCapacity
import R43FutureDiagonalSourceCapacityCollapse
import GameFCol5Rail
import EarlyOddAffineRails
import R200FloorPlusFromDiagDoubleSlack
import R198B43OwnerLeftAttack

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# The sharp interior ceiling

This is the first load-bearing step of the positional proof of
`ActualDiagDoubleSlack`.  The apparent circularity in the prose proof is
resolved by one strong induction on the source level.  Before treating a
cell at level `s`, the same induction already gives the sharp interior
ceiling below `s`; that is enough to improve the diagonal source bound from
`2*a+1` to `2*a` whenever `2*a < s`.
-/

/-- At source levels strictly below `s`, the sharp interior-cell ceiling
also rules out the last unit of the generic diagonal source-capacity bound. -/
private theorem gameF_diagonal_tight_below_of_interior_below
    {s a : Nat}
    (ha : 2 <= a)
    (has : 2 * a < s)
    (hinterior : forall q r, q + r < s -> 3 <= r -> r < q ->
      gameF q r <= q + r) :
    gameF a a <= 2 * a := by
  have hcap := recurrence_diagonal_source_capacity gameRecurrenceModel a
  change gameF a a <= a + a + 1 at hcap
  by_cases hle : gameF a a <= 2 * a
  · exact hle
  exfalso
  have heq : gameF a a = 2 * a + 1 := by omega
  have hsource : B gameF a a (2 * a) := by
    apply gameRecurrenceModel.mex_no_skip (Nat.le_refl a)
    · change a < gameF a a
      rw [heq]
      omega
    · omega
    · change 2 * a < gameF a a
      rw [heq]
      omega
  rcases hsource with hR | hC
  · rcases hR with ⟨t, hta, hval⟩
    have hmin : min t a = t := Nat.min_eq_left (Nat.le_of_lt hta)
    rw [hmin] at hval
    have htcap := recurrence_diagonal_source_capacity gameRecurrenceModel t
    change gameF t t <= t + t + 1 at htcap
    omega
  · rcases hC with ⟨b, hba, hval⟩
    by_cases hb0 : b = 0
    · subst b
      rw [gameF_col0] at hval
      omega
    · by_cases hb1 : b = 1
      · subst b
        rw [gameF_col1_rail (q := a) ha] at hval
        omega
      · by_cases hb2 : b = 2
        · subst b
          rw [gameF_col2_rail (q := a) ha] at hval
          omega
        · have hb3 : 3 <= b := by omega
          have hcell := hinterior a b (by omega) hb3 hba
          omega

/-- **T1 / NoInteriorCeiling.**  Every strict interior cell from column
three onward misses the generic source-capacity ceiling by one:

`3 <= c < r  ->  gameF r c <= r+c`.

No diagonal ceiling is assumed.  The proof simultaneously derives the
tight `d(c)<=2c` fact needed at the column-bottom source. -/
theorem gameF_noInteriorCeiling :
    forall q r, 3 <= r -> r < q -> gameF q r <= q + r := by
  intro q r hr hrq
  let s := q + r
  have hmain : forall s q r, q + r = s -> 3 <= r -> r < q ->
      gameF q r <= q + r := by
    intro s
    induction s using Nat.strongRecOn with
    | ind s ih =>
        intro q r hsum hr hrq
        by_cases hle : gameF q r <= q + r
        · exact hle
        · have hhigh : q < gameF q r := by omega
          have hcap := high_cell_output_source_capacity gameRecurrenceModel
            (q := q) (r := r) (m := gameF q r) (Nat.le_of_lt hrq)
            hhigh rfl
          have hout : gameF q r = q + r + 1 := by omega
          have hsource : B gameF q r (q + r) := by
            apply gameRecurrenceModel.mex_no_skip (Nat.le_of_lt hrq)
            · change q < gameF q r
              rw [hout]
              omega
            · omega
            · change q + r < gameF q r
              rw [hout]
              omega
          have hinterior : forall q' r', q' + r' < s ->
              3 <= r' -> r' < q' -> gameF q' r' <= q' + r' := by
            intro q' r' hlt hr' hrq'
            exact ih (q' + r') hlt q' r' rfl hr' hrq'
          rcases hsource with hR | hC
          · rcases hR with ⟨a, haq, hval⟩
            by_cases har : a < r
            · have hmin : min a r = a := Nat.min_eq_left (Nat.le_of_lt har)
              rw [hmin] at hval
              have hacap := recurrence_diagonal_source_capacity
                gameRecurrenceModel a
              change gameF a a <= a + a + 1 at hacap
              omega
            · by_cases hae : a = r
              · subst a
                have hdiag :=
                  gameF_diagonal_tight_below_of_interior_below
                    (s := s) (a := r) (by omega) (by omega) hinterior
                have hmin : min r r = r := Nat.min_self r
                rw [hmin] at hval
                omega
              · have hra : r < a := by omega
                have hmin : min a r = r := Nat.min_eq_right (Nat.le_of_lt hra)
                rw [hmin] at hval
                have hcell := hinterior a r (by omega) hr hra
                omega
          · rcases hC with ⟨b, hbr, hval⟩
            by_cases hb0 : b = 0
            · subst b
              rw [gameF_col0] at hval
              omega
            · by_cases hb1 : b = 1
              · subst b
                rw [gameF_col1_rail (q := q) (by omega)] at hval
                omega
              · by_cases hb2 : b = 2
                · subst b
                  rw [gameF_col2_rail (q := q) (by omega)] at hval
                  omega
                · have hb3 : 3 <= b := by omega
                  have hcell := hinterior q b (by omega) hb3 (by omega)
                  omega
  exact hmain s q r rfl hr hrq

/-- The tight diagonal source-capacity bound used by the saturation lemmas. -/
theorem gameF_diagonal_tight {a : Nat} (ha : 2 <= a) :
    gameF a a <= 2 * a := by
  apply gameF_diagonal_tight_below_of_interior_below
      (s := 2 * a + 1) ha (by omega)
  intro q r _hlevel hr hrq
  exact gameF_noInteriorCeiling q r hr hrq

/-- **ES / EvenSat forcing.**  An even-saturated diagonal can obtain its
predecessor only from the penultimate cell in the same row. -/
theorem gameF_evenSat_forces_ceil1 {a : Nat}
    (ha : 4 <= a) (hsat : gameF a a = 2 * a) :
    gameF a (a - 1) = 2 * a - 1 := by
  have hsource : B gameF a a (2 * a - 1) := by
    apply gameRecurrenceModel.mex_no_skip (Nat.le_refl a)
    · change a < gameF a a
      rw [hsat]
      omega
    · omega
    · change 2 * a - 1 < gameF a a
      rw [hsat]
      omega
  rcases hsource with hR | hC
  · rcases hR with ⟨t, hta, hval⟩
    have hmin : min t a = t := Nat.min_eq_left (Nat.le_of_lt hta)
    rw [hmin] at hval
    by_cases ht0 : t = 0
    · subst t
      rw [gameF_zero_zero] at hval
      omega
    · by_cases ht1 : t = 1
      · subst t
        rw [gameF_one_one] at hval
        omega
      · have ht2 : 2 <= t := by omega
        have htcap := gameF_diagonal_tight ht2
        omega
  · rcases hC with ⟨b, hba, hval⟩
    by_cases hb0 : b = 0
    · subst b
      rw [gameF_col0] at hval
      omega
    · by_cases hb1 : b = 1
      · subst b
        rw [gameF_col1_rail (q := a) (by omega)] at hval
        omega
      · by_cases hb2 : b = 2
        · subst b
          rw [gameF_col2_rail (q := a) (by omega)] at hval
          omega
        · have hb3 : 3 <= b := by omega
          have hcell := gameF_noInteriorCeiling a b hb3 hba
          have hbeq : b = a - 1 := by omega
          subst b
          exact hval

/-- **OS / OddSat forcing.**  An odd-saturated diagonal has exactly the
three positional predecessor routes used by the ceiling chain. -/
theorem gameF_oddSat_forces_three {a : Nat}
    (ha : 5 <= a) (hsat : gameF a a = 2 * a - 1) :
    gameF (a - 1) (a - 1) = 2 * a - 2 \/
      gameF a (a - 2) = 2 * a - 2 \/
      gameF a (a - 1) = 2 * a - 2 := by
  have hsource : B gameF a a (2 * a - 2) := by
    apply gameRecurrenceModel.mex_no_skip (Nat.le_refl a)
    · change a < gameF a a
      rw [hsat]
      omega
    · omega
    · change 2 * a - 2 < gameF a a
      rw [hsat]
      omega
  rcases hsource with hR | hC
  · rcases hR with ⟨t, hta, hval⟩
    have hmin : min t a = t := Nat.min_eq_left (Nat.le_of_lt hta)
    rw [hmin] at hval
    by_cases ht0 : t = 0
    · subst t
      rw [gameF_zero_zero] at hval
      omega
    · by_cases ht1 : t = 1
      · subst t
        rw [gameF_one_one] at hval
        omega
      · have ht2 : 2 <= t := by omega
        have htcap := gameF_diagonal_tight ht2
        have hteq : t = a - 1 := by omega
        subst t
        exact Or.inl hval
  · rcases hC with ⟨b, hba, hval⟩
    by_cases hb0 : b = 0
    · subst b
      rw [gameF_col0] at hval
      omega
    · by_cases hb1 : b = 1
      · subst b
        rw [gameF_col1_rail (q := a) (by omega)] at hval
        omega
      · by_cases hb2 : b = 2
        · subst b
          rw [gameF_col2_rail (q := a) (by omega)] at hval
          omega
        · have hb3 : 3 <= b := by omega
          have hcell := gameF_noInteriorCeiling a b hb3 hba
          have hbcase : b = a - 2 \/ b = a - 1 := by omega
          rcases hbcase with hbeq | hbeq
          · subst b
            exact Or.inr (Or.inl hval)
          · subst b
            exact Or.inr (Or.inr hval)

/-- The two bottom induction levels for J1.  They are recurrence-proved
rail facts, not a computational receipt. -/
private theorem gameF_noHighCeil1_base
    {q r : Nat} (hr : 3 <= r) (hrq : r < q)
    (hlevel : q + r = 11 \/ q + r = 12) :
    gameF q r ≠ q + r := by
  rcases hlevel with h11 | h12
  · have hcase :
        (q = 8 ∧ r = 3) \/ (q = 7 ∧ r = 4) \/ (q = 6 ∧ r = 5) := by
      omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [gameF_col3_rail (q := 8) (by omega)]
      omega
    · rw [gameF_col4_rail (q := 7) (by omega)]
      omega
    · rw [gameF_six_five]
      omega
  · have hcase :
        (q = 9 ∧ r = 3) \/ (q = 8 ∧ r = 4) \/ (q = 7 ∧ r = 5) := by
      omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [gameF_col3_rail (q := 9) (by omega)]
      omega
    · rw [gameF_col4_rail (q := 8) (by omega)]
      omega
    · rw [gameF_col5_rail (q := 7) (by omega)]
      omega

/-- **J1 / NoHighCeil1.**  The first sharp ceiling is never attained at
an interior cell of level at least eleven. -/
theorem gameF_noHighCeil1 :
    forall q r, 3 <= r -> r < q -> 11 <= q + r ->
      gameF q r ≠ q + r := by
  intro q r hr hrq hlevel
  have hmain : forall s, 11 <= s -> forall q r,
      q + r = s -> 3 <= r -> r < q -> gameF q r ≠ q + r := by
    intro s hs
    induction s using Nat.strongRecOn with
    | ind s ih =>
        intro q r hsum hr hrq hout
        by_cases hsmall : s <= 12
        · exact gameF_noHighCeil1_base hr hrq
            (by omega : q + r = 11 \/ q + r = 12) hout
        · have hs13 : 13 <= s := by omega
          by_cases hr3 : r = 3
          · subst r
            have hq5 : 5 <= q := by omega
            rw [gameF_col3_rail hq5] at hout
            omega
          · have hr4 : 4 <= r := by omega
            have hsource : B gameF q r (q + r - 1) := by
              apply gameRecurrenceModel.mex_no_skip (Nat.le_of_lt hrq)
              · change q < gameF q r
                rw [hout]
                omega
              · omega
              · change q + r - 1 < gameF q r
                rw [hout]
                omega
            rcases hsource with hR | hC
            · rcases hR with ⟨a, haq, hval⟩
              by_cases har : a < r
              · have hmin : min a r = a := Nat.min_eq_left (Nat.le_of_lt har)
                rw [hmin] at hval
                have hacap := recurrence_diagonal_source_capacity
                  gameRecurrenceModel a
                change gameF a a <= a + a + 1 at hacap
                omega
              · by_cases hae : a = r
                · subst a
                  have hmin : min r r = r := Nat.min_self r
                  rw [hmin] at hval
                  have hdiag := gameF_diagonal_tight (by omega : 2 <= r)
                  have hreq : q = r + 1 := by omega
                  have hsat : gameF r r = 2 * r := by omega
                  have hforce := gameF_evenSat_forces_ceil1 (by omega) hsat
                  have hcontra := ih (2 * r - 1) (by omega) (by omega)
                    r (r - 1) (by omega) (by omega) (by omega)
                  have hforce' : gameF r (r - 1) = r + (r - 1) := by
                    omega
                  exact hcontra hforce'
                · have hra : r < a := by omega
                  have hmin : min a r = r := Nat.min_eq_right (Nat.le_of_lt hra)
                  rw [hmin] at hval
                  have hcell := gameF_noInteriorCeiling a r (by omega) hra
                  have haeq : a = q - 1 := by omega
                  have hcontra := ih (q + r - 1) (by omega) (by omega)
                    a r (by omega) hr hra
                  exact hcontra (by omega)
            · rcases hC with ⟨b, hbr, hval⟩
              by_cases hb0 : b = 0
              · subst b
                rw [gameF_col0] at hval
                omega
              · by_cases hb1 : b = 1
                · subst b
                  rw [gameF_col1_rail (q := q) (by omega)] at hval
                  omega
                · by_cases hb2 : b = 2
                  · subst b
                    rw [gameF_col2_rail (q := q) (by omega)] at hval
                    omega
                  · have hb3 : 3 <= b := by omega
                    have hcell := gameF_noInteriorCeiling q b hb3 (by omega)
                    have hbeq : b = r - 1 := by omega
                    have hcontra := ih (q + r - 1) (by omega) (by omega)
                      q b (by omega) hb3 (by omega)
                    exact hcontra (by omega)
  exact hmain (q + r) hlevel q r rfl hr hrq

/-- Once J1 is known, an even-saturated diagonal cannot occur from row six
onward. -/
theorem gameF_diagonal_le_two_mul_sub_one {a : Nat} (ha : 6 <= a) :
    gameF a a <= 2 * a - 1 := by
  have hcap := gameF_diagonal_tight (by omega : 2 <= a)
  by_cases hle : gameF a a <= 2 * a - 1
  · exact hle
  exfalso
  have hsat : gameF a a = 2 * a := by omega
  have hforce := gameF_evenSat_forces_ceil1 (by omega) hsat
  have hno := gameF_noHighCeil1 a (a - 1)
    (by omega) (by omega) (by omega)
  apply hno
  omega

/-- Recurrence-proved finite base for J2. -/
private theorem gameF_noHighCeil2_base
    {q r : Nat} (hr : 6 <= r) (hrq : r < q)
    (hlevel : q + r = 17 \/ q + r = 18) :
    gameF q r ≠ q + r - 1 := by
  rcases hlevel with h17 | h18
  · have hcase :
        (q = 11 ∧ r = 6) \/ (q = 10 ∧ r = 7) \/ (q = 9 ∧ r = 8) := by
      omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [gameF_col6_rail (q := 11) (by omega)]
      omega
    · rw [gameF_col7_rail (q := 10) (by omega)]
      omega
    · rw [gameF_nine_eight]
      omega
  · have hcase :
        (q = 12 ∧ r = 6) \/ (q = 11 ∧ r = 7) \/ (q = 10 ∧ r = 8) := by
      omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [gameF_col6_rail (q := 12) (by omega)]
      omega
    · rw [gameF_col7_rail (q := 11) (by omega)]
      omega
    · rw [gameF_ten_eight]
      omega

/-- **J2 / NoHighCeil2.**  In columns six and higher the second ceiling is
never attained at level at least seventeen. -/
theorem gameF_noHighCeil2 :
    forall q r, 6 <= r -> r < q -> 17 <= q + r ->
      gameF q r ≠ q + r - 1 := by
  intro q r hr hrq hlevel
  have hmain : forall s, 17 <= s -> forall q r,
      q + r = s -> 6 <= r -> r < q -> gameF q r ≠ q + r - 1 := by
    intro s hs
    induction s using Nat.strongRecOn with
    | ind s ih =>
        intro q r hsum hr hrq hout
        by_cases hsmall : s <= 18
        · exact gameF_noHighCeil2_base hr hrq
            (by omega : q + r = 17 \/ q + r = 18) hout
        · have hs19 : 19 <= s := by omega
          by_cases hr6 : r = 6
          · subst r
            rw [gameF_col6_rail (q := q) (by omega)] at hout
            omega
          · have hr7 : 7 <= r := by omega
            have hsource : B gameF q r (q + r - 2) := by
              apply gameRecurrenceModel.mex_no_skip (Nat.le_of_lt hrq)
              · change q < gameF q r
                rw [hout]
                omega
              · omega
              · change q + r - 2 < gameF q r
                rw [hout]
                omega
            rcases hsource with hR | hC
            · rcases hR with ⟨a, haq, hval⟩
              by_cases har : a < r
              · have hmin : min a r = a := Nat.min_eq_left (Nat.le_of_lt har)
                rw [hmin] at hval
                by_cases ha0 : a = 0
                · subst a
                  rw [gameF_zero_zero] at hval
                  omega
                · by_cases ha1 : a = 1
                  · subst a
                    rw [gameF_one_one] at hval
                    omega
                  · have ha2 : 2 <= a := by omega
                    have hacap := gameF_diagonal_tight ha2
                    omega
              · by_cases hae : a = r
                · subst a
                  have hmin : min r r = r := Nat.min_self r
                  rw [hmin] at hval
                  have hdiag := gameF_diagonal_tight (by omega : 2 <= r)
                  have hqcase : q = r + 1 \/ q = r + 2 := by omega
                  rcases hqcase with hq1 | hq2
                  · have hsat : gameF r r = 2 * r - 1 := by omega
                    rcases gameF_oddSat_forces_three (by omega) hsat with
                      heven | hceil1 | hceil2
                    · have hcapPrev := gameF_diagonal_le_two_mul_sub_one
                        (a := r - 1) (by omega)
                      omega
                    · have hno1 := gameF_noHighCeil1 r (r - 2)
                        (by omega) (by omega) (by omega)
                      apply hno1
                      omega
                    · have hno2 := ih (2 * r - 1) (by omega) (by omega)
                        r (r - 1) (by omega) (by omega) (by omega)
                      apply hno2
                      omega
                  · have hcapR := gameF_diagonal_le_two_mul_sub_one
                      (a := r) (by omega)
                    omega
                · have hra : r < a := by omega
                  have hmin : min a r = r := Nat.min_eq_right (Nat.le_of_lt hra)
                  rw [hmin] at hval
                  have hcell := gameF_noInteriorCeiling a r (by omega) hra
                  have hacase : a = q - 2 \/ a = q - 1 := by omega
                  rcases hacase with ha2 | ha1
                  · have hno1 := gameF_noHighCeil1 a r
                      (by omega) hra (by omega)
                    apply hno1
                    omega
                  · have hno2 := ih (q + r - 1) (by omega) (by omega)
                      a r (by omega) hr hra
                    apply hno2
                    omega
            · rcases hC with ⟨b, hbr, hval⟩
              by_cases hb0 : b = 0
              · subst b
                rw [gameF_col0] at hval
                omega
              · by_cases hb1 : b = 1
                · subst b
                  rw [gameF_col1_rail (q := q) (by omega)] at hval
                  omega
                · by_cases hb2 : b = 2
                  · subst b
                    rw [gameF_col2_rail (q := q) (by omega)] at hval
                    omega
                  · have hb3 : 3 <= b := by omega
                    have hcell := gameF_noInteriorCeiling q b hb3 (by omega)
                    have hbcase : b = r - 2 \/ b = r - 1 := by omega
                    rcases hbcase with hb2 | hb1
                    · have hno1 := gameF_noHighCeil1 q b
                        hb3 (by omega) (by omega)
                      apply hno1
                      omega
                    · have hb6 : 6 <= b := by omega
                      have hno2 := ih (q + r - 1) (by omega) (by omega)
                        q b (by omega) hb6 (by omega)
                      apply hno2
                      omega
  exact hmain (q + r) hlevel q r rfl hr hrq

/-- **DiagDoubleSlack, closed.**  The diagonal misses the doubled
source-capacity ceiling by two from row nine onward.  This raw statement
does not mention any of the R200 supplier interfaces. -/
theorem gameF_diagDoubleSlack :
    forall a, 9 <= a -> gameF a a + 2 <= 2 * a := by
  intro a ha
  by_cases ha9 : a = 9
  · subst a
    rw [gameF_diag_nine]
    omega
  · have ha10 : 10 <= a := by omega
    have hcap := gameF_diagonal_le_two_mul_sub_one (a := a) (by omega)
    by_cases hle : gameF a a + 2 <= 2 * a
    · exact hle
    exfalso
    have hsat : gameF a a = 2 * a - 1 := by omega
    rcases gameF_oddSat_forces_three (by omega) hsat with
      heven | hceil1 | hceil2
    · have hcapPrev := gameF_diagonal_le_two_mul_sub_one
        (a := a - 1) (by omega)
      omega
    · have hno1 := gameF_noHighCeil1 a (a - 2)
        (by omega) (by omega) (by omega)
      apply hno1
      omega
    · have hno2 := gameF_noHighCeil2 a (a - 1)
        (by omega) (by omega) (by omega)
      apply hno2
      omega

/-- Interface wrapper for the formerly open R200 atom. -/
theorem gameF_actualDiagDoubleSlack : ActualDiagDoubleSlack :=
  gameF_diagDoubleSlack

/-- The formerly conditional Floor+ supplier is now unconditional. -/
theorem gameF_FloorPlus :
    forall {a k}, 16 <= a -> gameF a a = k ->
      3 * a + 5 <= 2 * k :=
  gameF_FloorPlus_of_diagDoubleSlack gameF_actualDiagDoubleSlack

/-- Sharp actual blocker-prefix ceiling, formerly conditional on DDS. -/
theorem gameFBlockerCountThrough_ceiling :
    forall {a}, 16 <= a ->
      2 * gameFBlockerCountThrough a + 4 <= a + 1 :=
  gameFBlockerCountThrough_ceiling_of_diagDoubleSlack
    gameF_actualDiagDoubleSlack

/-- Trivial ambient bound, used only to discharge the small-value side of
the middle-cohort separation theorem. -/
private theorem gameFBlockerCountThrough_le_index (n : Nat) :
    gameFBlockerCountThrough n <= n := by
  classical
  unfold gameFBlockerCountThrough gameFBlockersThroughList
  simpa using
    (List.length_filter_le (fun k : Nat => decide (S gameF k))
      (List.range' 1 n))

/-- The actual blocker-count AFloor, with no numerical premise remaining. -/
theorem gameFBlockerCountThrough_AFloor :
    forall {v}, 26 <= v ->
      v <= 3 * gameFBlockerCountThrough (v - 1) + 2 :=
  gameFBlockerCountThrough_AFloor_of_FloorPlus gameF_FloorPlus

/-- End-to-end discharge of the early-lag `K=10` future-cohort oracle. -/
theorem actualBlockerMiddleCohortList_earlyLag_K10_causal
    {u L : Nat}
    (hLu : L <= u)
    (hL : L = 13 \/ L = 18 \/ L = 20)
    (hRight : 25 <= u - L + 10) :
    actualBlockerMiddleCohortList (u - L) 10 =
        causalBlockerMiddleCohortListFrom
          (u - L + 10) (u - L) 10 ∧
      u - L + 10 < u :=
  actualBlockerMiddleCohortList_earlyLag_K10_causal_of_diagDoubleSlack
    gameF_actualDiagDoubleSlack hLu hL hRight

/-- Quantitative `K=10` middle-stream separation.  The exact arithmetic
threshold for a lookback `L` is `u >= 4*L+33`. -/
theorem actualBlockerMiddleCohortList_K10_above_target_of_margin
    {u L v : Nat}
    (hu : 4 * L + 33 <= u)
    (hv : v ∈ actualBlockerMiddleCohortList (u - L) 10) :
    u < v := by
  have hband := gameF_mem_actualBlockerMiddleCohortList.mp hv
  have hcountTrivial := gameFBlockerCountThrough_le_index (v - 1)
  have hv17 : 17 <= v := by
    unfold actualBlockerMidpoint countMidpoint at hband
    omega
  have hceil := gameFBlockerCountThrough_ceiling (a := v - 1) (by omega)
  have hmidFloor :
      2 * actualBlockerMidpoint v <=
        v + gameFBlockerCountThrough (v - 1) := by
    unfold actualBlockerMidpoint countMidpoint
    omega
  by_cases huv : u < v
  · exact huv
  · exfalso
    have hvu : v <= u := by omega
    omega

/-- **Terminal middle-stream elimination.**  From target 113 onward, every
actual `K=10` middle-cohort value at lags 13, 18, and 20 is strictly larger
than the target.  Such a value cannot participate in the MEX menu below
`u`; the entire middle stream is irrelevant to the target transition. -/
theorem actualBlockerMiddleCohortList_earlyLag_K10_above_target
    {u L v : Nat}
    (hu : 113 <= u)
    (hL : L = 13 \/ L = 18 \/ L = 20)
    (hv : v ∈ actualBlockerMiddleCohortList (u - L) 10) :
    u < v := by
  apply actualBlockerMiddleCohortList_K10_above_target_of_margin
      (u := u) (L := L)
  · rcases hL with rfl | rfl | rfl <;> omega
  · exact hv

/-- Direct B43 consequence: the numerical DDS/Floor+ premise disappears;
only the geometric three-unit host margin remains. -/
theorem b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_hostMargin
    (hmargin : B43FirstSuccessorFloorPlusHostMarginFrom83) :
    B43FirstSuccessorPlusTwoOwnerLeftFrom83 :=
  b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_diagDoubleSlack_hostMargin
    gameF_actualDiagDoubleSlack hmargin

end ChompLean

#print axioms ChompLean.gameF_noInteriorCeiling
#print axioms ChompLean.gameF_evenSat_forces_ceil1
#print axioms ChompLean.gameF_oddSat_forces_three
#print axioms ChompLean.gameF_noHighCeil1
#print axioms ChompLean.gameF_noHighCeil2
#print axioms ChompLean.gameF_diagDoubleSlack
#print axioms ChompLean.gameF_actualDiagDoubleSlack
#print axioms ChompLean.gameF_FloorPlus
#print axioms ChompLean.gameFBlockerCountThrough_ceiling
#print axioms ChompLean.gameFBlockerCountThrough_AFloor
#print axioms ChompLean.actualBlockerMiddleCohortList_earlyLag_K10_causal
#print axioms ChompLean.actualBlockerMiddleCohortList_K10_above_target_of_margin
#print axioms ChompLean.actualBlockerMiddleCohortList_earlyLag_K10_above_target
#print axioms ChompLean.b43FirstSuccessorPlusTwoOwnerLeftFrom83_of_hostMargin
