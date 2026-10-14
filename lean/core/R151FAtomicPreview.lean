import R151FLag4Boundary

set_option autoImplicit false

namespace ChompLean

/-!
R151F-A: [PREVIEW-SUPPLIER-CROSSING] attacked at the atomic case.

The atomic boundary configuration is `r=g+2` with the terminal burn
`F(v-4,g+1)=v` and the preview `F(v-3,H)=v`, `H<=g`.  The ladder side is
empty there, so this file attacks the preview column itself.  Three new
mechanisms are proved.

First, the freeze-skip dichotomy at column `g`: the freeze cell is
automatically saturated at column `g` as well, because `g` bounds every
owner.  A failure therefore forces, at column `g` itself, either a host
of the target strictly below the blocker or a sibling blocker frozen
exactly at `g` (whose constant branch then owns the column).

Second, under no-sibling-at-`g` the whole band machinery of R151F extends
one column left: the burn at `(v-4,g+1)` forces column `g` to be consumed
strictly below `v-4`, and the preview host is pushed strictly below `g`.

Third, the exact supplier law: the preview cell is a MEX cell, so every
blocker below it is blocked there; a blocker whose freeze column lies
strictly right of `H` cannot use the row prefix (fixed-row injectivity
pins its unique row-`v-3` occurrence to its own freeze column) nor the
diagonal (row-start values are not diagonal values), so it must appear in
column `H` itself, strictly before its own freeze row.  Each such supply
cell is in turn a fully saturated MEX cell — the recursion face.

Combining these, the atomic boundary splits into three exactly pinned
worlds; none is refuted here, and the file ends with the honest residual.
-/

/-! ## 0. Persistence helper -/

/-- A frozen blocker persists at its freeze column on every later row. -/
theorem gameF_freeze_persists
    {k rk t : Nat}
    (hrkk : rk < k)
    (hstartk : gameF k rk = k)
    (hkt : k <= t) :
    gameF t rk = k := by
  have hsmall : gameRecurrenceModel.f k rk < k + 1 := by
    change gameF k rk < k + 1
    rw [hstartk]
    omega
  have h := constant_from gameRecurrenceModel (q := k) (r := rk)
    hrkk hsmall (t - k)
  change gameF (k + (t - k)) rk = gameF k rk at h
  have hidx : k + (t - k) = t := by omega
  rw [hidx, hstartk] at h
  exact h

/-- Freeze columns are unique: one blocker per column, ever.  The earlier
blocker's constant branch owns the column at the later blocker's own row. -/
theorem gameF_freeze_column_unique
    {r k₁ k₂ : Nat}
    (hrk₁ : r < k₁)
    (h₁ : gameF k₁ r = k₁)
    (h₁₂ : k₁ < k₂)
    (h₂ : gameF k₂ r = k₂) :
    False := by
  have hpers : gameF k₂ r = k₁ :=
    gameF_freeze_persists hrk₁ h₁ (by omega)
  omega

/-- The preview column is freeze-free through the preview row: a blocker
at most `v-3` frozen at `H` would persist there and collide with the
preview value.  So the preview column's high phase must survive to the
lag-three row — its own eventual blocker, if any, is strictly later. -/
theorem gameF_preview_column_freeze_free
    {q H k rk : Nat}
    (hpreview : gameF q H = q + 3)
    (hkq : k <= q)
    (hrkk : rk < k)
    (hstartk : gameF k rk = k) :
    rk ≠ H := by
  intro hrkH
  have hpers : gameF q rk = k := gameF_freeze_persists hrkk hstartk hkq
  rw [hrkH] at hpers
  omega

/-! ## 1. The freeze-skip dichotomy at column `g` -/

/-- Any upper-rail failure forces, at the midpoint column `g` itself:
either a sibling blocker frozen exactly at `g`, or a host of the target
at column `g` strictly below the blocker.  Otherwise the freeze cell
argument runs at `(v,g)`: the carry branch would expose a `g`-frozen
sibling, owner coverage saturates every smaller value (diagonal owners
enter directly at column `g`; frozen row-starts persist in the prefix),
and the missing target would make `(v,g)` itself the freeze,
contradicting `g+1<r` by fixed-row injectivity. -/
theorem gameF_failure_column_g_dichotomy
    {v r g : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r) :
    (exists k0, g < k0 /\ k0 < v /\ gameF k0 g = k0) \/
    (exists s, g < s /\ s < v /\ gameF s g = v) := by
  by_cases hB : exists k0, g < k0 /\ k0 < v /\ gameF k0 g = k0
  · exact Or.inl hB
  · right
    have hnotfirst : Not (g < v /\ gameF (v - 1) g < v) := by
      rintro ⟨_, hcarry⟩
      have hrow := gameF_low_cell_has_rowstart (q := v - 1) (c := g)
        (by omega) (by omega)
      exact hB ⟨gameF (v - 1) g, hrow.1, by omega, hrow.2⟩
    have hmex := gameF_brouwerRecurrence.2 (q := v) (r := g)
      (by omega) hnotfirst
    have hsat : forall k, 0 < k -> k < v -> B gameF v g k := by
      intro k hkpos hkv
      rcases howners k hkpos hkv with
          ⟨a, hag, hdiag⟩ | ⟨rk, hrkg, hrkk, hstartk⟩
      · left
        exact ⟨a, by omega, by simpa [Nat.min_eq_left hag] using hdiag⟩
      · by_cases hrkg' : rk = g
        · exact False.elim
            (hB ⟨k, by omega, hkv, by rw [← hrkg']; exact hstartk⟩)
        · right
          exact ⟨rk, by omega,
            gameF_freeze_persists hrkk hstartk (by omega)⟩
    by_cases hBv : B gameF v g v
    · cases hBv with
      | inl hR =>
          rcases hR with ⟨w, hwt, hwval⟩
          by_cases hwe : w <= g
          · exact False.elim (disjoint_D_S gameRecurrenceModel
              ⟨w, by simpa [Nat.min_eq_left hwe] using hwval⟩
              ⟨r, hrv, hstart⟩)
          · have hgw : g < w := Nat.lt_of_not_ge hwe
            exact ⟨w, hgw, hwt,
              by simpa [Nat.min_eq_right (Nat.le_of_lt hgw)] using hwval⟩
      | inr hC =>
          rcases hC with ⟨b, hbg, hbval⟩
          have hbr : b = r := gameRecurrenceModel.fixed_q_injective
            (by omega) (by omega) (hbval.trans hstart.symm)
          omega
    · exfalso
      have hout : gameF v g = v := by
        by_cases hlt : gameF v g < v
        · exact False.elim (hmex.2.1 (hsat (gameF v g) hmex.1 hlt))
        · by_cases hgt' : v < gameF v g
          · exact False.elim (hBv (hmex.2.2 v (by omega) hgt'))
          · omega
      have hgr : g = r := gameRecurrenceModel.fixed_q_injective
        (by omega) (by omega) (hout.trans hstart.symm)
      omega

/-! ## 2. Band machinery extended to column `g` -/

/-- With no sibling frozen at `g`, owner coverage saturates column `g`
itself on every pre-blocker row: the exact hole in R151F's strict
inequality `g<e` was a blocker frozen exactly at `g`, and that is now
excluded by hypothesis. -/
theorem gameF_ownerCovered_saturation_at_g
    {v g t : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (hNB : Not (exists k0, g < k0 /\ k0 < v /\ gameF k0 g = k0))
    (hgt : g < t)
    (_htv : t < v) :
    forall k, 0 < k -> k < v -> B gameF t g k := by
  intro k hkpos hkv
  rcases howners k hkpos hkv with
      ⟨a, hag, hdiag⟩ | ⟨rk, hrkg, hrkk, hstartk⟩
  · left
    exact ⟨a, by omega, by simpa [Nat.min_eq_left hag] using hdiag⟩
  · by_cases hrkg' : rk = g
    · exact False.elim
        (hNB ⟨k, by omega, hkv, by rw [← hrkg']; exact hstartk⟩)
    · by_cases hkt : k <= t
      · right
        exact ⟨rk, by omega, gameF_freeze_persists hrkk hstartk hkt⟩
      · right
        have hC := rowStartPropagation gameRecurrenceModel
          (p := k) (r := rk) hstartk hrkk (q := t) (by omega) (by omega)
        rcases hC with ⟨b, hbrk, hbval⟩
        change gameF t b = k at hbval
        exact ⟨b, by omega, hbval⟩

/-- With no sibling frozen at `g`, column `g` has no carry branch below
the blocker: a carried low value would expose exactly such a sibling. -/
theorem gameF_noCarry_at_g_of_no_g_freeze
    {v g t : Nat}
    (hNB : Not (exists k0, g < k0 /\ k0 < v /\ gameF k0 g = k0))
    (hgt : g < t)
    (htv : t < v) :
    Not (g < t /\ gameF (t - 1) g < t) := by
  rintro ⟨_, hcarry⟩
  have hrow := gameF_low_cell_has_rowstart (q := t - 1) (c := g)
    (by omega) (by omega)
  exact hNB ⟨gameF (t - 1) g, hrow.1, by omega, hrow.2⟩

/-- The R151F trichotomy at column `g` under no-sibling-at-`g`. -/
theorem gameF_column_g_trichotomy
    {v r g t : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hNB : Not (exists k0, g < k0 /\ k0 < v /\ gameF k0 g = k0))
    (hgt : g < t)
    (htv : t < v) :
    (exists b, b < g /\ gameF t b = v) \/
    (exists w, g < w /\ w < t /\ gameF w g = v) \/
    gameF t g = v := by
  have hnotfirst := gameF_noCarry_at_g_of_no_g_freeze hNB hgt htv
  have hmex := gameF_brouwerRecurrence.2 (q := t) (r := g)
    (by omega) hnotfirst
  by_cases hBv : B gameF t g v
  · cases hBv with
    | inl hR =>
        rcases hR with ⟨w, hwt, hwval⟩
        by_cases hwe : w <= g
        · exact False.elim (disjoint_D_S gameRecurrenceModel
            ⟨w, by simpa [Nat.min_eq_left hwe] using hwval⟩
            ⟨r, hrv, hstart⟩)
        · have hgw : g < w := Nat.lt_of_not_ge hwe
          exact Or.inr (Or.inl ⟨w, hgw, hwt,
            by simpa [Nat.min_eq_right (Nat.le_of_lt hgw)] using hwval⟩)
    | inr hC =>
        rcases hC with ⟨b, hbe, hbval⟩
        exact Or.inl ⟨b, hbe, hbval⟩
  · have hsat := gameF_ownerCovered_saturation_at_g howners hNB hgt htv
    by_cases hlt : gameF t g < v
    · exact False.elim (hmex.2.1 (hsat (gameF t g) hmex.1 hlt))
    · by_cases hgt' : v < gameF t g
      · exact False.elim (hBv (hmex.2.2 v (by omega) hgt'))
      · have hout : gameF t g = v := by omega
        exact Or.inr (Or.inr hout)

/-- Atomic boundary, no sibling at `g`: the burn at `(v-4,g+1)` forces
column `g` to be consumed strictly below `v-4`, and the preview host is
then strictly below `g` by same-lower no-repeat. -/
theorem gameF_atomic_boundary_g_extension
    {q g H : Nat}
    (hrv : g + 2 < q + 3)
    (hstart : gameF (q + 3) (g + 2) = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hNB : Not (exists k0, g < k0 /\ k0 < q + 3 /\ gameF k0 g = k0))
    (hra : g + 2 <= q - 1)
    (hq1 : 1 <= q)
    (hburn : gameF (q - 1) (g + 1) = q + 3)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    (exists w, g < w /\ w < q - 1 /\ gameF w g = q + 3) /\ H < g := by
  have htri := gameF_column_g_trichotomy (v := q + 3) (r := g + 2)
    (t := q - 1) hrv hstart howners hNB (by omega) (by omega)
  have hmain : exists w, g < w /\ w < q - 1 /\ gameF w g = q + 3 := by
    rcases htri with ⟨b, hbg, hbval⟩ | hburned | hnow
    · have hbb : b = g + 1 := gameRecurrenceModel.fixed_q_injective
        (q := q - 1) (by omega) (by omega) (hbval.trans hburn.symm)
      omega
    · exact hburned
    · have hgg : g = g + 1 := gameRecurrenceModel.fixed_q_injective
        (q := q - 1) (by omega) (by omega) (hnow.trans hburn.symm)
      omega
  refine ⟨hmain, ?_⟩
  rcases hmain with ⟨w, hgw, hwq, hwval⟩
  by_cases hHg : H = g
  · exfalso
    rw [hHg] at hpreview
    exact encoding_same_lower_no_repeat game_encodes
      (s := g) (t₁ := w) (t₂ := q) (p := q + 3)
      hgw (by omega) (by omega) hwval hpreview
  · omega

/-! ## 3. The exact supplier law at the preview column -/

/-- Every blocker whose freeze column lies strictly right of the preview
column must visit the preview column strictly before its own freeze row.
The preview cell is a MEX cell, so the blocker is blocked there; the row
prefix is dead because fixed-row injectivity pins the unique row-`v-3`
occurrence of the blocker to its own persisted freeze column; the
diagonal is dead by `disjoint_D_S`; and a visit at or above the freeze
row would force a second freeze column via the low-cell row-start.  This
is [PREVIEW-SUPPLIER-CROSSING] as a theorem: the demand set is exactly
the blockers frozen in `(H,g]`. -/
theorem gameF_preview_crossing_blocker_prefreeze_visit
    {q H k rk : Nat}
    (hpreview : gameF q H = q + 3)
    (hkq : k <= q)
    (hrkH : H < rk)
    (hrkk : rk < k)
    (hstartk : gameF k rk = k) :
    exists a, H < a /\ a < k /\ gameF a H = k := by
  have hkpos : 0 < k := by omega
  have hnotfirst : Not (H < q /\ gameF (q - 1) H < q) := by
    rintro ⟨hHq, hsmall⟩
    have hconst := gameF_brouwerRecurrence.1 (q := q) (r := H) hHq hsmall
    rw [hpreview] at hconst
    omega
  have hmex := gameF_brouwerRecurrence.2 (q := q) (r := H)
    (by omega) hnotfirst
  have hkB : B gameF q H k :=
    hmex.2.2 k hkpos (by rw [hpreview]; omega)
  have hpersist : gameF q rk = k := gameF_freeze_persists hrkk hstartk hkq
  cases hkB with
  | inr hC =>
      rcases hC with ⟨b, hbH, hbval⟩
      have hbrk : b = rk := gameRecurrenceModel.fixed_q_injective
        (by omega) (by omega) (hbval.trans hpersist.symm)
      omega
  | inl hR =>
      rcases hR with ⟨a, haq, haval⟩
      by_cases haH : a <= H
      · have hdiag : gameF a a = k := by
          simpa [Nat.min_eq_left haH] using haval
        exact False.elim (disjoint_D_S gameRecurrenceModel
          ⟨a, hdiag⟩ ⟨rk, hrkk, hstartk⟩)
      · have hHa : H < a := Nat.lt_of_not_ge haH
        have hcol : gameF a H = k := by
          simpa [Nat.min_eq_right (Nat.le_of_lt hHa)] using haval
        by_cases hak : a < k
        · exact ⟨a, hHa, hak, hcol⟩
        · exfalso
          have hrow := gameF_low_cell_has_rowstart (q := a) (c := H)
            (by omega) (by omega)
          rw [hcol] at hrow
          have hHrk : H = rk := gameRecurrenceModel.fixed_q_injective
            (q := k) (by omega) (by omega) (hrow.2.trans hstartk.symm)
          omega

/-- Each crossing supply cell is itself a fully saturated MEX cell: the
recursion face of the supplier demand. -/
theorem gameF_crossing_supplier_is_saturated
    {a H k : Nat}
    (hHa : H < a)
    (hak : a < k)
    (hval : gameF a H = k) :
    forall j, 0 < j -> j < k -> B gameF a H j := by
  have hnotfirst : Not (H < a /\ gameF (a - 1) H < a) := by
    rintro ⟨_, hsmall⟩
    have hconst := gameF_brouwerRecurrence.1 (q := a) (r := H) hHa hsmall
    rw [hval] at hconst
    omega
  have hmex := gameF_brouwerRecurrence.2 (q := a) (r := H)
    (by omega) hnotfirst
  intro j hj0 hjk
  exact hmex.2.2 j hj0 (by rw [hval]; omega)

/-! ## 4. The three-worlds split of the atomic boundary -/

/-- The atomic boundary configuration splits into three exactly pinned
worlds: (W1) no sibling at `g` — then column `g` is consumed strictly
below the burn row and the preview host sits strictly below `g`;
(W2) a sibling blocker at most `v-3` frozen exactly at `g` — its constant
branch owns `(v-3,g)`, again pushing the preview strictly below `g`;
(W3) a top sibling `v-2` or `v-1` frozen exactly at `g`. -/
theorem gameF_atomic_boundary_three_worlds
    {q g H : Nat}
    (hrv : g + 2 < q + 3)
    (hstart : gameF (q + 3) (g + 2) = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hra : g + 2 <= q - 1)
    (hq1 : 1 <= q)
    (hburn : gameF (q - 1) (g + 1) = q + 3)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    ((exists w, g < w /\ w < q - 1 /\ gameF w g = q + 3) /\ H < g) \/
    ((exists k0, g < k0 /\ k0 <= q /\ gameF k0 g = k0) /\ H < g) \/
    (exists k0, (k0 = q + 1 \/ k0 = q + 2) /\ gameF k0 g = k0) := by
  by_cases hB : exists k0, g < k0 /\ k0 < q + 3 /\ gameF k0 g = k0
  · rcases hB with ⟨k0, hgk, hkv, hk0⟩
    by_cases hk0q : k0 <= q
    · refine Or.inr (Or.inl ⟨⟨k0, hgk, hk0q, hk0⟩, ?_⟩)
      by_cases hHg : H = g
      · exfalso
        have hpers : gameF q g = k0 :=
          gameF_freeze_persists (k := k0) (rk := g) hgk hk0 hk0q
        rw [hHg] at hpreview
        omega
      · omega
    · exact Or.inr (Or.inr ⟨k0, by omega, hk0⟩)
  · left
    exact gameF_atomic_boundary_g_extension hrv hstart howners hB hra hq1
      hburn hpreviewLeft hpreview

#print axioms gameF_freeze_persists
#print axioms gameF_freeze_column_unique
#print axioms gameF_preview_column_freeze_free
#print axioms gameF_failure_column_g_dichotomy
#print axioms gameF_ownerCovered_saturation_at_g
#print axioms gameF_noCarry_at_g_of_no_g_freeze
#print axioms gameF_column_g_trichotomy
#print axioms gameF_atomic_boundary_g_extension
#print axioms gameF_preview_crossing_blocker_prefreeze_visit
#print axioms gameF_crossing_supplier_is_saturated
#print axioms gameF_atomic_boundary_three_worlds

end ChompLean
