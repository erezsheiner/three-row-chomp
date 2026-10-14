import R160Lag8PreviewSourceMexReduction
import R153Col14Lag9FaceKill

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight preview: only one source-membership bit is needed

R160 isolated the assertion that `v-3` is the MEX of
`B gameF (v-3) (r-1)`.  In the failed-upper-rail frame this can be weakened
again.  `LowerOwnerCoveredBy v g` and `g < r-1` already put the value `v-3`
*into* that source: a diagonal owner enters `R`, while a row-start owner
enters the row prefix `C`.  Consequently the lag-eight branch is killed by
the single opposite bit

`Not (B gameF (v-3) (r-1) (v-3))`.

No saturation assertion for values below `v-3`, no MEX identification, and
no lower-freeze conclusion is needed for this contradiction.
-/

/-- The weakest source atom presently visible in the lag-eight branch.
It says only that the preview-row value itself is missing from its source.
The atom is defined here, not asserted as a theorem of `gameF`. -/
def Lag8PreviewSourceHole : Prop :=
  forall {v r : Nat},
    11 <= v ->
    r < v ->
    gameF v r = v ->
    r <= v - 8 ->
    gameF (v - 8) (r - 1) = v ->
    Not (B gameF (v - 3) (r - 1) (v - 3))

/-- Owner coverage on an earlier row already includes that row's own value
at every source strictly to the right of the owner cutoff.  This is the
single specialization of the earlier-row saturation theorem used below. -/
theorem lowerOwnerCoveredBy_preview_value_in_source
    {v g q e : Nat}
    (hqpos : 0 < q)
    (hqv : q < v)
    (hge : g < e)
    (heq : e <= q)
    (howners : LowerOwnerCoveredBy v g) :
    B gameF q e q := by
  exact lowerOwnerCoveredBy_source_saturation_on_earlier_row
    hqv hge heq howners q hqpos (Nat.le_refl q)

/-- In a failed owner-covered band, the preview value is already in the
terminal predecessor source.  Hence the one-bit lag-eight hole atom gives
an immediate contradiction. -/
theorem gameF_lag8_failed_band_impossible_of_previewSourceHole
    {v r g : Nat}
    (hv : 11 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v)
    (hhole : Lag8PreviewSourceHole) :
    False := by
  have hmem : B gameF (v - 3) (r - 1) (v - 3) :=
    lowerOwnerCoveredBy_preview_value_in_source
      (v := v) (g := g) (q := v - 3) (e := r - 1)
      (by omega) (by omega) (by omega) (by omega) howners
  exact hhole hv hrv hstart hra hburn hmem

/-- The source-MEX atom from R160 implies the weaker one-bit hole
atom, so every R160 closure theorem factors through this reduction. -/
theorem lag8PreviewSourceHole_of_sourceMex
    (hsource : Lag8PreviewSourceMex) :
    Lag8PreviewSourceHole := by
  intro v r hv hrv hstart hra hburn
  exact (hsource hv hrv hstart hra hburn).2.1

/-- Substituting the one-bit hole for fixed-lag HOST-OLD removes the exact
lag-eight endpoint from the proved first-failure normal form. -/
theorem gameF_firstFailure_burn_ladder_pre_lag9_of_previewSourceHole
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
    (hhole : Lag8PreviewSourceHole) :
    exists a, r <= a /\ a < q - 5 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_pre_lag8_actual
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with
      ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 5
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have ha : a = q - 5 := by omega
    subst a
    have hburn' : gameF ((q + 3) - 8) (r - 1) = q + 3 := by
      have hidx : (q + 3) - 8 = q - 5 := by omega
      rw [hidx]
      exact hburn
    exact False.elim
      (gameF_lag8_failed_band_impossible_of_previewSourceHole
        (v := q + 3) (r := r) (g := g)
        (by omega) hrv hstart howners hfailure (by omega) hburn' hhole)

/-- Combining the one-bit lag-eight exclusion with the already proved
column-fourteen lag-nine rail skips both exceptional endpoints.  Any
remaining first-failure witness is now at target lag at least ten. -/
theorem gameF_firstFailure_burn_ladder_pre_lag10_of_previewSourceHole
    {q r g H : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hhole : Lag8PreviewSourceHole) :
    exists a, r <= a /\ a < q - 6 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_lag8_or_pre_lag10_actual
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with
      ⟨a, hra, ha, hburn, hband, htail⟩
  rcases ha with ha8 | haearly
  · subst a
    have hburn' : gameF ((q + 3) - 8) (r - 1) = q + 3 := by
      have hidx : (q + 3) - 8 = q - 5 := by omega
      rw [hidx]
      exact hburn
    exact False.elim
      (gameF_lag8_failed_band_impossible_of_previewSourceHole
        (v := q + 3) (r := r) (g := g)
        (by omega) hrv hstart howners hfailure (by omega) hburn' hhole)
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩

#print axioms lowerOwnerCoveredBy_preview_value_in_source
#print axioms gameF_lag8_failed_band_impossible_of_previewSourceHole
#print axioms lag8PreviewSourceHole_of_sourceMex
#print axioms gameF_firstFailure_burn_ladder_pre_lag9_of_previewSourceHole
#print axioms gameF_firstFailure_burn_ladder_pre_lag10_of_previewSourceHole

end ChompLean
