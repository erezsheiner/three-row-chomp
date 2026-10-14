import R161Lag8PreviewSourceHoleReduction

set_option autoImplicit false

namespace ChompLean

/-!
# Lag-eight preview: the owner-order bit below the source-hole bit

The source-hole atom of R161 still excludes every possible source channel.
For first-failure closure that is stronger than necessary.  Owner coverage
uses only the actual opening owner of `q=v-3`: either a diagonal owner or a
row-start owner.  It is therefore enough to know that no such owner lies
strictly left of the terminal predecessor `c=r-1`.

The three N=12000 lag-eight packets have the sharp row-start equality
`gameF (v-3) c = v-3`; the definition below retains only the owner-order
consequence `c <= owner`.
-/

/-- In a lag-eight terminal packet, every possible opening owner of the
preview value `v-3` is at or to the right of the terminal predecessor.
This is a proposed actual-game chronology atom, not a theorem asserted here.
-/
def Lag8PreviewOwnerNotLeft : Prop :=
  forall {v r : Nat},
    11 <= v ->
    r < v ->
    gameF v r = v ->
    r <= v - 8 ->
    gameF (v - 8) (r - 1) = v ->
    (forall a, gameF a a = v - 3 -> r - 1 <= a) /\
    (forall s, s < v - 3 -> gameF (v - 3) s = v - 3 -> r - 1 <= s)

/-- Equivalent positive-witness form: the preview value has an actual
opening owner at or to the right of the terminal predecessor. -/
def Lag8PreviewHasRightOwner : Prop :=
  forall {v r : Nat},
    11 <= v ->
    r < v ->
    gameF v r = v ->
    r <= v - 8 ->
    gameF (v - 8) (r - 1) = v ->
    (exists a, r - 1 <= a /\ a < v - 3 /\ gameF a a = v - 3) \/
    (exists s, r - 1 <= s /\ s < v - 3 /\
      gameF (v - 3) s = v - 3)

/-- Opening-owner uniqueness makes the universal order form and the
positive right-owner witness equivalent in the actual game. -/
theorem lag8PreviewHasRightOwner_iff_ownerNotLeft :
    Lag8PreviewHasRightOwner <-> Lag8PreviewOwnerNotLeft := by
  constructor
  · intro hright v r hv hrv hstart hra hburn
    have hw := hright hv hrv hstart hra hburn
    constructor
    · intro a hdiag
      rcases hw with ⟨b, hcb, _hbq, hdiagb⟩ |
          ⟨s, _hcs, hsq, hrows⟩
      · have hab : a = b :=
          diagonal_injective gameRecurrenceModel (hdiag.trans hdiagb.symm)
        simpa [hab] using hcb
      · exact False.elim
          (disjoint_D_S gameRecurrenceModel
            ⟨a, hdiag⟩ ⟨s, hsq, hrows⟩)
    · intro s hsq hrows
      rcases hw with ⟨a, _hca, haq, hdiag⟩ |
          ⟨t, hct, htq, hrowt⟩
      · exact False.elim
          (disjoint_D_S gameRecurrenceModel
            ⟨a, hdiag⟩ ⟨s, hsq, hrows⟩)
      · have hst : s = t :=
          gameRecurrenceModel.fixed_q_injective
            (Nat.le_of_lt hsq) (Nat.le_of_lt htq)
            (hrows.trans hrowt.symm)
        simpa [hst] using hct
  · intro horder v r hv hrv hstart hra hburn
    have ho := horder hv hrv hstart hra hburn
    have hqpos : 0 < v - 3 := by omega
    rcases gameRecurrenceModel.opening_cover hqpos with
        ⟨a, haq, hdiag⟩ | ⟨s, hsq, hrow⟩
    · exact Or.inl ⟨a, ho.1 a hdiag, haq, hdiag⟩
    · exact Or.inr ⟨s, ho.2 s hsq hrow, hsq, hrow⟩

/-- A preview-source hole implies the weaker owner-order atom.  A diagonal
owner left of `c` enters `R`; a row-start owner left of `c` enters `C`. -/
theorem lag8PreviewOwnerNotLeft_of_sourceHole
    (hhole : Lag8PreviewSourceHole) :
    Lag8PreviewOwnerNotLeft := by
  intro v r hv hrv hstart hra hburn
  have hnotB := hhole hv hrv hstart hra hburn
  constructor
  · intro a hdiag
    apply Nat.le_of_not_gt
    intro hac
    apply hnotB
    left
    refine ⟨a, ?_, ?_⟩
    · have hgt := gameRecurrenceModel.diagonal_gt a
      change a < gameF a a at hgt
      rw [hdiag] at hgt
      exact hgt
    · have hmin : min a (r - 1) = a := Nat.min_eq_left (by omega)
      simpa [hmin] using hdiag
  · intro s hs hrow
    apply Nat.le_of_not_gt
    intro hsc
    exact hnotB (Or.inr ⟨s, hsc, hrow⟩)

/-- The owner-order bit alone contradicts an owner-covered failed band.
No statement about `B gameF (v-3) (r-1)` or about the intervening MEX
values is used. -/
theorem gameF_lag8_failed_band_impossible_of_previewOwnerNotLeft
    {v r g : Nat}
    (hv : 11 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (howners : LowerOwnerCoveredBy v g)
    (hfailure : g + 1 < r)
    (hra : r <= v - 8)
    (hburn : gameF (v - 8) (r - 1) = v)
    (horder : Lag8PreviewOwnerNotLeft) :
    False := by
  have hqpos : 0 < v - 3 := by omega
  have hqv : v - 3 < v := by omega
  have hnotLeft := horder hv hrv hstart hra hburn
  rcases howners (v - 3) hqpos hqv with
      ⟨a, hag, hdiag⟩ | ⟨s, hsg, hsq, hrow⟩
  · have hca : r - 1 <= a := hnotLeft.1 a hdiag
    omega
  · have hcs : r - 1 <= s := hnotLeft.2 s hsq hrow
    omega

/-- Combining the owner-order bit with the proved lag-nine fixed rail leaves
only terminal histories of target lag at least ten in a first-failure frame.
-/
theorem gameF_firstFailure_burn_ladder_pre_lag10_of_previewOwnerNotLeft
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
    (horder : Lag8PreviewOwnerNotLeft) :
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
      (gameF_lag8_failed_band_impossible_of_previewOwnerNotLeft
        (v := q + 3) (r := r) (g := g)
        (by omega) hrv hstart howners hfailure (by omega) hburn' horder)
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩

#print axioms lag8PreviewOwnerNotLeft_of_sourceHole
#print axioms lag8PreviewHasRightOwner_iff_ownerNotLeft
#print axioms gameF_lag8_failed_band_impossible_of_previewOwnerNotLeft
#print axioms gameF_firstFailure_burn_ladder_pre_lag10_of_previewOwnerNotLeft

end ChompLean
