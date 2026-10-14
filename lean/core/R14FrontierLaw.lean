import ChompLean.Proof
import Std

set_option autoImplicit false

namespace ChompLean

/-!
R14: recurrence-level saturation-frontier interface.

The file deliberately separates three issues which are easy to conflate:

* `LowerSaturated` is a statement about the source set `B` only;
* a lower hole controls a MEX output, but not an arbitrary carry output;
* for a high target `t < u`, an equality `f t e = u` is automatically on
  the live/MEX side, so a lower hole excludes that equality without a
  per-column liveness assumption.

At the eventual capture cell, however, source saturation and cleanliness do
not themselves kill the carry branch.  The exact non-carry guard is retained
as an explicit hypothesis in every capture theorem below.
-/

def LowerSaturated (f : Nat -> Nat -> Nat) (t e u : Nat) : Prop :=
  forall z, 0 < z -> z < u -> B f t e z

def HasLowerHole (f : Nat -> Nat -> Nat) (t e u : Nat) : Prop :=
  exists z, 0 < z /\ z < u /\ Not (B f t e z)

def IsSaturationFrontier
    (f : Nat -> Nat -> Nat) (t u fr : Nat) : Prop :=
  LowerSaturated f t fr u /\
    forall e, e < fr -> Not (LowerSaturated f t e u)

theorem hasLowerHole_iff_not_lowerSaturated
    {f : Nat -> Nat -> Nat} {t e u : Nat} :
    HasLowerHole f t e u <-> Not (LowerSaturated f t e u) := by
  constructor
  · rintro ⟨z, hz0, hzu, hzB⟩ hsat
    exact hzB (hsat z hz0 hzu)
  · intro hnotSat
    classical
    by_cases hhole : HasLowerHole f t e u
    · exact hhole
    · exfalso
      apply hnotSat
      intro z hz0 hzu
      by_cases hzB : B f t e z
      · exact hzB
      · exact False.elim (hhole ⟨z, hz0, hzu, hzB⟩)

/-! ## FRONTIER implies BODY-UNSAT -/

/-- This implication is purely definitional; it uses no recurrence facts. -/
theorem frontier_body_unsaturated
    {f : Nat -> Nat -> Nat} {t u fr e : Nat}
    (hfront : IsSaturationFrontier f t u fr) (he : e < fr) :
    Not (LowerSaturated f t e u) :=
  hfront.2 e he

/-- Hole-witness form of `frontier_body_unsaturated`. -/
theorem frontier_body_has_lower_hole
    {f : Nat -> Nat -> Nat} {t u fr e : Nat}
    (hfront : IsSaturationFrontier f t u fr) (he : e < fr) :
    HasLowerHole f t e u :=
  hasLowerHole_iff_not_lowerSaturated.mpr (frontier_body_unsaturated hfront he)

/-- R14's named body is the segment left of `star`; `star <= fr` is enough. -/
theorem frontier_ge_implies_body_unsaturated
    {f : Nat -> Nat -> Nat} {t u star fr : Nat}
    (hfront : IsSaturationFrontier f t u fr) (hstarFr : star <= fr) :
    forall e, e < star -> Not (LowerSaturated f t e u) := by
  intro e he
  exact frontier_body_unsaturated hfront (by omega)

/-! ## Exact MEX and recurrence consequences of a lower hole -/

/-- A MEX with a missing positive value below `u` must itself be below `u`. -/
theorem isMex_lt_of_lower_hole
    {S : Nat -> Prop} {m u : Nat} (hmex : IsMex S m)
    (hhole : exists z, 0 < z /\ z < u /\ Not (S z)) :
    m < u := by
  rcases hhole with ⟨z, hz0, hzu, hzS⟩
  by_cases hmu : m < u
  · exact hmu
  · have hum : u <= m := Nat.le_of_not_gt hmu
    exact False.elim (hzS (hmex.2.2 z hz0 (by omega)))

/-- Source-specialized MEX form. -/
theorem mex_cell_lt_of_lower_hole
    {f : Nat -> Nat -> Nat} {t e u out : Nat}
    (hmex : IsMex (B f t e) out) (hhole : HasLowerHole f t e u) :
    out < u :=
  isMex_lt_of_lower_hole hmex hhole

/--
If the actual recurrence cell is live, a lower hole forces its output below
`u`.  Liveness is used only to select the MEX branch.
-/
theorem recurrence_live_cell_lt_of_lower_hole
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t e u : Nat} (het : e <= t) (hlive : t < f t e)
    (hhole : HasLowerHole f t e u) :
    f t e < u := by
  have hnotCarry : Not (e < t /\ f (t - 1) e < t) := by
    intro hcarry
    have heq := hrec.1 hcarry.1 hcarry.2
    omega
  exact mex_cell_lt_of_lower_hole (hrec.2 het hnotCarry) hhole

/-- Liveness is a sufficient (but stronger) way to discharge non-carry. -/
theorem noncarry_of_live
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t e : Nat} (hlive : t < f t e) :
    Not (e < t /\ f (t - 1) e < t) := by
  intro hcarry
  have heq := hrec.1 hcarry.1 hcarry.2
  omega

/--
Branch-free exclusion for a high target.  If `f t e = u` and `t <= u`, the
carry branch is impossible because every carried value is `< t`; on the MEX
branch the hole forces the output below `u`.  Thus no strict `t<u` or
per-column liveness premise is needed.
-/
theorem recurrence_lower_hole_excludes_high_target
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t e u : Nat} (het : e <= t) (htu : t <= u)
    (hhole : HasLowerHole f t e u) :
    f t e ≠ u := by
  intro hout
  by_cases hcarry : e < t /\ f (t - 1) e < t
  · have heq := hrec.1 hcarry.1 hcarry.2
    rw [hout] at heq
    omega
  · have houtlt := mex_cell_lt_of_lower_hole (hrec.2 het hcarry) hhole
    rw [hout] at houtlt
    omega

/-- Every column strictly left of a high-target frontier is `u`-free. -/
theorem frontier_body_excludes_high_target
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t u fr : Nat} (hfrt : fr <= t) (htu : t <= u)
    (hfront : IsSaturationFrontier f t u fr) :
    forall e, e < fr -> f t e ≠ u := by
  intro e he
  exact recurrence_lower_hole_excludes_high_target hrec (by omega) htu
    (frontier_body_has_lower_hole hfront he)

/-! ## Free cardinality (pigeonhole) obstruction -/

def RValueList (f : Nat -> Nat -> Nat) (t e : Nat) : List Nat :=
  (List.range t).map (fun a => f a (min a e))

def CValueList (f : Nat -> Nat -> Nat) (t e : Nat) : List Nat :=
  (List.range e).map (fun b => f t b)

def BValueList (f : Nat -> Nat -> Nat) (t e : Nat) : List Nat :=
  RValueList f t e ++ CValueList f t e

theorem mem_RValueList_iff
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    z ∈ RValueList f t e <-> R f t e z := by
  simp [RValueList, R]

theorem mem_CValueList_iff
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    z ∈ CValueList f t e <-> C f t e z := by
  simp [CValueList, C]

theorem mem_BValueList_iff
    {f : Nat -> Nat -> Nat} {t e z : Nat} :
    z ∈ BValueList f t e <-> B f t e z := by
  simp [BValueList, B, mem_RValueList_iff, mem_CValueList_iff]

theorem length_BValueList
    (f : Nat -> Nat -> Nat) (t e : Nat) :
    (BValueList f t e).length = t + e := by
  simp [BValueList, RValueList, CValueList]

/-- A duplicate-free list included in an arbitrary list cannot be longer. -/
theorem nodup_subset_length_le {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : xs ⊆ ys) :
    xs.length <= ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      have hnd' := (List.nodup_cons.mp hnd)
      have ha : a ∈ ys := hsub (by simp)
      have hsubErase : xs ⊆ ys.erase a := by
        intro x hx
        have hxy : x ∈ ys := hsub (by simp [hx])
        have hxa : x ≠ a := by
          intro hxa
          apply hnd'.1
          simpa [hxa] using hx
        exact (List.mem_erase_of_ne hxa).mpr hxy
      have hlen := ih hnd'.2 hsubErase
      have herase := List.length_erase_of_mem ha
      have hypos := List.length_pos_of_mem ha
      simp only [List.length_cons]
      rw [herase] at hlen
      omega

/-- A source with at most `t+e` slots cannot cover more positive values. -/
theorem lowerSaturated_card_bound
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hsat : LowerSaturated f t e u) :
    u - 1 <= t + e := by
  have hsubset : List.range' 1 (u - 1) ⊆ BValueList f t e := by
    intro z hz
    have hz' := List.mem_range'_1.mp hz
    apply mem_BValueList_iff.mpr
    exact hsat z (by omega) (by omega)
  have hlen := nodup_subset_length_le (List.nodup_range' 1) hsubset
  simpa [length_BValueList] using hlen

/-- Subtraction-free form of the R14 pigeonhole bound. -/
theorem pigeonhole_body_unsaturated
    {f : Nat -> Nat -> Nat} {s e u : Nat}
    (hsmall : s + e + 2 < u) :
    Not (LowerSaturated f (s + 1) e u) := by
  intro hsat
  have hcard := lowerSaturated_card_bound hsat
  omega

/-- Exact stated form; the strict inequality handles truncated subtraction. -/
theorem pigeonhole_body_unsaturated_sub
    {f : Nat -> Nat -> Nat} {s e u : Nat}
    (hsmall : e < u - s - 2) :
    Not (LowerSaturated f (s + 1) e u) := by
  apply pigeonhole_body_unsaturated
  omega

/-! ## Capture at, and after, a rolling frontier -/

/-- A lower-saturated MEX source which is target-clean has MEX exactly `u`. -/
theorem isMex_eq_of_lowerSaturated_and_clean
    {S : Nat -> Prop} {m u : Nat} (hmex : IsMex S m)
    (hu0 : 0 < u)
    (hsat : forall z, 0 < z -> z < u -> S z)
    (hclean : Not (S u)) :
    m = u := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hum
    exact hclean (hmex.2.2 u hu0 hum)
  · apply Nat.le_of_not_gt
    intro hmu
    exact hmex.2.1 (hsat m hmex.1 hmu)

/--
Exact frontier-to-capture theorem.  Minimal recurrence-facing assumptions:
the target is high (`t<u`), `fr` is the first lower-saturated column, its
fixed channel `R` is `u`-clean, and the target cell is not a carry cell.
-/
theorem saturation_frontier_captures
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t u fr : Nat} (hfrt : fr <= t) (htu : t <= u) (hu0 : 0 < u)
    (hfront : IsSaturationFrontier f t u fr)
    (hRclean : Not (R f t fr u))
    (hnotCarry : Not (fr < t /\ f (t - 1) fr < t)) :
    f t fr = u := by
  have hCclean : Not (C f t fr u) := by
    rintro ⟨e, hefr, heq⟩
    exact (frontier_body_excludes_high_target hrec hfrt htu hfront e hefr) heq
  have hBclean : Not (B f t fr u) := by
    intro hB
    rcases hB with hR | hC
    · exact hRclean hR
    · exact hCclean hC
  have hmex := hrec.2 hfrt hnotCarry
  exact isMex_eq_of_lowerSaturated_and_clean hmex hu0 hfront.1 hBclean

/-- User-facing liveness wrapper for `saturation_frontier_captures`. -/
theorem saturation_frontier_captures_of_live
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t u fr : Nat} (hfrt : fr <= t) (htu : t <= u) (hu0 : 0 < u)
    (hfront : IsSaturationFrontier f t u fr)
    (hRclean : Not (R f t fr u))
    (hlive : t < f t fr) :
    f t fr = u := by
  exact saturation_frontier_captures hrec hfrt htu hu0 hfront hRclean
    (noncarry_of_live hrec hlive)

/--
Rolling-cover interface.  Saturation may first occur at `fr` and roll to a
later seat `seat`.  To make `seat` capture, it suffices to preserve lower
saturation there, keep its fixed channel and carry branch clean, and exclude
`u` only in the finite transition zone `[fr,seat)`.  The entire diffuse body
`e<fr` is discharged automatically by frontier minimality.
-/
theorem rolling_frontier_captures
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t u fr seat : Nat}
    (hseatT : seat <= t) (hfrSeat : fr <= seat) (htu : t <= u)
    (hu0 : 0 < u)
    (hfront : IsSaturationFrontier f t u fr)
    (hsatSeat : LowerSaturated f t seat u)
    (hRcleanSeat : Not (R f t seat u))
    (hnotCarrySeat : Not (seat < t /\ f (t - 1) seat < t))
    (hzoneClean : forall e, fr <= e -> e < seat -> f t e ≠ u) :
    f t seat = u := by
  have hfrT : fr <= t := by omega
  have hbodyClean := frontier_body_excludes_high_target hrec hfrT htu hfront
  have hCclean : Not (C f t seat u) := by
    rintro ⟨e, heSeat, heq⟩
    by_cases heFr : e < fr
    · exact (hbodyClean e heFr) heq
    · exact (hzoneClean e (Nat.le_of_not_gt heFr) heSeat) heq
  have hBclean : Not (B f t seat u) := by
    intro hB
    rcases hB with hR | hC
    · exact hRcleanSeat hR
    · exact hCclean hC
  have hmex := hrec.2 hseatT hnotCarrySeat
  exact isMex_eq_of_lowerSaturated_and_clean hmex hu0 hsatSeat hBclean

/-- Liveness wrapper for a later rolling-cover seat. -/
theorem rolling_frontier_captures_of_live
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t u fr seat : Nat}
    (hseatT : seat <= t) (hfrSeat : fr <= seat) (htu : t <= u)
    (hu0 : 0 < u)
    (hfront : IsSaturationFrontier f t u fr)
    (hsatSeat : LowerSaturated f t seat u)
    (hRcleanSeat : Not (R f t seat u))
    (hliveSeat : t < f t seat)
    (hzoneClean : forall e, fr <= e -> e < seat -> f t e ≠ u) :
    f t seat = u := by
  exact rolling_frontier_captures hrec hseatT hfrSeat htu hu0 hfront hsatSeat
    hRcleanSeat (noncarry_of_live hrec hliveSeat) hzoneClean

/--
Two-seat wrapper for the R14 dichotomy.  If the frontier is the first seat,
that seat captures.  If the frontier lies strictly to its right but no later
than BACKSTOP, the rolling interface makes BACKSTOP capture.  No separate
global provenance premise appears.
-/
theorem two_seat_capture_of_rolling_frontier
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t u star fr back : Nat}
    (hbackT : back <= t) (hfrBack : fr <= back)
    (htu : t <= u) (hu0 : 0 < u)
    (hfront : IsSaturationFrontier f t u fr)
    (hstarClean : fr = star -> Not (R f t star u))
    (hstarNotCarry : fr = star ->
      Not (star < t /\ f (t - 1) star < t))
    (hsatBack : fr ≠ star -> LowerSaturated f t back u)
    (hbackClean : fr ≠ star -> Not (R f t back u))
    (hbackNotCarry : fr ≠ star ->
      Not (back < t /\ f (t - 1) back < t))
    (hzoneClean : fr ≠ star ->
      forall e, fr <= e -> e < back -> f t e ≠ u) :
    f t star = u \/ f t back = u := by
  by_cases hEq : fr = star
  · left
    subst fr
    exact saturation_frontier_captures hrec (by omega) htu hu0 hfront
      (hstarClean rfl) (hstarNotCarry rfl)
  · right
    exact rolling_frontier_captures hrec hbackT hfrBack htu hu0 hfront
      (hsatBack hEq) (hbackClean hEq) (hbackNotCarry hEq) (hzoneClean hEq)

end ChompLean
