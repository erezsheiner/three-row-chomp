import R18OrderedLossRecovery

set_option autoImplicit false

namespace ChompLean

/-!
R19: the exact local capacity reduction for an `L=3` rescue window.

Write `e=c*`.  The relevant sources are `B(t,e)`, `B(t,e+1)`, and
`B(t,e+2)`; `e+2` is the penultimate source.  In this coordinate

* `f (e+2) (e+2)` is `d(s-3)`, and
* `f (e+1) e` is `V1(s-4)`.

The file deliberately does not assert the empirical upper-identity or
the row-prefix scheduling law.  It proves their exact consequences and
isolates the remaining scheduler statement in `hRiderExcludesNewLoss`.
-/

/-- The two R19 candidates for the upper value of an entry double loss,
written in the `e=c*` coordinate of an `L=3` window. -/
def L3UpperIdentity
    (f : Nat -> Nat -> Nat) (e z : Nat) : Prop :=
  z = f (e + 2) (e + 2) \/ z = f (e + 1) e

/-- A hole at the successor source must have been covered at the entry
source when the entry source has at most one sub-`u` hole and its cell is
a genuine MEX cell.  Thus every successor hole is an actual entry loss. -/
theorem successor_hole_was_entry_loss
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (hmex : IsMex (B f t e) (f t e))
    (hone :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hz : 0 < z) (hzu : z < u)
    (hmissingNext : Not (B f t (e + 1) z)) :
    B f t e z /\ Not (B f t (e + 1) z) := by
  constructor
  · by_cases hcurrent : B f t e z
    · exact hcurrent
    · exact False.elim (hmissingNext
        (one_hole_mex_seals_base hmex hone hz hzu hcurrent))
  · exact hmissingNext

/-- Exact diagonal-service equivalence for a value lost at `e -> e+1`.
If it has a diagonal-prefix channel at source `e+2`, its owner must be the
new owner `e+2`; conversely that owner supplies the channel. -/
theorem lost_then_diag_at_next_source_iff_next_diagonal
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hlost : Not (B f t (e + 1) z)) :
    DiagPrefix f t (e + 2) z <->
      (e + 2 < t /\ f (e + 2) (e + 2) = z) := by
  constructor
  · rintro ⟨a, hat, hae, hdiag⟩
    have hge : e + 2 <= a := by
      by_cases h : e + 2 <= a
      · exact h
      · have hae' : a <= e + 1 := by omega
        exact False.elim (hlost
          (Or.inl (R_iff_diagPrefix_or_colTail.mpr
            (Or.inl ⟨a, hat, hae', hdiag⟩))))
    have ha : a = e + 2 := by omega
    subst a
    exact ⟨hat, hdiag⟩
  · rintro ⟨het, hdiag⟩
    exact ⟨e + 2, het, Nat.le_refl _, hdiag⟩

/-- A value that is absent at two consecutive post-entry sources lies
strictly above the MEX emitted at the first of those sources. -/
theorem persistent_hole_has_lower_mex_hole
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hmex : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hz : 0 < z)
    (hmissingOne : Not (B f t (e + 1) z))
    (hmissingTwo : Not (B f t (e + 2) z)) :
    f t (e + 1) < z /\
      Not (B f t (e + 1) (f t (e + 1))) /\
      B f t (e + 2) (f t (e + 1)) := by
  have hneq : f t (e + 1) ≠ z := by
    intro heq
    exact hmissingTwo
      (fresh_emission_closes_next (e := e + 1) heq)
  have hlt : f t (e + 1) < z := by
    rcases Nat.lt_trichotomy (f t (e + 1)) z with h | h | h
    · exact h
    · exact False.elim (hneq h)
    · exact False.elim (hmissingOne (hmex.2.2 z hz h))
  exact ⟨hlt, hmex.2.1,
    fresh_emission_closes_next (e := e + 1) rfl⟩

/-- Bridge from the empirical wording "the upper of an exact double has
one of two identities" to the pairwise proof-facing wording below.  The
bridge needs the separate all-N statement that the entry edge has at most
two losses.  Without that cap, an exact-double receipt does not say anything
about an edge carrying three or more losses. -/
theorem pairwise_upper_identity_of_entry_loss_cap_two
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B f t e x -> Not (B f t (e + 1) x) ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hExactDoubleUpperIdentity :
      forall y z, 0 < y -> y < z -> z < u ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        (forall w, 0 < w -> w < u ->
          B f t e w -> Not (B f t (e + 1) w) -> w = y \/ w = z) ->
        L3UpperIdentity f e z) :
    forall y z, 0 < y -> y < z -> z < u ->
      B f t e y -> Not (B f t (e + 1) y) ->
      B f t e z -> Not (B f t (e + 1) z) ->
      L3UpperIdentity f e z := by
  intro y z hy hyz hzu hyCurrent hyLost hzCurrent hzLost
  apply hExactDoubleUpperIdentity y z hy hyz hzu
    hyCurrent hyLost hzCurrent hzLost
  intro w hw hwu hwCurrent hwLost
  rcases hEntryLossCapTwo y z w hy (by omega) (by omega) hzu hw hwu
      hyCurrent hyLost hzCurrent hzLost hwCurrent hwLost with h | h | h
  · exact False.elim (by omega)
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- `DOUBLE-UPPER-IDENTITY`, in a pairwise proof-facing form, collapses
every persistent post-entry hole to the single old-rider identity
`f(e+1,e)`.  The diagonal alternative is impossible because it would
already cover the value at source `e+2`.

The pairwise formulation is intentional: if an all-N proof has not first
excluded triple entry loss, it must apply to every ordered pair of entry
losses, not merely to edges known externally to have multiplicity exactly
two. -/
theorem persistent_hole_is_old_rider_of_pairwise_upper_identity
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (het : e + 2 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hUpperIdentity :
      forall y z, 0 < y -> y < z -> z < u ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        L3UpperIdentity f e z)
    (hz : 0 < z) (hzu : z < u)
    (hmissingOne : Not (B f t (e + 1) z))
    (hmissingTwo : Not (B f t (e + 2) z)) :
    z = f (e + 1) e := by
  have hlower := persistent_hole_has_lower_mex_hole
    hmexOne hz hmissingOne hmissingTwo
  let y := f t (e + 1)
  have hy : 0 < y := hmexOne.1
  have hyz : y < z := hlower.1
  have hyu : y < u := by omega
  have hyEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hy hyu hlower.2.1
  have hzEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hz hzu hmissingOne
  rcases hUpperIdentity y z hy hyz hzu
      hyEntry.1 hyEntry.2 hzEntry.1 hzEntry.2 with hdiag | hrider
  · exfalso
    apply hmissingTwo
    left
    exact R_iff_diagPrefix_or_colTail.mpr
      (Or.inl ⟨e + 2, het, Nat.le_refl _, hdiag.symm⟩)
  · exact hrider

/-- Consequently there is at most one hole which persists from source
`e+1` to source `e+2`: every such hole is the same named old rider. -/
theorem persistent_holes_unique_of_pairwise_upper_identity
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (het : e + 2 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hUpperIdentity :
      forall y z, 0 < y -> y < z -> z < u ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        L3UpperIdentity f e z) :
    forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
      Not (B f t (e + 1) y) -> Not (B f t (e + 2) y) ->
      Not (B f t (e + 1) z) -> Not (B f t (e + 2) z) ->
      y = z := by
  intro y z hy hyu hz hzu hy1 hy2 hz1 hz2
  have hyr := persistent_hole_is_old_rider_of_pairwise_upper_identity
    het hmexEntry honeEntry hmexOne hUpperIdentity hy hyu hy1 hy2
  have hzr := persistent_hole_is_old_rider_of_pairwise_upper_identity
    het hmexEntry honeEntry hmexOne hUpperIdentity hz hzu hz1 hz2
  omega

/-- The smallest direct transition principle.  Holes at the next source
have two provenances: persistent old holes and newly lost covered values.
If each class has capacity one and the two classes cannot coexist, the next
source has at most one hole. -/
theorem next_source_one_hole_of_two_provenance_caps
    {S T : Nat -> Prop} {u : Nat}
    (hPersistentSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (S y) -> Not (T y) -> Not (S z) -> Not (T z) -> y = z)
    (hNewLossSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        S y -> Not (T y) -> S z -> Not (T z) -> y = z)
    (hNoMix :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        Not (S old) -> Not (T old) -> S new -> Not (T new) -> False) :
    forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
      Not (T y) -> Not (T z) -> y = z := by
  intro y z hy hyu hz hzu hyT hzT
  by_cases hyS : S y
  · by_cases hzS : S z
    · exact hNewLossSingle y z hy hyu hz hzu hyS hyT hzS hzT
    · exact False.elim (hNoMix z y hz hzu hy hyu hzS hzT hyS hyT)
  · by_cases hzS : S z
    · exact False.elim (hNoMix y z hy hyu hz hzu hyS hyT hzS hzT)
    · exact hPersistentSingle y z hy hyu hz hzu hyS hyT hzS hzT

/-- Proof-facing `L=3` reduction.  Besides endpoint MEX/source algebra, its
only schedule inputs are:

* at most one actual loss on the position-1 edge; and
* if the named old rider remains unpaid, that edge creates no new loss.

The second is exactly the corrected
`UNRECOVERED-ENTRY-UPPER => NO-POS1-LOSS` target after the upper-identity
classifier has reduced every persistent entry upper to the old rider. -/
theorem penultimate_one_hole_of_l3_upper_identity
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (het : e + 2 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hUpperIdentity :
      forall y z, 0 < y -> y < z -> z < u ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        L3UpperIdentity f e z)
    (hPosOneSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        B f t (e + 1) y -> Not (B f t (e + 2) y) ->
        B f t (e + 1) z -> Not (B f t (e + 2) z) -> y = z)
    (hRiderExcludesNewLoss :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        old = f (e + 1) e ->
        Not (B f t (e + 1) old) -> Not (B f t (e + 2) old) ->
        B f t (e + 1) new -> Not (B f t (e + 2) new) -> False) :
    forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
      Not (B f t (e + 2) y) -> Not (B f t (e + 2) z) -> y = z := by
  apply next_source_one_hole_of_two_provenance_caps
  · exact persistent_holes_unique_of_pairwise_upper_identity
      het hmexEntry honeEntry hmexOne hUpperIdentity
  · exact hPosOneSingle
  · intro old new hold holdu hnew hnewu holdOne holdTwo hnewOne hnewTwo
    have hrider := persistent_hole_is_old_rider_of_pairwise_upper_identity
      het hmexEntry honeEntry hmexOne hUpperIdentity
      hold holdu holdOne holdTwo
    exact hRiderExcludesNewLoss old new hold holdu hnew hnewu
      hrider holdOne holdTwo hnewOne hnewTwo

/-- Complete mechanical tail of the corrected `L=3` route.  Once the
previous theorem supplies a one-hole penultimate source, the final MEX cell
and the last-edge seal give full sub-`u` saturation. -/
theorem l3_backstop_of_upper_identity_and_capacity
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (het : e + 2 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hmexTwo : IsMex (B f t (e + 2)) (f t (e + 2)))
    (hUpperIdentity :
      forall y z, 0 < y -> y < z -> z < u ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        L3UpperIdentity f e z)
    (hPosOneSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        B f t (e + 1) y -> Not (B f t (e + 2) y) ->
        B f t (e + 1) z -> Not (B f t (e + 2) z) -> y = z)
    (hRiderExcludesNewLoss :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        old = f (e + 1) e ->
        Not (B f t (e + 1) old) -> Not (B f t (e + 2) old) ->
        B f t (e + 1) new -> Not (B f t (e + 2) new) -> False)
    (hLastSeal :
      forall z, 0 < z -> z < u ->
        B f t (e + 2) z -> B f t (e + 3) z) :
    forall z, 0 < z -> z < u -> B f t (e + 3) z := by
  have honeTwo := penultimate_one_hole_of_l3_upper_identity
    het hmexEntry honeEntry hmexOne hUpperIdentity
    hPosOneSingle hRiderExcludesNewLoss
  simpa [Nat.add_assoc] using
    (penultimate_one_hole_mex_closure
      (e := e + 2) hmexTwo honeTwo hLastSeal)

/-! ## Strictly weaker final target: two named holes are enough

`PENULTIMATE-ONE-HOLE` is sufficient but not minimal.  The last source gains
both the fresh value of the penultimate cell and the new diagonal owner.
Thus two holes are harmless when they are exactly those two values.
-/

/-- If every remaining hole is either the fresh value of the current cell or
the next diagonal value, the next source is saturated.  Already covered
values use the independently proved last-edge seal. -/
theorem final_fresh_or_diagonal_holes_close
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (het : e + 1 < t)
    (hholes :
      forall z, 0 < z -> z < u -> Not (B f t e z) ->
        z = f t e \/ z = f (e + 1) (e + 1))
    (hseal :
      forall z, 0 < z -> z < u -> B f t e z -> B f t (e + 1) z) :
    forall z, 0 < z -> z < u -> B f t (e + 1) z := by
  intro z hz hzu
  by_cases hcurrent : B f t e z
  · exact hseal z hz hzu hcurrent
  · rcases hholes z hz hzu hcurrent with hfresh | hdiag
    · exact fresh_emission_closes_next hfresh.symm
    · left
      exact R_iff_diagPrefix_or_colTail.mpr
        (Or.inl ⟨e + 1, het, Nat.le_refl _, hdiag.symm⟩)

/-- A two-provenance capacity theorem with a final-diagonal escape.  Each
provenance class has capacity one.  If the two classes coexist, they need
not be forbidden: it suffices that their two values are exactly the MEX
emission and the next diagonal. -/
theorem next_source_holes_in_mex_or_diag_of_escape
    {S T : Nat -> Prop} {u m d : Nat}
    (hmex : IsMex T m)
    (hPersistentSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (S y) -> Not (T y) -> Not (S z) -> Not (T z) -> y = z)
    (hNewLossSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        S y -> Not (T y) -> S z -> Not (T z) -> y = z)
    (hMixedEscape :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        Not (S old) -> Not (T old) -> S new -> Not (T new) ->
        (old = m /\ new = d) \/ (old = d /\ new = m)) :
    forall z, 0 < z -> z < u -> Not (T z) -> z = m \/ z = d := by
  intro z hz hzu hzT
  have hmle : m <= z := by
    by_cases h : m <= z
    · exact h
    · have hzm : z < m := by omega
      exact False.elim (hzT (hmex.2.2 z hz hzm))
  have hm : 0 < m := hmex.1
  have hmu : m < u := by omega
  have hmT : Not (T m) := hmex.2.1
  by_cases hzS : S z
  · by_cases hmS : S m
    · have hzm := hNewLossSingle z m hz hzu hm hmu hzS hzT hmS hmT
      exact Or.inl hzm
    · rcases hMixedEscape m z hm hmu hz hzu hmS hmT hzS hzT with h | h
      · exact Or.inr h.2
      · exact Or.inl h.2
  · by_cases hmS : S m
    · rcases hMixedEscape z m hz hzu hm hmu hzS hzT hmS hmT with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · have hzm := hPersistentSingle z m hz hzu hm hmu hzS hzT hmS hmT
      exact Or.inl hzm

/-- A more order-theoretic form of the mixed escape.  Under the two
provenance caps and exact MEX, it is enough to prove that the larger member
of every mixed persistent/new pair is the final diagonal.  The smaller
member is then forced mechanically to be the MEX. -/
theorem mixed_mex_diagonal_pair_of_larger_is_diagonal
    {S T : Nat -> Prop} {u m d : Nat}
    (hmex : IsMex T m)
    (hPersistentSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (S y) -> Not (T y) -> Not (S z) -> Not (T z) -> y = z)
    (hNewLossSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        S y -> Not (T y) -> S z -> Not (T z) -> y = z)
    (hMixedLargerDiagonal :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        Not (S old) -> Not (T old) -> S new -> Not (T new) ->
        (old < new -> new = d) /\ (new < old -> old = d)) :
    forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
      Not (S old) -> Not (T old) -> S new -> Not (T new) ->
      (old = m /\ new = d) \/ (old = d /\ new = m) := by
  intro old new hold holdu hnew hnewu holdS holdT hnewS hnewT
  have hm : 0 < m := hmex.1
  have hmT : Not (T m) := hmex.2.1
  have horder := hMixedLargerDiagonal old new hold holdu hnew hnewu
    holdS holdT hnewS hnewT
  rcases Nat.lt_trichotomy old new with holt | heq | hnlt
  · have hnewd : new = d := horder.1 holt
    have hmle : m <= old := by
      by_cases h : m <= old
      · exact h
      · exact False.elim (holdT (hmex.2.2 old hold (by omega)))
    have hmu : m < u := by omega
    have holdm : old = m := by
      by_cases heq : old = m
      · exact heq
      · have hmlt : m < old := by omega
        by_cases hmS : S m
        · have hmn := hNewLossSingle m new hm hmu hnew hnewu
            hmS hmT hnewS hnewT
          omega
        · have hmo := hPersistentSingle m old hm hmu hold holdu
            hmS hmT holdS holdT
          omega
    exact Or.inl ⟨holdm, hnewd⟩
  · exact False.elim (holdS (by simpa [heq] using hnewS))
  · have holdd : old = d := horder.2 hnlt
    have hmle : m <= new := by
      by_cases h : m <= new
      · exact h
      · exact False.elim (hnewT (hmex.2.2 new hnew (by omega)))
    have hmu : m < u := by omega
    have hnewm : new = m := by
      by_cases heq : new = m
      · exact heq
      · have hmlt : m < new := by omega
        by_cases hmS : S m
        · have hmn := hNewLossSingle m new hm hmu hnew hnewu
            hmS hmT hnewS hnewT
          omega
        · have hmo := hPersistentSingle m old hm hmu hold holdu
            hmS hmT holdS holdT
          omega
    exact Or.inr ⟨holdd, hnewm⟩

/-- Weaker proof-facing replacement for
`UNRECOVERED-UPPER => NO-POS1-LOSS`.  A mixed old-rider/new-loss state is
allowed when the pair is exactly the two channels added on the final move.
This theorem proves full backstop saturation without proving
`PENULTIMATE-ONE-HOLE`. -/
theorem l3_backstop_of_upper_identity_and_final_escape
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (het : e + 2 < t)
    (hetFinal : e + 3 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hmexTwo : IsMex (B f t (e + 2)) (f t (e + 2)))
    (hUpperIdentity :
      forall y z, 0 < y -> y < z -> z < u ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        L3UpperIdentity f e z)
    (hPosOneSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        B f t (e + 1) y -> Not (B f t (e + 2) y) ->
        B f t (e + 1) z -> Not (B f t (e + 2) z) -> y = z)
    (hRiderMixedFinalEscape :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        old = f (e + 1) e ->
        Not (B f t (e + 1) old) -> Not (B f t (e + 2) old) ->
        B f t (e + 1) new -> Not (B f t (e + 2) new) ->
        (old = f t (e + 2) /\ new = f (e + 3) (e + 3)) \/
        (old = f (e + 3) (e + 3) /\ new = f t (e + 2)))
    (hLastSeal :
      forall z, 0 < z -> z < u ->
        B f t (e + 2) z -> B f t (e + 3) z) :
    forall z, 0 < z -> z < u -> B f t (e + 3) z := by
  have hPersistentSingle :=
    persistent_holes_unique_of_pairwise_upper_identity
      het hmexEntry honeEntry hmexOne hUpperIdentity
  have hMixedEscape :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        Not (B f t (e + 1) old) -> Not (B f t (e + 2) old) ->
        B f t (e + 1) new -> Not (B f t (e + 2) new) ->
        (old = f t (e + 2) /\ new = f (e + 3) (e + 3)) \/
        (old = f (e + 3) (e + 3) /\ new = f t (e + 2)) := by
    intro old new hold holdu hnew hnewu holdOne holdTwo hnewOne hnewTwo
    have hrider := persistent_hole_is_old_rider_of_pairwise_upper_identity
      het hmexEntry honeEntry hmexOne hUpperIdentity
      hold holdu holdOne holdTwo
    exact hRiderMixedFinalEscape old new hold holdu hnew hnewu hrider
      holdOne holdTwo hnewOne hnewTwo
  have hholes := next_source_holes_in_mex_or_diag_of_escape
    hmexTwo hPersistentSingle hPosOneSingle hMixedEscape
  have hclose := final_fresh_or_diagonal_holes_close
    (e := e + 2) (u := u) (by omega) hholes
  simpa [Nat.add_assoc] using hclose hLastSeal

/-! ## Counterframe: upper identity alone does not give the capacity law

The following source-level frame has the exact three consecutive MEX cells,
a saturated entry source, pairwise `L3UpperIdentity`, and at most one new
loss on the position-1 edge.  Nevertheless the old rider `7` stays missing
while the newly lost value `6` joins it.  Thus the penultimate source has two
holes.  This rules out deriving `PENULTIMATE-ONE-HOLE` from the identity
classifier alone, even after adding the observed position-1 single-loss cap.
-/

def upperIdentityMixCounter (a b : Nat) : Nat :=
  if a = 8 /\ b = 0 then 1
  else if a = 8 /\ b = 1 then 8
  else if a = 8 /\ b = 2 then 5
  else if a = 8 /\ b = 3 then 6
  else if a = 2 /\ b = 1 then 7
  else if a = 3 /\ b = 1 then 5
  else if a = 4 /\ b = 1 then 2
  else if a = 5 /\ b = 1 then 3
  else if a = 6 /\ b = 1 then 4
  else if a = 7 /\ b = 1 then 6
  else if a = 2 /\ b = 2 then 2
  else if a = 3 /\ b = 2 then 3
  else if a = 4 /\ b = 2 then 4
  else if a = 5 /\ b = 2 then 6
  else if a = 6 /\ b = 2 then 9
  else if a = 7 /\ b = 2 then 10
  else if a = 3 /\ b = 3 then 3
  else if a = 4 /\ b = 3 then 4
  else if a = 5 /\ b = 3 then 9
  else if a = 6 /\ b = 3 then 10
  else if a = 7 /\ b = 3 then 11
  else 0

private theorem upperIdentityMix_source_one_iff {z : Nat} :
    B upperIdentityMixCounter 8 1 z <->
      z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/
      z = 5 \/ z = 6 \/ z = 7 := by
  constructor
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hac : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/
          a = 4 \/ a = 5 \/ a = 6 \/ a = 7 := by omega
      rcases hac with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [upperIdentityMixCounter] at hval ⊢ <;> omega
    · have hb0 : b = 0 := by omega
      subst b
      simp [upperIdentityMixCounter] at hval ⊢
      omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; exact ⟨0, by omega, by simp [upperIdentityMixCounter]⟩
    · right; exact ⟨0, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨4, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨5, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨6, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨3, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨7, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨2, by omega, by simp [upperIdentityMixCounter]⟩

private theorem upperIdentityMix_source_two_iff {z : Nat} :
    B upperIdentityMixCounter 8 2 z <->
      z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/
      z = 6 \/ z = 8 \/ z = 9 \/ z = 10 := by
  constructor
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hac : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/
          a = 4 \/ a = 5 \/ a = 6 \/ a = 7 := by omega
      rcases hac with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [upperIdentityMixCounter] at hval ⊢ <;> omega
    · have hbc : b = 0 \/ b = 1 := by omega
      rcases hbc with rfl | rfl <;>
        simp [upperIdentityMixCounter] at hval ⊢ <;> omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; exact ⟨0, by omega, by simp [upperIdentityMixCounter]⟩
    · right; exact ⟨0, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨2, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨3, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨4, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨5, by omega, by simp [upperIdentityMixCounter]⟩
    · right; exact ⟨1, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨6, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨7, by omega, by simp [upperIdentityMixCounter]⟩

private theorem upperIdentityMix_source_three_iff {z : Nat} :
    B upperIdentityMixCounter 8 3 z <->
      z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/
      z = 5 \/ z = 8 \/ z = 9 \/ z = 10 \/ z = 11 := by
  constructor
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hac : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/
          a = 4 \/ a = 5 \/ a = 6 \/ a = 7 := by omega
      rcases hac with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [upperIdentityMixCounter] at hval ⊢ <;> omega
    · have hbc : b = 0 \/ b = 1 \/ b = 2 := by omega
      rcases hbc with rfl | rfl | rfl <;>
        simp [upperIdentityMixCounter] at hval ⊢ <;> omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; exact ⟨0, by omega, by simp [upperIdentityMixCounter]⟩
    · right; exact ⟨0, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨2, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨3, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨4, by omega, by simp [upperIdentityMixCounter]⟩
    · right; exact ⟨2, by omega, by simp [upperIdentityMixCounter]⟩
    · right; exact ⟨1, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨5, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨6, by omega, by simp [upperIdentityMixCounter]⟩
    · left; exact ⟨7, by omega, by simp [upperIdentityMixCounter]⟩

theorem upperIdentityMix_entry_mex :
    IsMex (B upperIdentityMixCounter 8 1)
      (upperIdentityMixCounter 8 1) := by
  have hout : upperIdentityMixCounter 8 1 = 8 := by
    simp [upperIdentityMixCounter]
  rw [hout]
  refine ⟨by omega, ?_, ?_⟩
  · rw [upperIdentityMix_source_one_iff]
    omega
  · intro z hz hlt
    rw [upperIdentityMix_source_one_iff]
    omega

theorem upperIdentityMix_position_one_mex :
    IsMex (B upperIdentityMixCounter 8 2)
      (upperIdentityMixCounter 8 2) := by
  have hout : upperIdentityMixCounter 8 2 = 5 := by
    simp [upperIdentityMixCounter]
  rw [hout]
  refine ⟨by omega, ?_, ?_⟩
  · rw [upperIdentityMix_source_two_iff]
    omega
  · intro z hz hlt
    rw [upperIdentityMix_source_two_iff]
    omega

theorem upperIdentityMix_penultimate_mex :
    IsMex (B upperIdentityMixCounter 8 3)
      (upperIdentityMixCounter 8 3) := by
  have hout : upperIdentityMixCounter 8 3 = 6 := by
    simp [upperIdentityMixCounter]
  rw [hout]
  refine ⟨by omega, ?_, ?_⟩
  · rw [upperIdentityMix_source_three_iff]
    omega
  · intro z hz hlt
    rw [upperIdentityMix_source_three_iff]
    omega

theorem upperIdentityMix_entry_saturated :
    forall y z, 0 < y -> y < 8 -> 0 < z -> z < 8 ->
      Not (B upperIdentityMixCounter 8 1 y) ->
      Not (B upperIdentityMixCounter 8 1 z) -> y = z := by
  intro y z hy hyu hz hzu hyMissing hzMissing
  rw [upperIdentityMix_source_one_iff] at hyMissing hzMissing
  omega

theorem upperIdentityMix_pairwise_upper_identity :
    forall y z, 0 < y -> y < z -> z < 8 ->
      B upperIdentityMixCounter 8 1 y ->
      Not (B upperIdentityMixCounter 8 2 y) ->
      B upperIdentityMixCounter 8 1 z ->
      Not (B upperIdentityMixCounter 8 2 z) ->
      L3UpperIdentity upperIdentityMixCounter 1 z := by
  intro y z hy hyz hzu hyCurrent hyLost hzCurrent hzLost
  rw [upperIdentityMix_source_one_iff] at hyCurrent hzCurrent
  rw [upperIdentityMix_source_two_iff] at hyLost hzLost
  have hz7 : z = 7 := by omega
  subst z
  exact Or.inr (by simp [upperIdentityMixCounter])

theorem upperIdentityMix_position_one_single_loss :
    forall y z, 0 < y -> y < 8 -> 0 < z -> z < 8 ->
      B upperIdentityMixCounter 8 2 y ->
      Not (B upperIdentityMixCounter 8 3 y) ->
      B upperIdentityMixCounter 8 2 z ->
      Not (B upperIdentityMixCounter 8 3 z) -> y = z := by
  intro y z hy hyu hz hzu hyCurrent hyLost hzCurrent hzLost
  rw [upperIdentityMix_source_two_iff] at hyCurrent hzCurrent
  rw [upperIdentityMix_source_three_iff] at hyLost hzLost
  omega

theorem upperIdentityMix_penultimate_has_two_holes :
    Not (B upperIdentityMixCounter 8 3 6) /\
    Not (B upperIdentityMixCounter 8 3 7) /\ 6 ≠ 7 := by
  rw [upperIdentityMix_source_three_iff, upperIdentityMix_source_three_iff]
  omega

/-- Direct witness that the missing clause is the mixed-provenance exclusion:
the persistent old rider is `7`, while `6` is a newly lost value. -/
theorem upperIdentityMix_rider_and_new_loss_coexist :
    7 = upperIdentityMixCounter (1 + 1) 1 /\
    Not (B upperIdentityMixCounter 8 2 7) /\
    Not (B upperIdentityMixCounter 8 3 7) /\
    B upperIdentityMixCounter 8 2 6 /\
    Not (B upperIdentityMixCounter 8 3 6) := by
  constructor
  · simp [upperIdentityMixCounter]
  rw [upperIdentityMix_source_two_iff, upperIdentityMix_source_three_iff,
    upperIdentityMix_source_two_iff, upperIdentityMix_source_three_iff]
  omega

/-- A compact, machine-checked refutation of the implication
`DOUBLE-UPPER-IDENTITY => PENULTIMATE-ONE-HOLE`.  Even exact MEX at all
three cells and the independent position-1 single-loss law do not repair
the implication; `hRiderExcludesNewLoss` is genuinely additional content. -/
theorem upper_identity_does_not_force_penultimate_one_hole :
    IsMex (B upperIdentityMixCounter 8 1)
      (upperIdentityMixCounter 8 1) /\
    IsMex (B upperIdentityMixCounter 8 2)
      (upperIdentityMixCounter 8 2) /\
    IsMex (B upperIdentityMixCounter 8 3)
      (upperIdentityMixCounter 8 3) /\
    (forall y z, 0 < y -> y < 8 -> 0 < z -> z < 8 ->
      Not (B upperIdentityMixCounter 8 1 y) ->
      Not (B upperIdentityMixCounter 8 1 z) -> y = z) /\
    (forall y z, 0 < y -> y < z -> z < 8 ->
      B upperIdentityMixCounter 8 1 y ->
      Not (B upperIdentityMixCounter 8 2 y) ->
      B upperIdentityMixCounter 8 1 z ->
      Not (B upperIdentityMixCounter 8 2 z) ->
      L3UpperIdentity upperIdentityMixCounter 1 z) /\
    (forall y z, 0 < y -> y < 8 -> 0 < z -> z < 8 ->
      B upperIdentityMixCounter 8 2 y ->
      Not (B upperIdentityMixCounter 8 3 y) ->
      B upperIdentityMixCounter 8 2 z ->
      Not (B upperIdentityMixCounter 8 3 z) -> y = z) /\
    Not (B upperIdentityMixCounter 8 3 6) /\
    Not (B upperIdentityMixCounter 8 3 7) /\ 6 ≠ 7 := by
  exact ⟨upperIdentityMix_entry_mex,
    upperIdentityMix_position_one_mex,
    upperIdentityMix_penultimate_mex,
    upperIdentityMix_entry_saturated,
    upperIdentityMix_pairwise_upper_identity,
    upperIdentityMix_position_one_single_loss,
    upperIdentityMix_penultimate_has_two_holes⟩

end ChompLean
