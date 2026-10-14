import R19PenultimateCapacity

set_option autoImplicit false

namespace ChompLean

/-!
R20: a MEX-queue capacity transfer for the corrected rescue-window route.

The main point is independent of the empirical `DOUBLE-UPPER-IDENTITY`:
if two distinct holes survive from the first post-entry source to the
penultimate source, then the first post-entry MEX is a third, distinct loss
on the entry edge.  Thus an entry-loss cap of two already forces persistent
capacity one.

The second part records a separate weakening of the R19 identity route: to
name a persistent hole as the old rider, the upper identity is needed only
for the pair consisting of that hole and the first post-entry MEX, not for
every pair of entry losses.
-/

/-- Only the entry loss paired with the first post-entry MEX needs the
R19 two-name upper identity.  This is strictly weaker than the pairwise
identity assumed in R19. -/
def MexPartnerUpperIdentity
    (f : Nat -> Nat -> Nat) (t e u : Nat) : Prop :=
  forall z, 0 < z -> z < u ->
    let m := f t (e + 1)
    m < z ->
    B f t e m -> Not (B f t (e + 1) m) ->
    B f t e z -> Not (B f t (e + 1) z) ->
    L3UpperIdentity f e z

/-- The R19 pairwise hypothesis implies the new MEX-partner hypothesis.
The converse is not used: the latter asks for the identity only when the
lower loss is the distinguished first post-entry MEX. -/
theorem mexPartnerUpperIdentity_of_pairwise
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hm : 0 < f t (e + 1))
    (hPairwise :
      forall y z, 0 < y -> y < z -> z < u ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        L3UpperIdentity f e z) :
    MexPartnerUpperIdentity f t e u := by
  unfold MexPartnerUpperIdentity
  intro z hz hzu
  dsimp
  intro hmz hmCurrent hmLost hzCurrent hzLost
  exact hPairwise (f t (e + 1)) z hm hmz hzu
    hmCurrent hmLost hzCurrent hzLost

theorem persistent_hole_is_old_rider_of_mex_partner_upper_identity
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (het : e + 2 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hMexPartner : MexPartnerUpperIdentity f t e u)
    (hz : 0 < z) (hzu : z < u)
    (hmissingOne : Not (B f t (e + 1) z))
    (hmissingTwo : Not (B f t (e + 2) z)) :
    z = f (e + 1) e := by
  have hlower := persistent_hole_has_lower_mex_hole
    hmexOne hz hmissingOne hmissingTwo
  let m := f t (e + 1)
  have hm : 0 < m := hmexOne.1
  have hmz : m < z := hlower.1
  have hmu : m < u := by omega
  have hmEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hm hmu hlower.2.1
  have hzEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hz hzu hmissingOne
  rcases hMexPartner z hz hzu hmz
      hmEntry.1 hmEntry.2 hzEntry.1 hzEntry.2 with hdiag | hrider
  · exfalso
    apply hmissingTwo
    left
    exact R_iff_diagPrefix_or_colTail.mpr
      (Or.inl ⟨e + 2, het, Nat.le_refl _, hdiag.symm⟩)
  · exact hrider

theorem persistent_holes_unique_of_mex_partner_upper_identity
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (het : e + 2 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hMexPartner : MexPartnerUpperIdentity f t e u) :
    forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
      Not (B f t (e + 1) y) -> Not (B f t (e + 2) y) ->
      Not (B f t (e + 1) z) -> Not (B f t (e + 2) z) ->
      y = z := by
  intro y z hy hyu hz hzu hy1 hy2 hz1 hz2
  have hyr := persistent_hole_is_old_rider_of_mex_partner_upper_identity
    het hmexEntry honeEntry hmexOne hMexPartner hy hyu hy1 hy2
  have hzr := persistent_hole_is_old_rider_of_mex_partner_upper_identity
    het hmexEntry honeEntry hmexOne hMexPartner hz hzu hz1 hz2
  omega

/-- A genuinely chronology-driven capacity transfer that does not need any
upper-identity classifier: two distinct holes surviving across both
post-entry sources would force three distinct losses on the entry edge (the
two survivors plus the first post-entry MEX).  Hence an entry-loss cap of two
already gives persistent capacity one. -/
theorem persistent_holes_unique_of_entry_loss_cap_two
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B f t e x -> Not (B f t (e + 1) x) ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        x = y \/ x = z \/ y = z) :
    forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
      Not (B f t (e + 1) y) -> Not (B f t (e + 2) y) ->
      Not (B f t (e + 1) z) -> Not (B f t (e + 2) z) ->
      y = z := by
  intro y z hy hyu hz hzu hyOne hyTwo hzOne hzTwo
  let m := f t (e + 1)
  have hmy := persistent_hole_has_lower_mex_hole
    hmexOne hy hyOne hyTwo
  have hmz := persistent_hole_has_lower_mex_hole
    hmexOne hz hzOne hzTwo
  have hm : 0 < m := hmexOne.1
  have hmu : m < u := by omega
  have hmEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hm hmu hmexOne.2.1
  have hyEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hy hyu hyOne
  have hzEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hz hzu hzOne
  rcases hEntryLossCapTwo m y z hm hmu hy hyu hz hzu
      hmEntry.1 hmEntry.2 hyEntry.1 hyEntry.2 hzEntry.1 hzEntry.2 with
      hmyEq | hmzEq | hyzEq
  · omega
  · omega
  · exact hyzEq

/-- Alternative R19 capacity route: entry-loss cap two replaces the entire
upper-identity input for the capacity count.  The only remaining scheduling
input is the (unnamed) exclusion of a persistent/new mixed pair. -/
theorem penultimate_one_hole_of_entry_loss_cap_two
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B f t e x -> Not (B f t (e + 1) x) ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hPosOneSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        B f t (e + 1) y -> Not (B f t (e + 2) y) ->
        B f t (e + 1) z -> Not (B f t (e + 2) z) -> y = z)
    (hNoPersistentNewMix :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        Not (B f t (e + 1) old) -> Not (B f t (e + 2) old) ->
        B f t (e + 1) new -> Not (B f t (e + 2) new) -> False) :
    forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
      Not (B f t (e + 2) y) -> Not (B f t (e + 2) z) -> y = z := by
  exact next_source_one_hole_of_two_provenance_caps
    (persistent_holes_unique_of_entry_loss_cap_two
      hmexEntry honeEntry hmexOne hEntryLossCapTwo)
    hPosOneSingle hNoPersistentNewMix

/-- Complete mechanical tail of the cap-two route.  This theorem makes the
remaining open inputs explicit: entry-loss cap two, position-one loss cap
one, exclusion of a persistent/new mixed pair, and the last-edge seal. -/
theorem backstop_of_entry_loss_cap_two
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hmexTwo : IsMex (B f t (e + 2)) (f t (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B f t e x -> Not (B f t (e + 1) x) ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hPosOneSingle :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        B f t (e + 1) y -> Not (B f t (e + 2) y) ->
        B f t (e + 1) z -> Not (B f t (e + 2) z) -> y = z)
    (hNoPersistentNewMix :
      forall old new, 0 < old -> old < u -> 0 < new -> new < u ->
        Not (B f t (e + 1) old) -> Not (B f t (e + 2) old) ->
        B f t (e + 1) new -> Not (B f t (e + 2) new) -> False)
    (hLastSeal :
      forall z, 0 < z -> z < u ->
        B f t (e + 2) z -> B f t (e + 3) z) :
    forall z, 0 < z -> z < u -> B f t (e + 3) z := by
  have honeTwo := penultimate_one_hole_of_entry_loss_cap_two
    hmexEntry honeEntry hmexOne hEntryLossCapTwo
    hPosOneSingle hNoPersistentNewMix
  simpa [Nat.add_assoc] using
    (penultimate_one_hole_mex_closure
      (e := e + 2) hmexTwo honeTwo hLastSeal)

theorem penultimate_one_hole_of_mex_partner_upper_identity
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (het : e + 2 < t)
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hMexPartner : MexPartnerUpperIdentity f t e u)
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
  · exact persistent_holes_unique_of_mex_partner_upper_identity
      het hmexEntry honeEntry hmexOne hMexPartner
  · exact hPosOneSingle
  · intro old new hold holdu hnew hnewu holdOne holdTwo hnewOne hnewTwo
    have hrider := persistent_hole_is_old_rider_of_mex_partner_upper_identity
      het hmexEntry honeEntry hmexOne hMexPartner
      hold holdu holdOne holdTwo
    exact hRiderExcludesNewLoss old new hold holdu hnew hnewu
      hrider holdOne holdTwo hnewOne hnewTwo

end ChompLean
