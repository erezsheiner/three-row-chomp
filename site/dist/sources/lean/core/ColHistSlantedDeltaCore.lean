import ChompLean.Proof
import Std

set_option autoImplicit false

namespace ChompLean

/-!
Abstract persistent-predicate core for a provenance-separated slanted
ColHist update.  This file proves only finite-menu algebra.  It does not
assert that the three-row Chomp recurrence satisfies the localization
premise.

Lists represent finite edit menus.  Duplicates are harmless: filtering a
menu with duplicates can only over-count the number of distinct edits, so a
list-length bound is already a valid mathematical O(1) edit bound.
-/

/-- Pointwise symmetric-difference predicate. -/
def PredChanged (A B : Nat -> Prop) (x : Nat) : Prop :=
  (A x /\ Not (B x)) \/ (B x /\ Not (A x))

/-- The constant candidate menu named by the proposed adjacent-tail lemma. -/
def slantedEditMenu
    (pivot : Nat) (oldTail11 newTail12 : List Nat) : List Nat :=
  pivot :: (oldTail11 ++ newTail12)

/-- Abstract localization premise: every changed membership lies in the
finite candidate menu. -/
def AdjacentTailLocalization
    (Cold Cnew : Nat -> Prop)
    (pivot : Nat) (oldTail11 newTail12 : List Nat) : Prop :=
  forall x,
    PredChanged Cold Cnew x ->
    x ∈ slantedEditMenu pivot oldTail11 newTail12

/-- Apply exact target-membership decisions only on `menu`; keep every old
membership outside it. -/
def persistentMenuUpdate
    (Cold : Nat -> Prop) (menu : List Nat)
    (targetMem : Nat -> Bool) (x : Nat) : Prop :=
  if x ∈ menu then targetMem x = true else Cold x

/-- Outside a localized symmetric difference, old and new membership agree. -/
theorem mem_iff_of_not_mem_localized_menu
    {Cold Cnew : Nat -> Prop} {menu : List Nat}
    (hloc : forall x, PredChanged Cold Cnew x -> x ∈ menu)
    {x : Nat} (hx : x ∉ menu) :
    (Cold x ↔ Cnew x) := by
  constructor
  · intro hOld
    by_cases hNew : Cnew x
    · exact hNew
    · exact False.elim (hx (hloc x (Or.inl ⟨hOld, hNew⟩)))
  · intro hNew
    by_cases hOld : Cold x
    · exact hOld
    · exact False.elim (hx (hloc x (Or.inr ⟨hNew, hOld⟩)))

/-- Exactness of the persistent update.  No decision outside the finite menu
is queried. -/
theorem persistentMenuUpdate_iff_target
    {Cold Cnew : Nat -> Prop} {menu : List Nat}
    {targetMem : Nat -> Bool}
    (hloc : forall x, PredChanged Cold Cnew x -> x ∈ menu)
    (hexact : forall x, x ∈ menu ->
      (targetMem x = true ↔ Cnew x)) :
    forall x,
      persistentMenuUpdate Cold menu targetMem x ↔ Cnew x := by
  intro x
  by_cases hx : x ∈ menu
  · simp [persistentMenuUpdate, hx, hexact x hx]
  · have hstable := mem_iff_of_not_mem_localized_menu hloc hx
    simp [persistentMenuUpdate, hx, hstable]

/-- Decidable Boolean form of `PredChanged`. -/
def predChangedBool
    (Cold Cnew : Nat -> Prop)
    [DecidablePred Cold] [DecidablePred Cnew]
    (x : Nat) : Bool :=
  decide (Cold x) != decide (Cnew x)

/-- The concrete list of true edits selected from a candidate menu. -/
def changedEditList
    (Cold Cnew : Nat -> Prop)
    [DecidablePred Cold] [DecidablePred Cnew]
    (menu : List Nat) : List Nat :=
  menu.filter (predChangedBool Cold Cnew)

/-- Every genuine edit is present in the filtered edit list, by localization. -/
theorem changed_mem_changedEditList
    {Cold Cnew : Nat -> Prop}
    [DecidablePred Cold] [DecidablePred Cnew]
    {menu : List Nat}
    (hloc : forall x, PredChanged Cold Cnew x -> x ∈ menu)
    {x : Nat} (hchange : PredChanged Cold Cnew x) :
    x ∈ changedEditList Cold Cnew menu := by
  rcases hchange with hchange | hchange
  · simp [changedEditList, predChangedBool,
      hloc x (Or.inl hchange), hchange.1, hchange.2]
  · simp [changedEditList, predChangedBool,
      hloc x (Or.inr hchange), hchange.1, hchange.2]

/-- Filtering never makes the edit list longer than its constant menu. -/
theorem changedEditList_length_le_menu
    {Cold Cnew : Nat -> Prop}
    [DecidablePred Cold] [DecidablePred Cnew]
    (menu : List Nat) :
    (changedEditList Cold Cnew menu).length <= menu.length := by
  unfold changedEditList
  exact List.length_filter_le (predChangedBool Cold Cnew) menu

/-- Parametric menu-length bound. -/
theorem slantedEditMenu_length_le
    {pivot kOld kNew : Nat} {oldTail newTail : List Nat}
    (hOld : oldTail.length <= kOld)
    (hNew : newTail.length <= kNew) :
    (slantedEditMenu pivot oldTail newTail).length <= 1 + kOld + kNew := by
  simp [slantedEditMenu]
  omega

/-- The original narrow menu has length at most `1+11+12=24`. -/
theorem slantedEditMenu_length_le_24
    {pivot : Nat} {oldTail11 newTail12 : List Nat}
    (hOld : oldTail11.length <= 11)
    (hNew : newTail12.length <= 12) :
    (slantedEditMenu pivot oldTail11 newTail12).length <= 24 := by
  simpa using slantedEditMenu_length_le
    (pivot := pivot) (kOld := 11) (kNew := 12) hOld hNew

/-- Complete parametric O(1)-edit theorem for a localized menu. -/
theorem localized_persistent_colHist_update_parametric
    {Cold Cnew : Nat -> Prop}
    [DecidablePred Cold] [DecidablePred Cnew]
    {pivot kOld kNew : Nat} {oldTail newTail : List Nat}
    {targetMem : Nat -> Bool}
    (hloc : AdjacentTailLocalization
      Cold Cnew pivot oldTail newTail)
    (hOld : oldTail.length <= kOld)
    (hNew : newTail.length <= kNew)
    (hexact : forall x,
      x ∈ slantedEditMenu pivot oldTail newTail ->
      (targetMem x = true ↔ Cnew x)) :
    (forall x,
      persistentMenuUpdate Cold
        (slantedEditMenu pivot oldTail newTail) targetMem x ↔ Cnew x) /\
    (changedEditList Cold Cnew
      (slantedEditMenu pivot oldTail newTail)).length <= 1 + kOld + kNew := by
  constructor
  · exact persistentMenuUpdate_iff_target hloc hexact
  · exact Nat.le_trans
      (changedEditList_length_le_menu
        (Cold := Cold) (Cnew := Cnew)
        (slantedEditMenu pivot oldTail newTail))
      (slantedEditMenu_length_le hOld hNew)

/-- Original narrow specialization, retained for compatibility. -/
theorem localized_persistent_colHist_update
    {Cold Cnew : Nat -> Prop}
    [DecidablePred Cold] [DecidablePred Cnew]
    {pivot : Nat} {oldTail11 newTail12 : List Nat}
    {targetMem : Nat -> Bool}
    (hloc : AdjacentTailLocalization
      Cold Cnew pivot oldTail11 newTail12)
    (hOld : oldTail11.length <= 11)
    (hNew : newTail12.length <= 12)
    (hexact : forall x,
      x ∈ slantedEditMenu pivot oldTail11 newTail12 ->
      (targetMem x = true ↔ Cnew x)) :
    (forall x,
      persistentMenuUpdate Cold
        (slantedEditMenu pivot oldTail11 newTail12) targetMem x ↔ Cnew x) /\
    (changedEditList Cold Cnew
      (slantedEditMenu pivot oldTail11 newTail12)).length <= 24 := by
  simpa using localized_persistent_colHist_update_parametric
    (pivot := pivot) (kOld := 11) (kNew := 12)
    hloc hOld hNew hexact

/-- Widened recursively-closed strip specialization:
`1+14+17=32` candidate edits. -/
theorem localized_persistent_colHist_update_wide
    {Cold Cnew : Nat -> Prop}
    [DecidablePred Cold] [DecidablePred Cnew]
    {pivot : Nat} {oldTail14 newTail17 : List Nat}
    {targetMem : Nat -> Bool}
    (hloc : AdjacentTailLocalization
      Cold Cnew pivot oldTail14 newTail17)
    (hOld : oldTail14.length <= 14)
    (hNew : newTail17.length <= 17)
    (hexact : forall x,
      x ∈ slantedEditMenu pivot oldTail14 newTail17 ->
      (targetMem x = true ↔ Cnew x)) :
    (forall x,
      persistentMenuUpdate Cold
        (slantedEditMenu pivot oldTail14 newTail17) targetMem x ↔ Cnew x) /\
    (changedEditList Cold Cnew
      (slantedEditMenu pivot oldTail14 newTail17)).length <= 32 := by
  simpa using localized_persistent_colHist_update_parametric
    (pivot := pivot) (kOld := 14) (kNew := 17)
    hloc hOld hNew hexact

/-! ## Causal selector corollary -/

/-- Indicator bit used by the value-ordered replay. -/
def propBit (P : Prop) [Decidable P] : Nat :=
  if P then 1 else 0

/-- Once the game-specific old-ColHist discriminator is proved, the blocker
bit is read from `C_-1`; no diagonal membership is an input. -/
theorem blockerBit_eq_oldColHistBit
    {u : Nat} {Cminus : Nat -> Prop} {IsBlocker : Nat -> Prop}
    [DecidablePred Cminus] [DecidablePred IsBlocker]
    (hselector : IsBlocker u ↔ Cminus u) :
    propBit (IsBlocker u) = propBit (Cminus u) := by
  unfold propBit
  by_cases hB : IsBlocker u <;> by_cases hC : Cminus u <;>
    simp_all

/-! ## The precise game theorems still needed

The following are propositions, not axioms and not proved statements about
`gameF`.  Supplying concrete causally generated `oldTail11/newTail12`
functions and proving these propositions are the outstanding
recurrence-level obligations.
-/

/-- Column-history membership through rows `<top`. -/
def ColHistPred
    (f : Nat -> Nat -> Nat) (top c z : Nat) : Prop :=
  exists a, c <= a /\ a < top /\ f a c = z

/-- Parametric exact all-rows statement needed for a horizontal slanted step
`(top,c) -> (top+1,c+1)`.  The two tail menus must themselves be generated
from already constructed prefix events; cardinality alone is not enough
algorithmically. -/
def GameAdjacentColHistLocalizationNeededAt
    (kOld kNew : Nat)
    (f : Nat -> Nat -> Nat) (d : Nat -> Nat)
    (oldTail newTail : Nat -> Nat -> List Nat) : Prop :=
  forall top c,
    c + 1 < top ->
    (oldTail top c).length <= kOld /\
    (newTail top c).length <= kNew /\
    AdjacentTailLocalization
      (ColHistPred f top c)
      (ColHistPred f (top + 1) (c + 1))
      (d c) (oldTail top c) (newTail top c)

/-- Original narrow localization specification. -/
def GameAdjacentColHistLocalizationNeeded
    (f : Nat -> Nat -> Nat) (d : Nat -> Nat)
    (oldTail11 newTail12 : Nat -> Nat -> List Nat) : Prop :=
  GameAdjacentColHistLocalizationNeededAt
    11 12 f d oldTail11 newTail12

/-- Widened recursively-closed-strip localization specification. -/
def GameAdjacentColHistLocalizationWideNeeded
    (f : Nat -> Nat -> Nat) (d : Nat -> Nat)
    (oldTail14 newTail17 : Nat -> Nat -> List Nat) : Prop :=
  GameAdjacentColHistLocalizationNeededAt
    14 17 f d oldTail14 newTail17

/-- Exact finite-menu decision statement needed in addition to localization.
The supplied `targetMem` function must be implemented from constructed
prefix data; this proposition records extensional correctness only. -/
def GameAdjacentColHistMenuDecisionNeeded
    (f : Nat -> Nat -> Nat) (d : Nat -> Nat)
    (oldTail11 newTail12 : Nat -> Nat -> List Nat)
    (targetMem : Nat -> Nat -> Nat -> Bool) : Prop :=
  forall top c x,
    c + 1 < top ->
    x ∈ slantedEditMenu (d c)
      (oldTail11 top c) (newTail12 top c) ->
    (targetMem top c x = true ↔
      ColHistPred f (top + 1) (c + 1) x)

/-- Parametric combined game-level delta specification. -/
def GameColHistSlantedDeltaNeededAt
    (kOld kNew : Nat)
    (f : Nat -> Nat -> Nat) (d : Nat -> Nat)
    (oldTail newTail : Nat -> Nat -> List Nat)
    (targetMem : Nat -> Nat -> Nat -> Bool) : Prop :=
  GameAdjacentColHistLocalizationNeededAt
    kOld kNew f d oldTail newTail /\
  GameAdjacentColHistMenuDecisionNeeded
    f d oldTail newTail targetMem

/-- Original narrow combined specification. -/
def GameColHistSlantedDeltaNeeded
    (f : Nat -> Nat -> Nat) (d : Nat -> Nat)
    (oldTail11 newTail12 : Nat -> Nat -> List Nat)
    (targetMem : Nat -> Nat -> Nat -> Bool) : Prop :=
  GameColHistSlantedDeltaNeededAt
    11 12 f d oldTail11 newTail12 targetMem

/-- Widened recursively-closed-strip combined specification. -/
def GameColHistSlantedDeltaWideNeeded
    (f : Nat -> Nat -> Nat) (d : Nat -> Nat)
    (oldTail14 newTail17 : Nat -> Nat -> List Nat)
    (targetMem : Nat -> Nat -> Nat -> Bool) : Prop :=
  GameColHistSlantedDeltaNeededAt
    14 17 f d oldTail14 newTail17 targetMem

/-- Separate game-specific selector and pending-diagonal statement needed on
residual collisions.  `ResidualCollision` must itself be recognized by
prefix-only transition legality.  This definition makes no claim that the
game satisfies the statement. -/
def GameOldColHistSelectorNeeded
    (f : Nat -> Nat -> Nat) (d g A : Nat -> Nat)
    (IsBlocker ResidualCollision : Nat -> Prop)
    [DecidablePred IsBlocker] : Prop :=
  forall u,
    ResidualCollision u ->
    let v := u - 1
    let Cminus := ColHistPred f v (g v - 1)
    let Czero := ColHistPred f v (g v)
    let t := u - A (u - 1) - 1
    (IsBlocker u ↔ Cminus u) /\
    (Cminus u ↔ Czero u) /\
    d t = u + propBit (IsBlocker u)

#print axioms persistentMenuUpdate_iff_target
#print axioms localized_persistent_colHist_update_parametric
#print axioms localized_persistent_colHist_update
#print axioms localized_persistent_colHist_update_wide
#print axioms blockerBit_eq_oldColHistBit

end ChompLean
