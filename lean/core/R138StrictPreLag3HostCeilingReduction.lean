import R137UpperRailTerminalTimingReduction

set_option autoImplicit false

namespace ChompLean

/-!
R138: conditional closure of the first upper-rail failure from the strict
pre-lag-three host ceiling.

Nothing in this file asserts the ceiling unconditionally.  The upper-rail
wrapper asks for it only on the exact bad branch `g+1<r`.  In particular,
the counterexample to unconditional terminal-predecessor no-early-history
is outside the scope of the theorem below.
-/

/-- Every host of blocker `v` strictly before its lag-three row lies in a
column strictly left of `g`.

The subtraction form is intentional: the intended instantiation is
`v=q+3`, so `v-3=q`.  The witness-side hypothesis `e<=a` is retained
explicitly rather than inferred from a history predicate. -/
def StrictPreLag3HostCeiling (v g : Nat) : Prop :=
  forall a e,
    e <= a ->
    a < v - 3 ->
    gameF a e = v ->
    e < g

/-- Exact first-failure contradiction.

R137 supplies an early terminal-predecessor sighting

```text
exists a, r<=a<q and gameF a (r-1)=q+3.
```

The strict host ceiling puts `r-1<g`, while the preserved bad-branch
premise `g+1<r` puts `g+1<=r-1`. -/
theorem gameF_firstFailure_false_of_strictPreLag3HostCeiling
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hceiling : StrictPreLag3HostCeiling (q + 3) g) :
    False := by
  rcases gameF_firstFailure_forces_early_terminal_sighting
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with
    ⟨a, hra, haq, hvalue⟩
  have hcolumn : r - 1 < g :=
    hceiling a (r - 1) (by omega) (by omega) hvalue
  omega

/-- First-failure-scoped form of the proposed atom.  This is the exact
interface needed by the closure theorem; it does not claim
`StrictPreLag3HostCeiling` for blockers on the good upper-rail branch. -/
def StrictPreLag3HostCeilingOnFirstFailure
    (v g r : Nat) : Prop :=
  g + 1 < r -> StrictPreLag3HostCeiling v g

/-- Upper-rail wrapper with the bad-branch premise preserved exactly.

The only new hypothesis beyond R137's owner/preview ledger is
`StrictPreLag3HostCeilingOnFirstFailure (q+3) g r`.  The proof opens the
strict failure branch, specializes that conditional atom there, and invokes
the preceding R137 terminal-predecessor contradiction. -/
theorem gameF_upperRail_of_strictPreLag3HostCeiling_on_firstFailure
    {q r g H : Nat}
    (hq : 1 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hceilingOnFailure :
      StrictPreLag3HostCeilingOnFirstFailure (q + 3) g r) :
    r <= g + 1 := by
  apply Nat.le_of_not_gt
  intro hfailure
  exact gameF_firstFailure_false_of_strictPreLag3HostCeiling
    hq hrv hstart howners hfailure hinterior hpreviewLe
    hpreviewLeft hpreview (hceilingOnFailure hfailure)

#print axioms gameF_firstFailure_false_of_strictPreLag3HostCeiling
#print axioms gameF_upperRail_of_strictPreLag3HostCeiling_on_firstFailure

end ChompLean
