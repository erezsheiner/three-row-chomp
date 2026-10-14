import R26ActualGameFutureGap

set_option autoImplicit false

namespace ChompLean

/-!
R27: actual-recurrence anatomy of the lower new loss left by R21.

A value which is lost on a source edge is not an anonymous set-theoretic
hole.  Immediately before the loss it is supported only by a column-tail
cell `f a c`, and the constant branch forces the host row strictly below
the value: `c < a < value`.  The first theorem below records this exact
host certificate.

For the `L=3` rescue geometry, RM2 sharpens the opening type of the R21
lower loss even further.  If it is a diagonal value, its owner is forced to
be exactly the final diagonal `e+3`; otherwise it is a row-start/blocker.
-/

/-- A named strict host for a value which is transient at source column
`c`.  The inequalities say that the encoded P-position is genuinely in the
interior: it is neither a carry above the value nor a diagonal endpoint. -/
def StrictParkedHost
    (M : RecurrenceModel) (t c v a : Nat) : Prop :=
  c < a /\ a < t /\ a < v /\ M.f a c = v

/-- A parked-only value whose current-row cell does not emit it has a
strict internal column-tail host.  The nontrivial inequality is `a<v`:
if `v<=a`, the constant branch would propagate `f a c=v` to `f t c=v`,
contrary to the no-fresh hypothesis. -/
theorem parkedOnly_has_strict_host_of_no_fresh
    (M : RecurrenceModel) {t c v : Nat}
    (hpark : ParkedOnly M.f t c v)
    (hnoFresh : M.f t c ≠ v) :
    exists a, StrictParkedHost M t c v a := by
  rcases hpark.1 with ⟨a, hat, hca, hval⟩
  have hav : a < v := by
    by_cases hav : a < v
    · exact hav
    · have hva : v <= a := Nat.le_of_not_gt hav
      have hsmall : M.f a c < a + 1 := by
        rw [hval]
        omega
      have hconst := constant_from M hca hsmall (t - a)
      have hsum : a + (t - a) = t := Nat.add_sub_of_le (Nat.le_of_lt hat)
      rw [hsum, hval] at hconst
      exact False.elim (hnoFresh hconst)
  exact ⟨a, hca, hat, hav, hval⟩

/-- Exact actual-recurrence host anatomy of a one-edge source loss. -/
theorem source_loss_has_strict_parked_host
    (M : RecurrenceModel) {t c v : Nat}
    (hhere : B M.f t c v)
    (hlost : Not (B M.f t (c + 1) v)) :
    ParkedOnly M.f t c v /\
      exists a, StrictParkedHost M t c v a := by
  have hnormal :=
    (source_loss_iff_parked_and_no_replacement
      (f := M.f) (t := t) (e := c) (z := v)).mp ⟨hhere, hlost⟩
  exact ⟨hnormal.1,
    parkedOnly_has_strict_host_of_no_fresh M hnormal.1 hnormal.2.2.2⟩

/-- The no-two-P-position attack law removes the only boundary case which
pure source membership leaves ambiguous.  Every winning opening of a value
lost at `c -> c+1` lies strictly to the right of `c`.

For a row start with freeze `r<c`, propagation/constancy puts the value in
the permanent row prefix, contradicting `ParkedOnly`.  At the boundary
`r=c`, the strict host `c<a<v` would be a forbidden middle P-position,
contradicting `rowstart_no_middle`. -/
theorem source_loss_opening_is_strictly_right
    (M : RecurrenceModel) {t c v : Nat}
    (hhere : B M.f t c v)
    (hlost : Not (B M.f t (c + 1) v)) :
    (forall i, i < v -> M.f i i = v -> c < i) /\
    (forall r, r < v -> M.f v r = v -> c < r) := by
  have hanatomy := source_loss_has_strict_parked_host M hhere hlost
  rcases hanatomy.2 with ⟨a, hca, hat, hav, hhost⟩
  have hpark := hanatomy.1
  constructor
  · intro i hiv hiOwner
    by_cases hit : i < t
    · by_cases hci : c < i
      · exact hci
      · have hic : i <= c := by omega
        exact False.elim (hpark.2.1 ⟨i, hit, hic, hiOwner⟩)
    · omega
  · intro r hrv hstart
    by_cases hrc : r < c
    · have hrow : C M.f t c v := by
        by_cases hvt : v <= t
        · have hsmall : M.f v r < v + 1 := by
            rw [hstart]
            omega
          have hconst := constant_from M hrv hsmall (t - v)
          have hsum : v + (t - v) = t := Nat.add_sub_of_le hvt
          have hcurrent : M.f t r = v := by
            simpa [hsum, hstart] using hconst
          exact ⟨r, hrc, hcurrent⟩
        · have htv : t < v := Nat.lt_of_not_ge hvt
          rcases rowStartPropagation M hstart hrv (by omega) htv with
            ⟨b, hbr, hbval⟩
          exact ⟨b, Nat.lt_trans hbr hrc, hbval⟩
      exact False.elim (hpark.2.2 hrow)
    · have hcr : c <= r := Nat.le_of_not_gt hrc
      by_cases hstrict : c < r
      · exact hstrict
      · have hre : r = c := by omega
        subst r
        exact False.elim ((M.rowstart_no_middle hstart hca hav) hhost)

/-- Opening-cover normal form for an actual source loss.  Both possible
opening coordinates are strictly beyond the lost source column. -/
theorem source_loss_future_opening_normal_form
    (M : RecurrenceModel) {t c v : Nat}
    (hhere : B M.f t c v)
    (hlost : Not (B M.f t (c + 1) v)) :
    (exists i, c < i /\ i < v /\ M.f i i = v) \/
      (exists r, c < r /\ r < v /\ M.f v r = v) := by
  have hanatomy := source_loss_has_strict_parked_host M hhere hlost
  rcases hanatomy.2 with ⟨a, hca, _hat, hav, _hhost⟩
  have hv : 0 < v := by omega
  have hright := source_loss_opening_is_strictly_right M hhere hlost
  rcases M.opening_cover hv with hDiag | hRow
  · rcases hDiag with ⟨i, hiv, hiOwner⟩
    exact Or.inl ⟨i, hright.1 i hiv hiOwner, hiv, hiOwner⟩
  · rcases hRow with ⟨r, hrv, hstart⟩
    exact Or.inr ⟨r, hright.2 r hrv hstart, hrv, hstart⟩

/-- A value which survives from the entry source to the first post-entry
source, but is lost on the next edge, is parked-only at both sources.  Its
column-tail support changes to a distinct host row.

This is the precise two-column relay hidden behind an R21 lower new loss. -/
theorem successor_loss_is_two_column_parked_relay
    (M : RecurrenceModel) {t e u q : Nat}
    (hmexEntry : IsMex (B M.f t e) (M.f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f t e y) -> Not (B M.f t e z) -> y = z)
    (hq : 0 < q) (hqu : q < u)
    (hqOne : B M.f t (e + 1) q)
    (hqMissingTwo : Not (B M.f t (e + 2) q)) :
    ParkedOnly M.f t e q /\
    ParkedOnly M.f t (e + 1) q /\
    exists a0 a1,
      StrictParkedHost M t e q a0 /\
      StrictParkedHost M t (e + 1) q a1 /\
      a0 ≠ a1 := by
  have hqAnatomyOne :
      ParkedOnly M.f t (e + 1) q /\
        exists a, StrictParkedHost M t (e + 1) q a := by
    have hstep : e + 2 = (e + 1) + 1 := by omega
    rw [hstep] at hqMissingTwo
    exact source_loss_has_strict_parked_host M hqOne hqMissingTwo
  have hqNeEntry : q ≠ M.f t e := by
    intro heq
    apply hqAnatomyOne.1.2.2
    exact ⟨e, by omega, heq.symm⟩
  have hqEntry : B M.f t e q := by
    let m := M.f t e
    have hm : 0 < m := hmexEntry.1
    rcases Nat.lt_trichotomy q m with hqm | hqm | hmq
    · exact hmexEntry.2.2 q hq hqm
    · exact False.elim (hqNeEntry hqm)
    · have hmu : m < u := Nat.lt_trans hmq hqu
      by_cases hcovered : B M.f t e q
      · exact hcovered
      · have heq := honeEntry q m hq hqu hm hmu
          hcovered hmexEntry.2.1
        omega
  have hnotDiagEntry : Not (DiagPrefix M.f t e q) := by
    intro hdiag
    apply hqAnatomyOne.1.2.1
    exact (diagPrefix_successor (f := M.f) (t := t) (e := e) (z := q)).2
      (Or.inl hdiag)
  have hnotRowEntry : Not (C M.f t e q) := by
    intro hrow
    apply hqAnatomyOne.1.2.2
    exact (C_successor (f := M.f) (t := t) (e := e) (z := q)).2
      (Or.inl hrow)
  have hcolEntry : ColTail M.f t e q := by
    rcases hqEntry with hR | hC
    · rcases R_iff_diagPrefix_or_colTail.mp hR with hD | hCol
      · exact False.elim (hnotDiagEntry hD)
      · exact hCol
    · exact False.elim (hnotRowEntry hC)
  have hparkEntry : ParkedOnly M.f t e q :=
    ⟨hcolEntry, hnotDiagEntry, hnotRowEntry⟩
  have hhostEntry :=
    parkedOnly_has_strict_host_of_no_fresh M hparkEntry hqNeEntry.symm
  rcases hhostEntry with ⟨a0, ha0⟩
  rcases hqAnatomyOne.2 with ⟨a1, ha1⟩
  have hne : a0 ≠ a1 := by
    intro heq
    subst a1
    have he0 : e <= a0 := Nat.le_of_lt ha0.1
    have he1 : e + 1 <= a0 := Nat.le_of_lt ha1.1
    have hcols : e = e + 1 :=
      M.fixed_q_injective he0 he1
        (ha0.2.2.2.trans ha1.2.2.2.symm)
    omega
  exact ⟨hparkEntry, hqAnatomyOne.1, a0, a1, ha0, ha1, hne⟩

/-- `L=3` penultimate-opening dichotomy under RM2.  A positive sub-`u`
value missing at `B(e+6,e+2)` is either the final diagonal `d(e+3)` or a
row-start/blocker.

Indeed, RM2 excludes diagonal owners at or after `e+6`; R22 then pins every
remaining diagonal owner to `e+3`. -/
theorem l3_missing_penultimate_is_final_diagonal_or_rowstart_of_rm2
    (M : RecurrenceModel) {e u v : Nat}
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hv : 0 < v) (hvu : v < u)
    (hvMissing : Not (B M.f (e + 6) (e + 2) v))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    M.f (e + 3) (e + 3) = v \/
      exists r, r < v /\ M.f v r = v := by
  rcases M.opening_cover hv with hDiagonal | hRowStart
  · rcases hDiagonal with ⟨a, hav, haOwner⟩
    have haPast : a < e + 6 := by
      by_cases h : a < e + 6
      · exact h
      · have hrecord : M.f (e + 4) (e + 4) < M.f a a :=
          hRM2 (by omega)
        rw [haOwner] at hrecord
        omega
    exact Or.inl (l3_persistent_past_owner_is_final_diagonal
      M huSeat hPrevDiagonalAbove hvu hvMissing haPast haOwner)
  · exact Or.inr hRowStart

/-- The R21-strengthened version of the preceding dichotomy.  Because the
lower value is actually lost on `e+1 -> e+2`, the no-attack boundary lemma
pushes a blocker freeze strictly beyond `e+1`. -/
theorem l3_lower_new_loss_is_final_diagonal_or_future_rowstart_of_rm2
    (M : RecurrenceModel) {e u v : Nat}
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hv : 0 < v) (hvu : v < u)
    (hvOne : B M.f (e + 6) (e + 1) v)
    (hvMissing : Not (B M.f (e + 6) (e + 2) v))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    M.f (e + 3) (e + 3) = v \/
      exists r, e + 1 < r /\ r < v /\ M.f v r = v := by
  have hopen := l3_missing_penultimate_is_final_diagonal_or_rowstart_of_rm2
    M huSeat hPrevDiagonalAbove hv hvu hvMissing hRM2
  rcases hopen with hFinal | hRow
  · exact Or.inl hFinal
  · rcases hRow with ⟨r, hrv, hstart⟩
    have hright := source_loss_opening_is_strictly_right
      M (c := e + 1) (t := e + 6) (v := v)
        hvOne (by simpa [Nat.add_assoc] using hvMissing)
    exact Or.inr ⟨r, hright.2 r hrv hstart, hrv, hstart⟩

/-- Full R21-facing package for `L=3`.  In the hypothetical unserved branch,
the lower MEX `q` is a two-column parked relay with two distinct strict
hosts; the persistent value `z` is an entry-edge parked loss with its own
strict historical host; and RM2 classifies the opening of `q` as exactly
the final diagonal or a blocker. -/
theorem l3_unserved_lower_loss_anatomy_and_opening_split_of_rm2
    (M : RecurrenceModel) {e u z : Nat}
    (hmexEntry : IsMex (B M.f (e + 6) e) (M.f (e + 6) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f (e + 6) e y) ->
        Not (B M.f (e + 6) e z) -> y = z)
    (hmexOne :
      IsMex (B M.f (e + 6) (e + 1)) (M.f (e + 6) (e + 1)))
    (hmexTwo :
      IsMex (B M.f (e + 6) (e + 2)) (M.f (e + 6) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + 6) e x -> Not (B M.f (e + 6) (e + 1) x) ->
        B M.f (e + 6) e y -> Not (B M.f (e + 6) (e + 1) y) ->
        B M.f (e + 6) e z -> Not (B M.f (e + 6) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + 6) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (hNotServed : M.f (e + 6) (e + 2) ≠ z)
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    let q := M.f (e + 6) (e + 2)
    0 < q /\ q < z /\
    ParkedOnly M.f (e + 6) e q /\
    ParkedOnly M.f (e + 6) (e + 1) q /\
    (exists a0 a1,
      StrictParkedHost M (e + 6) e q a0 /\
      StrictParkedHost M (e + 6) (e + 1) q a1 /\
      a0 ≠ a1) /\
    ParkedOnly M.f (e + 6) e z /\
    (exists az, StrictParkedHost M (e + 6) e z az) /\
    (M.f (e + 3) (e + 3) = q \/
      exists r, e + 1 < r /\ r < q /\ M.f q r = q) := by
  let q := M.f (e + 6) (e + 2)
  have hobs := unserved_persistent_hole_forces_lower_new_loss
    hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
      hz hzu hzMissingOne hzMissingTwo hNotServed
  dsimp only at hobs
  have hqu : q < u := Nat.lt_trans hobs.2.1 hzu
  have hrelay := successor_loss_is_two_column_parked_relay
    M hmexEntry honeEntry hobs.1 hqu hobs.2.2.1 hobs.2.2.2
  have hzEntry := successor_hole_was_entry_loss
    hmexEntry honeEntry hz hzu hzMissingOne
  have hzAnatomy := source_loss_has_strict_parked_host
    M hzEntry.1 hzEntry.2
  have hopen := l3_lower_new_loss_is_final_diagonal_or_future_rowstart_of_rm2
    M huSeat hPrevDiagonalAbove hobs.1 hqu hobs.2.2.1 hobs.2.2.2 hRM2
  exact ⟨hobs.1, hobs.2.1, hrelay.1, hrelay.2.1, hrelay.2.2,
    hzAnatomy.1, hzAnatomy.2, hopen⟩

end ChompLean
