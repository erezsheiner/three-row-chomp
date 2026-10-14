import Std

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# Uniform finiteness of blocker-midpoint cohorts

For an abstract blocker count `A`, assume each one-step increment is zero or
one.  The midpoint

`g(v) = (v + A(v-1)) / 2`

is monotone, and it increases strictly after two index steps.  Consequently
each fiber has at most two indices.  More generally, any strictly increasing
enumeration of the middle cohort

`r-K < g(v) <= r+K`

has length at most `4*K+2`.

Only monotonicity of `A` is used after it is derived; the upper increment
bound one is not needed for the cohort estimate.
-/

def UnitIncrement01 (A : Nat -> Nat) : Prop :=
  forall n, A (n + 1) = A n \/ A (n + 1) = A n + 1

def NatMonotone (f : Nat -> Nat) : Prop :=
  forall {a b}, a <= b -> f a <= f b

def countMidpoint (A : Nat -> Nat) (v : Nat) : Nat :=
  (v + A (v - 1)) / 2

theorem unitIncrement01_monotone
    {A : Nat -> Nat} (hstep : UnitIncrement01 A) :
    NatMonotone A := by
  intro a b hab
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := hstep (a + n)
      have hindex : a + (n + 1) = (a + n) + 1 := by omega
      rw [hindex]
      rcases hs with hs | hs <;> omega

/-- The midpoint is monotone. -/
theorem blockerMidpoint_monotone_of_unitIncrement01
    {A : Nat -> Nat} (hstep : UnitIncrement01 A) :
    NatMonotone (countMidpoint A) := by
  intro a b hab
  have hsub : a - 1 <= b - 1 := Nat.sub_le_sub_right hab 1
  have hA : A (a - 1) <= A (b - 1) :=
    unitIncrement01_monotone hstep hsub
  unfold countMidpoint
  exact Nat.div_le_div_right (Nat.add_le_add hab hA)

/-- Two index steps force at least one midpoint step.  This is the exact
source of the fiber bound two. -/
theorem blockerMidpoint_strict_after_two
    {A : Nat -> Nat} (hstep : UnitIncrement01 A) (v : Nat) :
    countMidpoint A v < countMidpoint A (v + 2) := by
  have hsub : v - 1 <= (v + 2) - 1 := by omega
  have hA : A (v - 1) <= A ((v + 2) - 1) :=
    unitIncrement01_monotone hstep hsub
  unfold countMidpoint
  omega

/-- Every midpoint sublevel is contained in an explicit finite index
prefix. -/
theorem countMidpoint_index_lt_of_le
    {A : Nat -> Nat} {v R : Nat}
    (hupper : countMidpoint A v <= R) :
    v < 2 * R + 2 := by
  unfold countMidpoint at hupper
  omega

/-- Two ordered indices in one fiber are consecutive. -/
theorem blockerMidpoint_equal_fiber_distance_le_one
    {A : Nat -> Nat} (hstep : UnitIncrement01 A)
    {a b : Nat}
    (heq : countMidpoint A a = countMidpoint A b) :
    b <= a + 1 := by
  apply Nat.le_of_not_gt
  intro hfar
  have ha2b : a + 2 <= b := by omega
  have hstrict := blockerMidpoint_strict_after_two hstep a
  have htail := blockerMidpoint_monotone_of_unitIncrement01 hstep ha2b
  omega

/-- Generic counting lemma: a monotone map which increases strictly every
two input steps uses each output level at most twice. -/
theorem twoStepStrict_pairwise_band_length_le
    (g : Nat -> Nat)
    (hmono : NatMonotone g)
    (hstrict2 : forall v, g v < g (v + 2))
    {lo hi : Nat} (xs : List Nat)
    (hpair : xs.Pairwise (fun a b => a < b))
    (hband : forall x, x ∈ xs -> lo <= g x /\ g x <= hi) :
    xs.length <= 2 * (hi - lo + 1) := by
  let P : Nat -> Prop := fun n =>
    forall (ys : List Nat), ys.length = n ->
      forall (lo hi : Nat),
        ys.Pairwise (fun a b => a < b) ->
        (forall y, y ∈ ys -> lo <= g y /\ g y <= hi) ->
        ys.length <= 2 * (hi - lo + 1)
  have hP : forall n, P n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro ys hlen lo hi hsorted hbounds
        cases ys with
        | nil => simp
        | cons a tail =>
            cases tail with
            | nil =>
                have ha := hbounds a (by simp)
                simp
                omega
            | cons b rest =>
                have htop := List.pairwise_cons.mp hsorted
                have hab : a < b := htop.1 b (by simp)
                have htailPair : (b :: rest).Pairwise
                    (fun x y => x < y) := htop.2
                have hbtop := List.pairwise_cons.mp htailPair
                have hrestPair : rest.Pairwise
                    (fun x y => x < y) := hbtop.2
                have hrestLower : forall z, z ∈ rest -> g a + 1 <= g z := by
                  intro z hz
                  have hbz : b < z := hbtop.1 z hz
                  have ha2z : a + 2 <= z := by omega
                  have hgaz : g (a + 2) <= g z := hmono ha2z
                  have hga2 : g a < g (a + 2) := hstrict2 a
                  omega
                have hrestBand : forall z, z ∈ rest ->
                    g a + 1 <= g z /\ g z <= hi := by
                  intro z hz
                  exact ⟨hrestLower z hz,
                    (hbounds z (by simp [hz])).2⟩
                have haBounds := hbounds a (by simp)
                by_cases hahi : g a < hi
                . have hrestLen : rest.length < n := by
                    simp at hlen
                    omega
                  have hrec := ih rest.length hrestLen rest rfl
                    (g a + 1) hi hrestPair hrestBand
                  simp only [List.length_cons]
                  omega
                . have hgaEq : g a = hi := by omega
                  have hrestNil : rest = [] := by
                    cases rest with
                    | nil => rfl
                    | cons z zs =>
                        have hz : z ∈ z :: zs := by simp
                        have hzLower := hrestLower z hz
                        have hzUpper := (hbounds z (by simp)).2
                        omega
                  subst rest
                  simp
                  omega
  exact hP xs.length xs rfl lo hi hpair hband

/-- Fiber-cardinality form: every strictly increasing enumeration of one
midpoint fiber has length at most two. -/
theorem blockerMidpoint_fiber_list_length_le_two
    {A : Nat -> Nat} (hstep : UnitIncrement01 A)
    {y : Nat} (xs : List Nat)
    (hpair : xs.Pairwise (fun a b => a < b))
    (hfiber : forall v, v ∈ xs -> countMidpoint A v = y) :
    xs.length <= 2 := by
  have hmono : NatMonotone (countMidpoint A) :=
    fun {_ _} h => blockerMidpoint_monotone_of_unitIncrement01 hstep h
  have hstrict := blockerMidpoint_strict_after_two hstep
  have hband : forall v, v ∈ xs ->
      y <= countMidpoint A v /\ countMidpoint A v <= y := by
    intro v hv
    have heq := hfiber v hv
    omega
  have h := twoStepStrict_pairwise_band_length_le
    (countMidpoint A) hmono hstrict xs hpair hband
  simpa using h

/-- Uniform middle-cohort bound.  The theorem is stated for an arbitrary
strictly increasing enumeration, so it applies equally to a causal prefix
or to the full extensional cohort. -/
theorem blockerMidpoint_middle_cohort_length_le
    {A : Nat -> Nat} (hstep : UnitIncrement01 A)
    {r K : Nat} (xs : List Nat)
    (hpair : xs.Pairwise (fun a b => a < b))
    (hcohort : forall v, v ∈ xs ->
      r - K < countMidpoint A v /\
        countMidpoint A v <= r + K) :
    xs.length <= 4 * K + 2 := by
  have hmono : NatMonotone (countMidpoint A) :=
    fun {_ _} h => blockerMidpoint_monotone_of_unitIncrement01 hstep h
  have hstrict := blockerMidpoint_strict_after_two hstep
  have hband : forall v, v ∈ xs ->
      r - K <= countMidpoint A v /\
        countMidpoint A v <= r + K := by
    intro v hv
    have h := hcohort v hv
    omega
  have h := twoStepStrict_pairwise_band_length_le
    (countMidpoint A) hmono hstrict xs hpair hband
  omega

/-!
## Causality warning

The cardinal theorem is extensional.  It does not place the cohort below
the current row `r`.  Even the zero count has middle-cohort indices near
`2*r`, so an induction which only knows `A` through row `r` cannot inspect
the full cohort without a separate horizon/localization argument.
-/

theorem unitIncrement01_zero :
    UnitIncrement01 (fun _ => 0) := by
  intro n
  exact Or.inl rfl

theorem middle_cohort_can_contain_future_index
    {r : Nat} (hr : 0 < r) :
    r - 1 < countMidpoint (fun _ => 0) (2 * r) /\
    countMidpoint (fun _ => 0) (2 * r) <= r + 1 /\
    r < 2 * r := by
  simp only [countMidpoint, Nat.add_zero]
  have hhalf : (2 * r) / 2 = r := by omega
  rw [hhalf]
  omega

#print axioms unitIncrement01_monotone
#print axioms blockerMidpoint_monotone_of_unitIncrement01
#print axioms blockerMidpoint_strict_after_two
#print axioms countMidpoint_index_lt_of_le
#print axioms blockerMidpoint_equal_fiber_distance_le_one
#print axioms twoStepStrict_pairwise_band_length_le
#print axioms blockerMidpoint_fiber_list_length_le_two
#print axioms blockerMidpoint_middle_cohort_length_le
#print axioms middle_cohort_can_contain_future_index

end ChompLean
