import ChompLean

set_option autoImplicit false

namespace ChompLean

/-!
`SparseDualFailures` formalizes the finite bracketing core of the
density-one AA theorem.

In the application, `x a = Int.natAbs (A (2*a + A a) - a)` and `bad a`
means that at least one of the two dual AA inequalities fails at `a`.
The elementary AA algebra gives:

* `x 0 = 0`;
* speed at most two;
* `x a <= 3` at every non-bad index.

The theorem below says that `B` bad indices cannot support height greater
than `2*B+3`.  It is independent of every Chomp-specific or asymptotic
hypothesis.
-/

/-- A path of speed at most two, caged below three away from `bad`, is
bounded by twice the number of bad sites in the ambient prefix plus three. -/
theorem sparseDualFailures_bracket
    {x : Nat -> Nat} {bad : Nat -> Prop}
    (hzero : x 0 = 0)
    (hlip : forall i j, i <= j -> x j <= x i + 2 * (j - i))
    (hgood : forall a, Not (bad a) -> x a <= 3)
    {N B r : Nat}
    (hrN : r <= N)
    (hbadBudget : Not (Exists fun f : Fin (B + 1) -> Nat =>
      Function.Injective f /\ forall j, f j <= N /\ bad (f j))) :
    x r <= 2 * B + 3 := by
  by_cases hbound : x r <= 2 * B + 3
  · exact hbound
  · have hxlarge : 2 * B + 3 < x r := Nat.lt_of_not_ge hbound
    have hxr : x r <= 2 * r := by
      have h := hlip 0 r (Nat.zero_le r)
      simpa [hzero] using h
    have hBr : B < r := by omega

    let f : Fin (B + 1) -> Nat := fun j => r - j.val

    have hfMap : forall j, f j <= N /\ bad (f j) := by
      intro j
      have hjr : j.val <= r := by omega
      have hfr : f j <= r := Nat.sub_le r j.val
      constructor
      · exact Nat.le_trans hfr hrN
      · by_cases hfbad : bad (f j)
        · exact hfbad
        · have hxsmall : x (f j) <= 3 := hgood (f j) hfbad
          have hmove := hlip (f j) r hfr
          have hdist : r - f j = j.val := by
            simp [f]
            omega
          rw [hdist] at hmove
          omega

    have hf : Function.Injective f := by
      intro i j hij
      have hval : r - i.val = r - j.val := by
        simpa [f] using hij
      have hir : i.val <= r := by omega
      have hjr : j.val <= r := by omega
      apply Fin.ext
      omega

    exfalso
    apply hbadBudget
    exact Exists.intro f ⟨hf, hfMap⟩

/-- Uniform prefix form of `sparseDualFailures_bracket`. -/
theorem sparseDualFailures_uniform
    {x : Nat -> Nat} {bad : Nat -> Prop}
    (hzero : x 0 = 0)
    (hlip : forall i j, i <= j -> x j <= x i + 2 * (j - i))
    (hgood : forall a, Not (bad a) -> x a <= 3)
    {N B : Nat}
    (hbadBudget : Not (Exists fun f : Fin (B + 1) -> Nat =>
      Function.Injective f /\ forall j, f j <= N /\ bad (f j))) :
    forall r, r <= N -> x r <= 2 * B + 3 := by
  intro r hr
  exact sparseDualFailures_bracket hzero hlip hgood hr hbadBudget

end ChompLean
