import R201CausalCohortFromWeakEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R202: a high-value stream cannot move a low MEX target

The middle stream seen in the W4 frontier contains many values above the
terminal target `u`.  Those values are irrelevant to the landing of `u` (and
to every smaller output).  This file proves that fact at recurrence level,
without appealing to an empirical greedy simulator.

Two candidate rows may have completely different outputs above `u`.  Assume
only that their vertical sources agree on values at most `u`, and that both
rows take the MEX branch.  Scanning left-to-right, every output at most `u`
then occurs in exactly the same physical column in the two rows.  The proof is
strong induction on the column: earlier low outputs make the horizontal
prefixes agree, while earlier high outputs cannot affect a MEX at most `u`.
-/

/-- Two MEXes are equal as soon as their source predicates agree through the
smaller relevant cutoff.  Nothing above `u` is inspected. -/
theorem isMex_eq_of_source_agree_through
    {P Q : Nat -> Prop} {m n u : Nat}
    (hmex : IsMex P m)
    (hnex : IsMex Q n)
    (hagree : forall k, 0 < k -> k <= u -> (P k <-> Q k))
    (hlow : m <= u \/ n <= u) :
    m = n := by
  rcases Nat.lt_trichotomy m n with hmn | heq | hnm
  . have hmu : m <= u := by
      rcases hlow with hmu | hnu
      . exact hmu
      . omega
    have hQm : Q m := hnex.2.2 m hmex.1 hmn
    exact False.elim (hmex.2.1 ((hagree m hmex.1 hmu).2 hQm))
  . exact heq
  . have hnu : n <= u := by
      rcases hlow with hmu | hnu
      . omega
      . exact hnu
    have hPn : P n := hmex.2.2 n hnex.1 hnm
    exact False.elim (hnex.2.1 ((hagree n hnex.1 hnu).1 hPn))

/-- The past-row (`R`) input to a current row agrees through a cutoff.  No
condition is imposed on values above that cutoff. -/
def VerticalSourceAgreeThrough
    (f g : Nat -> Nat -> Nat) (q u : Nat) : Prop :=
  forall c k, c <= q -> 0 < k -> k <= u ->
    (R f q c k <-> R g q c k)

/-- Low-output invariance for an entire MEX row.  Even if `f` and `g` differ
arbitrarily above `u`, every output `<= u` has the same value and column.

This is the formal high-tail-erasure lemma needed by the target-specific W4
transducer: future middle-cohort values above the induction target cannot
displace that target. -/
theorem mexRow_low_output_invariant
    {f g : Nat -> Nat -> Nat} {q u : Nat}
    (hvertical : VerticalSourceAgreeThrough f g q u)
    (hmexF : forall c, c <= q -> IsMex (B f q c) (f q c))
    (hmexG : forall c, c <= q -> IsMex (B g q c) (g q c)) :
    forall c, c <= q ->
      (f q c <= u \/ g q c <= u) ->
      f q c = g q c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro hcq hlow
      have hsource : forall k, 0 < k -> k <= u ->
          (B f q c k <-> B g q c k) := by
        intro k hkpos hku
        unfold B
        constructor
        . intro h
          rcases h with hR | hC
          . exact Or.inl ((hvertical c k hcq hkpos hku).1 hR)
          . rcases hC with ⟨b, hbc, hfb⟩
            have hbq : b <= q := by omega
            have hfg : f q b = g q b :=
              ih b hbc hbq (by left; omega)
            exact Or.inr ⟨b, hbc, hfg ▸ hfb⟩
        . intro h
          rcases h with hR | hC
          . exact Or.inl ((hvertical c k hcq hkpos hku).2 hR)
          . rcases hC with ⟨b, hbc, hgb⟩
            have hbq : b <= q := by omega
            have hfg : f q b = g q b :=
              ih b hbc hbq (by right; omega)
            exact Or.inr ⟨b, hbc, hfg.symm ▸ hgb⟩
      exact isMex_eq_of_source_agree_through
        (hmexF c hcq) (hmexG c hcq) hsource hlow

/-- Membership form: below the cutoff, the two current rows have identical
physical host columns. -/
theorem mexRow_low_host_iff
    {f g : Nat -> Nat -> Nat} {q u k c : Nat}
    (hvertical : VerticalSourceAgreeThrough f g q u)
    (hmexF : forall x, x <= q -> IsMex (B f q x) (f q x))
    (hmexG : forall x, x <= q -> IsMex (B g q x) (g q x))
    (hcq : c <= q)
    (hku : k <= u) :
    f q c = k <-> g q c = k := by
  constructor
  . intro hfk
    have heq := mexRow_low_output_invariant hvertical hmexF hmexG
      c hcq (by left; omega)
    omega
  . intro hgk
    have heq := mexRow_low_output_invariant hvertical hmexF hmexG
      c hcq (by right; omega)
    omega

/-- Mixed lifecycle/MEX form used by the physical W4 scan.  At a sealed or
otherwise causally pinned column the two rows have the same output; at every
other column both take their MEX branch.  Arbitrary discrepancies above `u`
on those MEX branches still cannot move a low target. -/
theorem mixedRow_low_output_invariant
    {f g : Nat -> Nat -> Nat} {q u : Nat}
    (hvertical : VerticalSourceAgreeThrough f g q u)
    (hstep : forall c, c <= q ->
      f q c = g q c \/
        (IsMex (B f q c) (f q c) /\
          IsMex (B g q c) (g q c))) :
    forall c, c <= q ->
      (f q c <= u \/ g q c <= u) ->
      f q c = g q c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      intro hcq hlow
      rcases hstep c hcq with heq | hmex
      . exact heq
      . have hsource : forall k, 0 < k -> k <= u ->
            (B f q c k <-> B g q c k) := by
          intro k hkpos hku
          unfold B
          constructor
          . intro h
            rcases h with hR | hC
            . exact Or.inl ((hvertical c k hcq hkpos hku).1 hR)
            . rcases hC with ⟨b, hbc, hfb⟩
              have hbq : b <= q := by omega
              have hfg : f q b = g q b :=
                ih b hbc hbq (by left; omega)
              exact Or.inr ⟨b, hbc, hfg ▸ hfb⟩
          . intro h
            rcases h with hR | hC
            . exact Or.inl ((hvertical c k hcq hkpos hku).2 hR)
            . rcases hC with ⟨b, hbc, hgb⟩
              have hbq : b <= q := by omega
              have hfg : f q b = g q b :=
                ih b hbc hbq (by right; omega)
              exact Or.inr ⟨b, hbc, hfg.symm ▸ hgb⟩
        exact isMex_eq_of_source_agree_through
          hmex.1 hmex.2 hsource hlow

/-- Host-column form of the mixed scan theorem. -/
theorem mixedRow_low_host_iff
    {f g : Nat -> Nat -> Nat} {q u k c : Nat}
    (hvertical : VerticalSourceAgreeThrough f g q u)
    (hstep : forall x, x <= q ->
      f q x = g q x \/
        (IsMex (B f q x) (f q x) /\
          IsMex (B g q x) (g q x)))
    (hcq : c <= q)
    (hku : k <= u) :
    f q c = k <-> g q c = k := by
  constructor
  . intro hfk
    have heq := mixedRow_low_output_invariant hvertical hstep
      c hcq (by left; omega)
    omega
  . intro hgk
    have heq := mixedRow_low_output_invariant hvertical hstep
      c hcq (by right; omega)
    omega

end ChompLean

#print axioms ChompLean.isMex_eq_of_source_agree_through
#print axioms ChompLean.mexRow_low_output_invariant
#print axioms ChompLean.mexRow_low_host_iff
#print axioms ChompLean.mixedRow_low_output_invariant
#print axioms ChompLean.mixedRow_low_host_iff
