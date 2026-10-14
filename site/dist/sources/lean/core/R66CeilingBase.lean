import R56TopTwoHoles

/-!
# R66 Stage A — ceiling base (T1, J1, J2, DiagDoubleSlack)

Formalization of `_v4r3_diagdoubleslack_PROOF.md` (R03), staged.

This file first builds the reusable **finite-base infrastructure**: a helper that
pins a non-carry cell to a concrete mex value from an explicit characterization of
its source `B = R ∨ C`, then the rails and the small diagonal table.

All values are proved from the recurrence (`gameF_brouwerRecurrence`); nothing is
postulated and no receipt is used as a premise.
-/

set_option autoImplicit false

namespace ChompLean

/-- Pin a non-carry cell's value from an explicit source characterization.
If `m` is positive, absent from the source `B`, and every positive value below
`m` is present, then the mex-cell equals `m`. -/
theorem gameF_value_of_source_mex {q r m : Nat}
    (hrq : r ≤ q)
    (hnc : ¬ (r < q ∧ gameF (q - 1) r < q))
    (hm0 : 0 < m)
    (habsent : ¬ B gameF q r m)
    (hlower : ∀ k, 0 < k → k < m → B gameF q r k) :
    gameF q r = m := by
  obtain ⟨hpos, hnotin, hcov⟩ := gameF_brouwerRecurrence.2 hrq hnc
  have hle : gameF q r ≤ m := by
    rcases Nat.lt_or_ge m (gameF q r) with hlt | hge
    · exact absurd (hcov m hm0 hlt) habsent
    · exact hge
  have hge : m ≤ gameF q r := by
    rcases Nat.lt_or_ge (gameF q r) m with hlt | hge2
    · exact absurd (hlower _ hpos hlt) hnotin
    · exact hge2
  omega

/-- **Column-0 rail** `f(r,0) = r+1` for every row (bank fact `f(b,0)=b+1`). -/
theorem gameF_col0 (r : Nat) : gameF r 0 = r + 1 := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    apply gameF_value_of_source_mex (by omega)
    · rintro ⟨hlt, hcarry⟩
      have hpred : gameF (r - 1) 0 = (r - 1) + 1 := ih (r - 1) (by omega)
      omega
    · omega
    · intro h
      simp only [B, R, C] at h
      rcases h with ⟨a, ha, hval⟩ | ⟨b, hb, _⟩
      · have hmin : min a 0 = 0 := by omega
        rw [hmin, ih a ha] at hval; omega
      · omega
    · intro k hk0 hkr
      refine Or.inl ⟨k - 1, by omega, ?_⟩
      have hmin : min (k - 1) 0 = 0 := by omega
      rw [hmin, ih (k - 1) (by omega)]; omega

/-- The empty-source diagonal opening `d(0) = 1`. -/
theorem gameF_zero_zero : gameF 0 0 = 1 := gameF_col0 0

#print axioms gameF_col0

end ChompLean
