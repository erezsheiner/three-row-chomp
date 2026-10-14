import R17OrderedLoss

set_option autoImplicit false

namespace ChompLean

/-!
R18 red-team boundary.

The young-column enumeration is mechanical.  The row-prefix re-emission of
the named values is not: it appears below as an explicit hypothesis.  The
last section gives a MEX-valid two-loss source frame, showing that a cap of
two parked values does not imply a cap of one death.
-/

/-- At source depth three the column tail has exactly two possible hosts. -/
theorem colTail_depth3_cases
    {f : Nat -> Nat -> Nat} {e z : Nat}
    (h : ColTail f (e + 3) e z) :
    f (e + 1) e = z \/ f (e + 2) e = z := by
  rcases h with ⟨a, hat, hea, hval⟩
  have : a = e + 1 \/ a = e + 2 := by omega
  rcases this with rfl | rfl
  · exact Or.inl hval
  · exact Or.inr hval

/-- At source depth four the column tail has exactly three possible hosts. -/
theorem colTail_depth4_cases
    {f : Nat -> Nat -> Nat} {e z : Nat}
    (h : ColTail f (e + 4) e z) :
    f (e + 1) e = z \/ f (e + 2) e = z \/ f (e + 3) e = z := by
  rcases h with ⟨a, hat, hea, hval⟩
  have : a = e + 1 \/ a = e + 2 \/ a = e + 3 := by omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl hval
  · exact Or.inr (Or.inl hval)
  · exact Or.inr (Or.inr hval)

/-- The exact proof obligation behind depth-three parked vanish: each of the
two named history values must either be at least `u`, or already have a
current-row witness strictly to the left of the source column. -/
theorem no_sub_u_parked_depth3_of_named_cover
    {f : Nat -> Nat -> Nat} {e u : Nat}
    (h1 : u <= f (e + 1) e \/
      DiagPrefix f (e + 3) e (f (e + 1) e) \/
      C f (e + 3) e (f (e + 1) e))
    (h2 : u <= f (e + 2) e \/
      DiagPrefix f (e + 3) e (f (e + 2) e) \/
      C f (e + 3) e (f (e + 2) e)) :
    forall z, z < u -> Not (ParkedOnly f (e + 3) e z) := by
  intro z hzu hpark
  rcases colTail_depth3_cases hpark.1 with h | h
  · rw [h] at h1
    rcases h1 with hhigh | hdiag | hrow
    · omega
    · exact hpark.2.1 hdiag
    · exact hpark.2.2 hrow
  · rw [h] at h2
    rcases h2 with hhigh | hdiag | hrow
    · omega
    · exact hpark.2.1 hdiag
    · exact hpark.2.2 hrow

/-- The analogous exact obligation at depth four. -/
theorem no_sub_u_parked_depth4_of_named_cover
    {f : Nat -> Nat -> Nat} {e u : Nat}
    (h1 : u <= f (e + 1) e \/
      DiagPrefix f (e + 4) e (f (e + 1) e) \/
      C f (e + 4) e (f (e + 1) e))
    (h2 : u <= f (e + 2) e \/
      DiagPrefix f (e + 4) e (f (e + 2) e) \/
      C f (e + 4) e (f (e + 2) e))
    (h3 : u <= f (e + 3) e \/
      DiagPrefix f (e + 4) e (f (e + 3) e) \/
      C f (e + 4) e (f (e + 3) e)) :
    forall z, z < u -> Not (ParkedOnly f (e + 4) e z) := by
  intro z hzu hpark
  rcases colTail_depth4_cases hpark.1 with h | h | h
  · rw [h] at h1
    rcases h1 with hhigh | hdiag | hrow
    · omega
    · exact hpark.2.1 hdiag
    · exact hpark.2.2 hrow
  · rw [h] at h2
    rcases h2 with hhigh | hdiag | hrow
    · omega
    · exact hpark.2.1 hdiag
    · exact hpark.2.2 hrow
  · rw [h] at h3
    rcases h3 with hhigh | hdiag | hrow
    · omega
    · exact hpark.2.1 hdiag
    · exact hpark.2.2 hrow

/-- Parked vanish really does seal an edge; this is the valid mechanical
corollary used at the L=3 final edge. -/
theorem no_sub_u_parked_implies_edge_seal
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hvanish : forall z, z < u -> Not (ParkedOnly f t e z)) :
    forall z, z < u -> B f t e z -> B f t (e + 1) z := by
  intro z hzu hcurrent
  by_cases hnext : B f t (e + 1) z
  · exact hnext
  · exact False.elim
      (hvanish z hzu (source_loss_implies_parkedOnly hcurrent hnext))

/-! Exact owner-index boundary for `L3-UPPER-OWNER`. -/

/-- A range owner already below the time horizon cannot lie at or before the
successor source column if its value is genuinely lost there. -/
theorem lost_past_range_owner_ge_next_next
    {f : Nat -> Nat -> Nat} {t e a z : Nat}
    (hat : a < t) (hdiag : f a a = z)
    (hlost : Not (B f t (e + 1) z)) :
    e + 2 <= a := by
  by_cases h : e + 2 <= a
  · exact h
  · have hae : a <= e + 1 := by omega
    exact False.elim (hlost (Or.inl
      (R_iff_diagPrefix_or_colTail.mpr
        (Or.inl ⟨a, hat, hae, hdiag⟩))))

/-- Consequently, once a separate structural argument supplies the upper
bound `a <= e+2`, the owner pin is pure arithmetic.  Neither past-range
classification nor this upper bound follows from source loss itself. -/
theorem lost_past_range_owner_eq_next_next
    {f : Nat -> Nat -> Nat} {t e a z : Nat}
    (hat : a < t) (hdiag : f a a = z)
    (hlost : Not (B f t (e + 1) z))
    (hupper : a <= e + 2) :
    a = e + 2 := by
  have hlower := lost_past_range_owner_ge_next_next hat hdiag hlost
  omega

/-- Proof-facing form: past-range classification plus the owner upper bound
turns the lost value into the next diagonal sink. -/
theorem lost_past_range_owner_is_next_diagonal
    {f : Nat -> Nat -> Nat} {t e a z : Nat}
    (hat : a < t) (hdiag : f a a = z)
    (hlost : Not (B f t (e + 1) z))
    (hupper : a <= e + 2) :
    f (e + 2) (e + 2) = z := by
  have haeq := lost_past_range_owner_eq_next_next hat hdiag hlost hupper
  simpa [haeq] using hdiag

/-! A MEX-valid source counterframe to the counting shortcut. -/

def twoParkedMexCounter (a b : Nat) : Nat :=
  if a = 2 /\ b = 1 then 5
  else if a = 3 /\ b = 1 then 7
  else if a = 7 /\ b = 1 then 1
  else if a = 7 /\ b = 2 then 2
  else 0

private theorem twoParked_source_one_iff {z : Nat} :
    B twoParkedMexCounter 7 1 z <-> z = 0 \/ z = 5 \/ z = 7 := by
  constructor
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hac : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 := by omega
      rcases hac with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [twoParkedMexCounter] at hval ⊢ <;> omega
    · have hbeq : b = 0 := by omega
      subst b
      simp [twoParkedMexCounter] at hval ⊢
      omega
  · intro h
    rcases h with rfl | rfl | rfl
    · left; exact ⟨0, by omega, by simp [twoParkedMexCounter]⟩
    · left; exact ⟨2, by omega, by simp [twoParkedMexCounter]⟩
    · left; exact ⟨3, by omega, by simp [twoParkedMexCounter]⟩

private theorem twoParked_source_two_iff {z : Nat} :
    B twoParkedMexCounter 7 2 z <-> z = 0 \/ z = 1 := by
  constructor
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hac : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 := by omega
      rcases hac with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [twoParkedMexCounter] at hval ⊢ <;> omega
    · have hbc : b = 0 \/ b = 1 := by omega
      rcases hbc with rfl | rfl <;>
        simp [twoParkedMexCounter] at hval ⊢ <;> omega
  · intro h
    rcases h with rfl | rfl
    · left; exact ⟨0, by omega, by simp [twoParkedMexCounter]⟩
    · right; exact ⟨1, by omega, by simp [twoParkedMexCounter]⟩

theorem twoParked_old_cell_is_mex :
    IsMex (B twoParkedMexCounter 7 1) (twoParkedMexCounter 7 1) := by
  have hout : twoParkedMexCounter 7 1 = 1 := by simp [twoParkedMexCounter]
  rw [hout]
  refine ⟨by omega, ?_, ?_⟩
  · rw [twoParked_source_one_iff]
    omega
  · intro z hz hlt
    omega

theorem twoParked_next_cell_is_mex :
    IsMex (B twoParkedMexCounter 7 2) (twoParkedMexCounter 7 2) := by
  have hout : twoParkedMexCounter 7 2 = 2 := by simp [twoParkedMexCounter]
  rw [hout]
  refine ⟨by omega, ?_, ?_⟩
  · rw [twoParked_source_two_iff]
    omega
  · intro z hz hlt
    rw [twoParked_source_two_iff]
    omega

/-- Even with both adjacent current-row cells on their exact MEX branches,
two parked values can die on the same edge.  Therefore
`parked-count <= 2` does not imply `death-count <= 1`. -/
theorem two_parked_values_can_both_die_under_mex :
    IsMex (B twoParkedMexCounter 7 1) (twoParkedMexCounter 7 1) /\
    IsMex (B twoParkedMexCounter 7 2) (twoParkedMexCounter 7 2) /\
    ParkedOnly twoParkedMexCounter 7 1 5 /\
    ParkedOnly twoParkedMexCounter 7 1 7 /\
    Not (B twoParkedMexCounter 7 2 5) /\
    Not (B twoParkedMexCounter 7 2 7) /\
    twoParkedMexCounter (1 + 2) (1 + 2) != 7 := by
  refine ⟨twoParked_old_cell_is_mex, twoParked_next_cell_is_mex, ?_, ?_, ?_, ?_, ?_⟩
  · exact source_loss_implies_parkedOnly
      ((twoParked_source_one_iff).2 (Or.inr (Or.inl rfl)))
      (by rw [twoParked_source_two_iff]; omega)
  · exact source_loss_implies_parkedOnly
      ((twoParked_source_one_iff).2 (Or.inr (Or.inr rfl)))
      (by rw [twoParked_source_two_iff]; omega)
  · rw [twoParked_source_two_iff]
    omega
  · rw [twoParked_source_two_iff]
    omega
  · simp [twoParkedMexCounter]

end ChompLean
