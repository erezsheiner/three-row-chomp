import R130AssignmentNoGapReduction

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
Specialized one-column closure for the dense alternating prefix in the
R141/A_k interface frame.

The general NoAssignmentGap theorem asks that all lower opening owners lie
strictly before a frontier `s`.  At the near-diagonal candidate `v-2` one
range owner is allowed to sit at the candidate column itself.  This file
proves the sharper boundary version directly.  The only old-history rows
available to the target are `v-2` and `v-1`; the exact lag-two/lag-one rail
theorems exclude both.
-/

/-- Every lower value is opened no later than the candidate column `v-2`;
blocker openings are required one column earlier, at most `v-3`. -/
def PenultimateOwnerCovered (v : Nat) : Prop :=
  forall k, 0 < k -> k < v ->
    (exists a, a <= v - 2 /\ gameF a a = k) \/
    (exists r, r <= v - 3 /\ r < k /\ gameF k r = k)

/-- The ordinary opening partition reduces the owner certificate to the
single assertion that every lower row-start owner is at most `v-3`.
Range owners need no extra theorem: their owner `a<k<v` automatically has
`a<=v-2`. -/
theorem penultimateOwnerCovered_of_lower_freeze_bound
    {v : Nat}
    (hfreeze : forall {k r}, 0 < k -> k < v -> r < k ->
      gameF k r = k -> r <= v - 3) :
    PenultimateOwnerCovered v := by
  intro k hkpos hkv
  rcases gameRecurrenceModel.opening_cover hkpos with
      ⟨a, hak, hdiag⟩ | ⟨r, hrk, hstart⟩
  · exact Or.inl ⟨a, by omega, hdiag⟩
  · exact Or.inr ⟨r, hfreeze hkpos hkv hrk hstart, hrk, hstart⟩

/-- At the candidate cell `(v,v-2)`, every positive value below `v` is in
the literal Brouwer source.  A range value is supplied by its diagonal
owner, including the boundary possibility `a=v-2`; a blocker value is
supplied by persistence from its row-start owner at most `v-3`. -/
theorem penultimateOwnerCovered_source_saturation
    {v : Nat} (hv : 4 <= v) (howners : PenultimateOwnerCovered v) :
    forall k, 0 < k -> k < v -> B gameF v (v - 2) k := by
  intro k hkpos hkv
  rcases howners k hkpos hkv with
      ⟨a, hac, hdiag⟩ | ⟨r, hrc, hrk, hstart⟩
  · left
    refine ⟨a, by omega, ?_⟩
    have hmin : min a (v - 2) = a := Nat.min_eq_left hac
    simpa [hmin] using hdiag
  · right
    refine ⟨r, by omega, ?_⟩
    have hsmall : gameRecurrenceModel.f k r < k + 1 := by
      change gameF k r < k + 1
      rw [hstart]
      omega
    have hpersist := constant_from gameRecurrenceModel hrk
      hsmall (v - k)
    have hsum : k + (v - k) = v := by omega
    change gameF (k + (v - k)) r = gameF k r at hpersist
    rw [hsum, hstart] at hpersist
    exact hpersist

/-- A blocker `v` cannot occur in the old history of column `v-2` before
row `v`.  Only rows `v-2` and `v-1` are geometrically possible, and the
exact lag-two and lag-one host theorems put `v` at columns `2` and `0`
there. -/
theorem gameF_penultimate_candidate_clean
    {v : Nat} (hv : 6 <= v) :
    Not (ColHistPred gameF v (v - 2) v) := by
  rintro ⟨a, hca, hav, hvalue⟩
  have haCases : a = v - 2 \/ a = v - 1 := by omega
  rcases haCases with ha | ha
  · subst a
    have hq : 2 <= v - 2 := by omega
    have hcol := gameF_lag_two_host_only_col2
      (q := v - 2) (c := v - 2) hq (Nat.le_refl _) (by
        simpa [show v - 2 + 2 = v by omega] using hvalue)
    omega
  · have hrow : a = (v - 2) + 1 := by omega
    have hcol := gameF_lag_one_host_only_col0
      (q := v - 2) (c := v - 2) (by omega) (by
        rw [hrow] at hvalue
        simpa [show v - 2 + 2 = v by omega] using hvalue)
    omega

/-- Boundary NoAssignmentGap at one column.

If `v` is assumed to freeze at the penultimate column `v-1`, while every
lower opening is already owned by `v-2` (and every lower blocker by `v-3`),
then the preceding column `v-2` is a live MEX cell with value `v`.  Fixed-row
injectivity contradicts the alleged freeze at `v-1`.

This is the exact game-level atom needed after aggregate Hall forces the
early A_k schedule `c_i=2i-1` (`v=2i`).  It does not assume MaxPlus,
HalfPin, FreezeOrder, or any finite-table invariant. -/
theorem gameF_no_penultimate_freeze_of_owner_coverage
    {v : Nat}
    (hv : 6 <= v)
    (hstart : gameF v (v - 1) = v)
    (howners : PenultimateOwnerCovered v) : False := by
  let c := v - 2
  have hcv : c <= v := by dsimp [c]; omega

  have hnotCarry : Not (c < v /\ gameF (v - 1) c < v) := by
    rintro ⟨hcvt, hprevLow⟩
    have hcprev : c <= v - 1 := by dsimp [c]; omega
    have hrow := gameF_low_cell_has_rowstart hcprev (by omega)
    let k := gameF (v - 1) c
    have hkpos : 0 < k := by dsimp [k]; omega
    have hkv : k < v := hprevLow
    rcases howners k hkpos hkv with
        ⟨a, _hac, hdiag⟩ | ⟨r, hrc, hrk, hstart'⟩
    · exact disjoint_D_S gameRecurrenceModel
        ⟨a, hdiag⟩ ⟨c, hrow.1, hrow.2⟩
    · have hcr : c = r :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hrow.1) (Nat.le_of_lt hrk)
          (hrow.2.trans hstart'.symm)
      dsimp [c] at hcr
      omega

  have hclean : Not (ColHistPred gameF v c v) := by
    dsimp [c]
    exact gameF_penultimate_candidate_clean hv

  have habsent : Not (B gameF v c v) := by
    intro hsource
    rcases hsource with hR | hC
    · rcases hR with ⟨a, hav, hvalue⟩
      by_cases hac : a < c
      · have hmin : min a c = a := Nat.min_eq_left (Nat.le_of_lt hac)
        have hdiag : gameF a a = v := by simpa [hmin] using hvalue
        exact disjoint_D_S gameRecurrenceModel
          ⟨a, hdiag⟩ ⟨v - 1, by omega, hstart⟩
      · apply hclean
        have hca : c <= a := Nat.le_of_not_gt hac
        have hmin : min a c = c := Nat.min_eq_right hca
        exact ⟨a, hca, hav, by simpa [hmin] using hvalue⟩
    · rcases hC with ⟨b, hbc, hvalue⟩
      have hbr : b = v - 1 :=
        gameRecurrenceModel.fixed_q_injective
          (by dsimp [c] at hbc; omega) (by omega)
          (hvalue.trans hstart.symm)
      dsimp [c] at hbc
      omega

  have hlower : forall k, 0 < k -> k < v -> B gameF v c k := by
    dsimp [c]
    exact penultimateOwnerCovered_source_saturation (by omega) howners

  have hcandidate : gameF v c = v :=
    gameF_value_of_source_mex hcv hnotCarry (by omega) habsent hlower

  have hcol : c = v - 1 :=
    gameRecurrenceModel.fixed_q_injective hcv (by omega)
      (hcandidate.trans hstart.symm)
  dsimp [c] at hcol
  omega

/-- Convenient wrapper exposing only the lower-freeze-column hypothesis. -/
theorem gameF_no_penultimate_freeze_of_lower_freeze_bound
    {v : Nat}
    (hv : 6 <= v)
    (hstart : gameF v (v - 1) = v)
    (hfreeze : forall {k r}, 0 < k -> k < v -> r < k ->
      gameF k r = k -> r <= v - 3) : False := by
  exact gameF_no_penultimate_freeze_of_owner_coverage hv hstart
    (penultimateOwnerCovered_of_lower_freeze_bound hfreeze)

#print axioms penultimateOwnerCovered_source_saturation
#print axioms gameF_penultimate_candidate_clean
#print axioms gameF_no_penultimate_freeze_of_owner_coverage
#print axioms gameF_no_penultimate_freeze_of_lower_freeze_bound

end ChompLean
