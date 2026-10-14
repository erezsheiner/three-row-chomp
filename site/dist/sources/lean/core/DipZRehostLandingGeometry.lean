import DipZRehostRM2Reduction
import PrefreezeHostDiagonalCriterion

set_option autoImplicit false

namespace ChompLean

/-!
Emission-branch audit for `ZRehost`.

Nothing in this file assumes `TwoStepDiagonalRecordLaw`.  The first theorem
shows that, once UNIT-DIP is granted, rehosting the named dip hole on the
next row is *exactly* the exclusion of a consecutive dip.  The later
theorems use the two empirically rigid entry hosts and the actual encoding's
same-lower no-repeat law to remove recovery depths two and four.
-/

/-- A positive non-diagonal hole immediately below `d(t)` is hosted on row
`t+1` exactly when that next row is not another dip, assuming UNIT-DIP.

The `hnotPast` premise is the formal margin-at-least-two guard.  It excludes
the historical-diagonal branch of the next diagonal source.  No RM2 premise
is used. -/
theorem dip_hole_next_hosted_iff_no_consecutive_dip
    (M : RecurrenceModel) (hU : UnitDip M) {t z : Nat}
    (hzpos : 0 < z)
    (hdipHole : M.f t t = z + 1)
    (hnotPast : forall j, j < t -> M.f j j ≠ z) :
    C M.f (t + 1) (t + 1) z <->
      Not (M.f (t + 1) (t + 1) < M.f t t) := by
  constructor
  · intro hhost hnextDip
    rcases hhost with ⟨b, hb, hvalue⟩
    have hmax := diagonalMaximal M (q := t + 1) (s := b)
      (Nat.le_of_lt hb)
    rw [hvalue] at hmax
    have hstrict : z < M.f (t + 1) (t + 1) := by
      have hne : z ≠ M.f (t + 1) (t + 1) := by
        intro heq
        have hcols := M.fixed_q_injective
          (q := t + 1) (b₁ := b) (b₂ := t + 1)
          (Nat.le_of_lt hb) (Nat.le_refl _) (hvalue.trans heq)
        omega
      omega
    have hunit := hU t hnextDip
    rw [hdipHole] at hunit
    omega
  · intro hnoNextDip
    have hdiagNe : M.f t t ≠ M.f (t + 1) (t + 1) := by
      intro heq
      have hidx := diagonal_injective M heq
      omega
    have hdiagRise : M.f t t < M.f (t + 1) (t + 1) := by
      omega
    have hzBelow : z < M.f (t + 1) (t + 1) := by
      rw [hdipHole] at hdiagRise
      omega
    have hB : B M.f (t + 1) (t + 1) z :=
      M.mex_no_skip (Nat.le_refl _) (M.diagonal_gt _) hzpos hzBelow
    rcases hB with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hmin : min a (t + 1) = a :=
        Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at hvalue
      by_cases hat : a < t
      · exact False.elim ((hnotPast a hat) hvalue)
      · have haEq : a = t := by omega
        subst a
        rw [hdipHole] at hvalue
        omega
    · exact hC

/-- The two rigid entry hosts of event E forbid landing in their same
columns on the recovery row.  In depth notation these are depths four and
two, respectively. -/
theorem gameF_dip_recovery_host_avoids_depths_two_four
    {e z b : Nat}
    (hprevV2 : gameF (e + 3) (e + 1) = z)
    (hdipV1 : gameF (e + 4) (e + 3) = z)
    (hhigh : e + 5 < z)
    (hb : b < e + 5)
    (hhost : gameF (e + 5) b = z) :
    b ≠ e + 1 /\ b ≠ e + 3 := by
  constructor
  · intro hbEq
    subst b
    exact encoding_same_lower_no_repeat game_encodes
      (s := e + 1) (t₁ := e + 3) (t₂ := e + 5) (p := z)
      (by omega) (by omega) hhigh hprevV2 hhost
  · intro hbEq
    subst b
    exact encoding_same_lower_no_repeat game_encodes
      (s := e + 3) (t₁ := e + 4) (t₂ := e + 5) (p := z)
      (by omega) (by omega) hhigh hdipV1 hhost

/-- Exact four-way landing geometry supplied by the two no-repeat
certificates.  A rehost is either deeper than depth five, at depth five, at
depth three, or at depth one.  Depths two and four are impossible. -/
theorem gameF_dip_zrehost_four_way
    {e z : Nat}
    (hprevV2 : gameF (e + 3) (e + 1) = z)
    (hdipV1 : gameF (e + 4) (e + 3) = z)
    (hhigh : e + 5 < z)
    (hrehost : C gameF (e + 5) (e + 5) z) :
    C gameF (e + 5) e z \/
      gameF (e + 5) e = z \/
      gameF (e + 5) (e + 2) = z \/
      gameF (e + 5) (e + 4) = z := by
  rcases hrehost with ⟨b, hb, hhost⟩
  have hav := gameF_dip_recovery_host_avoids_depths_two_four
    hprevV2 hdipV1 hhigh hb hhost
  by_cases hdeep : b < e
  · exact Or.inl ⟨b, hdeep, hhost⟩
  · have hcases : b = e \/ b = e + 2 \/ b = e + 4 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact Or.inr (Or.inl hhost)
    · exact Or.inr (Or.inr (Or.inl hhost))
    · exact Or.inr (Or.inr (Or.inr hhost))

/-- The advertised `{depth 3, depth 5}` landing is now reduced to exactly
two chronology exclusions: no host deeper than five, and no `V1` reclaim.
Both are stated explicitly; neither is smuggled in through RM2. -/
theorem gameF_dip_zrehost_depth_three_or_five
    {e z : Nat}
    (hprevV2 : gameF (e + 3) (e + 1) = z)
    (hdipV1 : gameF (e + 4) (e + 3) = z)
    (hhigh : e + 5 < z)
    (hrehost : C gameF (e + 5) (e + 5) z)
    (hnoDeep : Not (C gameF (e + 5) e z))
    (hnoV1 : gameF (e + 5) (e + 4) ≠ z) :
    gameF (e + 5) e = z \/ gameF (e + 5) (e + 2) = z := by
  rcases gameF_dip_zrehost_four_way
      hprevV2 hdipV1 hhigh hrehost with hdeep | h5 | h3 | h1
  · exact False.elim (hnoDeep hdeep)
  · exact Or.inl h5
  · exact Or.inr h3
  · exact False.elim (hnoV1 h1)

/-! ## Exact entry-side scheduler reductions -/

/--
If `d(r+1)=z+1` and `z` is not an earlier diagonal, the last off-diagonal
cell emits `z` exactly when `z` has not already been emitted in the strict
prefix of that row.  Thus the advertised `V1=z` entry identity is precisely
a first-eligible/assignment assertion, not an additional MEX calculation.
-/
theorem diagonal_predecessor_at_v1_iff_no_early_host
    (M : RecurrenceModel) {r z : Nat}
    (hzpos : 0 < z)
    (hdiag : M.f (r + 1) (r + 1) = z + 1)
    (hnotPast : forall a, a < r + 1 -> M.f a a ≠ z) :
    M.f (r + 1) r = z <-> Not (C M.f (r + 1) r z) := by
  constructor
  · intro hlast hearly
    rcases hearly with ⟨b, hbr, hvalue⟩
    have hcols := M.fixed_q_injective
      (q := r + 1) (b₁ := b) (b₂ := r)
      (by omega) (by omega) (hvalue.trans hlast.symm)
    omega
  · intro hnoEarly
    have hB : B M.f (r + 1) (r + 1) z := by
      apply M.mex_no_skip (Nat.le_refl _) (M.diagonal_gt _) hzpos
      rw [hdiag]
      omega
    rcases hB with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hmin : min a (r + 1) = a :=
        Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at hvalue
      exact False.elim ((hnotPast a ha) hvalue)
    · rcases hC with ⟨b, hb, hvalue⟩
      have hbCases : b < r \/ b = r := by omega
      rcases hbCases with hbEarly | rfl
      · exact False.elim (hnoEarly ⟨b, hbEarly, hvalue⟩)
      · exact hvalue

/--
Two cells before the diagonal, the analogous statement has exactly two
guards.  The value `z=d(r+2)-2` lands at `V2` iff it has no deeper current-row
host and the following `V1` cell is not itself `z`.
-/
theorem diagonal_two_below_at_v2_iff_scheduler_guards
    (M : RecurrenceModel) {r z : Nat}
    (hzpos : 0 < z)
    (hdiag : M.f (r + 2) (r + 2) = z + 2)
    (hnotPast : forall a, a < r + 2 -> M.f a a ≠ z) :
    M.f (r + 2) r = z <->
      Not (C M.f (r + 2) r z) /\ M.f (r + 2) (r + 1) ≠ z := by
  constructor
  · intro hV2
    constructor
    · rintro ⟨b, hbr, hvalue⟩
      have hcols := M.fixed_q_injective
        (q := r + 2) (b₁ := b) (b₂ := r)
        (by omega) (by omega) (hvalue.trans hV2.symm)
      omega
    · intro hV1
      have hcols := M.fixed_q_injective
        (q := r + 2) (b₁ := r) (b₂ := r + 1)
        (by omega) (by omega) (hV2.trans hV1.symm)
      omega
  · rintro ⟨hnoDeep, hnoV1⟩
    have hB : B M.f (r + 2) (r + 2) z := by
      apply M.mex_no_skip (Nat.le_refl _) (M.diagonal_gt _) hzpos
      rw [hdiag]
      omega
    rcases hB with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have hmin : min a (r + 2) = a :=
        Nat.min_eq_left (Nat.le_of_lt ha)
      rw [hmin] at hvalue
      exact False.elim ((hnotPast a ha) hvalue)
    · rcases hC with ⟨b, hb, hvalue⟩
      by_cases hbr : b < r
      · exact False.elim (hnoDeep ⟨b, hbr, hvalue⟩)
      · have hcases : b = r \/ b = r + 1 := by omega
        rcases hcases with rfl | rfl
        · exact hvalue
        · exact False.elim (hnoV1 hvalue)

/--
Complete entry-rigidity reduction at a numerical margin-at-least-two unit
dip.  The three observed identities

* `V1(t-1)=z+1`,
* `V2(t-1)=z`,
* `V1(t)=z`

hold iff three explicit early-placement events are absent.  This theorem
uses UNIT-DIP only to identify `d(t-1)=z+2`; it does not assume RM2.
-/
theorem gameF_margin_two_entry_rigidity_iff_no_early_placements
    {e z : Nat}
    (hU : UnitDip gameRecurrenceModel)
    (hdip : gameF (e + 4) (e + 4) < gameF (e + 3) (e + 3))
    (hdiag : gameF (e + 4) (e + 4) = z + 1)
    (hmargin : forall j, j <= e + 2 -> gameF j j < z) :
    (gameF (e + 3) (e + 2) = z + 1 /\
      gameF (e + 3) (e + 1) = z /\
      gameF (e + 4) (e + 3) = z) <->
    (Not (C gameF (e + 3) (e + 2) (z + 1)) /\
      Not (C gameF (e + 3) (e + 1) z) /\
      Not (C gameF (e + 4) (e + 3) z)) := by
  have hzpos : 0 < z := by
    have hgt := gameRecurrenceModel.diagonal_gt (e + 4)
    change e + 4 < gameF (e + 4) (e + 4) at hgt
    rw [hdiag] at hgt
    omega
  have hprevDiag : gameF (e + 3) (e + 3) = z + 2 := by
    have hunit := hU (e + 3) (by simpa [Nat.add_assoc] using hdip)
    rw [show e + 3 + 1 = e + 4 by omega] at hunit
    change gameF (e + 4) (e + 4) + 1 =
      gameF (e + 3) (e + 3) at hunit
    rw [hdiag] at hunit
    omega
  have hnotPastPreZ : forall a, a < e + 3 -> gameF a a ≠ z := by
    intro a ha heq
    have hlt := hmargin a (by omega)
    omega
  have hnotPastPreSucc : forall a, a < e + 3 -> gameF a a ≠ z + 1 := by
    intro a ha heq
    have hlt := hmargin a (by omega)
    omega
  have hnotPastDipZ : forall a, a < e + 4 -> gameF a a ≠ z := by
    intro a ha
    by_cases haOld : a < e + 3
    · exact hnotPastPreZ a haOld
    · have haEq : a = e + 3 := by omega
      subst a
      rw [hprevDiag]
      omega
  have hV1PreIff :
      gameF (e + 3) (e + 2) = z + 1 <->
        Not (C gameF (e + 3) (e + 2) (z + 1)) := by
    apply diagonal_predecessor_at_v1_iff_no_early_host
      gameRecurrenceModel (z := z + 1)
    · omega
    · simpa [Nat.add_assoc] using hprevDiag
    · simpa [Nat.add_assoc] using hnotPastPreSucc
  have hV2PreIff :
      gameF (e + 3) (e + 1) = z <->
        Not (C gameF (e + 3) (e + 1) z) /\
          gameF (e + 3) (e + 2) ≠ z := by
    apply diagonal_two_below_at_v2_iff_scheduler_guards
      gameRecurrenceModel (r := e + 1) (z := z)
    · exact hzpos
    · simpa [Nat.add_assoc] using hprevDiag
    · simpa [Nat.add_assoc] using hnotPastPreZ
  have hV1DipIff :
      gameF (e + 4) (e + 3) = z <->
        Not (C gameF (e + 4) (e + 3) z) := by
    apply diagonal_predecessor_at_v1_iff_no_early_host
      gameRecurrenceModel (r := e + 3) (z := z)
    · exact hzpos
    · simpa [Nat.add_assoc] using hdiag
    · simpa [Nat.add_assoc] using hnotPastDipZ
  constructor
  · rintro ⟨hV1Pre, hV2Pre, hV1Dip⟩
    exact ⟨hV1PreIff.mp hV1Pre, (hV2PreIff.mp hV2Pre).1,
      hV1DipIff.mp hV1Dip⟩
  · rintro ⟨hnoSucc, hnoZPre, hnoZDip⟩
    have hV1Pre := hV1PreIff.mpr hnoSucc
    have hV2Pre : gameF (e + 3) (e + 1) = z := by
      apply hV2PreIff.mpr
      exact ⟨hnoZPre, by omega⟩
    have hV1Dip := hV1DipIff.mpr hnoZDip
    exact ⟨hV1Pre, hV2Pre, hV1Dip⟩

end ChompLean
