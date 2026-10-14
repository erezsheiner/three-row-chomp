import R50EventETripleHostGeometry

set_option autoImplicit false

namespace ChompLean

/-!
R51: attack the `p=s+2` branch of the maximal-defect event-E survivor.

The terminal occurrence is the actual row start `gameF (s+2) b2=s+2`.
Backward row-start propagation forces both earlier hosts strictly to its
left.  The recurrence at the terminal column says its preceding-row value
cannot be below `s+2`; fixed-row injectivity then leaves only the preceding
`z` host or the preceding diagonal.  Repeating the same recurrence audit at
the middle host leaves four old-row predecessors.
-/

/-- Local high-survivor atom, independent of the event-E derivation of its
displayed packet values. -/
theorem gameF_top_three_survivor_order_and_predecessor_menu
    {s c b0 bz g b1 b2 : Nat}
    (hc : c < s) (hb0 : b0 < s) (hbz : bz < s + 1)
    (hg : g < s) (hb1 : b1 < s + 1) (hb2 : b2 < s + 2)
    (hgb1 : g ≠ b1) (hb1b2 : b1 ≠ b2)
    (hBase : gameF s b0 = s + 3)
    (hSucc : gameF s c = s + 4)
    (hDiag : gameF s s = s + 5)
    (hZNext : gameF (s + 1) bz = s + 3)
    (hDiagNext : gameF (s + 1) (s + 1) = s + 4)
    (hOld : gameF s g = s + 2)
    (hMiddle : gameF (s + 1) b1 = s + 2)
    (hStart : gameF (s + 2) b2 = s + 2) :
    g < b2 ∧ b1 < b2 ∧
      (b2 = bz ∨ b2 = s + 1) ∧
      (gameF s b1 = s + 1 ∨ b1 = b0 ∨ b1 = c ∨ b1 = s) := by
  have hb1Before : b1 < b2 := by
    by_cases hb2lt : b2 < s + 1
    · have hprop := rowStartPropagation gameRecurrenceModel
        hStart hb2 (q := s + 1) hb2lt (by omega)
      rcases hprop with ⟨a, hab2, haValue⟩
      have haEq : a = b1 :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt (by omega : a < s + 1))
          (Nat.le_of_lt hb1) (haValue.trans hMiddle.symm)
      omega
    · omega
  have hgBefore : g < b2 := by
    by_cases hb2lt : b2 < s
    · have hprop := rowStartPropagation gameRecurrenceModel
        hStart hb2 (q := s) hb2lt (by omega)
      rcases hprop with ⟨a, hab2, haValue⟩
      have haEq : a = g :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt (by omega : a < s))
          (Nat.le_of_lt hg) (haValue.trans hOld.symm)
      omega
    · omega

  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  have hprevTerminalLower : s + 2 ≤ gameF (s + 1) b2 := by
    apply Nat.le_of_not_gt
    intro hlt
    have hcarry := hrec.1 (q := s + 2) (r := b2) hb2 hlt
    change gameF (s + 2) b2 = gameF (s + 1) b2 at hcarry
    rw [hStart] at hcarry
    omega
  have hprevTerminalUpper : gameF (s + 1) b2 ≤ s + 4 := by
    have hmax := diagonalMaximal gameRecurrenceModel
      (q := s + 1) (s := b2) (by omega)
    change gameF (s + 1) b2 ≤ gameF (s + 1) (s + 1) at hmax
    rw [hDiagNext] at hmax
    exact hmax
  have hprevTerminalNe : gameF (s + 1) b2 ≠ s + 2 := by
    intro heq
    have hcols := gameRecurrenceModel.fixed_q_injective
      (q := s + 1) (b₁ := b2) (b₂ := b1)
      (by omega) (Nat.le_of_lt hb1) (heq.trans hMiddle.symm)
    exact hb1b2 hcols.symm
  have hterminalMenu : b2 = bz ∨ b2 = s + 1 := by
    have hvalueCases : gameF (s + 1) b2 = s + 3 ∨
        gameF (s + 1) b2 = s + 4 := by omega
    rcases hvalueCases with hvalue | hvalue
    · left
      exact gameRecurrenceModel.fixed_q_injective
        (q := s + 1) (b₁ := b2) (b₂ := bz)
        (by omega) (Nat.le_of_lt hbz)
        (hvalue.trans hZNext.symm)
    · right
      exact gameRecurrenceModel.fixed_q_injective
        (q := s + 1) (b₁ := b2) (b₂ := s + 1)
        (by omega) (Nat.le_refl _)
        (hvalue.trans hDiagNext.symm)

  have hprevMiddleLower : s + 1 ≤ gameF s b1 := by
    apply Nat.le_of_not_gt
    intro hlt
    have hcarry := hrec.1 (q := s + 1) (r := b1) hb1 hlt
    change gameF (s + 1) b1 = gameF s b1 at hcarry
    rw [hMiddle] at hcarry
    omega
  have hprevMiddleUpper : gameF s b1 ≤ s + 5 := by
    have hmax := diagonalMaximal gameRecurrenceModel
      (q := s) (s := b1) (by omega)
    change gameF s b1 ≤ gameF s s at hmax
    rw [hDiag] at hmax
    exact hmax
  have hprevMiddleNe : gameF s b1 ≠ s + 2 := by
    intro heq
    have hcols := gameRecurrenceModel.fixed_q_injective
      (q := s) (b₁ := b1) (b₂ := g)
      (by omega) (Nat.le_of_lt hg) (heq.trans hOld.symm)
    exact hgb1 hcols.symm
  have hmiddleMenu : gameF s b1 = s + 1 ∨
      b1 = b0 ∨ b1 = c ∨ b1 = s := by
    have hvalueCases : gameF s b1 = s + 1 ∨
        gameF s b1 = s + 3 ∨ gameF s b1 = s + 4 ∨
        gameF s b1 = s + 5 := by omega
    rcases hvalueCases with hvalue | hvalue | hvalue | hvalue
    · exact Or.inl hvalue
    · exact Or.inr (Or.inl
        (gameRecurrenceModel.fixed_q_injective
          (q := s) (b₁ := b1) (b₂ := b0)
          (by omega) (Nat.le_of_lt hb0)
          (hvalue.trans hBase.symm)))
    · exact Or.inr (Or.inr (Or.inl
        (gameRecurrenceModel.fixed_q_injective
          (q := s) (b₁ := b1) (b₂ := c)
          (by omega) (Nat.le_of_lt hc)
          (hvalue.trans hSucc.symm))))
    · exact Or.inr (Or.inr (Or.inr
        (gameRecurrenceModel.fixed_q_injective
          (q := s) (b₁ := b1) (b₂ := s)
          (by omega) (Nat.le_refl _)
          (hvalue.trans hDiag.symm))))
  exact ⟨hgBefore, hb1Before, hterminalMenu, hmiddleMenu⟩

/-- The precise remaining atom in the `p=s+2` branch.  Besides the ordered
three-host charge, it has only a `2 x 4` predecessor menu. -/
def MaximalEventEHighSurvivorAtom
    (s c b0 bz g b1 b2 r : Nat) : Prop :=
  gameF s g = s + 2 ∧ r = b2 ∧
    3 ≤ c ∧ 2 ≤ b0 ∧ 1 ≤ bz ∧ 2 ≤ g ∧ 3 ≤ b2 ∧
    g < b2 ∧ b1 < b2 ∧
    (b2 = bz ∨ b2 = s + 1) ∧
    (gameF s b1 = s + 1 ∨ b1 = b0 ∨ b1 = c ∨ b1 = s) ∧
    (b2 = bz → gameF s b1 = s + 1 ∨ b1 = b0 ∨ b1 = c) ∧
    (b1 = s → b2 = s + 1)

/-- Under `UnitDip` and the displayed maximal-defect numerical-margin
Event-E frame, the R49 survivor has already reached its owner by row `s+1`,
or satisfies the explicit high-survivor atom above. -/
theorem gameF_margin_eventE_maximal_defect_high_survivor_reduction
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    delta + 4 = s →
      ∃ c b0 bz g b1 b2 r,
        z = s + 3 ∧
        c < s ∧ b0 < s ∧ bz < s + 1 ∧
        gameF s c = z + 1 ∧ gameF s b0 = z ∧
        gameF (s + 1) bz = z ∧
        g ∈ EventEDefectBandSlots s delta c b0 ∧
        g < s ∧ g ≠ c ∧ g ≠ b0 ∧
        b1 < s + 1 ∧ b2 < s + 2 ∧
        gameF (s + 1) b1 = gameF s g ∧
        gameF (s + 2) b2 = gameF s g ∧
        r < gameF s g ∧ gameF (gameF s g) r = gameF s g ∧
        ThreeConsecutiveHostGeometry s (gameF s g) g b1 b2 ∧
        (gameF s g ≤ s + 1 ∨
          MaximalEventEHighSurvivorAtom s c b0 bz g b1 b2 r) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hcert :=
    gameF_margin_eventE_maximal_defect_triple_host_geometry
      hU hdip hmargin hnextDip hmax
  rcases hcert with
    ⟨c, b0, bz, g, b1, b2, r, hzMax,
      hc, hb0, hbz, hSucc, hBase, hHostZ,
      hgBand, hgs, hgc, hgb0, hb1, hb2,
      hHost1, hHost2, _hqPos, _hqz,
      hr, hstart, _hcount, hgeometry⟩
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  rcases hInv with
    ⟨_hdeltaPos, _hdeltaUpper, _hdeltaSum, hzDiag, _rest⟩
  have hDiagNext : gameF (s + 1) (s + 1) = s + 4 := by
    change z = s + 3 at hzMax
    change d = s + 4
    calc
      d = z + 1 := hzDiag.symm
      _ = (s + 3) + 1 := congrArg (fun x => x + 1) hzMax
      _ = s + 4 := by simp [Nat.add_assoc]
  have hunit := hU s hdip
  change d + 1 = gameF s s at hunit
  have hDiag : gameF s s = s + 5 := by omega
  have hcLower : 3 ≤ c := by
    have hcap := high_cell_output_source_capacity
      gameRecurrenceModel (q := s) (r := c) (m := s + 4)
      (Nat.le_of_lt hc) (by omega) (by simpa [hzMax] using hSucc)
    omega
  have hb0Lower : 2 ≤ b0 := by
    have hcap := high_cell_output_source_capacity
      gameRecurrenceModel (q := s) (r := b0) (m := s + 3)
      (Nat.le_of_lt hb0) (by omega) (by simpa [hzMax] using hBase)
    omega
  have hbzLower : 1 ≤ bz := by
    have hcap := high_cell_output_source_capacity
      gameRecurrenceModel (q := s + 1) (r := bz) (m := s + 3)
      (Nat.le_of_lt hbz) (by omega) (by simpa [hzMax] using hHostZ)
    omega
  have hgLower : 2 ≤ g := by
    have houter := List.mem_of_mem_erase hgBand
    have hinner := List.mem_of_mem_erase houter
    have hrange := List.mem_range'_1.mp hinner
    dsimp [EventEDefectBandSlots] at hgBand
    omega

  by_cases hlow : gameF s g ≤ s + 1
  · exact ⟨c, b0, bz, g, b1, b2, r, hzMax,
      hc, hb0, hbz, hSucc, hBase, hHostZ,
      hgBand, hgs, hgc, hgb0, hb1, hb2,
      hHost1, hHost2, hr, hstart, hgeometry, Or.inl hlow⟩
  · have hp : gameF s g = s + 2 := by
      have hpUpper := hgeometry.1
      omega
    have hgeoCopy := hgeometry
    rcases hgeoCopy with
      ⟨_hpBound, _hgp, _hb1p, _hb2p,
        hfirstIff, hsecondIff, hspanIff, _hcases⟩
    have hgb1' : g ≠ b1 := by
      intro heq
      have hle := hfirstIff.mp heq
      omega
    have hb1b2' : b1 ≠ b2 := by
      intro heq
      have hle := hsecondIff.mp heq
      omega
    have hgb2' : g ≠ b2 := by
      intro heq
      have hle := hspanIff.mp heq
      omega
    have hmenu := gameF_top_three_survivor_order_and_predecessor_menu
      hc hb0 hbz hgs hb1 hb2 hgb1' hb1b2'
      (by simpa [hzMax] using hBase)
      (by simpa [hzMax] using hSucc)
      hDiag
      (by simpa [hzMax] using hHostZ)
      hDiagNext
      hp (by simpa [hp] using hHost1) (by simpa [hp] using hHost2)
    rcases hmenu with ⟨hgBefore, hb1Before, hterminal, hmiddle⟩
    have hterminalRefined : b2 = bz →
        gameF s b1 = s + 1 ∨ b1 = b0 ∨ b1 = c := by
      intro hb2z
      have hmiddleCopy := hmiddle
      rcases hmiddleCopy with hlowMiddle | hb0Middle | hcMiddle | hsMiddle
      · exact Or.inl hlowMiddle
      · exact Or.inr (Or.inl hb0Middle)
      · exact Or.inr (Or.inr hcMiddle)
      · subst b1
        subst b2
        omega
    have hmiddleBoundary : b1 = s → b2 = s + 1 := by
      intro hb1s
      have hterminalCopy := hterminal
      rcases hterminalCopy with hb2z | hb2Boundary
      · subst b1
        subst b2
        omega
      · exact hb2Boundary
    have hrEq : r = b2 := by
      exact gameRecurrenceModel.fixed_q_injective
        (q := s + 2) (b₁ := r) (b₂ := b2)
        (by rw [hp] at hr; omega) (Nat.le_of_lt hb2)
        (by rw [hp] at hstart hHost2; exact hstart.trans hHost2.symm)
    have hb2Lower : 3 ≤ b2 := by omega
    refine ⟨c, b0, bz, g, b1, b2, r, hzMax,
      hc, hb0, hbz, hSucc, hBase, hHostZ,
      hgBand, hgs, hgc, hgb0, hb1, hb2,
      hHost1, hHost2, hr, hstart, hgeometry, Or.inr ?_⟩
    exact ⟨hp, hrEq, hcLower, hb0Lower, hbzLower,
      hgLower, hb2Lower, hgBefore, hb1Before, hterminal, hmiddle,
      hterminalRefined, hmiddleBoundary⟩

#print axioms gameF_top_three_survivor_order_and_predecessor_menu
#print axioms gameF_margin_eventE_maximal_defect_high_survivor_reduction

end ChompLean
