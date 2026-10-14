import R50EventETripleHostGeometry
import R27ActualGameGapCharge

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R51: close the two frozen owner-time branches of the maximal Event-E
triple-prefix survivor.

If `p<=s`, the row start has already completed in the original band column
and exact encoding keeps that same column frozen on rows `s,s+1,s+2` (and
also on `s-1` when `p<s`).  This is a nonrecursive completed-rowstart
terminal.

If `p=s+1`, the row start completes on the next row in a new column and then
freezes.  Relative to the high Event-E value `z=s+3`, either `z` is already
served in prefix `g`, or R26 produces a strictly later prefix gap.  Since
`z=d(s+2)` and that gap row is at most `s+2`, the gap is either a full source
gap or has a concrete boundary-column owner.  The remaining-height measure
strictly decreases.

Thus only the live branch `p=s+2` remains outside a named terminal.  No new
global assumption is used.
-/

/-- A `C`-gap for a diagonal value whose owner has not yet been passed is
either a full source gap or is covered by a genuinely right-boundary
column owner.  This is the future-diagonal analogue of R27's row-start gap
classification. -/
theorem future_diagonal_C_gap_is_source_gap_or_boundary_owner
    (M : RecurrenceModel) {c x a z : Nat}
    (haOwner : M.f a a = z)
    (hxa : x <= a)
    (hxgap : Not (C M.f x c z)) :
    Not (B M.f x c z) \/
      exists i, c < i /\ i < x /\ M.f i c = z := by
  by_cases hB : B M.f x c z
  · right
    rcases hB with hR | hC
    · rcases hR with ⟨i, hix, hvalue⟩
      have hci : c < i := by
        apply Nat.lt_of_not_ge
        intro hic
        have hdiag : M.f i i = z := by
          simpa [Nat.min_eq_left hic] using hvalue
        have hia : i = a :=
          diagonal_injective M (hdiag.trans haOwner.symm)
        omega
      have hboundary : M.f i c = z := by
        simpa [Nat.min_eq_right (Nat.le_of_lt hci)] using hvalue
      exact ⟨i, hci, hix, hboundary⟩
    · exact False.elim (hxgap hC)
  · exact Or.inl hB

/-- Once a completed row start is known, the diagonal-owner alternative in
`EventELowerTransition` is impossible by `D/S` disjointness. -/
theorem completed_rowstart_eventELowerTransition_no_diagonal
    {s z g p r : Nat}
    (hOld : gameF s g = p)
    (hrp : r < p) (hstart : gameF p r = p)
    (htransition : EventELowerTransition s z g) :
    (p < s /\ gameF (s - 1) g = p) \/
      C gameF (s + 1) (s + 1) p := by
  dsimp [EventELowerTransition] at htransition
  rw [hOld] at htransition
  rcases htransition.2.2 with hcarry | hdiag | hnext
  · exact Or.inl hcarry
  · rcases hdiag with ⟨a, _hga, _has, haOwner⟩
    exact False.elim
      (disjoint_D_S gameRecurrenceModel
        ⟨a, haOwner⟩ ⟨r, hrp, hstart⟩)
  · exact Or.inr hnext

/-- Exact nonrecursive terminal for the branch `p<=s`. -/
def EventEFrozenCarryTerminal (s z g p : Nat) : Prop :=
  g < p /\ p <= s /\ p < z /\
    z - p < z - g /\
    gameF p g = p /\
    gameF (s + 1) g = p /\
    gameF (s + 2) g = p /\
    (p < s -> gameF (s - 1) g = p) /\
    EventELowerTransition s z g /\
    ((p < s /\ gameF (s - 1) g = p) \/
      C gameF (s + 1) (s + 1) p)

/-- Boundary-owner/source-gap terminal for the branch `p=s+1`. -/
def EventENextOwnerGapTerminal (s z g p : Nat) : Prop :=
  p = s + 1 /\ z = s + 3 /\ g < p /\
    z - p < z - g /\
    exists u,
      u < p /\ g ≠ u /\
      gameF p u = p /\ gameF (s + 2) u = p /\
      EventELowerTransition s z g /\
      ((C gameF s g z) \/
        exists x,
          s < x /\ x < z /\ Not (C gameF x g z) /\
          z - x < z - s /\
          (Not (B gameF x g z) \/
            exists a, g < a /\ a < x /\ gameF a g = z))

/-- The low freeze regime is exactly a completed same-column carry
terminal. -/
theorem threePrefixFreezeRegime_low_is_carry_terminal
    {s z g p : Nat}
    (hg : g < s) (hOld : gameF s g = p)
    (hpPos : 0 < p) (hpz : p < z)
    (hregime : ThreePrefixHostFreezeRegime s g p)
    (hpLow : p <= s) :
    EventEFrozenCarryTerminal s z g p := by
  rcases hregime with
    ⟨u, v, hu, hv, hHostU, hHostV, hcases⟩
  rcases hcases with hPast | hNow | hLast
  · rcases hPast with
      ⟨_hpPast, huEq, hvEq, hstart⟩
    subst u
    subst v
    have hgp : g < p := by
      have hgt := gameRecurrenceModel.value_gt_index
        (q := s) (r := g) (Nat.le_of_lt hg)
      change g < gameF s g at hgt
      rw [hOld] at hgt
      exact hgt
    have hprev : p < s -> gameF (s - 1) g = p := by
      intro hps
      have hsmall : gameF p g < p + 1 := by rw [hstart]; omega
      have hconst := constant_from gameRecurrenceModel
        hgp hsmall (s - 1 - p)
      have hsum : p + (s - 1 - p) = s - 1 := by omega
      rw [hsum] at hconst
      change gameF (s - 1) g = gameF p g at hconst
      rw [hstart] at hconst
      exact hconst
    have htransition : EventELowerTransition s z g := by
      dsimp [EventELowerTransition]
      rw [hOld]
      exact ⟨hpPos, hpz, Or.inr (Or.inr ⟨g, by omega, hHostU⟩)⟩
    have hreduced := completed_rowstart_eventELowerTransition_no_diagonal
      hOld hgp hstart htransition
    exact ⟨hgp, hpLow, hpz, by omega, hstart,
      hHostU, hHostV, hprev, htransition, hreduced⟩
  · exact False.elim (by rcases hNow with ⟨hp, _⟩; omega)
  · exact False.elim (by rcases hLast with ⟨hp, _⟩; omega)

/-- At owner time `p=s+1`, completed row-start geometry plus the R26 hole
transport gives a service terminal or a strictly smaller source-gap /
boundary-owner terminal. -/
theorem threePrefixFreezeRegime_next_owner_is_gap_terminal
    {s z g p : Nat}
    (hg : g < s) (hOld : gameF s g = p)
    (hpPos : 0 < p) (hpz : p < z)
    (hzExact : z = s + 3)
    (hzOwner : gameF (s + 2) (s + 2) = z)
    (hregime : ThreePrefixHostFreezeRegime s g p)
    (hpNext : p = s + 1) :
    EventENextOwnerGapTerminal s z g p := by
  rcases hregime with
    ⟨u, v, hu, hv, hHostU, hHostV, hcases⟩
  rcases hcases with hPast | hNow | hLast
  · exact False.elim (by rcases hPast with ⟨hp, _⟩; omega)
  · rcases hNow with ⟨_hp, hgu, hvEq, hstart⟩
    subst v
    have hup : u < p := by omega
    have hgp : g < p := by
      have hgt := gameRecurrenceModel.value_gt_index
        (q := s) (r := g) (Nat.le_of_lt hg)
      change g < gameF s g at hgt
      rw [hOld] at hgt
      exact hgt
    have htransition : EventELowerTransition s z g := by
      dsimp [EventELowerTransition]
      rw [hOld]
      exact ⟨hpPos, hpz, Or.inr (Or.inr ⟨u, by omega, hHostU⟩)⟩
    have hterminal : C gameF s g z \/
        exists x,
          s < x /\ x < z /\ Not (C gameF x g z) /\
          z - x < z - s /\
          (Not (B gameF x g z) \/
            exists a, g < a /\ a < x /\ gameF a g = z) := by
      by_cases hserved : C gameF s g z
      · exact Or.inl hserved
      · right
        rcases rightmost_hole_forces_future_prefix_gap
            gameRecurrenceModel hg hOld (by omega) hpz hserved with
          ⟨x, hsx, hxz, hxgap⟩
        have hxa : x <= s + 2 := by omega
        have hsource := future_diagonal_C_gap_is_source_gap_or_boundary_owner
          gameRecurrenceModel hzOwner hxa hxgap
        exact ⟨x, hsx, hxz, hxgap, by omega, hsource⟩
    exact ⟨hpNext, hzExact, hgp, by omega,
      u, hup, hgu, hstart, hHostV, htransition, hterminal⟩
  · exact False.elim (by rcases hLast with ⟨hp, _⟩; omega)

/-- Maximal Event E: both frozen branches are now named terminals.  The
only unresolved owner-time geometry is the fully live branch `p=s+2`. -/
theorem gameF_margin_eventE_maximal_frozen_branches_terminal_reduction
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    delta + 4 = s ->
      exists c b0 b1 g p r,
        c < s /\ b0 < s /\ b1 < s + 1 /\
        gameF s c = z + 1 /\ gameF s b0 = z /\
        gameF (s + 1) b1 = z /\
        g ∈ EventEDefectBandSlots s delta c b0 /\
        g < s /\ g ≠ c /\ g ≠ b0 /\
        p = gameF s g /\ 0 < p /\ p < z /\ p <= s + 2 /\
        r < p /\ gameF p r = p /\
        EventELowerTransition s z g /\
        (p = s + 2 \/
          EventEFrozenCarryTerminal s z g p \/
          EventENextOwnerGapTerminal s z g p) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hcompleted :=
    gameF_margin_eventE_maximal_defect_forces_completed_rowstart
      hU hdip hmargin hnextDip hmax
  rcases hcompleted with
    ⟨c, b0, b1, g, p, r,
      hc, hb0, hb1, hSucc, hBase, hHostZ,
      hgBand, hg, hgc, hgb0, hpEq, hpPos, hpz, hpUpper,
      hrp, hstart, hregime⟩
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzSucc : z + 1 = d := hInv.2.2.2.1
  have hzExact : z = s + 3 := by omega
  have hunitNext := hU (s + 1) hnextDip
  change gameF (s + 2) (s + 2) + 1 = d at hunitNext
  have hzOwner : gameF (s + 2) (s + 2) = z := by omega
  have htransition : EventELowerTransition s z g := by
    rcases hregime with ⟨u, _v, hu, _hv, hHostU, _hHostV, _hcases⟩
    dsimp [EventELowerTransition]
    rw [← hpEq]
    exact ⟨hpPos, hpz, Or.inr (Or.inr ⟨u, hu, hHostU⟩)⟩
  have hcases : p <= s \/ p = s + 1 \/ p = s + 2 := by omega
  have hterminal : p = s + 2 \/
      EventEFrozenCarryTerminal s z g p \/
      EventENextOwnerGapTerminal s z g p := by
    rcases hcases with hpLow | hpNext | hpLive
    · exact Or.inr (Or.inl
        (threePrefixFreezeRegime_low_is_carry_terminal
          hg hpEq.symm hpPos hpz hregime hpLow))
    · exact Or.inr (Or.inr
        (threePrefixFreezeRegime_next_owner_is_gap_terminal
          hg hpEq.symm hpPos hpz hzExact hzOwner
          hregime hpNext))
    · exact Or.inl hpLive
  exact ⟨c, b0, b1, g, p, r,
    hc, hb0, hb1, hSucc, hBase, hHostZ,
    hgBand, hg, hgc, hgb0, hpEq, hpPos, hpz, hpUpper,
    hrp, hstart, htransition, hterminal⟩

#print axioms future_diagonal_C_gap_is_source_gap_or_boundary_owner
#print axioms completed_rowstart_eventELowerTransition_no_diagonal
#print axioms threePrefixFreezeRegime_low_is_carry_terminal
#print axioms threePrefixFreezeRegime_next_owner_is_gap_terminal
#print axioms gameF_margin_eventE_maximal_frozen_branches_terminal_reduction

end ChompLean
