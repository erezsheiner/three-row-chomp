import R49EventETwoEdgeTriplePrefix

set_option autoImplicit false

namespace ChompLean

/-!
R50: exact host geometry of a value occurring in three consecutive strict
row prefixes.

The same-lower no-repeat law only applies before the value's square
`rowStartPos` has been reached.  After that row the row-start encoding is
allowed to persist forever in one column.  The correct statement is therefore
an exact three-regime normal form, not an unconditional three-column theorem.

In maximal-defect event E the R49 survivor is below `z = s+3`, hence its
row-start row is at most `s+2`.  R50 classifies all possibilities and, in
particular, extracts an actual row-start witness for the survivor.
-/

/-- Exact host geometry for a value `p` already present at `(s,g)` and also
present in the next two strict prefixes, under the sharp upper bound
`p <= s+2`.

* if `p <= s`, its row start has already happened, and the same column `g`
  hosts it on all three rows;
* if `p = s+1`, the old host differs from the row-start host, which then
  persists to row `s+2`;
* if `p = s+2`, all three hosts are distinct and the last one is the
  row-start column.
-/
def ThreePrefixHostFreezeRegime (s g p : Nat) : Prop :=
  exists u v,
    u < s + 1 /\ v < s + 2 /\
    gameF (s + 1) u = p /\ gameF (s + 2) v = p /\
    ((p <= s /\ u = g /\ v = g /\ gameF p g = p) \/
      (p = s + 1 /\ g ≠ u /\ v = u /\ gameF p u = p) \/
      (p = s + 2 /\ g ≠ u /\ u ≠ v /\ g ≠ v /\ gameF p v = p))

/-- General actual-game three-prefix host classification. -/
theorem gameF_three_prefix_host_freeze_regime
    {s g p : Nat}
    (hg : g < s)
    (hOld : gameF s g = p)
    (hNext : C gameF (s + 1) (s + 1) p)
    (hNext2 : C gameF (s + 2) (s + 2) p)
    (hpUpper : p <= s + 2) :
    ThreePrefixHostFreezeRegime s g p := by
  rcases hNext with ⟨u, hu, hHostU⟩
  rcases hNext2 with ⟨v, hv, hHostV⟩
  have hgp : g < p := by
    have hgt := encoded_gt game_encodes (Nat.le_of_lt hg)
    rw [hOld] at hgt
    exact hgt
  by_cases hpPast : p <= s
  · have hPstart : IsP (rowStartPos p g (Nat.le_of_lt hgp)) := by
      by_cases hps : p < s
      · have hPraw := encoded_isP_of_lt game_encodes
          (Nat.le_of_lt hg) (by
            rw [hOld]
            exact hps)
        simpa only [hOld] using hPraw
      · have hsp : s = p := by omega
        have hAtEq : gameF p g = p := by
          simpa only [hsp] using hOld
        have hP := encoded_isP_of_ge game_encodes
          (q := p) (r := g) (Nat.le_of_lt hgp) (by
            rw [hAtEq]
            exact Nat.le_refl p)
        simpa only [hAtEq, rowStartPos] using hP
    have hAtStart : gameF p g = p := by
      apply game_complete.2 (Nat.le_refl p) (Nat.le_of_lt hgp)
      simpa [rowStartPos] using hPstart
    have hPersist1 : gameF (s + 1) g = p := by
      exact game_complete.1 hgp (by omega) hPstart
    have hPersist2 : gameF (s + 2) g = p := by
      exact game_complete.1 hgp (by omega) hPstart
    exact ⟨g, g, by omega, by omega, hPersist1, hPersist2,
      Or.inl ⟨hpPast, rfl, rfl, hAtStart⟩⟩
  · have hsp : s < p := by omega
    have hpCases : p = s + 1 \/ p = s + 2 := by omega
    rcases hpCases with hp1 | hp2
    · have hStartU : gameF p u = p := by
        simpa [hp1] using hHostU
      have hgu : g ≠ u := by
        intro hEq
        subst u
        exact (encoding_rowstart_no_middle game_encodes
          hStartU hg (by omega)) hOld
      have hup : u < p := by omega
      have hPstart : IsP (rowStartPos p u (Nat.le_of_lt hup)) := by
        have hP := encoded_isP_of_ge game_encodes
          (q := p) (r := u) (Nat.le_of_lt hup) (by
            rw [hStartU]
            exact Nat.le_refl p)
        simpa [rowStartPos, hStartU] using hP
      have hPersist : gameF (s + 2) u = p := by
        exact game_complete.1 hup (by omega) hPstart
      exact ⟨u, u, hu, by omega, hHostU, hPersist,
        Or.inr (Or.inl ⟨hp1, hgu, rfl, hStartU⟩)⟩
    · have hStartV : gameF p v = p := by
        simpa [hp2] using hHostV
      have hgu : g ≠ u := by
        intro hEq
        subst u
        exact encoding_same_lower_no_repeat game_encodes
          hg (by omega) (by omega) hOld hHostU
      have huv : u ≠ v := by
        intro hEq
        subst v
        exact (encoding_rowstart_no_middle game_encodes
          hStartV hu (by omega)) hHostU
      have hgv : g ≠ v := by
        intro hEq
        subst v
        exact (encoding_rowstart_no_middle game_encodes
          hStartV hg (by omega)) hOld
      exact ⟨u, v, hu, hv, hHostU, hHostV,
        Or.inr (Or.inr ⟨hp2, hgu, huv, hgv, hStartV⟩)⟩

/-- A compact consequence of the host normal form: the three-prefix value
has an actual row-start witness no later than row `s+2`. -/
theorem gameF_three_prefix_value_has_completed_rowstart
    {s g p : Nat}
    (hg : g < s)
    (hOld : gameF s g = p)
    (hNext : C gameF (s + 1) (s + 1) p)
    (hNext2 : C gameF (s + 2) (s + 2) p)
    (hpUpper : p <= s + 2) :
    exists r, r < p /\ gameF p r = p /\
      ThreePrefixHostFreezeRegime s g p := by
  have hreg := gameF_three_prefix_host_freeze_regime
    hg hOld hNext hNext2 hpUpper
  rcases hreg with ⟨u, v, hu, hv, hHostU, hHostV, hcases⟩
  refine ?_
  rcases hcases with hPast | hNow | hLast
  · exact ⟨g, by
      have hgt := encoded_gt game_encodes (Nat.le_of_lt hg)
      rw [hOld] at hgt
      exact hgt,
      hPast.2.2.2,
      ⟨u, v, hu, hv, hHostU, hHostV, Or.inl hPast⟩⟩
  · exact ⟨u, by omega, hNow.2.2.2,
      ⟨u, v, hu, hv, hHostU, hHostV, Or.inr (Or.inl hNow)⟩⟩
  · exact ⟨v, by omega, hLast.2.2.2.2,
      ⟨u, v, hu, hv, hHostU, hHostV, Or.inr (Or.inr hLast)⟩⟩

/-- Maximal-defect event E forces a concrete lower row-start value, completed
by row `s+2`, together with the exact three-regime host geometry above. -/
theorem gameF_margin_eventE_maximal_defect_forces_completed_rowstart
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
        ThreePrefixHostFreezeRegime s g p := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzSucc : z + 1 = d := hInv.2.2.2.1
  have hzExact : z = s + 3 := by omega
  have htriple :=
    gameF_margin_eventE_maximal_defect_forces_triple_prefix_value
      hU hdip hmargin hnextDip
  change delta + 4 = s ->
    exists c b0 b1 g,
      c < s /\ b0 < s /\ b1 < s + 1 /\
      gameF s c = z + 1 /\ gameF s b0 = z /\
      gameF (s + 1) b1 = z /\
      g ∈ EventEDefectBandSlots s delta c b0 /\
      g < s /\ g ≠ c /\ g ≠ b0 /\
      0 < gameF s g /\ gameF s g < z /\
      C gameF (s + 1) (s + 1) (gameF s g) /\
      C gameF (s + 2) (s + 2) (gameF s g) at htriple
  rcases htriple hmax with
    ⟨c, b0, b1, g, hc, hb0, hb1, hSucc, hBase, hHost1,
      hgBand, hg, hgc, hgb0, hpPos, hpz, hC1, hC2⟩
  let p := gameF s g
  have hpUpper : p <= s + 2 := by
    dsimp [p]
    omega
  rcases gameF_three_prefix_value_has_completed_rowstart
      hg (by rfl) hC1 hC2 hpUpper with ⟨r, hrp, hstart, hregime⟩
  exact ⟨c, b0, b1, g, p, r,
    hc, hb0, hb1, hSucc, hBase, hHost1,
    hgBand, hg, hgc, hgb0, rfl, hpPos, hpz, hpUpper,
    hrp, hstart, hregime⟩

#print axioms gameF_three_prefix_host_freeze_regime
#print axioms gameF_three_prefix_value_has_completed_rowstart
#print axioms gameF_margin_eventE_maximal_defect_forces_completed_rowstart

end ChompLean
