import R177Lag8DiagonalOwnerEarlyDescent
import R14FrontierLaw

set_option autoImplicit false

namespace ChompLean

/-!
# Exact greedy target-seat ledger

The row scanner does not merely behave greedily in finite tables.  At a
high host `gameF t c = u`, the recurrence puts the cell on its positive-MEX
branch.  Consequently the target is absent, every smaller positive value is
present, and every earlier column which failed to host `u` has one of three
literal defects:

* it is a carry cell;
* it contains an old same-column occurrence of `u`; or
* its source has a concrete positive hole below `u`.

For a row-start target the fixed-history alternative is exactly `ColTail`.
This is the all-index theorem behind the empirical greedy-seat scan.  The
final lemmas isolate the lag-eight relay `u-5` on the same row `u-8`.
-/

/-- A row-start value can enter a fixed source channel only through an old
same-column host; a diagonal owner is excluded by D/S disjointness. -/
theorem gameF_rowstart_R_iff_colTail
    {u r t e : Nat}
    (hru : r < u) (hstart : gameF u r = u) :
    R gameF t e u <-> ColTail gameF t e u := by
  constructor
  · intro hR
    rcases R_iff_diagPrefix_or_colTail.mp hR with hD | hTail
    · rcases hD with ⟨a, _hat, _hae, hdiag⟩
      exact False.elim
        (disjoint_D_S gameRecurrenceModel
          ⟨a, hdiag⟩ ⟨r, hru, hstart⟩)
    · exact hTail
  · intro hTail
    exact R_iff_diagPrefix_or_colTail.mpr (Or.inr hTail)

/-- A high target host is an exact greedy seat: its source omits the target
and contains every smaller positive value. -/
theorem gameF_high_target_exact_greedy_seat
    {t c u : Nat}
    (hct : c <= t) (htu : t < u) (hhost : gameF t c = u) :
    IsMex (B gameF t c) u /\
      Not (R gameF t c u) /\
      Not (C gameF t c u) /\
      LowerSaturated gameF t c u := by
  have hmex := gameF_high_host_isMex hct htu hhost
  refine ⟨hmex, ?_, ?_, ?_⟩
  · intro hR
    exact hmex.2.1 (Or.inl hR)
  · intro hC
    exact hmex.2.1 (Or.inr hC)
  · intro z hz0 hzu
    exact hmex.2.2 z hz0 hzu

/-- Exact defect ledger before a high target seat.  Every skipped column is
a carry, has old target history, or exposes a concrete lower hole. -/
theorem gameF_before_high_target_carry_or_R_or_lowerHole
    {t c e u : Nat}
    (hct : c <= t) (htu : t < u) (hhost : gameF t c = u)
    (hec : e < c) :
    (e < t /\ gameF (t - 1) e < t) \/
      R gameF t e u \/ HasLowerHole gameF t e u := by
  classical
  by_cases hcarry : e < t /\ gameF (t - 1) e < t
  · exact Or.inl hcarry
  · right
    by_cases hR : R gameF t e u
    · exact Or.inl hR
    · right
      by_cases hhole : HasLowerHole gameF t e u
      · exact hhole
      · have hsat : LowerSaturated gameF t e u := by
          by_cases hsat : LowerSaturated gameF t e u
          · exact hsat
          · exact False.elim
              (hhole (hasLowerHole_iff_not_lowerSaturated.mpr hsat))
        have hC : Not (C gameF t e u) := by
          rintro ⟨b, hbe, hbhost⟩
          have hbc : b = c :=
            gameRecurrenceModel.fixed_q_injective
              (by omega) hct (hbhost.trans hhost.symm)
          omega
        have hB : Not (B gameF t e u) := by
          rintro (hBR | hBC)
          · exact hR hBR
          · exact hC hBC
        have hmexE : IsMex (B gameF t e) (gameF t e) :=
          gameF_brouwerRecurrence.2 (by omega) hcarry
        have heq : gameF t e = u :=
          isMex_eq_of_lowerSaturated_and_clean
            hmexE (by omega) hsat hB
        have hecEq : e = c :=
          gameRecurrenceModel.fixed_q_injective
            (by omega) hct (heq.trans hhost.symm)
        omega

/-- Terminal specialization: the history defect in the greedy ledger is a
literal old same-column target host. -/
theorem gameF_before_high_rowstart_carry_or_colTail_or_lowerHole
    {u r t c e : Nat}
    (hru : r < u) (hstart : gameF u r = u)
    (hct : c <= t) (htu : t < u) (hhost : gameF t c = u)
    (hec : e < c) :
    (e < t /\ gameF (t - 1) e < t) \/
      ColTail gameF t e u \/ HasLowerHole gameF t e u := by
  rcases gameF_before_high_target_carry_or_R_or_lowerHole
      hct htu hhost hec with hcarry | hR | hhole
  · exact Or.inl hcarry
  · exact Or.inr (Or.inl
      ((gameF_rowstart_R_iff_colTail hru hstart).mp hR))
  · exact Or.inr (Or.inr hhole)

/-- If a smaller value has a host on the same row and is clean in the fixed
channel of the higher target seat, its host must occur first.  This is the
two-value greedy precedence law. -/
theorem gameF_lower_sameRow_host_precedes_high_target_of_R_clean
    {t c d p u : Nat}
    (hct : c <= t) (hdt : d <= t)
    (htu : t < u) (hp0 : 0 < p) (hpu : p < u)
    (hu : gameF t c = u) (hp : gameF t d = p)
    (hRclean : Not (R gameF t c p)) :
    d < c := by
  have hmex := gameF_high_host_isMex hct htu hu
  have hB : B gameF t c p := hmex.2.2 p hp0 hpu
  rcases hB with hR | hC
  · exact False.elim (hRclean hR)
  · rcases hC with ⟨b, hbc, hb⟩
    have hbd : b = d :=
      gameRecurrenceModel.fixed_q_injective
        (by omega) hdt (hb.trans hp.symm)
    omega

/-- Before a blocker's row start, no fixed-history host can occur at or to
the right of its freeze column. -/
theorem gameF_rowstart_R_clean_at_or_right_of_freeze_before_start
    {p s t c : Nat}
    (hsp : s < p) (hstart : gameF p s = p)
    (htp : t < p) (hsc : s <= c) :
    Not (R gameF t c p) := by
  intro hR
  have hTail : ColTail gameF t c p :=
    (gameF_rowstart_R_iff_colTail hsp hstart).mp hR
  rcases hTail with ⟨a, hat, hca, hhost⟩
  have horder := rowstart_host_order_exact
    gameRecurrenceModel hsp hstart hca (by omega) hhost
  rcases horder with ⟨_hap, hcs⟩ | ⟨hap, _hcs⟩
  · omega
  · omega

/-- The exact W4 two-blocker relay.  On row `u-8`, if `u-5` is a blocker
whose freeze is no later than the lag-eight target seat, then its lag-three
host lies strictly before the target host.  No empirical "next seat" or
freeze-order axiom is assumed. -/
theorem gameF_lag8_lowerBlocker_host_precedes_target
    {u c d s : Nat}
    (hu : 8 <= u)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hsp : s < u - 5) (hfreeze : gameF (u - 5) s = u - 5)
    (hsc : s <= c)
    (hlowerHost : gameF (u - 8) d = u - 5) :
    d < c := by
  have hRclean : Not (R gameF (u - 8) c (u - 5)) :=
    gameF_rowstart_R_clean_at_or_right_of_freeze_before_start
      hsp hfreeze (by omega) hsc
  exact gameF_lower_sameRow_host_precedes_high_target_of_R_clean
    hct hdt (by omega) (by omega) (by omega)
      htarget hlowerHost hRclean

/-- Owner coverage turns the W4 order into a four-point staircase.  In a
failed-band packet the lower blocker's lag-three host `d`, its freeze `s`,
the owner cutoff `g`, and the target's lag-eight host `c` satisfy
`d < s <= g < c`. -/
theorem gameF_ownerCovered_lag8_lowerBlocker_staircase
    {u g c d s : Nat}
    (hu : 8 <= u)
    (howners : LowerOwnerCoveredBy u g)
    (hgc : g < c)
    (hct : c <= u - 8) (hdt : d <= u - 8)
    (htarget : gameF (u - 8) c = u)
    (hsp : s < u - 5) (hfreeze : gameF (u - 5) s = u - 5)
    (hlowerHost : gameF (u - 8) d = u - 5) :
    d < s /\ s <= g /\ g < c := by
  have hp0 : 0 < u - 5 := by omega
  have hpu : u - 5 < u := by omega
  have hsg : s <= g := by
    rcases howners (u - 5) hp0 hpu with
        ⟨a, _hag, hdiag⟩ | ⟨s', hs'g, hs'p, hfreeze'⟩
    · exact False.elim
        (disjoint_D_S gameRecurrenceModel
          ⟨a, hdiag⟩ ⟨s, hsp, hfreeze⟩)
    · have hss' : s = s' :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hsp) (Nat.le_of_lt hs'p)
          (hfreeze.trans hfreeze'.symm)
      omega
  have hds : d < s := by
    have hdtStrict : d < u - 8 := by
      by_cases hd : d < u - 8
      · exact hd
      · have hdEq : d = u - 8 := by omega
        subst d
        exact False.elim
          (disjoint_D_S gameRecurrenceModel
            ⟨u - 8, hlowerHost⟩ ⟨s, hsp, hfreeze⟩)
    have horder := rowstart_host_order_exact
      gameRecurrenceModel hsp hfreeze
        hdtStrict (by omega) hlowerHost
    rcases horder with ⟨_htp, hds⟩ | ⟨htp, _⟩
    · exact hds
    · omega
  have hdc : d < c :=
    gameF_lag8_lowerBlocker_host_precedes_target
      hu hct hdt htarget hsp hfreeze (by omega) hlowerHost
  exact ⟨hds, hsg, hgc⟩

/-!
## Localizing a greedy lower hole to the owner window

Below an owner cutoff `g`, a missing lower value is not diffuse.  Its named
owner must lie strictly to the right of the inspected column and at most
`g`, except for the single boundary event in which the inspected cell is
the value's row-start freeze on the current row.
-/

theorem gameF_ownerCovered_lowerHole_localizes_rightOwner_or_currentFreeze
    {v g t e z : Nat}
    (howners : LowerOwnerCoveredBy v g)
    (hgt : g < t)
    (hz0 : 0 < z) (hzv : z < v)
    (hhole : Not (B gameF t e z)) :
    (exists a,
      e < a /\ a <= g /\ gameF a a = z) \/
    (exists s,
      e < s /\ s <= g /\ s < z /\ gameF z s = z) \/
    (z = t /\ gameF t e = t) := by
  rcases howners z hz0 hzv with
      ⟨a, hag, hdiag⟩ | ⟨s, hsg, hsz, hstart⟩
  · by_cases hea : e < a
    · exact Or.inl ⟨a, hea, hag, hdiag⟩
    · have hae : a <= e := Nat.le_of_not_gt hea
      exact False.elim (hhole (Or.inl ⟨a, by omega, by
        have hmin : min a e = a := Nat.min_eq_left hae
        simpa [hmin] using hdiag⟩))
  · by_cases hes : e < s
    · exact Or.inr (Or.inl ⟨s, hes, hsg, hsz, hstart⟩)
    · have hse : s <= e := Nat.le_of_not_gt hes
      by_cases htz : t < z
      · rcases rowStartPropagation gameRecurrenceModel
          hstart hsz (by omega : s < t) htz with
          ⟨b, hbs, hbhost⟩
        exact False.elim (hhole (Or.inr
          ⟨b, by omega, hbhost⟩))
      · have hzt : z <= t := Nat.le_of_not_gt htz
        by_cases hztStrict : z < t
        · by_cases hseStrict : s < e
          · have hpersist := constant_from gameRecurrenceModel hsz
              (show gameF z s < z + 1 by rw [hstart]; omega)
              (t - z)
            have hsum : z + (t - z) = t := by omega
            change gameF (z + (t - z)) s = gameF z s at hpersist
            rw [hsum, hstart] at hpersist
            exact False.elim (hhole (Or.inr
              ⟨s, hseStrict, hpersist⟩))
          · have hseEq : s = e := by omega
            subst s
            exact False.elim (hhole (Or.inl ⟨z, hztStrict, by
              have hez : e <= z := by omega
              have hmin : min z e = e := Nat.min_eq_right hez
              simpa [hmin] using hstart⟩))
        · have hztEq : z = t := by omega
          subst z
          by_cases hseStrict : s < e
          · exact False.elim (hhole (Or.inr
              ⟨s, hseStrict, hstart⟩))
          · have hseEq : s = e := by omega
            subst s
            exact Or.inr (Or.inr ⟨rfl, hstart⟩)

/-- Complete sub-cutoff normal form for every skipped greedy seat.  A
skipped column is a carry, an old target column, or owns a concrete lower
hole in the finite window `(e,g]`; the only exception is a freeze-now cell.
-/
theorem gameF_before_high_rowstart_ownerWindow_ledger
    {u r g t c e : Nat}
    (hru : r < u) (hstart : gameF u r = u)
    (howners : LowerOwnerCoveredBy u g)
    (hgt : g < t) (hct : c <= t) (htu : t < u)
    (hhost : gameF t c = u)
    (hec : e < c) :
    (e < t /\ gameF (t - 1) e < t) \/
    ColTail gameF t e u \/
    exists z,
      0 < z /\ z < u /\
      ((exists a,
          e < a /\ a <= g /\ gameF a a = z) \/
       (exists s,
          e < s /\ s <= g /\ s < z /\ gameF z s = z) \/
       (z = t /\ gameF t e = t)) := by
  rcases gameF_before_high_rowstart_carry_or_colTail_or_lowerHole
      hru hstart hct htu hhost hec with hcarry | hTail | hhole
  · exact Or.inl hcarry
  · exact Or.inr (Or.inl hTail)
  · right
    right
    rcases hhole with ⟨z, hz0, hzu, hzHole⟩
    exact ⟨z, hz0, hzu,
      gameF_ownerCovered_lowerHole_localizes_rightOwner_or_currentFreeze
        howners hgt hz0 hzu hzHole⟩

/-- A skipped column which is neither a carry nor dirty with old target
history emits a distinct value in the short vertical band `[t,u)`.  Its
actual MEX value, not an arbitrary hole witness, owns a seat in `(e,g]`, or
is the unique freeze-now boundary value `t`. -/
theorem gameF_clean_noncarry_before_target_outputBand_and_ownerWindow
    {u g t c e : Nat}
    (howners : LowerOwnerCoveredBy u g)
    (hgt : g < t) (hct : c <= t) (htu : t < u)
    (hhost : gameF t c = u)
    (hec : e < c)
    (hnotCarry : Not (e < t /\ gameF (t - 1) e < t))
    (hRclean : Not (R gameF t e u)) :
    t <= gameF t e /\ gameF t e < u /\
      ((exists a,
          e < a /\ a <= g /\ gameF a a = gameF t e) \/
       (exists s,
          e < s /\ s <= g /\ s < gameF t e /\
            gameF (gameF t e) s = gameF t e) \/
       (gameF t e = t /\ gameF t e = t)) := by
  have hCclean : Not (C gameF t e u) := by
    rintro ⟨b, hbe, hbhost⟩
    have hbc : b = c :=
      gameRecurrenceModel.fixed_q_injective
        (by omega) hct (hbhost.trans hhost.symm)
    omega
  have hBclean : Not (B gameF t e u) := by
    rintro (hR | hC)
    · exact hRclean hR
    · exact hCclean hC
  have hmex : IsMex (B gameF t e) (gameF t e) :=
    gameF_brouwerRecurrence.2 (by omega) hnotCarry
  have houtLt : gameF t e < u := by
    apply Nat.lt_of_le_of_ne
    · apply Nat.le_of_not_gt
      intro huout
      exact hBclean (hmex.2.2 u (by omega) huout)
    · intro houtEq
      have heq : e = c :=
        gameRecurrenceModel.fixed_q_injective
          (by omega) hct (houtEq.trans hhost.symm)
      omega
  have htout : t <= gameF t e := by
    apply Nat.le_of_not_gt
    intro houtLow
    have hlowStart := gameF_low_cell_has_rowstart
      (q := t) (c := e) (by omega) (by omega)
    have hpersist := constant_from gameRecurrenceModel hlowStart.1
      (show gameF (gameF t e) e < gameF t e + 1 by
        rw [hlowStart.2]
        omega)
      ((t - 1) - gameF t e)
    have hsum : gameF t e + ((t - 1) - gameF t e) = t - 1 := by
      omega
    change gameF (gameF t e + ((t - 1) - gameF t e)) e =
      gameF (gameF t e) e at hpersist
    rw [hsum, hlowStart.2] at hpersist
    exact hnotCarry ⟨by omega, by omega⟩
  have howner :=
    gameF_ownerCovered_lowerHole_localizes_rightOwner_or_currentFreeze
      howners hgt hmex.1 houtLt hmex.2.1
  exact ⟨htout, houtLt, howner⟩

/-- Lag-eight terminal ledger in the coordinates used by the failed-band
packet. -/
theorem gameF_lag8_target_host_greedy_ledger
    {u r c : Nat}
    (hu : 8 <= u) (hru : r < u) (hstart : gameF u r = u)
    (hct : c <= u - 8) (hhost : gameF (u - 8) c = u) :
    IsMex (B gameF (u - 8) c) u /\
      LowerSaturated gameF (u - 8) c u /\
      (forall e, e < c ->
        (e < u - 8 /\ gameF ((u - 8) - 1) e < u - 8) \/
          ColTail gameF (u - 8) e u \/
          HasLowerHole gameF (u - 8) e u) := by
  have hseat := gameF_high_target_exact_greedy_seat
    hct (by omega) hhost
  refine ⟨hseat.1, hseat.2.2.2, ?_⟩
  intro e hec
  exact gameF_before_high_rowstart_carry_or_colTail_or_lowerHole
    hru hstart hct (by omega) hhost hec

#print axioms gameF_rowstart_R_iff_colTail
#print axioms gameF_high_target_exact_greedy_seat
#print axioms gameF_before_high_target_carry_or_R_or_lowerHole
#print axioms gameF_before_high_rowstart_carry_or_colTail_or_lowerHole
#print axioms gameF_lower_sameRow_host_precedes_high_target_of_R_clean
#print axioms gameF_rowstart_R_clean_at_or_right_of_freeze_before_start
#print axioms gameF_lag8_lowerBlocker_host_precedes_target
#print axioms gameF_ownerCovered_lag8_lowerBlocker_staircase
#print axioms gameF_ownerCovered_lowerHole_localizes_rightOwner_or_currentFreeze
#print axioms gameF_before_high_rowstart_ownerWindow_ledger
#print axioms gameF_clean_noncarry_before_target_outputBand_and_ownerWindow
#print axioms gameF_lag8_target_host_greedy_ledger

end ChompLean
