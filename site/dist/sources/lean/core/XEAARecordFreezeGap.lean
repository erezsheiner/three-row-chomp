import XGapTwoForcing
import R203MiddleStreamAboveTarget

set_option autoImplicit false

namespace ChompLean

/-!
# A height-dependent freeze gap for positive EAA blockers

Work-ID: `X-EAA-RECORD-FREEZE-REFRACTORY-001`
Run-ID: `XERFR-20260729-151100-ROOT`

For a blocker value `q`, put

* `k = gameFBlockerCountThrough q`,
* `h = gameFBlockerCountThrough k + 2*k - q`,
* `a = q-k`.

Thus `h` is the positive EAA height and `a` is the canonical rank address
used by the record-freeze route.  The theorem below proves, without any
record or spacing hypothesis, that a freeze seat `f` of `q` lies to the
right of `a` by a distance growing linearly with `h`.

This file deliberately does not assume or prove `RecordFreezeRefractory`;
that separate cross-record spacing statement is the remaining debt.
-/

/-- Local composition of the terminal Hall endpoint and the global
blocker-count floor.  It is kept private because the same theorem is also
available in an uncompiled downstream research source. -/
private theorem xeaa_terminal_freeze_three_fifths_floor
    {v c : Nat}
    (hv : 50 <= v)
    (hcv : c < v)
    (hfreeze : gameF v c = v) :
    3 * v <= 5 * c + 4 := by
  have hHall :=
    gameF_terminal_actual_blocker_count_endpoint hcv hfreeze
  have hc25 : 25 <= c := by omega
  have hAF :=
    gameFBlockerCountThrough_AFloor
      (v := c + 1) (by omega : 26 <= c + 1)
  have hidx : c + 1 - 1 = c := by omega
  rw [hidx] at hAF
  omega

/-- Ranked form of the height-dependent freeze-gap theorem.

The sole large-value premise is `q >= 50`: the blocker-count floor at
`q+1` automatically yields `k >= 16`, which enters the sharp prefix
ceiling at `k`.
-/
theorem gameF_positiveEAA_ranked_freeze_gap
    {q k h f : Nat}
    (hq : 50 <= q)
    (hrank : gameFBlockerCountThrough q = k)
    (hhdef :
      h = gameFBlockerCountThrough k + 2 * k - q)
    (hh : 1 <= h)
    (hfq : f < q)
    (hfreeze : gameF q f = q) :
    q - k < f /\
      2 * h - 1 <= 5 * (f - (q - k)) := by
  have hqCeiling :=
    gameFBlockerCountThrough_ceiling (a := q) (by omega)
  rw [hrank] at hqCeiling
  have hkq : k <= q := by omega
  have hqFloor :=
    gameFBlockerCountThrough_AFloor
      (v := q + 1) (by omega : 26 <= q + 1)
  have hqIndex : q + 1 - 1 = q := by omega
  rw [hqIndex, hrank] at hqFloor
  have hk : 16 <= k := by omega
  have hkCeiling :=
    gameFBlockerCountThrough_ceiling (a := k) hk
  have hfreezeFloor :=
    xeaa_terminal_freeze_three_fifths_floor
      hq hfq hfreeze
  omega

/-- Direct EAA form, with the blocker rank expanded at `q`. -/
theorem gameF_positiveEAA_freeze_gap
    {q h f : Nat}
    (hq : 50 <= q)
    (hhdef :
      h =
        gameFBlockerCountThrough
            (gameFBlockerCountThrough q) +
          2 * gameFBlockerCountThrough q - q)
    (hh : 1 <= h)
    (hfq : f < q)
    (hfreeze : gameF q f = q) :
    q - gameFBlockerCountThrough q < f /\
      2 * h - 1 <=
        5 * (f - (q - gameFBlockerCountThrough q)) := by
  exact gameF_positiveEAA_ranked_freeze_gap
    hq rfl hhdef hh hfq hfreeze

/-- A freeze seat is unique within its row. -/
theorem gameF_freeze_seat_unique
    {q f g : Nat}
    (hfq : f < q)
    (hfreezeF : gameF q f = q)
    (hgq : g < q)
    (hfreezeG : gameF q g = q) :
    f = g := by
  exact gameRecurrenceModel.fixed_q_injective
    (Nat.le_of_lt hfq)
    (Nat.le_of_lt hgq)
    (hfreezeF.trans hfreezeG.symm)

/-- Every freeze witness of a blocker equals its canonical freeze seat. -/
theorem gameF_freeze_seat_eq_gapTwo
    {q f : Nat}
    (hS : S gameF q)
    (hfq : f < q)
    (hfreeze : gameF q f = q) :
    f = gameFGapTwoFreezeColumn q := by
  have hcanonical := gameFGapTwoFreezeColumn_spec hS
  exact gameF_freeze_seat_unique
    hfq hfreeze hcanonical.1 hcanonical.2

#print axioms ChompLean.gameF_positiveEAA_ranked_freeze_gap
#print axioms ChompLean.gameF_positiveEAA_freeze_gap
#print axioms ChompLean.gameF_freeze_seat_eq_gapTwo

end ChompLean
