import R181ActualTerminalBlockerOrderedHall
import R165Lag8HorizontalSeededChronologyNormalForm
import EventEPacketSourceCapacity
import R30FreezeServiceOrder

set_option autoImplicit false

namespace ChompLean

/-!
# Forward freeze collisions are forced exchanges

If a copy of a terminal target `v` uses a column `c` before a smaller
blocker `k` freezes that same column, persistence first forces the temporal
order `t < k`.  Row-start propagation then forces a simultaneous copy of
`k` strictly to the left of `c` on row `t`.  Source capacity gives the
sharp deadline `k - t - 1 <= b` for that companion column.

When `v` itself is a terminal row start at column `r`, row `k` also has a
new copy of `v` below `r`, distinct from the collision column.  Thus every
forward collision is a literal four-cell exchange, not merely an overlap
in a Hall count.

The final theorem specializes this to the fixed seven-row lag-eight tail.
The six affine rail hosts can never be future freeze columns.  Hence the
only possible tail collision is at the one dynamic host on row `q`, and
its blocker is one of the two top values `q+1,q+2`.
-/

/-- Exact same-row companion forced by a forward target/freeze collision. -/
theorem gameF_forward_freeze_collision_forces_left_companion
    {v t c k : Nat}
    (hct : c < t)
    (hhost : gameF t c = v)
    (hck : c < k)
    (hfreeze : gameF k c = k)
    (hkv : k < v) :
    t < k /\
      exists b,
        k - t - 1 <= b /\ b < c /\ gameF t b = k /\
        forall b', b' < c -> gameF t b' = k -> b' = b := by
  have htk : t < k :=
    gameF_targetHost_freezeCollision_forces_futureBlocker
      hhost hck hfreeze hkv
  rcases rowStartPropagation gameRecurrenceModel hfreeze hck hct htk with
    ⟨b, hbc, hbhost⟩
  have hbt : b <= t := by omega
  have hcapacity := high_cell_output_source_capacity
    gameRecurrenceModel hbt htk hbhost
  refine ⟨htk, b, by omega, hbc, hbhost, ?_⟩
  intro b' hb'c hb'host
  exact gameRecurrenceModel.fixed_q_injective
    (by omega) hbt (hb'host.trans hbhost.symm)

/-- A collision inside the active relay of a terminal target is a complete
four-cell exchange.  The target moves to a fresh column on row `k`, while
the future blocker moves left on row `t` before freezing at `c`. -/
theorem gameF_terminal_relay_forward_collision_exchange
    {v r t c k : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hrt : r < t)
    (htv : t < v)
    (hcr : c < r)
    (hhost : gameF t c = v)
    (hck : c < k)
    (hfreeze : gameF k c = k)
    (hkv : k < v) :
    exists b d,
      k - t - 1 <= b /\ b < c /\ gameF t b = k /\
      d < r /\ gameF k d = v /\ d ≠ c /\
      t < k /\ k < v /\
      (forall b', b' < c -> gameF t b' = k -> b' = b) /\
      (forall d', d' < r -> gameF k d' = v -> d' = d) := by
  have hct : c < t := by omega
  have hcomp' := gameF_forward_freeze_collision_forces_left_companion
    hct hhost hck hfreeze hkv
  rcases hcomp' with ⟨htk, b, hbdeadline, hbc, hbhost, hbunique⟩
  rcases rowStartPropagation gameRecurrenceModel hstart hrv
      (by omega : r < k) hkv with ⟨d, hdr, hdhost⟩
  have hdc : d ≠ c := by
    intro heq
    have hsame : gameF k d = k := by
      rw [heq]
      exact hfreeze
    have hvk : v = k := hdhost.symm.trans hsame
    omega
  refine ⟨b, d, hbdeadline, hbc, hbhost, hdr, hdhost, hdc,
    htk, hkv, hbunique, ?_⟩
  intro d' hd'r hd'host
  exact gameRecurrenceModel.fixed_q_injective
    (by omega) (by omega) (hd'host.trans hdhost.symm)

/-- In the exact lag-eight seven-host tail, every future-freeze collision
is confined to the dynamic middle host.  The six fixed rail hosts are
globally freeze-free in the relevant value window. -/
theorem gameF_lag8_tail_forward_collision_only_dynamic_topTwo
    {q g t c k : Nat}
    (hq : 26 <= q)
    (host : Nat -> Nat)
    (hschedule : Lag8TargetSevenHostSchedule q g host)
    (ht0 : q - 4 <= t)
    (ht1 : t <= q + 2)
    (hc : c = host t)
    (hck : c < k)
    (hfreeze : gameF k c = k)
    (hkv : k < q + 3) :
    t = q /\ c = host q /\ (k = q + 1 \/ k = q + 2) := by
  have htHost : gameF t c = q + 3 := by
    rw [hc]
    exact (hschedule.1 t ht0 ht1).2
  have htk : t < k :=
    gameF_targetHost_freezeCollision_forces_futureBlocker
      htHost hck hfreeze hkv
  have htcases :
      t = q - 4 \/ t = q - 3 \/ t = q - 2 \/ t = q - 1 \/
      t = q \/ t = q + 1 \/ t = q + 2 := by omega
  rcases htcases with ht | ht | ht | ht | ht | ht | ht
  . subst t
    have hc11 : c = 11 := hc.trans hschedule.2.2.1
    rw [hc11] at hfreeze
    have hrail := gameF_col11_rail (q := k) (by omega)
    omega
  . subst t
    have hc9 : c = 9 := hc.trans hschedule.2.2.2.1
    rw [hc9] at hfreeze
    have hrail := gameF_col9_rail (q := k) (by omega)
    omega
  . subst t
    have hc7 : c = 7 := hc.trans hschedule.2.2.2.2.1
    rw [hc7] at hfreeze
    have hrail := gameF_col7_rail (q := k) (by omega)
    omega
  . subst t
    have hc5 : c = 5 := hc.trans hschedule.2.2.2.2.2.1
    rw [hc5] at hfreeze
    have hrail := gameF_col5_rail (q := k) (by omega)
    omega
  . subst t
    exact ⟨rfl, hc, by omega⟩
  . subst t
    have hc2 : c = 2 := hc.trans hschedule.2.2.2.2.2.2.1
    rw [hc2] at hfreeze
    have hrail := gameF_col2_rail (q := k) (by omega)
    omega
  . omega

/-!
## The exact W4 seat-order bridge

The empirical W4 observation compares two values on the same row:
`u` at its lag-eight host and `u-5` at its lag-three host.  The only
obstruction to putting the lower host strictly to the left is the `R`
(old-history) arm of the MEX source at the lag-eight cell.

For a row-start blocker this obstruction disappears at every column at or
to the right of its freeze.  Indeed, an `R` witness is either a forbidden
diagonal owner of the blocker, or a genuine pre-freeze host in that column;
the latter must lie strictly left of the freeze.
-/

/-- A row-start blocker has no `R`-history at a column at or to the right
of its freeze, on any row strictly before the blocker row. -/
theorem gameF_rowStart_R_clean_at_or_right_of_freeze
    {k s t c : Nat}
    (hsk : s < k)
    (hfreeze : gameF k s = k)
    (htk : t < k)
    (hsc : s <= c) :
    Not (R gameF t c k) := by
  rintro ⟨a, hat, hvalue⟩
  by_cases hac : a <= c
  . have hdiag : gameF a a = k := by
      simpa [Nat.min_eq_left hac] using hvalue
    exact disjoint_D_S gameRecurrenceModel
      ⟨a, hdiag⟩ ⟨s, hsk, hfreeze⟩
  . have hca : c < a := by omega
    have hhost : gameF a c = k := by
      simpa [Nat.min_eq_right (Nat.le_of_lt hca)] using hvalue
    rcases rowstart_host_order_exact gameRecurrenceModel
        hsk hfreeze hca (by omega : a <= k) hhost with
      hbefore | hboundary
    . omega
    . omega

/-- At a genuine high MEX cell, an `R`-clean lower value already hosted
elsewhere on the row must occur strictly to the left of that cell. -/
theorem gameF_sameRow_lower_host_left_of_R_clean_high_mex
    {t c d k u : Nat}
    (hc : c <= t)
    (hd : d <= t)
    (htu : t < u)
    (hkpos : 0 < k)
    (hku : k < u)
    (hhigh : gameF t c = u)
    (hlow : gameF t d = k)
    (hclean : Not (R gameF t c k)) :
    d < c := by
  have hsource : B gameF t c k := by
    apply gameRecurrenceModel.mex_no_skip hc
    . change t < gameF t c
      rw [hhigh]
      exact htu
    . exact hkpos
    . change k < gameF t c
      rw [hhigh]
      exact hku
  rcases hsource with hR | hC
  . exact False.elim (hclean hR)
  . rcases hC with ⟨b, hbc, hbvalue⟩
    have hbd : b = d :=
      gameRecurrenceModel.fixed_q_injective
        (q := t) (b₁ := b) (b₂ := d)
        (by omega) hd (hbvalue.trans hlow.symm)
    omega

/-- W4 specialization.  If `u-5` is a blocker whose freeze is no later
than the lag-eight host column, its lag-three host on the common row
`u-8` is strictly to the left of the lag-eight host. -/
theorem gameF_lag8_host_after_lag3_blocker_host
    {u c d s : Nat}
    (hu : 8 <= u)
    (hc : c <= u - 8)
    (hd : d <= u - 8)
    (h8 : gameF (u - 8) c = u)
    (h3 : gameF (u - 8) d = u - 5)
    (hsk : s < u - 5)
    (hfreeze : gameF (u - 5) s = u - 5)
    (hsc : s <= c) :
    d < c := by
  have hclean : Not (R gameF (u - 8) c (u - 5)) :=
    gameF_rowStart_R_clean_at_or_right_of_freeze
      hsk hfreeze (by omega) hsc
  exact gameF_sameRow_lower_host_left_of_R_clean_high_mex
    hc hd (by omega) (by omega) (by omega) h8 h3 hclean

/-!
## Why descent alone is not a density gain

The next construction is deliberately only an interface counterframe, not
a fake recurrence table.  It shows that the exact scalar output of the
collision theorem (forward time, strict left movement, and its deadline)
admits chains of arbitrary length in which every companion is already the
next relay seat.  Consequently acyclicity/column descent alone cannot be
charged as a fresh Hall seat; some genuine candidate-cleanliness or
non-reuse theorem is indispensable.
-/

private def r182ChainSeat (n : Nat) (i : Fin (n + 1)) : Nat :=
  n - i.val

private def r182ChainCompanion (n : Nat) (i : Fin n) : Nat :=
  n - (i.val + 1)

private def r182ChainRow (n : Nat) (i : Fin n) : Nat :=
  2 * n + i.val + 1

private def r182ChainBlocker (n : Nat) (i : Fin n) : Nat :=
  r182ChainRow n i + 1

/-- Arbitrarily long strictly descending companion chains satisfy every
scalar inequality exported by the forward-collision lemma while adding no
new seat outside the relay-seat range. -/
theorem r182_descending_companion_interface_has_arbitrary_noFresh_chains
    (n : Nat) :
    Function.Injective (r182ChainSeat n) /\
      (forall i : Fin n,
        r182ChainCompanion n i <
          r182ChainSeat n ⟨i.val, by omega⟩ /\
        r182ChainSeat n ⟨i.val, by omega⟩ < r182ChainRow n i /\
        r182ChainRow n i < r182ChainBlocker n i /\
        r182ChainBlocker n i < 4 * n + 4 /\
        r182ChainBlocker n i - r182ChainRow n i - 1 <=
          r182ChainCompanion n i /\
        exists j : Fin (n + 1),
          r182ChainCompanion n i = r182ChainSeat n j) := by
  constructor
  . intro i j hij
    apply Fin.ext
    simp only [r182ChainSeat] at hij
    have hi : i.val <= n := by omega
    have hj : j.val <= n := by omega
    omega
  . intro i
    have hi : i.val < n := i.isLt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    . simp only [r182ChainCompanion, r182ChainSeat]
      omega
    . simp only [r182ChainSeat, r182ChainRow]
      omega
    . simp only [r182ChainRow, r182ChainBlocker]
      omega
    . simp only [r182ChainBlocker, r182ChainRow]
      omega
    . simp only [r182ChainBlocker]
      omega
    . let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      refine ⟨j, ?_⟩
      simp [j, r182ChainCompanion, r182ChainSeat]

#print axioms gameF_forward_freeze_collision_forces_left_companion
#print axioms gameF_terminal_relay_forward_collision_exchange
#print axioms gameF_lag8_tail_forward_collision_only_dynamic_topTwo
#print axioms gameF_rowStart_R_clean_at_or_right_of_freeze
#print axioms gameF_sameRow_lower_host_left_of_R_clean_high_mex
#print axioms gameF_lag8_host_after_lag3_blocker_host
#print axioms r182_descending_companion_interface_has_arbitrary_noFresh_chains

end ChompLean
