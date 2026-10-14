import R174TerminalRelayHallSaturation
import R175TerminalRelayForbiddenRailHall
import R148bPersistentHostOrderedHall

set_option autoImplicit false

namespace ChompLean

/-!
# Actual blocker / terminal-relay ordered Hall

The row-start blockers born by row `r` occupy distinct permanent columns.
A terminal row start `gameF v r = v` has one distinct relay column on every
row in `(r,v)`.  These two packets are cross-disjoint: every old blocker has
already frozen before every active relay row.  Hence

`v - r - 1 + A_actual(r) <= r`.

The final section records the sharp limitation.  A blocker born after `r`
may reuse a relay column, but only after that column has hosted `v`.  This is
the exact forward temporal collision which prevents replacing `A_actual(r)`
by `A_actual(v-1)`.  A scalar family shows that the resulting early-blocker
Hall slack can remain linear even at the assignment midpoint.
-/

private theorem r181_nodup_get_injective
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {xs : List alpha} (hxs : xs.Nodup) :
    Function.Injective xs.get := by
  induction xs with
  | nil => intro i; exact Fin.elim0 i
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro _; rfl
        · intro hij
          exfalso
          have haj : a = as.get j' := by simpa using hij
          exact hxs.1 (by rw [haj]; exact List.get_mem as j')
      · intro j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij
          exfalso
          have hia : as.get i' = a := by simpa using hij
          exact hxs.1 (by rw [← hia]; exact List.get_mem as i')
        · intro hij
          have htail : i' = j' := ih hxs.2 (by simpa using hij)
          exact Fin.ext (by simpa using congrArg Fin.val htail)

/-- The canonical finite list of actual row-start values in `[1,r]`. -/
noncomputable def gameFBlockersThroughList (r : Nat) : List Nat := by
  classical
  exact (List.range' 1 r).filter (fun k => decide (S gameF k))

/-- The actual blocker count through row `r`, defined directly from the
proved row-start predicate `S gameF`. -/
noncomputable def gameFBlockerCountThrough (r : Nat) : Nat :=
  (gameFBlockersThroughList r).length

theorem gameF_mem_blockersThroughList {r k : Nat} :
    k ∈ gameFBlockersThroughList r ↔
      0 < k ∧ k <= r ∧ S gameF k := by
  classical
  simp only [gameFBlockersThroughList, List.mem_filter, decide_eq_true_eq,
    List.mem_range'_1]
  constructor
  · rintro ⟨⟨hk1, hkr⟩, hS⟩
    exact ⟨by omega, by omega, hS⟩
  · rintro ⟨hk, hkr, hS⟩
    exact ⟨⟨by omega, by omega⟩, hS⟩

theorem gameF_blockersThroughList_nodup (r : Nat) :
    (gameFBlockersThroughList r).Nodup := by
  classical
  exact List.filter_sublist.nodup (List.nodup_range' 1)

/-- A target host and a later freeze may share a column only in the forward
temporal order: the host row is strictly before the blocker is born.  This
is the exact dynamic escape from the full-blocker Hall packet. -/
theorem gameF_targetHost_freezeCollision_forces_futureBlocker
    {v t c k : Nat}
    (hhost : gameF t c = v)
    (hck : c < k)
    (hfreeze : gameF k c = k)
    (hkv : k < v) :
    t < k := by
  apply Nat.lt_of_not_ge
  intro hkt
  have hpersist : gameF t c = k :=
    gameF_freeze_persists hck hfreeze hkt
  omega

/-- Generic actual-game ordered Hall theorem.  `blocker` enumerates any
injective packet of row-start blockers already born by the terminal freeze
row. -/
theorem gameF_terminal_relay_blocker_ordered_hall
    {v r n : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v)
    (blocker : Fin n -> Nat)
    (hblockerInj : Function.Injective blocker)
    (hblocker : forall i,
      0 < blocker i ∧ blocker i <= r ∧ S gameF (blocker i)) :
    v - r - 1 + n <= r := by
  classical
  rcases gameF_terminal_freeze_relay_hall_certificate hrv hstart with
    ⟨host, hcert⟩
  let row : Fin (v - r - 1) -> Nat := fun i => r + 1 + i.val
  have hrow : forall i : Fin (v - r - 1),
      r < row i ∧ row i < v := by
    intro i
    have hi := i.isLt
    dsimp [row]
    omega
  let relay : Fin (v - r - 1) -> Fin r := fun i =>
    ⟨host (row i), (hcert.hosted (row i) (hrow i).1 (hrow i).2).1⟩
  have hRelayInj : Function.Injective relay := by
    intro i j hij
    have hhosteq : host (row i) = host (row j) := congrArg Fin.val hij
    by_cases hijArg : i = j
    · exact hijArg
    · by_cases hijVal : i.val < j.val
      · exact False.elim (hcert.noReuse (row i) (row j)
          (hrow i).1 (by dsimp [row]; omega) (hrow j).2 hhosteq)
      · have hjiVal : j.val < i.val := by
          have hiv := i.isLt
          have hjv := j.isLt
          omega
        exact False.elim (hcert.noReuse (row j) (row i)
          (hrow j).1 (by dsimp [row]; omega) (hrow i).2 hhosteq.symm)
  have hfreezeExists : forall i : Fin n,
      exists c, c < blocker i ∧ gameF (blocker i) c = blocker i := by
    intro i
    exact (hblocker i).2.2
  let freezeNat : Fin n -> Nat := fun i =>
    Classical.choose (hfreezeExists i)
  have hfreezeSpec : forall i : Fin n,
      freezeNat i < blocker i ∧
        gameF (blocker i) (freezeNat i) = blocker i := by
    intro i
    exact Classical.choose_spec (hfreezeExists i)
  let frozen : Fin n -> Fin r := fun i =>
    ⟨freezeNat i, by
      have hi := hblocker i
      have hf := hfreezeSpec i
      omega⟩
  have hFrozenInj : Function.Injective frozen := by
    intro i j hij
    have hcol : freezeNat i = freezeNat j := congrArg Fin.val hij
    by_cases hvalue : blocker i = blocker j
    · exact hblockerInj hvalue
    · by_cases hijValue : blocker i < blocker j
      · exfalso
        exact gameF_freeze_column_unique
          (hfreezeSpec i).1 (hfreezeSpec i).2 hijValue
          (by simpa [hcol] using (hfreezeSpec j).2)
      · have hjiValue : blocker j < blocker i := by omega
        exfalso
        exact gameF_freeze_column_unique
          (hfreezeSpec j).1 (hfreezeSpec j).2 hjiValue
          (by simpa [hcol] using (hfreezeSpec i).2)
  have hCross : forall i j, relay i ≠ frozen j := by
    intro i j heq
    have hcol : host (row i) = freezeNat j := congrArg Fin.val heq
    have htarget :=
      (hcert.hosted (row i) (hrow i).1 (hrow i).2).2
    have hpersist : gameF (row i) (freezeNat j) = blocker j :=
      gameF_freeze_persists (hfreezeSpec j).1 (hfreezeSpec j).2
        (by
          have hj := hblocker j
          have hir := (hrow i).1
          omega)
    rw [← hcol] at hpersist
    have hj := hblocker j
    omega
  exact r148b_two_packet_ordered_hall relay frozen
    hRelayInj hFrozenInj hCross

/-- Canonical count form: every actual terminal freeze satisfies the
cumulative early-blocker Hall inequality. -/
theorem gameF_terminal_relay_actual_blockersThrough_hall
    {v r : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v) :
    v - r - 1 + gameFBlockerCountThrough r <= r := by
  classical
  let xs := gameFBlockersThroughList r
  let blocker : Fin xs.length -> Nat := fun i => xs.get i
  have hblockerInj : Function.Injective blocker := by
    exact r181_nodup_get_injective (gameF_blockersThroughList_nodup r)
  have hblocker : forall i,
      0 < blocker i ∧ blocker i <= r ∧ S gameF (blocker i) := by
    intro i
    apply gameF_mem_blockersThroughList.mp
    exact List.get_mem xs i
  have hhall := gameF_terminal_relay_blocker_ordered_hall
    hrv hstart blocker hblockerInj hblocker
  simpa [xs, gameFBlockerCountThrough] using hhall

theorem gameF_terminal_actual_blocker_count_endpoint
    {v r : Nat}
    (hrv : r < v)
    (hstart : gameF v r = v) :
    v + gameFBlockerCountThrough r <= 2 * r + 1 := by
  have h := gameF_terminal_relay_actual_blockersThrough_hall hrv hstart
  omega

/-! ## Sharp obstruction audit -/

/-- The seven early fixed rails used by the terminal Hall theorem are not
new seats relative to the full blocker packet: each is already the freeze
column of the displayed actual lower blocker. -/
theorem gameF_seven_terminal_rails_are_blocker_freezes :
    gameF 2 1 = 2 ∧
    gameF 5 3 = 5 ∧
    gameF 7 4 = 7 ∧
    gameF 9 6 = 9 ∧
    gameF 12 8 = 12 ∧
    gameF 14 10 = 14 ∧
    gameF 17 12 = 17 := by
  exact ⟨
    gameF_col1_rail (q := 2) (by omega),
    gameF_col3_rail (q := 5) (by omega),
    gameF_col4_rail (q := 7) (by omega),
    gameF_col6_rail (q := 9) (by omega),
    gameF_col8_rail (q := 12) (by omega),
    gameF_col10_rail (q := 14) (by omega),
    gameF_col12_rail (q := 17) (by omega)⟩

private def r181CounterV (k : Nat) : Nat := 10 * k
private def r181CounterATotal (k : Nat) : Nat := 4 * k
private def r181CounterG (k : Nat) : Nat := 7 * k
private def r181CounterR (k : Nat) : Nat := 7 * k + 2
private def r181CounterAEarly (k : Nat) : Nat := 3 * k

/-- Scalar counterframe for the logical strength of the unconditional
early-blocker theorem.  It has the exact midpoint and atomic failed-rail
offset, satisfies count monotonicity and the cumulative Hall inequality,
but its unused capacity is `k+5`, hence unbounded. -/
theorem r181_earlyBlockerHall_linearSlack_counterframe
    (k : Nat) (hk : 1 <= k) :
    r181CounterG k =
        (r181CounterV k + r181CounterATotal k) / 2 ∧
    r181CounterR k = r181CounterG k + 2 ∧
    r181CounterAEarly k <= r181CounterATotal k ∧
    r181CounterV k - r181CounterR k - 1 +
        r181CounterAEarly k <= r181CounterR k ∧
    r181CounterR k -
        (r181CounterV k - r181CounterR k - 1 +
          r181CounterAEarly k) = k + 5 := by
  simp [r181CounterG, r181CounterV, r181CounterATotal,
    r181CounterR, r181CounterAEarly]
  omega

/-- In the same scalar frame, using *all* blockers would indeed leave only
five seats.  The forward temporal collisions above are exactly what blocks
this replacement in the actual-game Hall proof. -/
theorem r181_fullBlockerPacket_would_have_five_slack
    (k : Nat) (hk : 1 <= k) :
    r181CounterR k -
        (r181CounterV k - r181CounterR k - 1 +
          r181CounterATotal k) = 5 := by
  simp [r181CounterV, r181CounterR, r181CounterATotal]
  omega

#print axioms gameF_targetHost_freezeCollision_forces_futureBlocker
#print axioms gameF_terminal_relay_actual_blockersThrough_hall
#print axioms gameF_terminal_actual_blocker_count_endpoint
#print axioms gameF_seven_terminal_rails_are_blocker_freezes
#print axioms r181_earlyBlockerHall_linearSlack_counterframe

end ChompLean
