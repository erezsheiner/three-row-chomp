import R209B43ChargeTailReduction

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R212: audit of the blocker-rank slack 39 tail

The proved AFloor gives only

`u <= 3*A(u-1)+2`,

whereas R209 needs `u+39 <= 3*A(u-1)`.  Neither the count ceiling nor the
current diagonal envelope, Floor+, and DiagDoubleSlack close the forty-one
unit difference.  A one-step scalar counterframe below makes this precise.

There is, however, a sharp induction normal form.  Put

`sigma(u) = 3*A(u-1)-u`.

Moving from `u` to `u+1` lowers `sigma` by one at a nonblocker and raises it
by two at a blocker.  Hence the tail follows from a base slack at 173 and
only the boundary law

`sigma(u)=39 -> S gameF u`.

This is the minimal state-dependent density input: away from the boundary,
monotonicity of the blocker count alone preserves the inequality.
-/

/-! ## Exact blocker-count step -/

/-- A blocker contributes exactly one new element to the cumulative count. -/
theorem gameFBlockerCountThrough_succ_of_blocker
    {n : Nat}
    (hS : S gameF (n + 1)) :
    gameFBlockerCountThrough (n + 1) =
      gameFBlockerCountThrough n + 1 := by
  classical
  have hS' : S gameF (1 + n) := by
    simpa [Nat.add_comm] using hS
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList]
  rw [List.range'_concat, List.filter_append, List.length_append]
  simp [hS']

/-! ## Minimal induction interfaces -/

/-- Initial rank slack at the first tail target. -/
def GameFBlockerRankSlack39Base173 : Prop :=
  173 + 39 <= 3 * gameFBlockerCountThrough 172

/-- State-dependent density barrier: whenever the slack reaches exactly
39, the current value must be a blocker and replenish it before the next
target. -/
def GameFBlockerRankSlack39BarrierFrom173 : Prop :=
  forall {u : Nat},
    173 <= u ->
    u + 39 = 3 * gameFBlockerCountThrough (u - 1) ->
    S gameF u

/-- One induction step.  If the inequality is strict, monotonicity alone
absorbs the next unit.  At equality, the barrier supplies an exact count
increment of one. -/
theorem gameF_blockerRankSlack39_step
    {u : Nat}
    (hu : 0 < u)
    (hslack : u + 39 <=
      3 * gameFBlockerCountThrough (u - 1))
    (hbarrier :
      u + 39 = 3 * gameFBlockerCountThrough (u - 1) ->
        S gameF u) :
    u + 1 + 39 <= 3 * gameFBlockerCountThrough u := by
  have hindex : u - 1 + 1 = u := by omega
  have hunit := gameFBlockerCountThrough_unitIncrement01 (u - 1)
  rw [hindex] at hunit
  have hmono :
      gameFBlockerCountThrough (u - 1) <=
        gameFBlockerCountThrough u := by
    rcases hunit with hsame | hplus <;> omega
  by_cases heq :
      u + 39 = 3 * gameFBlockerCountThrough (u - 1)
  . have hS : S gameF u := hbarrier heq
    have hinc0 :=
      gameFBlockerCountThrough_succ_of_blocker
        (n := u - 1) (by simpa only [hindex] using hS)
    have hinc :
        gameFBlockerCountThrough u =
          gameFBlockerCountThrough (u - 1) + 1 := by
      simpa only [hindex] using hinc0
    omega
  . omega

/-- Base plus the exact boundary barrier prove the entire R209 rank tail. -/
theorem gameFBlockerRankSlack39From173_of_base_barrier
    (hbase : GameFBlockerRankSlack39Base173)
    (hbarrier : GameFBlockerRankSlack39BarrierFrom173) :
    GameFBlockerRankSlack39From173 := by
  intro u hu173
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hu173
  induction n with
  | zero =>
      simpa [GameFBlockerRankSlack39Base173] using hbase
  | succ n ih =>
      have hstep := gameF_blockerRankSlack39_step
        (u := 173 + n) (by omega) (ih (by omega))
        (fun heq => hbarrier (by omega) heq)
      simpa [Nat.add_assoc] using hstep

/-- Concrete base receipt suggested by the cache.  It is exposed only as a
certificate interface, not asserted here. -/
def GameFBlockerCountThrough172Eq71 : Prop :=
  gameFBlockerCountThrough 172 = 71

theorem gameFBlockerRankSlack39Base173_of_count172
    (hcount : GameFBlockerCountThrough172Eq71) :
    GameFBlockerRankSlack39Base173 := by
  unfold GameFBlockerCountThrough172Eq71 at hcount
  unfold GameFBlockerRankSlack39Base173
  omega

/-- Compact sharp induction package. -/
def GameFBlockerRankSlack39InductionPackage : Prop :=
  GameFBlockerRankSlack39Base173 /\
    GameFBlockerRankSlack39BarrierFrom173

theorem gameFBlockerRankSlack39From173_of_inductionPackage
    (hpackage : GameFBlockerRankSlack39InductionPackage) :
    GameFBlockerRankSlack39From173 := by
  rcases hpackage with ⟨hbase, hbarrier⟩
  exact gameFBlockerRankSlack39From173_of_base_barrier hbase hbarrier

/-! ## Scalar red team for the current bank -/

/-- The currently proved numerical count and diagonal laws permit a
nonblocker exactly at slack 39, followed by failure at the next target.

Here `a` is a prospective diagonal owner of `u`.  The frame satisfies the
overlap lower envelope, Floor+, DiagDoubleSlack, AFloor, the blocker-count
ceiling, and a legal zero count increment.  It is not a recurrence-model
counterexample; it shows that those exported inequalities cannot prove the
missing boundary law. -/
theorem gameF_rankSlack39_not_forced_by_current_scalar_bank :
    let u := 174
    let a := 100
    let Aprev := 71
    let Anext := 71
    173 <= u /\
      u + 39 = 3 * Aprev /\
      Anext = Aprev /\
      u <= 3 * Aprev + 2 /\
      u + 1 <= 3 * Anext + 2 /\
      2 * Aprev + 4 <= u /\
      2 * Anext + 4 <= u + 1 /\
      a < u /\
      a + 1 + (a + 1) / 2 <= u /\
      3 * a + 5 <= 2 * u /\
      u + 2 <= 2 * a /\
      Not (u + 1 + 39 <= 3 * Anext) := by
  dsimp
  omega

#print axioms gameFBlockerCountThrough_succ_of_blocker
#print axioms gameF_blockerRankSlack39_step
#print axioms gameFBlockerRankSlack39From173_of_base_barrier
#print axioms gameFBlockerRankSlack39Base173_of_count172
#print axioms gameFBlockerRankSlack39From173_of_inductionPackage
#print axioms gameF_rankSlack39_not_forced_by_current_scalar_bank

end ChompLean
