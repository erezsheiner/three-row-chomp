import R30FreezeServiceOrder
import R56EchoLeft

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean.R132OldLossTerminalCellKill

/-!
R132: a standalone kernel for the terminal-cell reduction and the deletion
of the `q = t + 6` OLD-LOSS packet.

This file does not define, assume, or prove an `OLD_LOSS` predicate.  Its
game-specific local frame is displayed in the hypotheses of the two main
theorems.  The recurrence facts `opening_cover`, fixed-row injectivity,
ECHO-LEFT, `rowstart_host_order_exact`, and diagonal/row-start disjointness
are imported actual-game theorems.  Every currently paper-banked envelope,
freeze-gap, and encoding bridge is represented by a named explicit
hypothesis below.
-/

/-- `ceil (3*n/2)` in subtraction-free natural-number form. -/
def ceilThreeHalves (n : Nat) : Nat := (3 * n + 1) / 2

/-- Explicit parity predicates, kept local to avoid importing algebraic
typeclass machinery that is irrelevant to this arithmetic kernel. -/
def IsOdd (n : Nat) : Prop := exists k, n = 2 * k + 1
def IsEven (n : Nat) : Prop := exists k, n = 2 * k

/-- Paper-bank port for the lower diagonal envelope. -/
def LowerDiagonalEnvelope : Prop :=
  forall a, ceilThreeHalves a + 1 <= gameF a a

/-- LOW terminal-cell encoding/completeness port. -/
def LowTerminalBridge (fb : Nat -> Nat) : Prop :=
  forall t, gameF (t + 2) t = t + 1 -> fb t = t + 1

/-- Boundary terminal-cell port at `gameF (t+2,t)=t+2`. -/
def BoundaryTerminalBridge (Blocker : Nat -> Prop) (fb : Nat -> Nat) : Prop :=
  forall t, gameF (t + 2) t = t + 2 ->
    Blocker (t + 2) /\ fb t = t + 2

/-- Exact row-start/blocker/freeze identification port. -/
def RowstartFreezeIdentification
    (Blocker : Nat -> Prop) (fb : Nat -> Nat) : Prop :=
  forall {v r}, r < v ->
    (gameF v r = v <-> Blocker v /\ fb r = v)

/-- A freeze gap of one is impossible from column two onward. -/
def GapOneKill (fb : Nat -> Nat) : Prop :=
  forall c, 2 <= c -> Not (fb c = c + 1)

/-- The unique freeze gap of two is at column three. -/
def GapTwoForcing (fb : Nat -> Nat) : Prop :=
  forall c, fb c = c + 2 -> c = 3

/-- NECP-2 port: a blocker of value at least 16 has no gap-three freeze. -/
def NECP2 (Blocker : Nat -> Prop) (fb : Nat -> Nat) : Prop :=
  forall {v c}, Blocker v -> 16 <= v -> fb c = v -> v = c + 3 -> False

/-- R128.2 port: an even blocker of value at least 16 has no gap-four freeze. -/
def EvenGapFourKill (Blocker : Nat -> Prop) (fb : Nat -> Nat) : Prop :=
  forall {v c}, Blocker v -> IsEven v -> 16 <= v ->
    fb c = v -> v = c + 4 -> False

/-- Monotonicity of the arithmetic lower-envelope expression. -/
theorem ceilThreeHalves_mono {a b : Nat} (hab : a <= b) :
    ceilThreeHalves a <= ceilThreeHalves b := by
  unfold ceilThreeHalves
  exact Nat.div_le_div_right (by omega)

set_option linter.unusedVariables false in
/--
Task A: parametric terminal-blocker reduction.

The cutoff `c` and its bound are retained in the signature because they are
part of the R126 ray frame, even though only the resulting terminal sandwich
is needed after the frame has been unpacked.
-/
theorem terminal_blocker_reduction
    {t q s c : Nat} (Blocker : Nat -> Prop) (fb : Nat -> Nat)
    (hq : q = t + 2 + s)
    (ht : 4 <= t)
    (hc : c <= t - 1)
    (hTerminalLower : t < gameF (t + 2) t)
    (hTerminalUpper : gameF (t + 2) t < q)
    (hCone : q <= ceilThreeHalves (t + 1) + 1)
    (hLowerDiagonal : LowerDiagonalEnvelope)
    (hLowBridge : LowTerminalBridge fb)
    (hBoundaryBridge : BoundaryTerminalBridge Blocker fb)
    (hGapOne : GapOneKill fb)
    (hGapTwo : GapTwoForcing fb)
    (hIdentify : RowstartFreezeIdentification Blocker fb) :
    exists y c_y,
      y = gameF (t + 2) t /\
      t + 2 < y /\
      t < c_y /\
      c_y < y /\
      y < q /\
      Blocker y /\
      fb c_y = y /\
      1 <= y - c_y /\
      y - c_y <= s := by
  let T := t + 2
  let y := gameF T t
  have hty : t < y := by
    simpa [T, y] using hTerminalLower
  have hyq : y < q := by
    simpa [T, y] using hTerminalUpper

  have hTy : T < y := by
    apply Nat.lt_of_not_ge
    intro hyT
    have hboundary : y = t + 1 \/ y = t + 2 := by
      dsimp [T] at hyT
      omega
    rcases hboundary with hyLow | hyBoundary
    · have hfb : fb t = t + 1 :=
        hLowBridge t (by simpa [T, y] using hyLow)
      exact (hGapOne t (by omega)) hfb
    · have hfb : fb t = t + 2 :=
        (hBoundaryBridge t (by simpa [T, y] using hyBoundary)).2
      have ht3 : t = 3 := hGapTwo t hfb
      omega

  have hypos : 0 < y := by omega
  rcases gameRecurrenceModel.opening_cover hypos with hDiagonal | hRowstart
  · rcases hDiagonal with ⟨a, hay, hdiag⟩
    have hta : t < a := by
      by_cases haT : a < T
      · exact gameF_past_diagonal_echo_strictly_left haT (by omega)
          (by
            calc
              gameF T t = y := rfl
              _ = gameF a a := hdiag.symm)
      · have hTa : T <= a := Nat.le_of_not_gt haT
        by_cases haEq : a = T
        · subst a
          have hcols : t = T :=
            gameRecurrenceModel.fixed_q_injective
              (show t <= T by dsimp [T]; omega) (Nat.le_refl T)
              (by
                calc
                  gameF T t = y := rfl
                  _ = gameF T T := hdiag.symm)
          omega
        · omega
    have hmono :
        ceilThreeHalves (t + 1) <= ceilThreeHalves a :=
      ceilThreeHalves_mono (by omega)
    have henv : ceilThreeHalves a + 1 <= y := by
      have henv' := hLowerDiagonal a
      have hdiagGame : gameF a a = y := hdiag
      rw [hdiagGame] at henv'
      exact henv'
    omega
  · rcases hRowstart with ⟨c_y, hcyy, hstart⟩
    have hhost : gameF T t = y := rfl
    have htcy : t < c_y := by
      rcases rowstart_host_order_exact gameRecurrenceModel hcyy hstart
          (by omega : t < T) (Nat.le_of_lt hTy) hhost with
          hStrict | hBoundary
      · exact hStrict.2
      · omega
    have hspecies : Blocker y /\ fb c_y = y :=
      (hIdentify hcyy).mp hstart
    refine ⟨y, c_y, ?_, ?_, htcy, hcyy, hyq,
      hspecies.1, hspecies.2, ?_, ?_⟩
    · rfl
    · simpa [T] using hTy
    · omega
    · apply (Nat.sub_le_iff_le_add').2
      rw [hq] at hyq
      omega

/--
The symbolic threshold certificate used by Task B.  It is an actual-game
consequence of `d(8)=15` and the already exported diagonal/row-start
disjointness theorem; it contains no finite table.
-/
theorem symbolic_q17_base_false
    (hSaturationBase : gameF 8 8 = 15)
    (hRowstart15 : gameF 15 12 = 15) : False := by
  exact disjoint_D_S gameRecurrenceModel
    ⟨8, hSaturationBase⟩ ⟨12, by omega, hRowstart15⟩

/--
Task B: deletion of the complete `q=t+6` packet, conditional only on the
displayed R126/R128 local frame and the named paper-bank ports.
-/
theorem gap_four_packet_false
    {t q c : Nat} (Blocker : Nat -> Prop) (fb : Nat -> Nat)
    (hq : q = t + 6)
    (htOdd : IsOdd t)
    (ht11 : 11 <= t)
    (hc : c <= t - 1)
    (hTerminalLower : t < gameF (t + 2) t)
    (hTerminalUpper : gameF (t + 2) t < q)
    (hLowerDiagonal : LowerDiagonalEnvelope)
    (hLowBridge : LowTerminalBridge fb)
    (hBoundaryBridge : BoundaryTerminalBridge Blocker fb)
    (hIdentify : RowstartFreezeIdentification Blocker fb)
    (hGapOne : GapOneKill fb)
    (hGapTwo : GapTwoForcing fb)
    (hNECP2 : NECP2 Blocker fb)
    (hEvenGapFour : EvenGapFourKill Blocker fb)
    (hSaturationBase : gameF 8 8 = 15) : False := by
  rcases htOdd with ⟨k, hk⟩
  have hCone : q <= ceilThreeHalves (t + 1) + 1 := by
    unfold ceilThreeHalves
    omega
  have hqFrame : q = t + 2 + 4 := by omega
  rcases terminal_blocker_reduction
      (t := t) (q := q) (s := 4) (c := c)
      Blocker fb hqFrame (by omega) hc hTerminalLower hTerminalUpper
      hCone hLowerDiagonal hLowBridge hBoundaryBridge hGapOne hGapTwo
      hIdentify with
    ⟨y, c_y, hy, hTy, htcy, hcyy, hyq, hBlocker, hfreeze,
      _hGapPositive, hGapUpper⟩

  have hstart : gameF y c_y = y :=
    (hIdentify hcyy).mpr ⟨hBlocker, hfreeze⟩
  have hNoGapOne : Not (y = c_y + 1) := by
    intro hgap
    exact (hGapOne c_y (by omega)) (by omega)
  have hNoGapTwo : Not (y = c_y + 2) := by
    intro hgap
    have hc3 : c_y = 3 := hGapTwo c_y (by omega)
    omega
  have hyCases : y = t + 3 \/ y = t + 4 \/ y = t + 5 := by
    omega

  rcases hyCases with hy3 | hy4 | hy5
  · omega
  · by_cases htBase : t = 11
    · have hq17 : q = 17 := by omega
      have hy15 : y = 15 := by omega
      have hcy12 : c_y = 12 := by omega
      have hRowstart15 : gameF 15 12 = 15 := by
        simpa [hy15, hcy12] using hstart
      exact symbolic_q17_base_false hSaturationBase hRowstart15
    · have hyThreshold : 16 <= y := by omega
      have hgapThree : y = c_y + 3 := by omega
      exact hNECP2 hBlocker hyThreshold hfreeze hgapThree
  · have hyThreshold : 16 <= y := by omega
    have hyEven : IsEven y := by
      refine ⟨k + 3, ?_⟩
      omega
    by_cases hgapThree : y = c_y + 3
    · exact hNECP2 hBlocker hyThreshold hfreeze hgapThree
    · have hgapFour : y = c_y + 4 := by omega
      exact hEvenGapFour hBlocker hyEven hyThreshold hfreeze hgapFour

#print axioms ceilThreeHalves_mono
#print axioms terminal_blocker_reduction
#print axioms symbolic_q17_base_false
#print axioms gap_four_packet_false

end ChompLean.R132OldLossTerminalCellKill
