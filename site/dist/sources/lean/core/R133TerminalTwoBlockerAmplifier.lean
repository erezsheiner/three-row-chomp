import R132OldLossTerminalCellKill
import R132UpperRailOwnerCoverageReduction
import R31TopTailCoreMexNormalForm

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean.R133TerminalTwoBlockerAmplifier

open ChompLean
open ChompLean.R132OldLossTerminalCellKill

/-!
R133 kernel for the terminal two-blocker amplifier, the exact terminal
two-hole interface, and the clean-history upper-rail wrapper.

The OLD-LOSS frame, blocker counts, PiZero identities, lower diagonal
envelope, and empty-ray target hole are not asserted here.  They occur as
named hypotheses at the theorem boundary.  In particular, no theorem in
this file assumes RM2, Upper Rail, HalfPin, NIE, or NO-OLD-FALLER.
-/

/-! ## A. Pure subtraction-free terminal amplifier -/

/-- Target half of the amplifier.  `cq + Kq = 2*Aq+1` is the
subtraction-free PiZero identity. -/
theorem terminal_target_bound
    {T q s cq Kq Aq Dq : Nat}
    (hq : q = T + s)
    (hTargetHost : T <= cq)
    (hPiQ : cq + Kq = 2 * Aq + 1)
    (hCountQ : 2 * Aq + Dq <= q) :
    Dq + Kq <= s + 1 := by
  omega

/-- Terminal half of the amplifier.  The order hypothesis is written as
`T <= cy+1`, avoiding truncated subtraction in the input. -/
theorem terminal_terminal_bound
    {T q s y gap cy Ky Ay Dy : Nat}
    (hq : q = T + s)
    (hygap : y + gap = q)
    (hTerminalHost : T <= cy + 1)
    (hPiY : cy + Ky = 2 * Ay + 1)
    (hCountY : 2 * Ay + Dy <= y) :
    gap + Dy + Ky <= s + 2 := by
  omega

/-- Pair form `(AMP)`.  The target defect `Kq` is absent: it cancels before
this subtraction-free inequality is stated. -/
theorem terminal_pair_bound
    {T q s cy Ky Ay Aq B Dq : Nat}
    (hq : q = T + s)
    (hTerminalHost : T <= cy + 1)
    (hMass : Aq = Ay + B)
    (hPiY : cy + Ky = 2 * Ay + 1)
    (hCountQ : 2 * Aq + Dq <= q) :
    Dq + 2 * B + Ky <= s + 2 := by
  omega

set_option linter.unusedVariables false in
/-- The three conclusions of R133 Section 3 in one interface.  Every
quantity in the two PiZero/count frames remains explicit.  `B>=1` is kept
in the interface for the specializations, although the raw pair inequality
itself does not consume it. -/
theorem terminal_amplifier_three_bounds
    {T q s y gap cq cy Kq Ky Aq Ay B Dq Dy : Nat}
    (hq : q = T + s)
    (hygap : y + gap = q)
    (hTargetHost : T <= cq)
    (hTerminalHost : T <= cy + 1)
    (hB : 1 <= B)
    (hMass : Aq = Ay + B)
    (hPiQ : cq + Kq = 2 * Aq + 1)
    (hPiY : cy + Ky = 2 * Ay + 1)
    (hCountQ : 2 * Aq + Dq <= q)
    (hCountY : 2 * Ay + Dy <= y) :
    Dq + Kq <= s + 1 /\
      gap + Dy + Ky <= s + 2 /\
      Dq + 2 * B + Ky <= s + 2 := by
  refine ⟨terminal_target_bound hq hTargetHost hPiQ hCountQ, ?_, ?_⟩
  · exact terminal_terminal_bound hq hygap hTerminalHost hPiY hCountY
  · exact terminal_pair_bound hq hTerminalHost hMass hPiY hCountQ

/-- Basic odd-target specialization: the external parity count theorem is
represented by its exact defect-five ceiling. -/
theorem terminal_amplifier_basic_odd
    {T q s cy Ky Ay Aq B : Nat}
    (hOdd : IsOdd q)
    (hq : q = T + s)
    (hTerminalHost : T <= cy + 1)
    (hB : 1 <= B)
    (hMass : Aq = Ay + B)
    (hPiY : cy + Ky = 2 * Ay + 1)
    (hOddCount : 2 * Aq + 5 <= q) :
    IsOdd q /\ 5 + Ky <= s := by
  refine ⟨hOdd, ?_⟩
  have hAmp := terminal_pair_bound
    (Dq := 5) hq hTerminalHost hMass hPiY hOddCount
  omega

/-- Basic even-target specialization: the external parity count theorem is
represented by its exact defect-six ceiling. -/
theorem terminal_amplifier_basic_even
    {T q s cy Ky Ay Aq B : Nat}
    (hEven : IsEven q)
    (hq : q = T + s)
    (hTerminalHost : T <= cy + 1)
    (hB : 1 <= B)
    (hMass : Aq = Ay + B)
    (hPiY : cy + Ky = 2 * Ay + 1)
    (hEvenCount : 2 * Aq + 6 <= q) :
    IsEven q /\ 6 + Ky <= s := by
  refine ⟨hEven, ?_⟩
  have hAmp := terminal_pair_bound
    (Dq := 6) hq hTerminalHost hMass hPiY hEvenCount
  omega

/-- Abstract J9 specialization `Dq=12+epsilon`.  The first conclusion keeps
the full blocker mass; the second uses only `B>=1`. -/
theorem terminal_amplifier_J9
    {T q s cy Ky Ay Aq B epsilon : Nat}
    (hq : q = T + s)
    (hTerminalHost : T <= cy + 1)
    (hB : 1 <= B)
    (hMass : Aq = Ay + B)
    (hPiY : cy + Ky = 2 * Ay + 1)
    (hJ9Count : 2 * Aq + (12 + epsilon) <= q) :
    2 * B + Ky + 10 + epsilon <= s /\
      12 + epsilon + Ky <= s := by
  have hAmp := terminal_pair_bound
    (Dq := 12 + epsilon) hq hTerminalHost hMass hPiY hJ9Count
  omega

/-! ## B. Terminal two-blocker source interface -/

/-- Convenient name for the strict future-range-cone inequality used in
R133.  It is a frame predicate, not an asserted global envelope. -/
def BelowFutureRangeCone (T q : Nat) : Prop :=
  q < ceilThreeHalves (T + 1) + 1

/-- `ceil(n/2)` on naturals. -/
def ceilHalf (n : Nat) : Nat := (n + 1) / 2

/-- R133's slack form of the cone implies the direct diagonal-envelope
form used by the game-level proofs below. -/
theorem belowFutureRangeCone_of_slack
    {T q s : Nat}
    (hq : q = T + s)
    (hslack : s < ceilHalf (T + 5)) :
    BelowFutureRangeCone T q := by
  unfold ceilHalf at hslack
  unfold BelowFutureRangeCone ceilThreeHalves
  omega

/-- Below the future-range cone, a target occupying `V1(T)` cannot be a
diagonal opening value.  Opening cover therefore makes it a row start, and
exact host order puts its freeze column at or to the right of `T`.

`LowerDiagonalEnvelope` remains the explicit paper-bank input. -/
theorem gameF_target_rowstart_below_future_range_cone
    {T q : Nat}
    (hT : 1 <= T)
    (hV1 : gameF T (T - 1) = q)
    (hTq : T < q)
    (hCone : BelowFutureRangeCone T q)
    (hLowerDiagonal : LowerDiagonalEnvelope) :
    Exists fun cq => cq < q /\ gameF q cq = q /\ T <= cq := by
  have hqpos : 0 < q := by omega
  rcases gameRecurrenceModel.opening_cover hqpos with hDiagonal | hRowstart
  · rcases hDiagonal with ⟨a, haq, hdiag⟩
    have hTa : T < a := by
      by_cases haT : a < T
      · have hleft := gameF_past_diagonal_echo_strictly_left
          haT (by omega : T - 1 <= T)
          (by
            calc
              gameF T (T - 1) = q := hV1
              _ = gameF a a := hdiag.symm)
        omega
      · have hTle : T <= a := Nat.le_of_not_gt haT
        by_cases haEq : a = T
        · subst a
          have hcols : T - 1 = T :=
            gameRecurrenceModel.fixed_q_injective
              (by omega) (Nat.le_refl T)
              (hV1.trans hdiag.symm)
          omega
        · omega
    have hmono :
        ceilThreeHalves (T + 1) <= ceilThreeHalves a :=
      ceilThreeHalves_mono (by omega)
    have henv := hLowerDiagonal a
    have hdiagGame : gameF a a = q := hdiag
    rw [hdiagGame] at henv
    unfold BelowFutureRangeCone at hCone
    omega
  · rcases hRowstart with ⟨cq, hcq, hstart⟩
    have hTcq : T <= cq := by
      rcases rowstart_host_order_exact gameRecurrenceModel hcq hstart
          (by omega : T - 1 < T) (Nat.le_of_lt hTq) hV1 with
          hStrict | hBoundary
      · omega
      · omega
    exact ⟨cq, hcq, hstart, hTcq⟩

/-- The terminal RANGE arm is impossible in the R133 rebound/cone frame.
The only extra rebound datum needed is the displayed previous-diagonal
inequality; the owner `a=T` is deleted by fixed-row injectivity. -/
theorem gameF_terminal_range_impossible_below_future_range_cone
    {T y q : Nat}
    (hT : 2 <= T)
    (hV2 : gameF T (T - 2) = y)
    (hyq : y < q)
    (hPrevDiagonalAbove : q < gameF (T - 1) (T - 1))
    (hCone : BelowFutureRangeCone T q)
    (hLowerDiagonal : LowerDiagonalEnvelope) :
    Not (Exists fun a => a < y /\ gameF a a = y) := by
  rintro ⟨a, hay, hdiag⟩
  by_cases haT : a < T
  · have hleft := gameF_past_diagonal_echo_strictly_left
      haT (by omega : T - 2 <= T)
      (by
        calc
          gameF T (T - 2) = y := hV2
          _ = gameF a a := hdiag.symm)
    have haPrev : a = T - 1 := by omega
    subst a
    omega
  · have hTle : T <= a := Nat.le_of_not_gt haT
    by_cases haEq : a = T
    · subst a
      have hcols : T - 2 = T :=
        gameRecurrenceModel.fixed_q_injective
          (by omega) (Nat.le_refl T)
          (hV2.trans hdiag.symm)
      omega
    · have hTa : T < a := by omega
      have hmono :
          ceilThreeHalves (T + 1) <= ceilThreeHalves a :=
        ceilThreeHalves_mono (by omega)
      have henv := hLowerDiagonal a
      rw [hdiag] at henv
      unfold BelowFutureRangeCone at hCone
      omega

/-- Once the two boundary values have been removed (`T<y`), the preceding
RANGE exclusion and opening cover make the terminal a row start.  Exact
host order gives both the literal and subtraction-free forms of
`T-1 <= cy`. -/
theorem gameF_terminal_rowstart_below_future_range_cone
    {T y q : Nat}
    (hT : 2 <= T)
    (hV2 : gameF T (T - 2) = y)
    (hTy : T < y)
    (hyq : y < q)
    (hPrevDiagonalAbove : q < gameF (T - 1) (T - 1))
    (hCone : BelowFutureRangeCone T q)
    (hLowerDiagonal : LowerDiagonalEnvelope) :
    Exists fun cy => cy < y /\ gameF y cy = y /\
      T - 1 <= cy /\ T <= cy + 1 := by
  have hNoRange := gameF_terminal_range_impossible_below_future_range_cone
    hT hV2 hyq hPrevDiagonalAbove hCone hLowerDiagonal
  have hypos : 0 < y := by omega
  rcases gameRecurrenceModel.opening_cover hypos with hDiagonal | hRowstart
  · exact False.elim (hNoRange hDiagonal)
  · rcases hRowstart with ⟨cy, hcyy, hstart⟩
    have hOrder : T - 1 <= cy /\ T <= cy + 1 := by
      rcases rowstart_host_order_exact gameRecurrenceModel hcyy hstart
          (by omega : T - 2 < T) (Nat.le_of_lt hTy) hV2 with
          hStrict | hBoundary
      · omega
      · omega
    exact ⟨cy, hcyy, hstart, hOrder.1, hOrder.2⟩

/-- A terminal freeze column strictly beyond `T-2` excludes the V2 carry
branch before any V2 MEX conclusion is used. -/
theorem gameF_terminal_v2_mex_after_carry_exclusion
    {T y cy : Nat}
    (hT : 2 <= T)
    (hV2 : gameF T (T - 2) = y)
    (hcyLower : T - 2 < cy)
    (hcyy : cy < y) :
    IsMex (B gameF T (T - 2)) y := by
  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  have htop := ceiling_top_two_mex_branches
    hrec gameRecurrenceModel.diagonal_gt (T - 2)
  have hrow1 : T - 2 + 1 = T - 1 := by omega
  have hrow2 : T - 2 + 2 = T := by omega
  rcases htop.2.2 with hcarry | hmex
  · rw [hrow1, hrow2, hV2] at hcarry
    omega
  · rw [hrow1, hrow2, hV2] at hmex
    exact hmex.2

/-- `y,q` are the first two positive holes of `S`: first `y` is filled,
then `q` is the next positive MEX. -/
def FirstTwoPositiveHoles (S : Nat -> Prop) (y q : Nat) : Prop :=
  IsMex S y /\ IsMex (fun p => S p \/ y = p) q

/-- Exact R125/R133 terminal-source theorem.

The source is literally the exported `TopTailCore` plus the preceding V1
singleton.  The proof derives the V2 MEX only after using `cy>T-2` to kill
carry, and rewrites both cells with `source_at_v2`/`source_at_v1`.

`hTargetAbsent` is the still-open R126 empty-ray wrapper: it is deliberately
visible and is not inferred from the local MEX equations. -/
theorem gameF_terminal_source_first_two_positive_holes
    {T y q cy : Nat}
    (hT : 2 <= T)
    (hV2 : gameF T (T - 2) = y)
    (hV1 : gameF T (T - 1) = q)
    (hcyLower : T - 2 < cy)
    (hcyy : cy < y)
    (hyq : y < q)
    (hPrevDiagonalHigh : q < gameF (T - 1) (T - 1))
    (hTargetAbsent :
      Not (TopTailCore gameF (T - 2) q \/
        gameF (T - 1) (T - 2) = q)) :
    FirstTwoPositiveHoles
      (fun p => TopTailCore gameF (T - 2) p \/
        gameF (T - 1) (T - 2) = p) y q := by
  let K := TopTailCore gameF (T - 2)
  let x := gameF (T - 1) (T - 2)
  let l := gameF (T - 1) (T - 1)
  let S := fun p => K p \/ x = p
  have hrow1 : T - 2 + 1 = T - 1 := by omega
  have hrow2 : T - 2 + 2 = T := by omega

  have hyMexB : IsMex (B gameF T (T - 2)) y :=
    gameF_terminal_v2_mex_after_carry_exclusion hT hV2 hcyLower hcyy
  have hyMexS : IsMex S y := by
    apply (isMex_congr (S := B gameF T (T - 2)) (T := S)
      (m := y) (fun p => ?_)).1 hyMexB
    dsimp [S, K, x]
    simpa [hrow1, hrow2] using
      (source_at_v2 (f := gameF) (r := T - 2) (p := p))

  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  have htop := ceiling_top_two_mex_branches
    hrec gameRecurrenceModel.diagonal_gt (T - 2)
  have hqMexB : IsMex (B gameF T (T - 1)) q := by
    have hmex := htop.1
    rw [hrow1, hrow2, hV1] at hmex
    exact hmex
  have hqMexExpanded :
      IsMex (fun p => K p \/ l = p \/ y = p) q := by
    apply (isMex_congr (S := B gameF T (T - 1))
      (T := fun p => K p \/ l = p \/ y = p)
      (m := q) (fun p => ?_)).1 hqMexB
    dsimp [K, l]
    simpa [hrow1, hrow2, hV2] using
      (source_at_v1 (f := gameF) (r := T - 2) (p := p))

  have hqMexSecond : IsMex (fun p => S p \/ y = p) q := by
    refine ⟨hqMexExpanded.1, ?_, ?_⟩
    · rintro (hSq | hyEq)
      · apply hTargetAbsent
        simpa [S, K, x] using hSq
      · omega
    · intro k hkpos hkq
      by_cases hky : k < y
      · exact Or.inl (hyMexS.2.2 k hkpos hky)
      · by_cases hEq : k = y
        · subst k
          exact Or.inr rfl
        · have hyk : y < k := by omega
          rcases hqMexExpanded.2.2 k hkpos hkq with hK | hl | hy
          · exact Or.inl (Or.inl hK)
          · dsimp [l] at hl
            omega
          · omega
  exact ⟨hyMexS, hqMexSecond⟩

/-! ## C. Upper-rail induction wrapper with CLEAN explicit -/

/-- The blocker midpoint used in the assignment upper rail. -/
def blockerMidpoint (A : Nat -> Nat) (v : Nat) : Nat :=
  (v + A (v - 1)) / 2

/-- Instantiate R132's owner-coverage tail theorem at the actual midpoint.
The conclusion is the upper rail, and the candidate-column clean-history
atom is an explicit premise exactly as requested.

`A` and its count-growth facts remain abstract because no unconditional
global blocker-count/freeze API is exported in the local kernel. -/
theorem gameF_upper_rail_from_midpoint_clean_history
    (A : Nat -> Nat) {v r : Nat}
    (hvBase : 26 <= v)
    (hrv : r < v)
    (hstart : gameF v r = v)
    (hAFloor : v <= 3 * A (v - 1) + 2)
    (hdiagFloor : forall {k a},
      0 < k -> k < v -> a < k -> gameF a a = k -> 16 <= a ->
      3 * a + 5 <= 2 * k)
    (hfreezeInductionData : forall {k rk},
      0 < k -> k < v -> rk < k -> gameF k rk = k ->
      A (k - 1) + 1 <= A (v - 1) /\
        rk <= blockerMidpoint A k + 1)
    (hclean :
      Not (ColHistPred gameF v (blockerMidpoint A v + 1) v)) :
    r <= blockerMidpoint A v + 1 := by
  have hmidVUpper :
      v + A (v - 1) < 2 * blockerMidpoint A v + 2 := by
    unfold blockerMidpoint
    omega
  have howners : LowerOwnerCoveredBy v (blockerMidpoint A v) := by
    apply lowerOwnerCoveredBy_target_midpoint_of_upperRail_induction_tail
      hvBase hAFloor hmidVUpper hdiagFloor
    intro k rk hkpos hkv hrk hstartk
    rcases hfreezeInductionData hkpos hkv hrk hstartk with
      ⟨hcount, hrail⟩
    refine ⟨A (k - 1), blockerMidpoint A k, hcount, ?_, hrail⟩
    unfold blockerMidpoint
    omega
  exact gameF_freeze_le_midpoint_succ_of_owner_coverage
    (by omega) hrv hstart howners hclean

#print axioms terminal_target_bound
#print axioms terminal_terminal_bound
#print axioms terminal_pair_bound
#print axioms terminal_amplifier_three_bounds
#print axioms terminal_amplifier_basic_odd
#print axioms terminal_amplifier_basic_even
#print axioms terminal_amplifier_J9
#print axioms belowFutureRangeCone_of_slack
#print axioms gameF_target_rowstart_below_future_range_cone
#print axioms gameF_terminal_range_impossible_below_future_range_cone
#print axioms gameF_terminal_rowstart_below_future_range_cone
#print axioms gameF_terminal_v2_mex_after_carry_exclusion
#print axioms gameF_terminal_source_first_two_positive_holes
#print axioms gameF_upper_rail_from_midpoint_clean_history

end ChompLean.R133TerminalTwoBlockerAmplifier
