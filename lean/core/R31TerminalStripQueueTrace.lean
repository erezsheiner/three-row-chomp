import R29TerminalBlockerMexCompletion
import R27LowerNewLossAnatomy
import TopTwoSourceExpansion
import CeilingTopTwoMexAudit
import LineHolePreservation

set_option autoImplicit false

namespace ChompLean

/-!
R31: exact queue trace in the three terminal cells of the `L=3` row.

Put `t=e+6` and let

* `q = f(t,e+2)` be the lower loss supplied by R21;
* `x = f(t,e+3)` (`V3`), `w = f(t,e+4)` (`V2`), and
  `y = f(t,e+5)` (`V1`);
* `K = TopTailCore f (e+4)` be the common top-two source core.

R29 gives `t <= z < u`, where `u=f(t-1,t-2)`.  Therefore `V2` cannot
be a carry of `u`; both `V2` and `V1` are MEX cells.  The theorem at the
end of this file gives the exact three-way trace according as `z` is
hosted at `V3`, `V2`, or `V1`.
-/

/-- The common core contains a row-start value exactly when its named host
in row `r+2` lies strictly before the `V2` column `r`.  This is an exact
source statement: diagonal membership is excluded by `D`/`S` disjointness,
and a second row host is excluded by fixed-row injectivity. -/
theorem rowstart_top_tail_core_iff_host_before_v2
    (M : RecurrenceModel) {r z s b : Nat}
    (hsz : s < z) (hstart : M.f z s = z)
    (hb : b <= r + 2) (hhost : M.f (r + 2) b = z) :
    TopTailCore M.f r z <-> b < r := by
  constructor
  · intro hcore
    rcases hcore with hdiag | hrow
    · rcases hdiag with ⟨i, _hi, hvalue⟩
      exact False.elim
        (disjoint_D_S M ⟨i, hvalue⟩ ⟨s, hsz, hstart⟩)
    · rcases hrow with ⟨b', hb'r, hvalue⟩
      have hb' : b' <= r + 2 := by omega
      have heq : b' = b :=
        M.fixed_q_injective hb' hb (hvalue.trans hhost.symm)
      omega
  · intro hbr
    exact Or.inr ⟨b, hbr, hhost⟩

/-- If yesterday's `V1` is at least the current row, the current `V2` is
on its MEX branch.  The current `V1` is unconditionally a MEX cell. -/
theorem top_two_are_mex_of_high_previous_v1
    {f : Nat -> Nat -> Nat}
    (hrec : BrouwerRecurrence f)
    (hdiag : forall a, a < f a a)
    {r u : Nat}
    (hseat : f (r + 1) r = u) (hhigh : r + 2 <= u) :
    IsMex (B f (r + 2) r) (f (r + 2) r) /\
      IsMex (B f (r + 2) (r + 1)) (f (r + 2) (r + 1)) := by
  have htop := ceiling_top_two_mex_branches hrec hdiag r
  have hv2 : IsMex (B f (r + 2) r) (f (r + 2) r) := by
    rcases htop.2.2 with hcarry | hmex
    · rw [hseat] at hcarry
      omega
    · exact hmex.2
  exact ⟨hv2, htop.1⟩

/-- The four consecutive current-row queue outputs are pairwise distinct. -/
theorem gameF_l3_queue_four_pairwise_distinct (e : Nat) :
    gameF (e + 6) (e + 2) ≠ gameF (e + 6) (e + 3) /\
    gameF (e + 6) (e + 2) ≠ gameF (e + 6) (e + 4) /\
    gameF (e + 6) (e + 2) ≠ gameF (e + 6) (e + 5) /\
    gameF (e + 6) (e + 3) ≠ gameF (e + 6) (e + 4) /\
    gameF (e + 6) (e + 3) ≠ gameF (e + 6) (e + 5) /\
    gameF (e + 6) (e + 4) ≠ gameF (e + 6) (e + 5) := by
  have hne (a b : Nat) (ha : a <= e + 6) (hb : b <= e + 6)
      (hab : a ≠ b) : gameF (e + 6) a ≠ gameF (e + 6) b := by
    intro hvalue
    exact hab (gameRecurrenceModel.fixed_q_injective ha hb hvalue)
  exact ⟨
    hne (e + 2) (e + 3) (by omega) (by omega) (by omega),
    hne (e + 2) (e + 4) (by omega) (by omega) (by omega),
    hne (e + 2) (e + 5) (by omega) (by omega) (by omega),
    hne (e + 3) (e + 4) (by omega) (by omega) (by omega),
    hne (e + 3) (e + 5) (by omega) (by omega) (by omega),
    hne (e + 4) (e + 5) (by omega) (by omega) (by omega)⟩

/-- The compact proposition proved by the terminal queue theorem below. -/
def L3TerminalQueueTrace (e z : Nat) : Prop :=
  let q := gameF (e + 6) (e + 2)
  let x := gameF (e + 6) (e + 3)
  let w := gameF (e + 6) (e + 4)
  let y := gameF (e + 6) (e + 5)
  let K := TopTailCore gameF (e + 4)
  q < z /\ K q /\
  q ≠ x /\ q ≠ w /\ q ≠ y /\ x ≠ w /\ x ≠ y /\ w ≠ y /\
  IsMex (B gameF (e + 6) (e + 4)) w /\
  IsMex (B gameF (e + 6) (e + 5)) y /\
  ((x = z /\ K z) \/
   (x < z /\ w = z /\ z < y /\ Not (K z) /\
     (forall v, 0 < v -> v < z -> K v) /\ IsMex K z) \/
   (x < z /\ w < z /\ y = z /\ Not (K z) /\
     0 < w /\ Not (K w) /\
     (forall v, 0 < v -> v < z -> (Not (K v) <-> v = w)) /\
     IsMex K w /\ IsMex (fun v => K v \/ v = w) z))

/-- Exact terminal queue trace.

The second branch says that a blocker served at `V2` is the least positive
hole of the common core, and inserting it forces `V1` strictly above it.
The third branch says that, when the blocker waits until `V1`, the preceding
`V2` value is strictly smaller and is the *unique* positive core hole below
the blocker.  The first branch records the exact core membership in the
remaining `V3` case; no unconditional order between its later `V2,V1`
outputs follows from the source laws.
-/
theorem gameF_l3_terminal_queue_exact_trichotomy
    {e u z s : Nat}
    (hseat : gameF (e + 5) (e + 4) = u)
    (htz : e + 6 <= z) (hzu : z < u)
    (hsz : s < z) (hstart : gameF z s = z)
    (hqz : gameF (e + 6) (e + 2) < z)
    (hzMissingV3 : Not (B gameF (e + 6) (e + 3) z))
    (htop :
      gameF (e + 6) (e + 3) = z \/
      gameF (e + 6) (e + 4) = z \/
      gameF (e + 6) (e + 5) = z) :
    L3TerminalQueueTrace e z := by
  dsimp only [L3TerminalQueueTrace]
  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  have hhigh : e + 6 <= u := by omega
  have hmexTop := top_two_are_mex_of_high_previous_v1
    hrec gameRecurrenceModel.diagonal_gt hseat hhigh
  have hmexW :
      IsMex (B gameF (e + 6) (e + 4))
        (gameF (e + 6) (e + 4)) := by
    simpa [Nat.add_assoc] using hmexTop.1
  have hmexY :
      IsMex (B gameF (e + 6) (e + 5))
        (gameF (e + 6) (e + 5)) := by
    simpa [Nat.add_assoc] using hmexTop.2
  have hKq : TopTailCore gameF (e + 4)
      (gameF (e + 6) (e + 2)) := by
    right
    refine ⟨e + 2, by omega, ?_⟩
    rfl
  have hdistinct := gameF_l3_queue_four_pairwise_distinct e
  refine ⟨hqz, hKq,
    hdistinct.1, hdistinct.2.1, hdistinct.2.2.1,
    hdistinct.2.2.2.1, hdistinct.2.2.2.2.1,
    hdistinct.2.2.2.2.2, hmexW, hmexY, ?_⟩
  have hzpos : 0 < z := by omega
  have hdiagHigh : u < gameF (e + 5) (e + 5) := by
    have hle := game_diagonal_maximal (q := e + 5) (s := e + 4) (by omega)
    rw [hseat] at hle
    have hne : u ≠ gameF (e + 5) (e + 5) := by
      intro heq
      have hcols := gameRecurrenceModel.fixed_q_injective
        (q := e + 5) (b₁ := e + 4) (b₂ := e + 5)
        (by omega) (by omega) (hseat.trans heq)
      omega
    omega
  rcases htop with hxz | hwz | hyz
  · left
    have hKz : TopTailCore gameF (e + 4) z := by
      exact (rowstart_top_tail_core_iff_host_before_v2
        gameRecurrenceModel hsz hstart (b := e + 3) (r := e + 4)
          (by omega) hxz).2 (by omega)
    exact ⟨hxz, hKz⟩
  · right
    left
    have hxle : gameF (e + 6) (e + 3) <= z :=
      recurrence_guard_hole_bounds_cell hrec (by omega) htz hzpos
        hzMissingV3
    have hxlt : gameF (e + 6) (e + 3) < z := by
      have hxne : gameF (e + 6) (e + 3) ≠ z :=
        fun hx => hdistinct.2.2.2.1 (hx.trans hwz.symm)
      omega
    have hKz : Not (TopTailCore gameF (e + 4) z) := by
      have hiff := rowstart_top_tail_core_iff_host_before_v2
        gameRecurrenceModel hsz hstart (b := e + 4) (r := e + 4)
          (by omega) hwz
      change TopTailCore gameF (e + 4) z ↔ e + 4 < e + 4 at hiff
      exact fun hK => (by have := hiff.1 hK; omega)
    have hlowerK : forall v, 0 < v -> v < z ->
        TopTailCore gameF (e + 4) v := by
      intro v hvpos hvz
      have hB : B gameF (e + 6) (e + 4) v := by
        rw [hwz] at hmexW
        exact hmexW.2.2 v hvpos hvz
      have hsource := (source_at_v2 (f := gameF)
        (r := e + 4) (p := v)).1 (by
          simpa [Nat.add_assoc] using hB)
      rcases hsource with hK | hvu
      · exact hK
      · rw [hseat] at hvu
        omega
    have hzy : z < gameF (e + 6) (e + 5) := by
      apply Nat.lt_of_not_ge
      intro hyzle
      by_cases hyz' : gameF (e + 6) (e + 5) = z
      · exact hdistinct.2.2.2.2.2 (hwz.trans hyz'.symm)
      · have hylt : gameF (e + 6) (e + 5) < z := by omega
        have hypos := hmexY.1
        have hKy := hlowerK _ hypos hylt
        have hBy : B gameF (e + 6) (e + 5)
            (gameF (e + 6) (e + 5)) := by
          apply (source_at_v1 (f := gameF) (r := e + 4)
            (p := gameF (e + 6) (e + 5))).2
          exact Or.inl hKy
        exact hmexY.2.1 (by simpa [Nat.add_assoc] using hBy)
    have hmexCoreZ : IsMex (TopTailCore gameF (e + 4)) z :=
      ⟨hzpos, hKz, hlowerK⟩
    exact ⟨hxlt, hwz, hzy, hKz, hlowerK, hmexCoreZ⟩
  · right
    right
    have hxle : gameF (e + 6) (e + 3) <= z :=
      recurrence_guard_hole_bounds_cell hrec (by omega) htz hzpos
        hzMissingV3
    have hxlt : gameF (e + 6) (e + 3) < z := by
      have hxne : gameF (e + 6) (e + 3) ≠ z :=
        fun hx => hdistinct.2.2.2.2.1 (hx.trans hyz.symm)
      omega
    have hKz : Not (TopTailCore gameF (e + 4) z) := by
      have hiff := rowstart_top_tail_core_iff_host_before_v2
        gameRecurrenceModel hsz hstart (b := e + 5) (r := e + 4)
          (by omega) hyz
      change TopTailCore gameF (e + 4) z ↔ e + 5 < e + 4 at hiff
      exact fun hK => (by have := hiff.1 hK; omega)
    have hzMissingW : Not (B gameF (e + 6) (e + 4) z) := by
      intro hB
      have hsource := (source_at_v2 (f := gameF)
        (r := e + 4) (p := z)).1 (by
          simpa [Nat.add_assoc] using hB)
      rcases hsource with hK | hzuEq
      · exact hKz hK
      · rw [hseat] at hzuEq
        omega
    have hwle : gameF (e + 6) (e + 4) <= z :=
      mex_le_positive_hole hzpos hzMissingW hmexW
    have hwlt : gameF (e + 6) (e + 4) < z := by
      have hwne : gameF (e + 6) (e + 4) ≠ z :=
        fun hw => hdistinct.2.2.2.2.2 (hw.trans hyz.symm)
      omega
    have hwpos : 0 < gameF (e + 6) (e + 4) := hmexW.1
    have hKw : Not (TopTailCore gameF (e + 4)
        (gameF (e + 6) (e + 4))) := by
      intro hK
      apply hmexW.2.1
      have hB := (source_at_v2 (f := gameF) (r := e + 4)
        (p := gameF (e + 6) (e + 4))).2 (Or.inl hK)
      simpa [Nat.add_assoc] using hB
    have hholes : forall v, 0 < v -> v < z ->
        (Not (TopTailCore gameF (e + 4) v) <->
          v = gameF (e + 6) (e + 4)) := by
      intro v hvpos hvz
      constructor
      · intro hKv
        have hB : B gameF (e + 6) (e + 5) v := by
          rw [hyz] at hmexY
          exact hmexY.2.2 v hvpos hvz
        have hsource := (source_at_v1 (f := gameF)
          (r := e + 4) (p := v)).1 (by
            simpa [Nat.add_assoc] using hB)
        rcases hsource with hK | hd | hw
        · exact False.elim (hKv hK)
        · have : gameF (e + 5) (e + 5) = v := hd
          omega
        · exact hw.symm
      · intro hvw hK
        subst v
        exact hKw hK
    have hmexCoreW :
        IsMex (TopTailCore gameF (e + 4))
          (gameF (e + 6) (e + 4)) := by
      refine ⟨hwpos, hKw, ?_⟩
      intro v hvpos hvw
      have hB := hmexW.2.2 v hvpos hvw
      have hsource := (source_at_v2 (f := gameF)
        (r := e + 4) (p := v)).1 (by
          simpa [Nat.add_assoc] using hB)
      rcases hsource with hK | hvu
      · exact hK
      · rw [hseat] at hvu
        omega
    have hmexCoreSecond :
        IsMex
          (fun v => TopTailCore gameF (e + 4) v \/
            v = gameF (e + 6) (e + 4)) z := by
      refine ⟨hzpos, ?_, ?_⟩
      · intro hzSource
        rcases hzSource with hK | hzw
        · exact hKz hK
        · omega
      · intro v hvpos hvz
        by_cases hvw : v = gameF (e + 6) (e + 4)
        · exact Or.inr hvw
        · left
          exact Classical.byContradiction (fun hKv =>
            hvw ((hholes v hvpos hvz).1 hKv))
    exact ⟨hxlt, hwlt, hyz, hKz, hwpos, hKw, hholes,
      hmexCoreW, hmexCoreSecond⟩

/-- R21/R27-facing integration theorem.  In the hypothetical unserved
branch, the lower loss `q` has its two distinct strict parked hosts and its
RM2 opening split, while the unpaid blocker simultaneously satisfies the
exact terminal queue trace above. -/
theorem gameF_l3_unserved_residual_has_relay_and_terminal_queue_trace
    {e u z : Nat}
    (hmexEntry :
      IsMex (B gameF (e + 6) e) (gameF (e + 6) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B gameF (e + 6) e y) ->
        Not (B gameF (e + 6) e z) -> y = z)
    (hmexOne :
      IsMex (B gameF (e + 6) (e + 1))
        (gameF (e + 6) (e + 1)))
    (hmexTwo :
      IsMex (B gameF (e + 6) (e + 2))
        (gameF (e + 6) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B gameF (e + 6) e x ->
          Not (B gameF (e + 6) (e + 1) x) ->
        B gameF (e + 6) e y ->
          Not (B gameF (e + 6) (e + 1) y) ->
        B gameF (e + 6) e z ->
          Not (B gameF (e + 6) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B gameF (e + 6) (e + 1) z))
    (hzMissingTwo : Not (B gameF (e + 6) (e + 2) z))
    (huSeat : gameF (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < gameF (e + 4) (e + 4))
    (hzMissingBackstop : Not (B gameF (e + 6) (e + 3) z))
    (hRM2 : TwoStepDiagonalRecordLaw gameRecurrenceModel) :
    let q := gameF (e + 6) (e + 2)
    ParkedOnly gameF (e + 6) e q /\
    ParkedOnly gameF (e + 6) (e + 1) q /\
    (exists a0 a1,
      StrictParkedHost gameRecurrenceModel (e + 6) e q a0 /\
      StrictParkedHost gameRecurrenceModel (e + 6) (e + 1) q a1 /\
      a0 ≠ a1) /\
    (gameF (e + 3) (e + 3) = q \/
      exists r, e + 1 < r /\ r < q /\ gameF q r = q) /\
    L3TerminalQueueTrace e z := by
  dsimp only
  have hNotServed : gameF (e + 6) (e + 2) ≠ z := by
    intro hserved
    apply hzMissingBackstop
    exact Or.inr ⟨e + 2, by omega, hserved⟩
  have hanatomy :=
    l3_unserved_lower_loss_anatomy_and_opening_split_of_rm2
      gameRecurrenceModel hmexEntry honeEntry hmexOne hmexTwo
      hEntryLossCapTwo hz hzu hzMissingOne hzMissingTwo hNotServed
      huSeat hPrevDiagonalAbove hRM2
  dsimp only at hanatomy
  rcases hanatomy with
    ⟨_hqpos, hqz, hpark0, hpark1, hhosts,
      _hparkZ, _hzHost, hopen⟩
  have hres :=
    rescue_unserved_missing_backstop_is_lower_loss_plus_late_blocker
      (M := gameRecurrenceModel) (e := e) (L := 3) (by omega)
      hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
      hz hzu hzMissingOne hzMissingTwo hNotServed
      huSeat hPrevDiagonalAbove hzMissingBackstop hRM2
  rcases hres with
    ⟨_hqpos', _hqz', _hqBefore, _hqLost, _hqBackstop,
      r, hrLower, hrz, hstart⟩
  have htz : e + 6 <= z :=
    missing_l3_backstop_late_rowstart_is_at_least_current_row
      gameRecurrenceModel huSeat hzu hrLower hrz hstart
        hzMissingBackstop
  have hterminal :=
    rm2_missing_l3_backstop_rowstart_has_terminal_host
      gameRecurrenceModel hPrevDiagonalAbove hzu hrz hstart hRM2
        hzMissingBackstop
  rcases hterminal with ⟨b, hb, hhost⟩
  have htop :
      gameF (e + 6) (e + 3) = z \/
      gameF (e + 6) (e + 4) = z \/
      gameF (e + 6) (e + 5) = z := by
    rcases hb with h3 | h4 | h5
    · left
      simpa [h3] using hhost
    · right
      left
      simpa [h4] using hhost
    · right
      right
      simpa [h5] using hhost
  have htrace := gameF_l3_terminal_queue_exact_trichotomy
    huSeat htz hzu hrz hstart hqz hzMissingBackstop htop
  exact ⟨hpark0, hpark1, hhosts, hopen, htrace⟩

end ChompLean
