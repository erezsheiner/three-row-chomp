import G1LCarryDischarge
import R56TopTwoHoles
import R124FloorRankQuotient
import PenultimateFreezeGlobalKill

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# X-TAU: the full A1 window law (`X-TAU-BLOCKER-SHELL-THRESHOLD-2026-07-23.md`)

Formalization of the paper proofs of §§4–6 and §8.1/§8.3 of the X-TAU report.

## Vocabulary (statement-fidelity to the report's §3)

* A cell `(q,c)`, `c ≤ q`, is **live** iff `q ≤ gameF q c`.
* `LiveLe b c V` says: SOME live cell of column `c` with row ≤ cutoff `b` has
  value ≤ `V`.  This is exactly `CM_b(c) ≤ V` whenever column `c` is nonempty
  under the cutoff, so `liveLe_mono_left` IS the report's monotonicity
  `CM_b(c) ≤ CM_b(c+1)` in `≤ V`-instance form (and is vacuously stronger when
  the column is empty).  No `min` is extracted; every consumer below only ever
  uses the `≤ V` form.
* `A1Gate b e V` (`= ¬ LiveLe b (e+1) V`) is the report's anchor gate
  `CM_b(e+1) > V`.

## What is proved UNCONDITIONALLY here

* `gameF_adjacent_live_shadow` — §4 `AdjacentLiveShadow` (direct MEX-coverage
  proof, including the boundary case `p = a`; the banked
  `gameF_adjacent_high_host_rehost_or_freeze` is NOT used).
* `liveLe_mono_left` / `liveLe_mono` — §5.1 cutoff-dependent monotonicity.
* `a1Gate_no_break` — §5.2 no-break.
* `a1Gate_window_full` — §5.3 no-hole: under the gate and `b <= V`,
  ALL of row `b` on `(e,b]` is live.
* `a1Gate_anchor_mass` — §5.4 per-anchor exact mass: a gated anchor's window
  live-cell count is exactly `b - e`.
* `gated_range_anchor_is_future_preview` — §6.1: every gated range anchor
  sits strictly before the birth of its diagonal owner (`e < x < t`).
* `gameF_penultimate_gate_auto` — §6.3 (strengthened): ANY penultimate host
  `(x, x-1)` passes its own gate, via `gameF_v1_lt_diagonal`.
* `a1Gate_iff_lowerOwnerCoveredBy` — §8.1: for a blocker's freeze cell, the
  freeze-anchor gate is EQUIVALENT to R130's `LowerOwnerCoveredBy V c_V`.

## What is CONDITIONAL (open inputs as explicit hypotheses, never sorries)

* `GatedFutureDiagonalPin` — §6.2 target, DECLARED as a `Prop`;
  `gated_range_anchor_unique_of_pin` consumes it.  OPEN.
* `LowerOwnerCoveredBy V c_V` (= freeze-order/owner-cutoff debt, §8.2) is a
  HYPOTHESIS of `a1Gate_of_lowerOwnerCoveredBy` and
  `blocker_freeze_anchor_threshold`.  OPEN; nothing here closes it.

## What this file does NOT say

* It does not define Λ₃ globally and does not prove the boxed global sum of
  §5.4; it proves the per-anchor contribution law the sum is assembled from.
* It does not prove `BlockerShellThreshold`, `FreezeColumnMonotone`,
  UnitDip/DD1, or any all-`N` classification of the 292 exceptions.
* §8.2's "diagonal half automatic via Theorem A" is not formalized here
  (follow-up: package `interval_blocking_of_encoding`).  CORE: OPEN.
-/

/-- There is a LIVE cell in column `c` with row at most `b` and value at most
`V`.  (`CM_b(c) ≤ V` in the report's notation, without extracting the min.) -/
def LiveLe (b c V : Nat) : Prop :=
  ∃ q, c ≤ q ∧ q ≤ b ∧ q ≤ gameF q c ∧ gameF q c ≤ V

/-- The A1 anchor gate at `(b,e)` for value `V`: no live cell of the adjacent
column `e+1` under cutoff `b` has value ≤ `V` (`CM_b(e+1) > V`). -/
def A1Gate (b e V : Nat) : Prop :=
  ¬ LiveLe b (e + 1) V

/-- **§4 `AdjacentLiveShadow`.**  If column `e+1` hosts a live value `p` at row
`a` (`a ≤ p`), then column `e` has a live cell at some row `r ∈ (e, a]` with
value ≤ `p`.  Direct proof from the Brouwer recurrence: the carry case
descends to its row-start; the MEX case forces `p` into the sources of
`(a,e)`, where the row channel is killed by fixed-row injectivity, the
diagonal channel by diagonal/general no-attack, and the column channel IS the
witness.  The boundary case `p = a` is included. -/
theorem gameF_adjacent_live_shadow {e a p : Nat}
    (hea : e < a) (hap : a ≤ p) (hhost : gameF a (e + 1) = p) :
    ∃ r, e < r ∧ r ≤ a ∧ r ≤ gameF r e ∧ gameF r e ≤ p := by
  by_cases hLp : gameF a e ≤ p
  · by_cases haL : a ≤ gameF a e
    · -- the adjacent-left cell is itself live
      exact ⟨a, hea, Nat.le_refl a, haL, hLp⟩
    · -- carry: descend to the row-start of the carried value
      have hLa : gameF a e < a := Nat.lt_of_not_ge haL
      have heL : e < gameF a e := encoded_gt game_encodes (Nat.le_of_lt hea)
      have hdesc : gameF (gameF a e) e = gameF a e :=
        gameF_carry_descends_to_rowStart hea rfl hLa
      refine ⟨gameF a e, heL, Nat.le_of_lt hLa, ?_, ?_⟩
      · exact Nat.le_of_eq hdesc.symm
      · rw [hdesc]; exact hLp
  · -- p below the left value: the left cell is a strict-live MEX cell
    have hpL : p < gameF a e := Nat.lt_of_not_ge hLp
    have hnc : ¬ (e < a ∧ gameF (a - 1) e < a) := by
      rintro ⟨_, hprev⟩
      have hcarry := gameF_brouwerRecurrence.1 hea hprev
      omega
    have hmex : IsMex (B gameF a e) (gameF a e) :=
      gameF_brouwerRecurrence.2 (Nat.le_of_lt hea) hnc
    have hppos : 0 < p := by omega
    rcases hmex.2.2 p hppos hpL with hR | hC
    · rcases hR with ⟨t, hta, hft⟩
      by_cases hte : t ≤ e
      · -- diagonal source: killed by diagonal/general no-attack vs (a, e+1)
        rw [Nat.min_eq_left hte] at hft
        exact (encoding_diagonal_general_no_attack game_encodes
          (show t < e + 1 by omega) (show e + 1 ≤ a by omega)
          (hft.trans hhost.symm)).elim
      · -- column source: this is the witness
        have het : e < t := Nat.lt_of_not_ge hte
        rw [Nat.min_eq_right (Nat.le_of_lt het)] at hft
        refine ⟨t, het, Nat.le_of_lt hta, ?_, ?_⟩
        · rw [hft]; omega
        · exact Nat.le_of_eq hft
    · -- row source: killed by fixed-row injectivity vs column e+1
      rcases hC with ⟨bcol, hbe, hfb⟩
      have := encoding_fixed_q_injective game_encodes
        (show bcol ≤ a by omega) (show e + 1 ≤ a by omega)
        (hfb.trans hhost.symm)
      omega

/-- **§5.1 monotonicity, one step.**  Any live value achieved in column `c+1`
under cutoff `b` dominates a live value of column `c` under the same cutoff:
`CM_b(c) ≤ CM_b(c+1)` for every cutoff `b`. -/
theorem liveLe_mono_left {b c V : Nat} (h : LiveLe b (c + 1) V) :
    LiveLe b c V := by
  rcases h with ⟨q, hcq, hqb, hlive, hval⟩
  rcases gameF_adjacent_live_shadow (show c < q by omega) hlive rfl with
    ⟨r, hcr, hrq, hrlive, hrval⟩
  exact ⟨r, Nat.le_of_lt hcr, Nat.le_trans hrq hqb, hrlive,
    Nat.le_trans hrval hval⟩

/-- §5.1 monotonicity, iterated to any column pair `c' ≤ c`. -/
theorem liveLe_mono {b V : Nat} :
    ∀ {c c' : Nat}, c' ≤ c → LiveLe b c V → LiveLe b c' V := by
  intro c
  induction c with
  | zero =>
      intro c' hc h
      have hc0 : c' = 0 := Nat.le_zero.mp hc
      rw [hc0]; exact h
  | succ n ih =>
      intro c' hc h
      by_cases hceq : c' = n + 1
      · rw [hceq]; exact h
      · exact ih (by omega) (liveLe_mono_left h)

/-- **§5.2 no-break.**  A gate that holds at column `e+1` propagates to every
column strictly right of `e`: no live cell of value ≤ `V` appears anywhere in
`(e, ∞)` under cutoff `b`. -/
theorem a1Gate_no_break {b e V : Nat} (hgate : A1Gate b e V)
    {c : Nat} (hec : e < c) : ¬ LiveLe b c V :=
  fun h => hgate (liveLe_mono hec h)

/-- **§5.3 no-hole.**  Under the gate (and `b ≤ V`, the anchor-row liveness
bound), every row-`b` cell on `(e, b]` is live: a carry `w = gameF b c < b`
would descend to a live cell `(w, c)` of value `w ≤ V`, breaking the gate. -/
theorem a1Gate_window_full {b e V : Nat}
    (hgate : A1Gate b e V) (hbV : b ≤ V) :
    ∀ c, e < c → c ≤ b → b ≤ gameF b c := by
  intro c hec hcb
  rcases Nat.lt_or_ge (gameF b c) b with hwb | hge
  · have hcw : c < gameF b c := encoded_gt game_encodes hcb
    have hcb' : c < b := by omega
    have hdesc : gameF (gameF b c) c = gameF b c :=
      gameF_carry_descends_to_rowStart hcb' rfl hwb
    refine (a1Gate_no_break hgate hec
      ⟨gameF b c, Nat.le_of_lt hcw, by omega, Nat.le_of_eq hdesc.symm, ?_⟩).elim
    rw [hdesc]; omega
  · exact hge

private theorem filter_all_length (p : Nat → Bool) :
    ∀ (n s : Nat), (∀ c, s ≤ c → c < s + n → p c = true) →
      ((List.range' s n).filter p).length = n := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ m ih =>
      intro s hall
      have hs : p s = true := hall s (Nat.le_refl s) (by omega)
      have hrest : ((List.range' (s + 1) m).filter p).length = m :=
        ih (s + 1) (fun c hc1 hc2 => hall c (by omega) (by omega))
      rw [List.range'_succ, List.filter_cons]
      simp [hs, hrest]

/-- **§5.4 per-anchor exact mass.**  A gated anchor's window is the FULL run
`(e, b]`: its live-cell count is exactly `b - e`.  (The report's boxed global
formula `Λ₃(V) = Σ (b-e)` is the sum of this law over the gated anchors of
`V`; the sum itself is bookkeeping over this per-anchor content.  The anchor
equation `gameF b e = V` is carried for statement-fidelity; the count needs
only `e < b ≤ V` and the gate.) -/
theorem a1Gate_anchor_mass {b e V : Nat}
    (_hanchor : gameF b e = V) (heb : e < b) (hbV : b ≤ V)
    (hgate : A1Gate b e V) :
    ((List.range' (e + 1) (b - e)).filter
      (fun c => decide (b ≤ gameF b c))).length = b - e := by
  apply filter_all_length
  intro c hc1 hc2
  exact decide_eq_true
    (a1Gate_window_full hgate hbV c (by omega) (by omega))

/-- **§6.1.**  A gated range anchor is a FUTURE-diagonal preview: if the
anchor value is the diagonal value of `t` and the gated anchor sits at
`(x,e)`, `e < x ≤ gameF t t`, then `x < t` — the anchor precedes its
diagonal owner's birth row.  (`t ≤ e` dies inside the anchor's own MEX
sources; `e < t ≤ x` puts the live diagonal witness `(t,t)` inside the
no-break region.) -/
theorem gated_range_anchor_is_future_preview {x e t : Nat}
    (hanchor : gameF x e = gameF t t) (hex : e < x)
    (hxV : x ≤ gameF t t) (hgate : A1Gate x e (gameF t t)) :
    x < t := by
  rcases Nat.lt_or_ge x t with hxt | htx'
  · exact hxt
  · by_cases hte : t ≤ e
    · -- the anchor cell is a strict-live MEX cell, yet gameF t t sits in its
      -- diagonal sources
      have hlive : x ≤ gameF x e := by rw [hanchor]; exact hxV
      have hnc : ¬ (e < x ∧ gameF (x - 1) e < x) := by
        rintro ⟨_, hprev⟩
        have hcarry := gameF_brouwerRecurrence.1 hex hprev
        omega
      have hmex : IsMex (B gameF x e) (gameF x e) :=
        gameF_brouwerRecurrence.2 (Nat.le_of_lt hex) hnc
      exact (hmex.2.1 (Or.inl ⟨t, by omega,
        by rw [Nat.min_eq_left hte]; exact hanchor.symm⟩)).elim
    · -- the live diagonal cell (t,t) violates no-break at column t
      have het : e < t := Nat.lt_of_not_ge hte
      exact (a1Gate_no_break hgate het
        ⟨t, Nat.le_refl t, htx',
          Nat.le_of_lt (encoded_gt game_encodes (Nat.le_refl t)),
          Nat.le_refl _⟩).elim

/-- **§6.3 (strengthened).**  EVERY penultimate host `(x, x-1)` passes its own
gate automatically: the only adjacent column under cutoff `x` is the diagonal
`(x,x)`, and `gameF x (x-1) < gameF x x` (`gameF_v1_lt_diagonal`).  In
particular a future-diagonal penultimate echo `f(x,x-1) = d(t)`, `t > x`, is
always a gated anchor of contribution exactly 1. -/
theorem gameF_penultimate_gate_auto {x : Nat} (hx : 0 < x) :
    A1Gate x (x - 1) (gameF x (x - 1)) := by
  rintro ⟨q, hcq, hqb, hqlive, hqval⟩
  have hcol : x - 1 + 1 = x := by omega
  rw [hcol] at hcq hqlive hqval
  have hqx : q = x := by omega
  rw [hqx] at hqval
  have hlt := gameF_v1_lt_diagonal hx
  omega

/-- **§6.2 target (OPEN; declared, not proved).**  `GatedFutureDiagonalPin`:
a gated future-diagonal anchor is always the penultimate echo of the
IMMEDIATELY next diagonal: `t = x+1` and `e = x-1`.  Syntactically weaker
than the full R184 `FutureDiagonalPin` because the A1 gate is assumed. -/
def GatedFutureDiagonalPin : Prop :=
  ∀ x e t : Nat, e < x → x < t → x ≤ gameF t t →
    gameF x e = gameF t t → A1Gate x e (gameF t t) →
    t = x + 1 ∧ e = x - 1

/-- **§6.2 consumer.**  Under the pin, a gated range anchor of `d(t)` is
uniquely `(t-1, t-2)` and its window mass is exactly 1 — hence
`Λ₃(d(t)) ≤ 1` anchor-by-anchor. -/
theorem gated_range_anchor_unique_of_pin
    (hpin : GatedFutureDiagonalPin)
    {x e t : Nat}
    (hanchor : gameF x e = gameF t t) (hex : e < x)
    (hxV : x ≤ gameF t t) (hgate : A1Gate x e (gameF t t)) :
    x = t - 1 ∧ e = t - 2 ∧ x - e = 1 := by
  have hxt : x < t :=
    gated_range_anchor_is_future_preview hanchor hex hxV hgate
  rcases hpin x e t hex hxt hxV hanchor hgate with ⟨ht, he⟩
  omega

/-- **§8.1, gate ⟸ owner cutoff.**  For a blocker's freeze cell
`gameF V c_V = V`, R130's `LowerOwnerCoveredBy V c_V` implies the
freeze-anchor gate.  A live intruder of value `V` is killed by row injection
against the freeze cell (directly at row `V`, through `rowStartPropagation`
below it); an intruder of value `k < V` is killed against its own covered
owner (diagonal owner via no-attack, blocker owner via injection /
propagation).  `LowerOwnerCoveredBy` is the OPEN freeze-order debt — it is
consumed here as a hypothesis, not closed. -/
theorem a1Gate_of_lowerOwnerCoveredBy {V cV : Nat}
    (hfreeze : gameF V cV = V) (hcVV : cV < V)
    (hcov : LowerOwnerCoveredBy V cV) : A1Gate V cV V := by
  rintro ⟨q, hcq, hqV, hqlive, hqval⟩
  by_cases hkV : gameF q (cV + 1) = V
  · by_cases hqeqV : q = V
    · rw [hqeqV] at hkV
      have := encoding_fixed_q_injective game_encodes
        (Nat.le_of_lt hcVV) (show cV + 1 ≤ V by omega)
        (hfreeze.trans hkV.symm)
      omega
    · have hqltV : q < V := by omega
      rcases rowStartPropagation gameRecurrenceModel hfreeze hcVV
          (show cV < q by omega) hqltV with ⟨bb, hbbcV, hfbb⟩
      have := encoding_fixed_q_injective game_encodes
        (show bb ≤ q by omega) hcq (hfbb.trans hkV.symm)
      omega
  · have hkltV : gameF q (cV + 1) < V := by omega
    have hkpos : 0 < gameF q (cV + 1) := by
      have := encoded_gt game_encodes hcq
      omega
    rcases hcov _ hkpos hkltV with ⟨a, hacV, hdiagk⟩ | ⟨r, hrcV, hrk, hstartk⟩
    · exact encoding_diagonal_general_no_attack game_encodes
        (show a < cV + 1 by omega) hcq hdiagk
    · by_cases hqk : q = gameF q (cV + 1)
      · have hstartk' : gameF q r = q := by rw [← hqk] at hstartk; exact hstartk
        have := encoding_fixed_q_injective game_encodes
          (show r ≤ q by omega) hcq (hstartk'.trans hqk)
        omega
      · have hqltk : q < gameF q (cV + 1) := by omega
        rcases rowStartPropagation gameRecurrenceModel hstartk hrk
            (show r < q by omega) hqltk with ⟨bb, hbbr, hfbb⟩
        have := encoding_fixed_q_injective game_encodes
          (show bb ≤ q by omega) hcq hfbb
        omega

/-- **§8.1, gate ⟹ owner cutoff.**  The gate (with no-break) pushes every
lower owner weakly left of `c_V`: owners exist by `opening_cover`, and an
owner strictly right of `c_V` is itself a live cell of value < `V` inside the
no-break region.  (This direction does not even need the freeze cell.) -/
theorem lowerOwnerCoveredBy_of_a1Gate {V cV : Nat}
    (hgate : A1Gate V cV V) : LowerOwnerCoveredBy V cV := by
  intro k hkpos hkV
  rcases gameRecurrenceModel.opening_cover hkpos with
    ⟨a, hak, hdiagk⟩ | ⟨r, hrk, hstartk⟩
  · left
    have hdiagk' : gameF a a = k := hdiagk
    refine ⟨a, ?_, hdiagk'⟩
    rcases Nat.lt_or_ge cV a with hacV | hacV
    · exact (a1Gate_no_break hgate hacV
        ⟨a, Nat.le_refl a, by omega,
          Nat.le_of_lt (encoded_gt game_encodes (Nat.le_refl a)),
          by omega⟩).elim
    · exact hacV
  · right
    have hstartk' : gameF k r = k := hstartk
    refine ⟨r, ?_, hrk, hstartk'⟩
    rcases Nat.lt_or_ge cV r with hrcV | hrcV
    · exact (a1Gate_no_break hgate hrcV
        ⟨k, Nat.le_of_lt hrk, by omega, Nat.le_of_eq hstartk'.symm,
          by omega⟩).elim
    · exact hrcV

/-- **§8.1 combined.**  Freeze-anchor gate ⟺ `LowerOwnerCoveredBy V c_V`,
paper-proof equivalence, for every blocker freeze cell. -/
theorem a1Gate_iff_lowerOwnerCoveredBy {V cV : Nat}
    (hfreeze : gameF V cV = V) (hcVV : cV < V) :
    A1Gate V cV V ↔ LowerOwnerCoveredBy V cV :=
  ⟨lowerOwnerCoveredBy_of_a1Gate, a1Gate_of_lowerOwnerCoveredBy hfreeze hcVV⟩

/-- **§8.3 (CONDITIONAL on the open owner-cutoff/freeze-order debt).**  If a
blocker's freeze-anchor gate is granted, the threshold follows: the freeze
column obeys `c_V ≤ V-2` (`gameF_no_penultimate_freeze`), so the freeze
anchor alone contributes a full window of mass `V - c_V ≥ 2`.  This is the
report's clean conditional proof of the blocker side; it is NOT an
unconditional threshold. -/
theorem blocker_freeze_anchor_threshold {V cV : Nat}
    (hV : 5 ≤ V) (hfreeze : gameF V cV = V) (hcVV : cV < V)
    (hgate : A1Gate V cV V) :
    cV ≤ V - 2 ∧ 2 ≤ V - cV ∧
      ((List.range' (cV + 1) (V - cV)).filter
        (fun c => decide (V ≤ gameF V c))).length = V - cV := by
  have hnp : gameF V (V - 1) ≠ V := gameF_no_penultimate_freeze hV
  have hcV2 : cV ≤ V - 2 := by
    rcases Nat.lt_or_ge cV (V - 1) with h | h
    · omega
    · have hcVeq : cV = V - 1 := by omega
      rw [hcVeq] at hfreeze
      exact absurd hfreeze hnp
  exact ⟨hcV2, by omega,
    a1Gate_anchor_mass hfreeze hcVV (Nat.le_refl V) hgate⟩

end ChompLean

#print axioms ChompLean.gameF_adjacent_live_shadow
#print axioms ChompLean.liveLe_mono_left
#print axioms ChompLean.liveLe_mono
#print axioms ChompLean.a1Gate_no_break
#print axioms ChompLean.a1Gate_window_full
#print axioms ChompLean.a1Gate_anchor_mass
#print axioms ChompLean.gated_range_anchor_is_future_preview
#print axioms ChompLean.gameF_penultimate_gate_auto
#print axioms ChompLean.gated_range_anchor_unique_of_pin
#print axioms ChompLean.a1Gate_of_lowerOwnerCoveredBy
#print axioms ChompLean.lowerOwnerCoveredBy_of_a1Gate
#print axioms ChompLean.a1Gate_iff_lowerOwnerCoveredBy
#print axioms ChompLean.blocker_freeze_anchor_threshold
