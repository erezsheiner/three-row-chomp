import XOBUQHoleSqrtAdapter
import R198CausalMiddleCohortPullback
import R66CeilingBase

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace ChompLean
namespace OBUQ

/-!
# Reconstruction of the canonical game inside the ordered blocker-union quotient

Work-ID: `X-GAMEF-OBUQ-RECONSTRUCTION-001`
Run-ID: `XGOR-20260813-0753-ROOT`

The cut at physical row `q` retains exactly the old source values at least
`q`, normalized by subtracting `q`.  The row-zero positive-MEX convention is
represented by the one-time forcing list `[0]`; every later row is autonomous.
-/

/-- Retain the entries at least `q`, in their original order, and normalize
them to offsets from `q`. -/
def normalizeAt (q : Nat) (xs : List Nat) : List Nat :=
  (xs.filter (fun p => decide (q <= p))).map (fun p => p - q)

theorem normalizeAt_append (q : Nat) (xs ys : List Nat) :
    normalizeAt q (xs ++ ys) = normalizeAt q xs ++ normalizeAt q ys := by
  simp [normalizeAt, List.filter_append, List.map_append]

theorem normalizeAt_cons (q p : Nat) (xs : List Nat) :
    normalizeAt q (p :: xs) =
      if q <= p then (p - q) :: normalizeAt q xs else normalizeAt q xs := by
  by_cases hqp : q <= p
  · simp [normalizeAt, hqp]
  · simp [normalizeAt, hqp]

theorem mem_normalizeAt_iff {q k : Nat} {xs : List Nat} :
    k ∈ normalizeAt q xs <-> q + k ∈ xs := by
  constructor
  · intro hk
    rcases List.mem_map.mp hk with ⟨p, hp, hpk⟩
    have hp' := (List.mem_filter.mp hp)
    have hqp : q <= p := of_decide_eq_true hp'.2
    have heq : p = q + k := by omega
    simpa [heq] using hp'.1
  · intro hk
    apply List.mem_map.mpr
    refine ⟨q + k, ?_, by omega⟩
    apply List.mem_filter.mpr
    exact ⟨hk, by simp⟩

theorem normalizeAt_succ (q : Nat) (xs : List Nat) :
    normalizeAt (q + 1) xs = shiftQueue (normalizeAt q xs) := by
  induction xs with
  | nil => simp [normalizeAt, shiftQueue]
  | cons p xs ih =>
      rw [normalizeAt_cons, normalizeAt_cons]
      by_cases hpq : p < q
      · have hnq : ¬ q <= p := by omega
        have hns : ¬ q + 1 <= p := by omega
        simp [hnq, hns, ih]
      · by_cases heq : p = q
        · subst p
          simp [ih, shiftQueue]
        · have hq : q < p := by omega
          have hqs : q + 1 <= p := by omega
          have hqp : q <= p := by omega
          obtain ⟨u, rfl⟩ : ∃ u, p = q + 1 + u := by
            exact ⟨p - (q + 1), by omega⟩
          rw [if_pos hqs, if_pos hqp, ih]
          have hsub : q + 1 + u - q = u + 1 := by omega
          have hsub' : q + 1 + u - (q + 1) = u := by omega
          rw [hsub]
          rw [hsub']
          rfl

/-- The chronological `R`-source list at cut `q` and physical column `r`. -/
noncomputable def sourceValues (q r : Nat) : List Nat :=
  (List.range q).map (fun a => gameF a (min a r))

noncomputable def sourceQueue (q r : Nat) : List Nat :=
  normalizeAt q (sourceValues q r)

/-- Current-row values strictly to the left of `r`, normalized at `q`. -/
noncomputable def rowQueue (q r : Nat) : List Nat :=
  normalizeAt q ((List.range r).map (fun b => gameF q b))

theorem mem_sourceValues_iff {q r p : Nat} :
    p ∈ sourceValues q r <-> R gameF q r p := by
  simp [sourceValues, R]

theorem mem_sourceQueue_iff {q r k : Nat} :
    k ∈ sourceQueue q r <-> R gameF q r (q + k) := by
  rw [sourceQueue, mem_normalizeAt_iff, mem_sourceValues_iff]

theorem mem_rowQueue_iff {q r k : Nat} :
    k ∈ rowQueue q r <-> C gameF q r (q + k) := by
  rw [rowQueue, mem_normalizeAt_iff]
  simp [C]

theorem mem_sourceRowQueue_iff {q r k : Nat} :
    k ∈ sourceQueue q r ++ rowQueue q r <->
      B gameF q r (q + k) := by
  simp only [List.mem_append, mem_sourceQueue_iff, mem_rowQueue_iff, B]

/-- Columns whose current row value is still visible at the cut.  Equality
is included: normalized service zero participates in the row prefix and is
then removed from the survivor word. -/
noncomputable def liveCols (q : Nat) : List Nat := by
  classical
  exact (List.range q).filter (fun e => decide (q <= gameF q e))

noncomputable def liveColsPrefix (q r : Nat) : List Nat := by
  classical
  exact (List.range r).filter (fun e => decide (q <= gameF q e))

noncomputable def canonicalQState (q : Nat) : QState :=
  ⟨(liveCols q).map (fun e => sourceQueue q e), sourceQueue q q⟩

def canonicalForcing (q : Nat) : List Nat :=
  if q = 0 then [0] else []

theorem liveCols_eq_prefix (q : Nat) : liveCols q = liveColsPrefix q q := by
  rfl

theorem liveColsPrefix_succ (q r : Nat) :
    liveColsPrefix q (r + 1) =
      liveColsPrefix q r ++ if q <= gameF q r then [r] else [] := by
  classical
  rw [liveColsPrefix, List.range_succ, List.filter_append]
  change (List.range r).filter (fun e => decide (q <= gameF q e)) ++ _ = _
  change liveColsPrefix q r ++ _ = liveColsPrefix q r ++ _
  by_cases h : q <= gameF q r <;> simp [h]

theorem rowQueue_succ (q r : Nat) :
    rowQueue q (r + 1) =
      rowQueue q r ++
        if q <= gameF q r then [gameF q r - q] else [] := by
  classical
  rw [rowQueue, List.range_succ, List.map_append, normalizeAt_append]
  change normalizeAt q ((List.range r).map (fun b => gameF q b)) ++ _ = _
  change rowQueue q r ++ _ = rowQueue q r ++ _
  by_cases h : q <= gameF q r <;> simp [normalizeAt, h]

theorem gameF_visible_isMex {q r : Nat} (hrq : r <= q)
    (hvisible : q <= gameF q r) : IsMex (B gameF q r) (gameF q r) := by
  have hnot : ¬ (r < q ∧ gameF (q - 1) r < q) := by
    rintro ⟨hrlt, hprev⟩
    have heq := gameF_brouwerRecurrence.1 hrlt hprev
    omega
  exact gameF_brouwerRecurrence.2 hrq hnot

theorem gameF_normalized_cell_mex {q r : Nat} (hq : 0 < q)
    (hrq : r <= q) (hvisible : q <= gameF q r) :
    queueMex (sourceQueue q r ++ rowQueue q r) = gameF q r - q := by
  have hmex := gameF_visible_isMex hrq hvisible
  apply queueMex_eq_of_spec
  · intro hmem
    have hb := mem_sourceRowQueue_iff.mp hmem
    have heq : q + (gameF q r - q) = gameF q r := by omega
    exact hmex.2.1 (by simpa [heq] using hb)
  · intro k hk
    apply mem_sourceRowQueue_iff.mpr
    apply hmex.2.2
    · omega
    · omega

theorem scanCanonicalPrefix_outputs {q r : Nat} (hq : 0 < q)
    (hrq : r <= q) :
    (scanQueues [] []
      ((liveColsPrefix q r).map (fun e => sourceQueue q e))).outputs =
        rowQueue q r := by
  induction r with
  | zero => simp [liveColsPrefix, rowQueue, normalizeAt, scanQueues]
  | succ r ih =>
      have hrq' : r <= q := by omega
      rw [liveColsPrefix_succ, rowQueue_succ]
      by_cases hvisible : q <= gameF q r
      · simp only [hvisible, if_pos, List.map_append, List.map_singleton]
        rw [scanQueues_outputs_append]
        rw [ih hrq']
        have hmex := gameF_normalized_cell_mex hq hrq' hvisible
        simpa [List.append_assoc] using hmex
      · simp only [hvisible]
        simpa [hvisible] using ih hrq'

private theorem sourceQueue_old_update_pre {q e : Nat} (heq : e <= q)
    (hlive : q <= gameF q e) :
    sourceQueue (q + 1) e =
      updateQueue (sourceQueue q e) (gameF q e - q) := by
  have hs :
      sourceValues (q + 1) e = sourceValues q e ++ [gameF q e] := by
    simp [sourceValues, List.range_succ, List.map_append,
      Nat.min_eq_right heq]
  unfold sourceQueue
  rw [hs, normalizeAt_append, normalizeAt_succ, updateQueue]
  by_cases hstrict : q + 1 <= gameF q e
  · have hy : gameF q e - q ≠ 0 := by omega
    have hsub : gameF q e - (q + 1) = gameF q e - q - 1 := by omega
    simp [normalizeAt, hstrict, hy, hsub]
  · have heqv : gameF q e = q := by omega
    simp [normalizeAt, heqv]

theorem scanQueues_survivors_append (U R q : List Nat)
    (pre : List (List Nat)) :
    (scanQueues U R (pre ++ [q])).survivors =
      (scanQueues U R pre).survivors ++
        (let y := queueMex
          (U ++ (q ++ (R ++ (scanQueues U R pre).outputs)))
         if y = 0 then [] else [updateQueue q y]) := by
  induction pre generalizing R with
  | nil => simp [scanQueues]
  | cons p pre ih =>
      simp only [List.cons_append, scanQueues]
      let y := queueMex (U ++ (p ++ R))
      change
        (if y = 0 then
          (scanQueues U (R ++ [y]) (pre ++ [q])).survivors
        else updateQueue p y ::
          (scanQueues U (R ++ [y]) (pre ++ [q])).survivors) = _
      rw [ih (R := R ++ [y])]
      by_cases hy : y = 0
      · simp [y, hy, List.append_assoc]
      · simp [y, hy, List.append_assoc]

noncomputable def survivingColsPrefix (q r : Nat) : List Nat := by
  classical
  exact (liveColsPrefix q r).filter (fun e => decide (gameF q e ≠ q))

theorem survivingColsPrefix_succ (q r : Nat) :
    survivingColsPrefix q (r + 1) =
      survivingColsPrefix q r ++
        if q < gameF q r then [r] else [] := by
  classical
  rw [survivingColsPrefix, liveColsPrefix_succ, List.filter_append]
  change (liveColsPrefix q r).filter
      (fun e => decide (gameF q e ≠ q)) ++ _ = _
  change survivingColsPrefix q r ++ _ = survivingColsPrefix q r ++ _
  by_cases hvisible : q <= gameF q r
  · by_cases hstrict : q < gameF q r
    · have hne : gameF q r ≠ q := by omega
      simp [hvisible, hstrict, hne]
    · have heq : gameF q r = q := by omega
      simp [heq]
  · have hstrict : ¬ q < gameF q r := by omega
    simp [hvisible, hstrict]

theorem scanCanonicalPrefix_survivors {q r : Nat} (hq : 0 < q)
    (hrq : r <= q) :
    (scanQueues [] []
      ((liveColsPrefix q r).map (fun e => sourceQueue q e))).survivors =
        (survivingColsPrefix q r).map (fun e => sourceQueue (q + 1) e) := by
  induction r with
  | zero =>
      simp [liveColsPrefix, survivingColsPrefix, scanQueues]
  | succ r ih =>
      have hrq' : r <= q := by omega
      rw [liveColsPrefix_succ, survivingColsPrefix_succ]
      by_cases hvisible : q <= gameF q r
      · simp only [hvisible, if_pos, List.map_append, List.map_singleton]
        rw [scanQueues_survivors_append]
        rw [scanCanonicalPrefix_outputs hq hrq']
        have hmex := gameF_normalized_cell_mex hq hrq' hvisible
        rw [ih hrq']
        by_cases hstrict : q < gameF q r
        · have hy : gameF q r - q ≠ 0 := by omega
          have hup := sourceQueue_old_update_pre (q := q) (e := r) hrq' hvisible
          simp only [hstrict, if_pos, List.map_singleton]
          have hmex' :
              queueMex ([] ++ (sourceQueue q r ++ ([] ++ rowQueue q r))) =
                gameF q r - q := by simpa using hmex
          rw [hmex']
          simp [hy, hup]
        · have heq : gameF q r = q := by omega
          simp [heq, hmex]
      · have hstrict : ¬ q < gameF q r := by omega
        simp only [hvisible]
        simpa [hstrict] using ih hrq'

theorem scanCanonical_outputs {q : Nat} (hq : 0 < q) :
    (scanQueues [] [] (canonicalQState q).queues).outputs = rowQueue q q := by
  unfold canonicalQState
  dsimp only
  rw [liveCols_eq_prefix]
  exact scanCanonicalPrefix_outputs hq (Nat.le_refl q)

theorem scanCanonical_survivors {q : Nat} (hq : 0 < q) :
    (scanQueues [] [] (canonicalQState q).queues).survivors =
      (survivingColsPrefix q q).map (fun e => sourceQueue (q + 1) e) := by
  unfold canonicalQState
  dsimp only
  rw [liveCols_eq_prefix]
  exact scanCanonicalPrefix_survivors hq (Nat.le_refl q)

theorem canonical_output_pos {q : Nat} (hq : 0 < q) :
    qOutput [] (canonicalQState q) = gameF q q - q := by
  have hscan := scanCanonical_outputs hq
  unfold qOutput
  dsimp only
  rw [hscan]
  simpa using gameF_normalized_cell_mex hq (Nat.le_refl q)
    (Nat.le_of_lt (gameRecurrenceModel.diagonal_gt q))

theorem live_next_iff_current_strict {q e : Nat} (heq : e < q) :
    q + 1 <= gameF (q + 1) e <-> q < gameF q e := by
  constructor
  · intro hnext
    by_cases hsmall : gameF q e < q + 1
    · have hcarry := gameF_brouwerRecurrence.1 (q := q + 1) (r := e)
        (by omega) hsmall
      have hcarry' : gameF (q + 1) e = gameF q e := by
        simpa using hcarry
      omega
    · omega
  · intro hstrict
    have hnot : ¬ (e < q + 1 ∧ gameF q e < q + 1) := by omega
    exact not_first_implies_ge_of_encoding game_encodes game_complete
      (q := q + 1) (r := e) (by omega) hnot

theorem sourceValues_succ (q r : Nat) :
    sourceValues (q + 1) r = sourceValues q r ++ [gameF q (min q r)] := by
  simp [sourceValues, List.range_succ, List.map_append]

theorem sourceQueue_succ (q r : Nat) :
    sourceQueue (q + 1) r =
      shiftQueue (sourceQueue q r) ++
        (if q + 1 <= gameF q (min q r)
          then [gameF q (min q r) - (q + 1)] else []) := by
  unfold sourceQueue
  rw [sourceValues_succ, normalizeAt_append, normalizeAt_succ]
  by_cases hnew : q + 1 <= gameF q (min q r)
  · simp [normalizeAt, hnew]
  · simp [normalizeAt, hnew]

theorem sourceQueue_old_update {q e : Nat} (heq : e <= q)
    (hlive : q <= gameF q e) :
    sourceQueue (q + 1) e =
      updateQueue (sourceQueue q e) (gameF q e - q) := by
  have hmin : min q e = e := Nat.min_eq_right heq
  rw [sourceQueue_succ, updateQueue, hmin]
  by_cases hstrict : q + 1 <= gameF q e
  · have hy : gameF q e - q ≠ 0 := by omega
    have hsub : gameF q e - (q + 1) = gameF q e - q - 1 := by omega
    simp [hstrict, hy, hsub]
  · have heqv : gameF q e = q := by omega
    simp [heqv]

theorem liveCols_succ_membership {q e : Nat} :
    e ∈ liveCols (q + 1) <->
      (e < q ∧ e ∈ liveCols q ∧ gameF q e ≠ q) ∨ e = q := by
  classical
  simp only [liveCols, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨he, hlive⟩
    by_cases heq : e = q
    · exact Or.inr heq
    · have hel : e < q := by omega
      have hstrict := (live_next_iff_current_strict hel).mp hlive
      exact Or.inl ⟨hel, ⟨hel, by omega⟩, by omega⟩
  · intro h
    rcases h with ⟨hel, ⟨_, hlive⟩, hne⟩ | heq
    · refine ⟨by omega, ?_⟩
      apply (live_next_iff_current_strict hel).mpr
      omega
    · subst e
      exact ⟨by omega,
        by
          have hg := encoded_gt game_encodes
            (q := q + 1) (r := q) (by omega)
          omega⟩

theorem liveCols_succ_list (q : Nat) :
    liveCols (q + 1) = survivingColsPrefix q q ++ [q] := by
  classical
  rw [liveCols, List.range_succ, List.filter_append]
  change (List.range q).filter
      (fun e => decide (q + 1 <= gameF (q + 1) e)) ++ _ = _
  have hprefix :
      (List.range q).filter
          (fun e => decide (q + 1 <= gameF (q + 1) e)) =
        survivingColsPrefix q q := by
    unfold survivingColsPrefix liveColsPrefix
    rw [List.filter_filter]
    apply List.filter_congr
    intro e he
    have heq : e < q := List.mem_range.mp he
    by_cases hnext : q + 1 <= gameF (q + 1) e
    · have hstrict := (live_next_iff_current_strict heq).mp hnext
      have hne : gameF q e ≠ q := by omega
      have hvisible : q <= gameF q e := by omega
      simp [hnext, hne, hvisible]
    · have hnstrict : ¬ q < gameF q e := by
        intro hs
        exact hnext ((live_next_iff_current_strict heq).mpr hs)
      by_cases hvisible : q <= gameF q e
      · have heqv : gameF q e = q := by omega
        simp [hnext, heqv]
      · simp [hnext, hvisible]
  rw [hprefix]
  have hnew : q + 1 <= gameF (q + 1) q := by
    have hg := encoded_gt game_encodes
      (q := q + 1) (r := q) (by omega)
    omega
  simp [hnew]

theorem sourceQueue_newborn (q : Nat) :
    sourceQueue (q + 1) q =
      updateQueue (sourceQueue q q) (gameF q q - q) := by
  have hdiag : q < gameF q q := gameRecurrenceModel.diagonal_gt q
  exact sourceQueue_old_update (q := q) (e := q) (Nat.le_refl q)
    (Nat.le_of_lt hdiag)

theorem sourceQueue_youngest_eq_diagonal (q : Nat) :
    sourceQueue (q + 1) q = sourceQueue (q + 1) (q + 1) := by
  unfold sourceQueue sourceValues
  apply congrArg (normalizeAt (q + 1))
  apply List.map_congr_left
  intro a ha
  have haq : a < q + 1 := List.mem_range.mp ha
  have hminq : min a q = a := Nat.min_eq_left (by omega)
  have hmins : min a (q + 1) = a := Nat.min_eq_left (by omega)
  simp [hminq, hmins]

theorem canonicalQState_zero :
    canonicalQState 0 = QState.mk [] [] := by
  simp [canonicalQState, liveCols, sourceQueue, sourceValues, normalizeAt]

theorem canonicalQState_one :
    canonicalQState 1 = QState.mk [[0]] [0] := by
  change
    QState.mk
      (([0].filter (fun e => decide (1 <= gameF 1 e))).map
        (fun e => sourceQueue 1 e)) (sourceQueue 1 1) =
      QState.mk [[0]] [0]
  simp [sourceQueue, sourceValues, normalizeAt, gameF_col0]

theorem canonical_output_zero :
    qOutput [0] (canonicalQState 0) = gameF 0 0 := by
  rw [canonicalQState_zero, gameF_zero_zero]
  rfl

theorem canonical_step_zero :
    qStep [0] (canonicalQState 0) = canonicalQState 1 := by
  rw [canonicalQState_zero, canonicalQState_one]
  rfl

theorem canonical_step_pos {q : Nat} (hq : 0 < q) :
    qStep [] (canonicalQState q) = canonicalQState (q + 1) := by
  have hscanO := scanCanonical_outputs hq
  have hscanS := scanCanonical_survivors hq
  have hk := canonical_output_pos hq
  have hlive := liveCols_succ_list q
  have hnew := sourceQueue_newborn q
  have hkpos : gameF q q - q ≠ 0 := by
    have hd : q < gameF q q := gameRecurrenceModel.diagonal_gt q
    omega
  unfold qStep
  dsimp only
  rw [hscanO, hscanS]
  change
    QState.mk
      (_ ++ if queueMex ([] ++ (sourceQueue q q ++ rowQueue q q)) = 0
        then [] else
          [updateQueue (sourceQueue q q)
            (queueMex ([] ++ (sourceQueue q q ++ rowQueue q q)))])
      (updateQueue (sourceQueue q q)
        (queueMex ([] ++ (sourceQueue q q ++ rowQueue q q)))) = _
  have hmex :
      queueMex ([] ++ (sourceQueue q q ++ rowQueue q q)) =
        gameF q q - q := by
    simpa [qOutput, hscanO] using hk
  rw [hmex]
  unfold canonicalQState
  rw [hlive, List.map_append, List.map_singleton]
  simp only [hkpos, ↓reduceIte]
  rw [hnew]
  rw [← sourceQueue_youngest_eq_diagonal q, hnew]

theorem canonical_step (q : Nat) :
    qStep (canonicalForcing q) (canonicalQState q) =
      canonicalQState (q + 1) := by
  by_cases hq : q = 0
  · subst q
    simpa [canonicalForcing] using canonical_step_zero
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    simpa [canonicalForcing, hq] using canonical_step_pos hqpos

theorem canonical_output (q : Nat) :
    qOutput (canonicalForcing q) (canonicalQState q) = gameF q q - q := by
  by_cases hq : q = 0
  · subst q
    simpa [canonicalForcing, gameF_zero_zero] using canonical_output_zero
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    simpa [canonicalForcing, hq] using canonical_output_pos hqpos

def canonicalSeed : QState := QState.mk [[0]] [0]

theorem canonicalSeed_eq_state_one : canonicalSeed = canonicalQState 1 := by
  simpa [canonicalSeed] using canonicalQState_one.symm

theorem canonicalSeed_anchored : Anchored canonicalSeed := by
  refine ⟨[], ?_⟩
  rfl

theorem canonicalSeed_diagonal_nodup : canonicalSeed.diagonal.Nodup := by
  simp [canonicalSeed]

theorem canonicalOrbit_eq_state (n : Nat) :
    autonomousOrbit canonicalSeed n = canonicalQState (n + 1) := by
  induction n with
  | zero => simpa [autonomousOrbit] using canonicalSeed_eq_state_one
  | succ n ih =>
      rw [autonomousOrbit, ih]
      simpa using canonical_step_pos (q := n + 1) (by omega)

theorem canonicalOrbit_output (n : Nat) :
    qOutput [] (autonomousOrbit canonicalSeed n) =
      gameF (n + 1) (n + 1) - (n + 1) := by
  rw [canonicalOrbit_eq_state]
  exact canonical_output_pos (by omega)

theorem canonical_diagonalTarget_eq_gameF_sub_one (n : Nat) :
    diagonalTarget canonicalSeed n = gameF (n + 1) (n + 1) - 1 := by
  unfold diagonalTarget
  rw [canonicalOrbit_output]
  have hgt : n + 1 < gameF (n + 1) (n + 1) :=
    gameRecurrenceModel.diagonal_gt (n + 1)
  omega

theorem canonical_absoluteTarget_iff_diagonalOwner (t : Nat) :
    AbsoluteDiagonalTarget canonicalSeed t <-> D gameF (t + 1) := by
  unfold AbsoluteDiagonalTarget D
  constructor
  · intro ht
    rcases ht with hinit | ⟨i, hi⟩
    · have ht0 : t = 0 := by simpa [canonicalSeed] using hinit
      subst t
      exact ⟨0, gameF_zero_zero⟩
    · refine ⟨i + 1, ?_⟩
      rw [canonical_diagonalTarget_eq_gameF_sub_one] at hi
      have hgt : i + 1 < gameF (i + 1) (i + 1) :=
        gameRecurrenceModel.diagonal_gt (i + 1)
      omega
  · rintro ⟨a, ha⟩
    cases a with
    | zero =>
        left
        rw [gameF_zero_zero] at ha
        have ht0 : t = 0 := by omega
        simp [canonicalSeed, ht0]
    | succ i =>
        right
        refine ⟨i, ?_⟩
        rw [canonical_diagonalTarget_eq_gameF_sub_one]
        have hgt : i + 1 < gameF (i + 1) (i + 1) :=
          gameRecurrenceModel.diagonal_gt (i + 1)
        omega

theorem canonical_absoluteHoleBit_eq_one_iff_blocker (n : Nat) :
    absoluteHoleBit canonicalSeed n = 1 <-> S gameF (n + 1) := by
  rw [absoluteHoleBit_eq_one_iff canonicalSeed_anchored]
  rw [canonical_absoluteTarget_iff_diagonalOwner]
  exact (gameF_blocker_iff_no_diagonal_owner (by omega)).symm

private theorem gameFBlockerCountThrough_succ_of_blocker
    {n : Nat} (hblocker : S gameF (n + 1)) :
    gameFBlockerCountThrough (n + 1) =
      gameFBlockerCountThrough n + 1 := by
  classical
  have hblocker' : S gameF (1 + n) := by
    simpa [Nat.add_comm] using hblocker
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList]
  rw [List.range'_concat, List.filter_append, List.length_append]
  simp [hblocker']

private theorem gameFBlockerCountThrough_succ_of_not_blocker
    {n : Nat} (hnot : ¬ S gameF (n + 1)) :
    gameFBlockerCountThrough (n + 1) = gameFBlockerCountThrough n := by
  classical
  have hnot' : ¬ S gameF (1 + n) := by
    simpa [Nat.add_comm] using hnot
  simp only [gameFBlockerCountThrough, gameFBlockersThroughList]
  rw [List.range'_concat, List.filter_append, List.length_append]
  simp [hnot']

theorem canonical_absoluteHoleCount_eq_gameFBlockerCountThrough : ∀ N,
    absoluteHoleCount canonicalSeed N = gameFBlockerCountThrough N := by
  intro N
  induction N with
  | zero =>
      simp [absoluteHoleCount, gameFBlockerCountThrough,
        gameFBlockersThroughList]
  | succ N ih =>
      rw [absoluteHoleCount, ih]
      by_cases hblocker : S gameF (N + 1)
      · have hbit : absoluteHoleBit canonicalSeed N = 1 :=
          (canonical_absoluteHoleBit_eq_one_iff_blocker N).mpr hblocker
        rw [hbit, gameFBlockerCountThrough_succ_of_blocker hblocker]
      · have hbit : absoluteHoleBit canonicalSeed N = 0 := by
          unfold absoluteHoleBit
          by_cases ht : N ∈ absoluteTargetsBefore canonicalSeed N
          · simp [ht]
          · have hone : absoluteHoleBit canonicalSeed N = 1 := by
              simp [absoluteHoleBit, ht]
            exact False.elim (hblocker
              ((canonical_absoluteHoleBit_eq_one_iff_blocker N).mp hone))
        rw [hbit, gameFBlockerCountThrough_succ_of_not_blocker hblocker]
        omega

theorem gameFBlockerCountThrough_quadratic_bound (N : Nat) :
    2 * N <= gameFBlockerCountThrough N * gameFBlockerCountThrough N +
      5 * gameFBlockerCountThrough N + 2 := by
  have hbound := autonomousOrbit_absoluteHole_doubled_bound
    canonicalSeed_anchored canonicalSeed_diagonal_nodup N
  rw [canonical_absoluteHoleCount_eq_gameFBlockerCountThrough] at hbound
  change
    2 * N <=
      2 * gameFBlockerCountThrough N +
        2 * (gameFBlockerCountThrough N + 1) * 1 +
          gameFBlockerCountThrough N *
            (gameFBlockerCountThrough N + 1) at hbound
  simp only [Nat.mul_add, Nat.mul_one] at hbound ⊢
  omega

theorem gameFBlockerCountThrough_strict_square (N : Nat) :
    2 * N < (gameFBlockerCountThrough N + 3) *
      (gameFBlockerCountThrough N + 3) := by
  have hsq := autonomousOrbit_absoluteHole_strict_square
    canonicalSeed_anchored canonicalSeed_diagonal_nodup N
  rw [canonical_absoluteHoleCount_eq_gameFBlockerCountThrough] at hsq
  simpa [canonicalSeed] using hsq

theorem gameFBlockerCountThrough_sqrt_certificate
    (N R : Nat) (hroot : R * R <= 2 * N) :
    R - 2 <= gameFBlockerCountThrough N := by
  have hsqrt := autonomousOrbit_absoluteHole_sqrt_certificate
    canonicalSeed_anchored canonicalSeed_diagonal_nodup N R hroot
  rw [canonical_absoluteHoleCount_eq_gameFBlockerCountThrough] at hsqrt
  simpa [canonicalSeed] using hsqrt

#print axioms canonical_step
#print axioms canonical_output
#print axioms canonicalOrbit_eq_state
#print axioms canonicalOrbit_output
#print axioms canonical_absoluteTarget_iff_diagonalOwner
#print axioms canonical_absoluteHoleCount_eq_gameFBlockerCountThrough
#print axioms gameFBlockerCountThrough_quadratic_bound
#print axioms gameFBlockerCountThrough_strict_square
#print axioms gameFBlockerCountThrough_sqrt_certificate

theorem canonicalForcing_zero : canonicalForcing 0 = [0] := by
  simp [canonicalForcing]

theorem canonicalForcing_pos {q : Nat} (hq : 0 < q) :
    canonicalForcing q = [] := by
  simp [canonicalForcing, Nat.ne_of_gt hq]

end OBUQ
end ChompLean
