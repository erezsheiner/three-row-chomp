import XGameFOrderedBlockerUnionReconstruction
import SelectorColHistCausalDepth
import GameFCol5Rail

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace ChompLean
namespace OBUQ

/-!
# Canonical rank-three prefix with source provenance, and the peeled `[1,2,4]` tail

Work-ID: `AUG-G1-CANONICAL-MACRO-001`
Lane: `CLAUDE-G1-RANK3-PEEL-001`
Run-ID: `CLAUDE-G1-20260813-001`

* **P0** (`liveCols_rank3_prefix`, `sourceQueue_col0`, `sourceQueue_col2`,
  `sourceQueue_col5`): for every physical row `q ≥ 10` the live-column word
  starts literally with the source columns `[0, 2, 5]`, and their normalized
  source queues are `[0]`, `[0,1]`, `[0,1,2,3]`.
* **P1** (`canonicalQState_rank3_prefix`): consequently
  `(canonicalQState q).queues = [[0],[0,1],[0,1,2,3]] ++ T` where `T` is the
  image of the remaining live columns `6 ≤ e < q` under `sourceQueue q`, so
  the queue word stays aligned with its physical source columns.
* **P2** (`scanQueues_rank3_peel`): generically in the tail `T` and
  independently of `gameF`, scanning `[[0],[0,1],[0,1,2,3]] ++ T` from empty
  forcing and empty service history emits `[1, 2, 4]` followed by the outputs
  of `scanQueues [] [1,2,4] T`, and keeps the three prefix queues literally,
  followed by that tail scan's survivors.
* **P3** (`canonical_rank3_peeled_tail`): the combination for
  `canonicalQState q`.

Computable-vs-moving split: the prefix `[[0],[0,1],[0,1,2,3]]`, its source
columns `[0,2,5]`, and the emitted services `[1,2,4]` are literal constants,
available upstream with no oracle.  The moving suffix is exactly
`((List.range' 6 (q-6)).filter (fun e => decide (q ≤ gameF q e))).map
(fun e => sourceQueue q e)`; it still depends on `gameF` on columns `≥ 6`
and nothing below claims it computable.  No new definition wraps `gameF`,
`d`, `A`, freeze, the full prefix, or the target theorems.
-/

/-- Members of `List.range' s n` (unit step) sit in `[s, s + n)`. -/
private theorem mem_range'_bounds {s n a : Nat} (h : a ∈ List.range' s n) :
    s ≤ a ∧ a < s + n := by
  induction n generalizing s with
  | zero => nomatch h
  | succ n ih =>
      have h' : a = s ∨ a ∈ List.range' (s + 1) n := List.mem_cons.mp h
      rcases h' with rfl | h'
      · omega
      · have := ih h'
        omega

/-- Splitting `List.range'` by length. -/
private theorem range'_split (s m n : Nat) :
    List.range' s (m + n) = List.range' s m ++ List.range' (s + m) n := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 + n = (m + n) + 1 by omega]
      show s :: List.range' (s + 1) (m + n) =
        (s :: List.range' (s + 1) m) ++ List.range' (s + (m + 1)) n
      rw [List.cons_append, ih (s + 1),
        show s + 1 + m = s + (m + 1) by omega]

/-- Splitting `List.range` at a cut `k`. -/
private theorem range_split (k d : Nat) :
    List.range (k + d) = List.range k ++ List.range' k d := by
  rw [List.range_eq_range', List.range_eq_range', range'_split 0 k d,
    Nat.zero_add]

/-- `normalizeAt` kills a list whose members all sit below the cut. -/
private theorem normalizeAt_nil_of_lt {q : Nat} {xs : List Nat}
    (h : ∀ x, x ∈ xs → x < q) : normalizeAt q xs = [] := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      rw [normalizeAt_cons,
        if_neg (by have := h p List.mem_cons_self; omega)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem p hx))

/-- P0, queue part, column 0: only the youngest source value `q` survives. -/
theorem sourceQueue_col0 {q : Nat} (hq : 10 ≤ q) : sourceQueue q 0 = [0] := by
  have hvals : sourceValues q 0 = (List.range q).map (fun a => a + 1) := by
    unfold sourceValues
    apply List.map_congr_left
    intro a _
    rw [Nat.min_zero, gameF_col0]
  have hsplit : List.range q = List.range (q - 1) ++ List.range' (q - 1) 1 := by
    have hs := range_split (q - 1) 1
    rw [show q - 1 + 1 = q by omega] at hs
    exact hs
  have hlow : normalizeAt q ((List.range (q - 1)).map (fun a => a + 1)) = [] := by
    apply normalizeAt_nil_of_lt
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    have := List.mem_range.mp ha
    omega
  unfold sourceQueue
  rw [hvals, hsplit, List.map_append, normalizeAt_append, hlow,
    List.nil_append]
  show normalizeAt q [q - 1 + 1] = [0]
  rw [normalizeAt_cons, if_pos (by omega : q ≤ q - 1 + 1),
    show q - 1 + 1 - q = 0 by omega]
  rfl

/-- P0, queue part, column 2: exactly the sources `q, q+1` survive. -/
theorem sourceQueue_col2 {q : Nat} (hq : 10 ≤ q) : sourceQueue q 2 = [0, 1] := by
  have h1 : List.range q = List.range 2 ++ List.range' 2 (q - 2) := by
    have hs := range_split 2 (q - 2)
    rw [show 2 + (q - 2) = q by omega] at hs
    exact hs
  have h2 : List.range' 2 (q - 2) =
      List.range' 2 (q - 4) ++ List.range' (q - 2) 2 := by
    have hs := range'_split 2 (q - 4) 2
    rw [show q - 4 + 2 = q - 2 by omega] at hs
    rw [show 2 + (q - 4) = q - 2 by omega] at hs
    exact hs
  have hval2 : (List.range 2).map (fun a => gameF a (min a 2)) = [1, 3] := by
    show [gameF 0 0, gameF 1 1] = [1, 3]
    rw [gameF_zero_zero, gameF_one_one]
  have hlow : normalizeAt q ([1, 3] : List Nat) = [] := by
    apply normalizeAt_nil_of_lt
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> omega
  have hmid : normalizeAt q
      ((List.range' 2 (q - 4)).map (fun a => gameF a (min a 2))) = [] := by
    apply normalizeAt_nil_of_lt
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    have ha' := mem_range'_bounds ha
    rw [Nat.min_eq_right (by omega : 2 ≤ a),
      gameF_col2_rail (by omega : 2 ≤ a)]
    omega
  unfold sourceQueue sourceValues
  rw [h1, List.map_append, normalizeAt_append, hval2, hlow, List.nil_append,
    h2, List.map_append, normalizeAt_append, hmid, List.nil_append]
  show normalizeAt q
    [gameF (q - 2) (min (q - 2) 2), gameF (q - 2 + 1) (min (q - 2 + 1) 2)] =
      [0, 1]
  rw [Nat.min_eq_right (by omega : 2 ≤ q - 2),
    Nat.min_eq_right (by omega : 2 ≤ q - 2 + 1),
    gameF_col2_rail (by omega : 2 ≤ q - 2),
    gameF_col2_rail (by omega : 2 ≤ q - 2 + 1),
    normalizeAt_cons, if_pos (by omega : q ≤ q - 2 + 2),
    normalizeAt_cons, if_pos (by omega : q ≤ q - 2 + 1 + 2),
    show q - 2 + 2 - q = 0 by omega,
    show q - 2 + 1 + 2 - q = 1 by omega]
  rfl

/-- P0, queue part, column 5: exactly the sources `q, q+1, q+2, q+3`
survive.  At `q = 10` the value `q` is the diagonal cell `gameF 5 5 = 10`;
for `q ≥ 11` all four values come from the affine rail rows `q-4..q-1`. -/
theorem sourceQueue_col5 {q : Nat} (hq : 10 ≤ q) :
    sourceQueue q 5 = [0, 1, 2, 3] := by
  have g22 : gameF 2 2 = 4 := by
    have := gameF_col2_rail (q := 2) (by omega)
    omega
  have hd3 : gameF 3 3 < 10 := by
    rw [gameF_diag_three]
    omega
  rcases Nat.lt_or_ge q 11 with hq10 | hq11
  · -- q = 10: finite source word [1,3,4,d₃,8,10,9,11,12,13]
    have hq' : q = 10 := by omega
    subst hq'
    have g75 : gameF 7 5 = 11 := by
      have := gameF_col5_rail (q := 7) (by omega)
      omega
    have g85 : gameF 8 5 = 12 := by
      have := gameF_col5_rail (q := 8) (by omega)
      omega
    have g95 : gameF 9 5 = 13 := by
      have := gameF_col5_rail (q := 9) (by omega)
      omega
    have hval : sourceValues 10 5 =
        [1, 3, 4, gameF 3 3, 8, 10, 9, 11, 12, 13] := by
      show [gameF 0 0, gameF 1 1, gameF 2 2, gameF 3 3, gameF 4 4,
        gameF 5 5, gameF 6 5, gameF 7 5, gameF 8 5, gameF 9 5] = _
      rw [gameF_zero_zero, gameF_one_one, g22, gameF_diag_four,
        gameF_diag_five, gameF_six_five, g75, g85, g95]
    unfold sourceQueue
    rw [hval,
      normalizeAt_cons, if_neg (by omega : ¬ 10 ≤ 1),
      normalizeAt_cons, if_neg (by omega : ¬ 10 ≤ 3),
      normalizeAt_cons, if_neg (by omega : ¬ 10 ≤ 4),
      normalizeAt_cons, if_neg (by omega : ¬ 10 ≤ gameF 3 3),
      normalizeAt_cons, if_neg (by omega : ¬ 10 ≤ 8),
      normalizeAt_cons, if_pos (by omega : 10 ≤ 10),
      normalizeAt_cons, if_neg (by omega : ¬ 10 ≤ 9),
      normalizeAt_cons, if_pos (by omega : 10 ≤ 11),
      normalizeAt_cons, if_pos (by omega : 10 ≤ 12),
      normalizeAt_cons, if_pos (by omega : 10 ≤ 13)]
    rfl
  · -- q ≥ 11: segments 0..6 / rail rows 7..q-5 / rail rows q-4..q-1
    have h1 : List.range q = List.range 7 ++ List.range' 7 (q - 7) := by
      have hs0 := range_split 7 (q - 7)
      rw [show 7 + (q - 7) = q by omega] at hs0
      exact hs0
    have h2 : List.range' 7 (q - 7) =
        List.range' 7 (q - 11) ++ List.range' (q - 4) 4 := by
      have hs := range'_split 7 (q - 11) 4
      rw [show q - 11 + 4 = q - 7 by omega] at hs
      rw [show 7 + (q - 11) = q - 4 by omega] at hs
      exact hs
    have hval7 : (List.range 7).map (fun a => gameF a (min a 5)) =
        [1, 3, 4, gameF 3 3, 8, 10, 9] := by
      show [gameF 0 0, gameF 1 1, gameF 2 2, gameF 3 3, gameF 4 4,
        gameF 5 5, gameF 6 5] = _
      rw [gameF_zero_zero, gameF_one_one, g22, gameF_diag_four,
        gameF_diag_five, gameF_six_five]
    have hlow : normalizeAt q ([1, 3, 4, gameF 3 3, 8, 10, 9] : List Nat) = [] := by
      apply normalizeAt_nil_of_lt
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hmid : normalizeAt q
        ((List.range' 7 (q - 11)).map (fun a => gameF a (min a 5))) = [] := by
      apply normalizeAt_nil_of_lt
      intro x hx
      rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
      have ha' := mem_range'_bounds ha
      rw [Nat.min_eq_right (by omega : 5 ≤ a),
        gameF_col5_rail (by omega : 7 ≤ a)]
      omega
    unfold sourceQueue sourceValues
    rw [h1, List.map_append, normalizeAt_append, hval7, hlow,
      List.nil_append, h2, List.map_append, normalizeAt_append, hmid,
      List.nil_append]
    show normalizeAt q
      [gameF (q - 4) (min (q - 4) 5),
        gameF (q - 4 + 1) (min (q - 4 + 1) 5),
        gameF (q - 4 + 1 + 1) (min (q - 4 + 1 + 1) 5),
        gameF (q - 4 + 1 + 1 + 1) (min (q - 4 + 1 + 1 + 1) 5)] = [0, 1, 2, 3]
    rw [Nat.min_eq_right (by omega : 5 ≤ q - 4),
      Nat.min_eq_right (by omega : 5 ≤ q - 4 + 1),
      Nat.min_eq_right (by omega : 5 ≤ q - 4 + 1 + 1),
      Nat.min_eq_right (by omega : 5 ≤ q - 4 + 1 + 1 + 1),
      gameF_col5_rail (by omega : 7 ≤ q - 4),
      gameF_col5_rail (by omega : 7 ≤ q - 4 + 1),
      gameF_col5_rail (by omega : 7 ≤ q - 4 + 1 + 1),
      gameF_col5_rail (by omega : 7 ≤ q - 4 + 1 + 1 + 1),
      normalizeAt_cons, if_pos (by omega : q ≤ q - 4 + 4),
      normalizeAt_cons, if_pos (by omega : q ≤ q - 4 + 1 + 4),
      normalizeAt_cons, if_pos (by omega : q ≤ q - 4 + 1 + 1 + 4),
      normalizeAt_cons, if_pos (by omega : q ≤ q - 4 + 1 + 1 + 1 + 4),
      show q - 4 + 4 - q = 0 by omega,
      show q - 4 + 1 + 4 - q = 1 by omega,
      show q - 4 + 1 + 1 + 4 - q = 2 by omega,
      show q - 4 + 1 + 1 + 1 + 4 - q = 3 by omega]
    rfl

/-- P0, column part: for `q ≥ 10` the live-column word starts literally with
the source columns `0, 2, 5`; the tail is the filter over columns `6..q-1`. -/
theorem liveCols_rank3_prefix {q : Nat} (hq : 10 ≤ q) :
    liveCols q = [0, 2, 5] ++
      (List.range' 6 (q - 6)).filter (fun e => decide (q ≤ gameF q e)) := by
  have c0 : q ≤ gameF q 0 := by rw [gameF_col0]; omega
  have c1 : ¬ q ≤ gameF q 1 := by
    rw [gameF_col1_rail (by omega : 2 ≤ q)]; omega
  have c2 : q ≤ gameF q 2 := by
    rw [gameF_col2_rail (by omega : 2 ≤ q)]; omega
  have c3 : ¬ q ≤ gameF q 3 := by
    rw [gameF_col3_rail (by omega : 5 ≤ q)]; omega
  have c4 : ¬ q ≤ gameF q 4 := by
    rw [gameF_col4_rail (by omega : 7 ≤ q)]; omega
  have c5 : q ≤ gameF q 5 := by
    rw [gameF_col5_rail (by omega : 7 ≤ q)]; omega
  have hsplit : List.range q = List.range 6 ++ List.range' 6 (q - 6) := by
    have hs := range_split 6 (q - 6)
    rw [show 6 + (q - 6) = q by omega] at hs
    exact hs
  show (List.range q).filter (fun e => decide (q ≤ gameF q e)) = _
  rw [hsplit, List.filter_append]
  congr 1
  show List.filter (fun e => decide (q ≤ gameF q e)) [0, 1, 2, 3, 4, 5] =
    [0, 2, 5]
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  rw [if_pos c0, if_neg c1, if_pos c2, if_neg c3, if_neg c4, if_pos c5]

/-- P1: the canonical queue word for `q ≥ 10` is literally
`[[0],[0,1],[0,1,2,3]]` followed by the queues of the remaining live
columns, in source-column alignment with `liveCols_rank3_prefix`. -/
theorem canonicalQState_rank3_prefix {q : Nat} (hq : 10 ≤ q) :
    (canonicalQState q).queues =
      [[0], [0, 1], [0, 1, 2, 3]] ++
        ((List.range' 6 (q - 6)).filter
          (fun e => decide (q ≤ gameF q e))).map (fun e => sourceQueue q e) := by
  show (liveCols q).map (fun e => sourceQueue q e) = _
  rw [liveCols_rank3_prefix hq, List.map_append]
  congr 1
  show [sourceQueue q 0, sourceQueue q 2, sourceQueue q 5] = _
  rw [sourceQueue_col0 hq, sourceQueue_col2 hq, sourceQueue_col5 hq]

/-- P2: generic peeled scan.  Scanning the literal rank-three prefix from
empty forcing and empty history emits the services `[1, 2, 4]`, keeps the
three prefix queues literally, and continues as `scanQueues [] [1,2,4] T`.
Fully generic in `T`; `gameF` does not occur. -/
theorem scanQueues_rank3_peel (T : List (List Nat)) :
    scanQueues [] [] ([[0], [0, 1], [0, 1, 2, 3]] ++ T) =
      ⟨[1, 2, 4] ++ (scanQueues [] [1, 2, 4] T).outputs,
        [[0], [0, 1], [0, 1, 2, 3]] ++ (scanQueues [] [1, 2, 4] T).survivors⟩ :=
  rfl

/-- P3: canonical peeled-tail corollary for `q ≥ 10`.  The first conjunct is
the source-column prefix, the second the aligned queue-word prefix, the third
the peeled scan.  The prefix queues, source columns, and services are literal
constants computable upstream; the moving suffix is exactly the mapped filter
over columns `6..q-1` and is not claimed computable. -/
theorem canonical_rank3_peeled_tail {q : Nat} (hq : 10 ≤ q) :
    liveCols q = [0, 2, 5] ++
      (List.range' 6 (q - 6)).filter (fun e => decide (q ≤ gameF q e)) ∧
    (canonicalQState q).queues =
      [[0], [0, 1], [0, 1, 2, 3]] ++
        ((List.range' 6 (q - 6)).filter
          (fun e => decide (q ≤ gameF q e))).map (fun e => sourceQueue q e) ∧
    scanQueues [] [] (canonicalQState q).queues =
      ⟨[1, 2, 4] ++
        (scanQueues [] [1, 2, 4]
          (((List.range' 6 (q - 6)).filter
            (fun e => decide (q ≤ gameF q e))).map
              (fun e => sourceQueue q e))).outputs,
        [[0], [0, 1], [0, 1, 2, 3]] ++
          (scanQueues [] [1, 2, 4]
            (((List.range' 6 (q - 6)).filter
              (fun e => decide (q ≤ gameF q e))).map
                (fun e => sourceQueue q e))).survivors⟩ := by
  refine ⟨liveCols_rank3_prefix hq, canonicalQState_rank3_prefix hq, ?_⟩
  rw [canonicalQState_rank3_prefix hq, scanQueues_rank3_peel]

#print axioms sourceQueue_col0
#print axioms sourceQueue_col2
#print axioms sourceQueue_col5
#print axioms liveCols_rank3_prefix
#print axioms canonicalQState_rank3_prefix
#print axioms scanQueues_rank3_peel
#print axioms canonical_rank3_peeled_tail

end OBUQ
end ChompLean
