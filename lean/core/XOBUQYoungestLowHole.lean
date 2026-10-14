import XOrderedBlockerUnionQuotient

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean
namespace OBUQ

/-!
# Anchored youngest queues and the low-hole sawtooth

Work-ID: `X-OBUQ-GLOBAL-LEAN-AND-CONVOY-001`
Run-ID: `XOGC-20260812-2321-ROOT`

This file proves the anchored last-queue reduction for the ordered
blocker-union transducer.  It then derives the exact private-MEX drain and
Nodup cardinality recharge laws for the youngest/diagonal queue.  The final
section proves the abstract integer sawtooth bound used by the square-root
escape argument.  It assumes no gameF reconstruction, NoTriple or host-cover
statement.
-/

theorem queueMex_eq_of_spec {xs : List Nat} {m : Nat}
    (habsent : m ∉ xs) (hlower : ∀ k, k < m → k ∈ xs) :
    queueMex xs = m := by
  have hspec := queueMex_spec xs
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hgt
    exact habsent (hspec.2 m hgt)
  · apply Nat.le_of_not_gt
    intro hgt
    exact hspec.1 (hlower (queueMex xs) hgt)

theorem queueMex_append_self_gt (xs : List Nat) :
    queueMex xs < queueMex (xs ++ [queueMex xs]) := by
  let m := queueMex xs
  let n := queueMex (xs ++ [m])
  have hnabsent : n ∉ xs ++ [m] := queueMex_spec (xs ++ [m]) |>.1
  have hm : m ∈ xs ++ [m] := by simp
  have hne : n ≠ m := by
    intro heq
    exact hnabsent (by simpa [heq] using hm)
  have hnlt : ¬ n < m := by
    intro hlt
    have hmem : n ∈ xs := (queueMex_spec xs).2 n hlt
    exact hnabsent (by simp [hmem])
  dsimp [m, n] at hne hnlt ⊢
  omega

theorem scanQueues_outputs_append (U R q : List Nat)
    (pre : List (List Nat)) :
    (scanQueues U R (pre ++ [q])).outputs =
      (scanQueues U R pre).outputs ++
        [queueMex
          (U ++ (q ++ (R ++ (scanQueues U R pre).outputs)))] := by
  induction pre generalizing R with
  | nil =>
      simp [scanQueues]
  | cons p pre ih =>
      simp only [List.cons_append, scanQueues]
      rw [ih (R := R ++ [queueMex (U ++ (p ++ R))])]
      congr 2
      simp [List.append_assoc]

def Anchored (Q : QState) : Prop :=
  ∃ pre, Q.queues = pre ++ [Q.diagonal]

theorem anchored_nonempty {Q : QState} (h : Anchored Q) :
    Q.queues ≠ [] := by
  intro hnil
  rcases h with ⟨pre, hpre⟩
  rw [hnil] at hpre
  have hlen := congrArg List.length hpre
  simp at hlen

theorem anchored_scan_output_normal_form {Q : QState} (h : Anchored Q)
    (U : List Nat) :
    ∃ R : List Nat,
      (scanQueues U [] Q.queues).outputs =
        R ++ [queueMex (U ++ (Q.diagonal ++ R))] := by
  rcases h with ⟨pre, hpre⟩
  refine ⟨(scanQueues U [] pre).outputs, ?_⟩
  rw [hpre]
  simpa using scanQueues_outputs_append U [] Q.diagonal pre

theorem anchored_output_gt_youngest_service {Q : QState}
    (h : Anchored Q) (U : List Nat) :
    ∃ y, y < qOutput U Q := by
  rcases anchored_scan_output_normal_form h U with ⟨R, hout⟩
  let A := U ++ (Q.diagonal ++ R)
  let y := queueMex A
  refine ⟨y, ?_⟩
  unfold qOutput
  dsimp only
  rw [hout]
  have hgt := queueMex_append_self_gt A
  simpa [A, y, List.append_assoc] using hgt

theorem anchored_output_pos {Q : QState} (h : Anchored Q)
    (U : List Nat) : 0 < qOutput U Q := by
  rcases anchored_output_gt_youngest_service h U with ⟨y, hy⟩
  omega

theorem anchored_preserved {Q : QState} (h : Anchored Q)
    (U : List Nat) : Anchored (qStep U Q) := by
  have hk : qOutput U Q ≠ 0 :=
    Nat.ne_of_gt (anchored_output_pos h U)
  have hk' :
      queueMex
        (U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs)) ≠ 0 := by
    simpa [qOutput] using hk
  unfold Anchored
  refine ⟨(scanQueues U [] Q.queues).survivors, ?_⟩
  simp [qStep, hk']

theorem anchored_privateMex_mem_diagonal_input {Q : QState}
    (h : Anchored Q) (U : List Nat) :
    queueMex Q.diagonal ∈
      U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs) := by
  rcases anchored_scan_output_normal_form h U with ⟨R, hout⟩
  rw [hout]
  let L := queueMex Q.diagonal
  let A := U ++ (Q.diagonal ++ R)
  have htarget :
      MemEq
        (U ++ (Q.diagonal ++
          (R ++ [queueMex (U ++ (Q.diagonal ++ R))])))
        (A ++ [queueMex A]) := by
    intro n
    simp [A, List.append_assoc]
  apply (htarget L).mpr
  by_cases hLA : L ∈ A
  · simp [hLA]
  · have hlow : ∀ k, k < L → k ∈ A := by
      intro k hk
      have hkdiag : k ∈ Q.diagonal :=
        (queueMex_spec Q.diagonal).2 k hk
      simp [A, hkdiag]
    have hmex : queueMex A = L := queueMex_eq_of_spec hLA hlow
    simp [hmex]

theorem anchored_output_ne_privateMex {Q : QState} (h : Anchored Q)
    (U : List Nat) : qOutput U Q ≠ queueMex Q.diagonal := by
  intro heq
  have hmem := anchored_privateMex_mem_diagonal_input h U
  have habsent :
      qOutput U Q ∉
        U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs) := by
    unfold qOutput
    exact (queueMex_spec _).1
  exact habsent (by simpa [heq] using hmem)

theorem privateMex_update_of_pos {G : List Nat} {d : Nat}
    (hL : 0 < queueMex G) (hne : d ≠ queueMex G) :
    queueMex (updateQueue G d) = queueMex G - 1 := by
  let L := queueMex G
  apply queueMex_eq_of_spec
  · rw [mem_updateQueue_iff]
    intro hsource
    rcases hsource with hold | hbirth
    · have hparent : queueMex G ∈ G := by
        have heq : (queueMex G - 1) + 1 = queueMex G := by omega
        rw [heq] at hold
        exact hold
      exact (queueMex_spec G).1 hparent
    · rcases hbirth with ⟨hd, heq⟩
      apply hne
      omega
  · intro j hj
    rw [mem_updateQueue_iff]
    left
    exact (queueMex_spec G).2 (j + 1) (by
      omega)

theorem anchored_privateMex_drain {Q : QState} (h : Anchored Q)
    (U : List Nat) (hL : 0 < queueMex Q.diagonal) :
    queueMex (qStep U Q).diagonal = queueMex Q.diagonal - 1 := by
  unfold qStep
  dsimp only
  exact privateMex_update_of_pos hL (anchored_output_ne_privateMex h U)

theorem shiftQueue_nodup {G : List Nat} (hG : G.Nodup) :
    (shiftQueue G).Nodup := by
  induction G with
  | nil => simp [shiftQueue]
  | cons x G ih =>
      have hhead := (List.nodup_cons.mp hG).1
      have htail := (List.nodup_cons.mp hG).2
      cases x with
      | zero =>
          simpa [shiftQueue] using ih htail
      | succ x =>
          rw [shiftQueue, List.nodup_cons]
          constructor
          · intro hx
            have hx' : x + 1 ∈ G := mem_shiftQueue_iff.mp hx
            exact hhead hx'
          · exact ih htail

theorem updateQueue_nodup {G : List Nat} {d : Nat}
    (hG : G.Nodup) (hd : d ∉ G) : (updateQueue G d).Nodup := by
  unfold updateQueue
  by_cases hd0 : d = 0
  · simp [hd0, shiftQueue_nodup hG]
  · simp only [hd0, ↓reduceIte]
    apply List.nodup_append.mpr
    refine ⟨shiftQueue_nodup hG, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro heq
    have haG : a + 1 ∈ G := mem_shiftQueue_iff.mp ha
    have had : a + 1 = d := by omega
    exact hd (by simpa [had] using haG)

theorem shiftQueue_length_of_zero_absent {G : List Nat}
    (hzero : 0 ∉ G) : (shiftQueue G).length = G.length := by
  induction G with
  | nil => rfl
  | cons x G ih =>
      cases x with
      | zero => exact False.elim (hzero (by simp))
      | succ x =>
          have hzG : 0 ∉ G := by
            intro hz
            exact hzero (by simp [hz])
          simp [shiftQueue, ih hzG]

theorem shiftQueue_length_of_zero_mem {G : List Nat}
    (hG : G.Nodup) (hzero : 0 ∈ G) :
    (shiftQueue G).length + 1 = G.length := by
  induction G with
  | nil => simp at hzero
  | cons x G ih =>
      have hhead := (List.nodup_cons.mp hG).1
      have htail := (List.nodup_cons.mp hG).2
      cases x with
      | zero =>
          have hlen := shiftQueue_length_of_zero_absent hhead
          simp only [shiftQueue, List.length_cons]
          omega
      | succ x =>
          have hzG : 0 ∈ G := by simpa using hzero
          have hlen := ih htail hzG
          simp only [shiftQueue, List.length_cons]
          omega

theorem updateQueue_length_recharge {G : List Nat} {d : Nat}
    (hG : G.Nodup) (hdpos : 0 < d) :
    (updateQueue G d).length =
      G.length + (if queueMex G = 0 then 1 else 0) := by
  have hmex0 : queueMex G = 0 ↔ 0 ∉ G := by
    constructor
    · intro hm hmem
      exact (queueMex_spec G).1 (by simpa [hm] using hmem)
    · intro hnot
      apply queueMex_eq_of_spec hnot
      intro k hk
      omega
  unfold updateQueue
  have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
  simp only [hd0, ↓reduceIte, List.length_append, List.length_singleton]
  by_cases hz : 0 ∈ G
  · have hm : queueMex G ≠ 0 := by
      intro heq
      exact (hmex0.mp heq) hz
    simp only [hm, ↓reduceIte, Nat.add_zero]
    have hlen := shiftQueue_length_of_zero_mem hG hz
    omega
  · have hm : queueMex G = 0 := hmex0.mpr hz
    simp only [hm, ↓reduceIte]
    rw [shiftQueue_length_of_zero_absent hz]

theorem qOutput_absent_diagonal {Q : QState} (U : List Nat) :
    qOutput U Q ∉ Q.diagonal := by
  intro hmem
  unfold qOutput at hmem
  dsimp only at hmem
  have habsent :=
    (queueMex_spec
      (U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs))).1
  apply habsent
  simp only [List.mem_append]
  exact Or.inr (Or.inl hmem)

theorem anchored_youngest_nodup_preserved {Q : QState}
    (hG : Q.diagonal.Nodup) (U : List Nat) :
    (qStep U Q).diagonal.Nodup := by
  unfold qStep
  dsimp only
  apply updateQueue_nodup hG
  exact qOutput_absent_diagonal U

theorem anchored_youngestCard_recharge {Q : QState} (h : Anchored Q)
    (hG : Q.diagonal.Nodup) (U : List Nat) :
    (qStep U Q).diagonal.length =
      Q.diagonal.length +
        (if queueMex Q.diagonal = 0 then 1 else 0) := by
  unfold qStep
  dsimp only
  apply updateQueue_length_recharge hG
  exact anchored_output_pos h U

/-! ## The abstract integer sawtooth and recharge bound -/

def rechargeCount (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rechargeCount c n + c n

def noRechargeCount (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => noRechargeCount c n + (if c n = 0 then 1 else 0)

structure LowHoleSaw (l s c : Nat → Nat) (s0 : Nat) : Prop where
  init : s 0 = s0
  bit : ∀ n, c n = 0 ∨ c n = 1
  size_step : ∀ n, s (n + 1) = s n + c n
  low_le_size : ∀ n, l n ≤ s n
  low_pos_of_no_recharge : ∀ n, c n = 0 → 0 < l n
  low_drain : ∀ n, c n = 0 → l (n + 1) + 1 = l n

theorem lowHoleSaw_size_eq {l s c : Nat → Nat} {s0 : Nat}
    (h : LowHoleSaw l s c s0) :
    ∀ n, s n = s0 + rechargeCount c n := by
  intro n
  induction n with
  | zero => simpa [rechargeCount] using h.init
  | succ n ih =>
      rw [h.size_step n, ih]
      simp only [rechargeCount]
      omega

theorem lowHoleSaw_count_partition {l s c : Nat → Nat} {s0 : Nat}
    (h : LowHoleSaw l s c s0) :
    ∀ n, n = rechargeCount c n + noRechargeCount c n := by
  intro n
  induction n with
  | zero => simp [rechargeCount, noRechargeCount]
  | succ n ih =>
      cases h.bit n with
      | inl hc => simp [rechargeCount, noRechargeCount, hc]; omega
      | inr hc => simp [rechargeCount, noRechargeCount, hc]; omega

theorem recharge_credit_succ (r s0 : Nat) :
    2 * ((r + 1) + 1) * s0 + (r + 1) * ((r + 1) + 1) =
      (2 * (r + 1) * s0 + r * (r + 1)) +
        2 * (s0 + r + 1) := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem lowHoleSaw_exact_credit {l s c : Nat → Nat} {s0 : Nat}
    (h : LowHoleSaw l s c s0) : ∀ n,
    2 * noRechargeCount c n + 2 * l n ≤
      2 * (rechargeCount c n + 1) * s0 +
        rechargeCount c n * (rechargeCount c n + 1) := by
  intro n
  induction n with
  | zero =>
      simp only [rechargeCount, noRechargeCount]
      have hl := h.low_le_size 0
      rw [h.init] at hl
      omega
  | succ n ih =>
      cases h.bit n with
      | inl hc =>
          have hd := h.low_drain n hc
          simp [rechargeCount, noRechargeCount, hc]
          omega
      | inr hc =>
          have hs := lowHoleSaw_size_eq h (n + 1)
          simp [rechargeCount, hc] at hs
          have hl := h.low_le_size (n + 1)
          rw [hs] at hl
          have hform := recharge_credit_succ (rechargeCount c n) s0
          simp [rechargeCount, noRechargeCount, hc]
          omega

theorem lowHoleSaw_doubled_recharge_bound
    {l s c : Nat → Nat} {s0 : Nat}
    (h : LowHoleSaw l s c s0) : ∀ n,
    2 * n ≤
      2 * rechargeCount c n +
        2 * (rechargeCount c n + 1) * s0 +
          rechargeCount c n * (rechargeCount c n + 1) := by
  intro n
  have hp := lowHoleSaw_count_partition h n
  have hc := lowHoleSaw_exact_credit h n
  omega

#print axioms anchored_output_pos
#print axioms anchored_preserved
#print axioms anchored_output_ne_privateMex
#print axioms anchored_privateMex_drain
#print axioms anchored_youngest_nodup_preserved
#print axioms anchored_youngestCard_recharge
#print axioms lowHoleSaw_exact_credit
#print axioms lowHoleSaw_doubled_recharge_bound

end OBUQ
end ChompLean
