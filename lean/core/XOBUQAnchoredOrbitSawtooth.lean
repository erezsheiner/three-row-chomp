import XOBUQYoungestLowHole

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean
namespace OBUQ

/-!
# Autonomous anchored orbit to the low-hole sawtooth

Work-ID: `X-OBUQ-GLOBAL-LEAN-AND-CONVOY-001`
Run-ID: `XOGC-20260812-2321-ROOT`

This file composes the local anchored-youngest laws with the abstract
integer sawtooth theorem.  It concerns autonomous quotient states only.
It assumes neither a reconstruction from gameF nor an asymptotic library.
-/

theorem interval_length_le_of_nodup
    {base width : Nat} {G : List Nat}
    (hG : G.Nodup)
    (hmem : ∀ k, k < width → base + k ∈ G) :
    width ≤ G.length := by
  induction width generalizing base G with
  | zero => omega
  | succ width ih =>
      have hbase : base ∈ G := by
        simpa using hmem 0 (by omega)
      have hG' : (G.erase base).Nodup := hG.erase base
      have hmem' :
          ∀ k, k < width → (base + 1) + k ∈ G.erase base := by
        intro k hk
        apply (List.Nodup.mem_erase_iff hG).mpr
        constructor
        · omega
        · have hold := hmem (k + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hold
      have hsmall := ih hG' hmem'
      have hlen := List.length_erase_of_mem hbase
      have hpos := List.length_pos_of_mem hbase
      omega

theorem queueMex_le_length_of_nodup {G : List Nat} (hG : G.Nodup) :
    queueMex G ≤ G.length := by
  apply interval_length_le_of_nodup (base := 0) hG
  intro k hk
  simpa using (queueMex_spec G).2 k hk

def autonomousOrbit (Q0 : QState) : Nat → QState
  | 0 => Q0
  | n + 1 => qStep [] (autonomousOrbit Q0 n)

def orbitLow (Q0 : QState) (n : Nat) : Nat :=
  queueMex (autonomousOrbit Q0 n).diagonal

def orbitSize (Q0 : QState) (n : Nat) : Nat :=
  (autonomousOrbit Q0 n).diagonal.length

def orbitRecharge (Q0 : QState) (n : Nat) : Nat :=
  if orbitLow Q0 n = 0 then 1 else 0

theorem autonomousOrbit_anchored {Q0 : QState} (hA : Anchored Q0) :
    ∀ n, Anchored (autonomousOrbit Q0 n) := by
  intro n
  induction n with
  | zero => simpa [autonomousOrbit] using hA
  | succ n ih =>
      simpa [autonomousOrbit] using anchored_preserved ih []

theorem autonomousOrbit_diagonal_nodup {Q0 : QState}
    (hN : Q0.diagonal.Nodup) :
    ∀ n, (autonomousOrbit Q0 n).diagonal.Nodup := by
  intro n
  induction n with
  | zero => simpa [autonomousOrbit] using hN
  | succ n ih =>
      simpa [autonomousOrbit] using
        anchored_youngest_nodup_preserved ih []

theorem autonomousOrbit_isLowHoleSaw {Q0 : QState}
    (hA : Anchored Q0) (hN : Q0.diagonal.Nodup) :
    LowHoleSaw
      (orbitLow Q0)
      (orbitSize Q0)
      (orbitRecharge Q0)
      Q0.diagonal.length := by
  constructor
  · rfl
  · intro n
    unfold orbitRecharge
    by_cases hz : orbitLow Q0 n = 0
    · simp [hz]
    · simp [hz]
  · intro n
    have hstep := anchored_youngestCard_recharge
      (autonomousOrbit_anchored hA n)
      (autonomousOrbit_diagonal_nodup hN n)
      ([] : List Nat)
    simpa [orbitSize, orbitLow, orbitRecharge, autonomousOrbit] using hstep
  · intro n
    unfold orbitLow orbitSize
    exact queueMex_le_length_of_nodup
      (autonomousOrbit_diagonal_nodup hN n)
  · intro n hc
    unfold orbitRecharge at hc
    by_cases hz : orbitLow Q0 n = 0
    · simp [hz] at hc
    · exact Nat.pos_of_ne_zero hz
  · intro n hc
    have hpos : 0 < orbitLow Q0 n := by
      unfold orbitRecharge at hc
      by_cases hz : orbitLow Q0 n = 0
      · simp [hz] at hc
      · exact Nat.pos_of_ne_zero hz
    have hdrain := anchored_privateMex_drain
      (autonomousOrbit_anchored hA n)
      ([] : List Nat)
      (by simpa [orbitLow] using hpos)
    unfold orbitLow at hpos ⊢
    rw [autonomousOrbit]
    rw [hdrain]
    omega

theorem autonomousOrbit_exact_credit {Q0 : QState}
    (hA : Anchored Q0) (hN : Q0.diagonal.Nodup) (N : Nat) :
    2 * noRechargeCount (orbitRecharge Q0) N +
        2 * orbitLow Q0 N ≤
      2 * (rechargeCount (orbitRecharge Q0) N + 1) *
          Q0.diagonal.length +
        rechargeCount (orbitRecharge Q0) N *
          (rechargeCount (orbitRecharge Q0) N + 1) := by
  exact lowHoleSaw_exact_credit
    (autonomousOrbit_isLowHoleSaw hA hN) N

theorem autonomousOrbit_doubled_recharge_bound {Q0 : QState}
    (hA : Anchored Q0) (hN : Q0.diagonal.Nodup) (N : Nat) :
    2 * N ≤
      2 * rechargeCount (orbitRecharge Q0) N +
        2 * (rechargeCount (orbitRecharge Q0) N + 1) *
          Q0.diagonal.length +
        rechargeCount (orbitRecharge Q0) N *
          (rechargeCount (orbitRecharge Q0) N + 1) := by
  exact lowHoleSaw_doubled_recharge_bound
    (autonomousOrbit_isLowHoleSaw hA hN) N

#print axioms queueMex_le_length_of_nodup
#print axioms autonomousOrbit_anchored
#print axioms autonomousOrbit_diagonal_nodup
#print axioms autonomousOrbit_isLowHoleSaw
#print axioms autonomousOrbit_exact_credit
#print axioms autonomousOrbit_doubled_recharge_bound

end OBUQ
end ChompLean
