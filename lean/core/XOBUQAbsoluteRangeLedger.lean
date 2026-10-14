import XOBUQAnchoredOrbitSawtooth

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean
namespace OBUQ

/-!
# Absolute diagonal-range ledger for an autonomous anchored orbit

Work-ID: `X-OBUQ-GLOBAL-LEAN-AND-CONVOY-001`
Run-ID: `XOGC-20260812-2321-ROOT`

The relative diagonal queue at time `n` is decoded into its absolute target
labels.  This identifies recharge rows with permanent omissions from the
initial-and-produced diagonal range and rewrites the quadratic recharge bound
as an honest finite hole-count bound.  No gameF reconstruction or asymptotic
claim is made here.
-/

def diagonalTarget (Q0 : QState) (n : Nat) : Nat :=
  n + qOutput [] (autonomousOrbit Q0 n)

def absoluteTargetsBefore (Q0 : QState) : Nat → List Nat
  | 0 => Q0.diagonal
  | n + 1 => absoluteTargetsBefore Q0 n ++ [diagonalTarget Q0 n]

def AbsoluteDiagonalTarget (Q0 : QState) (t : Nat) : Prop :=
  t ∈ Q0.diagonal ∨ ∃ i, diagonalTarget Q0 i = t

theorem diagonalTarget_gt_index {Q0 : QState} (hA : Anchored Q0)
    (n : Nat) : n < diagonalTarget Q0 n := by
  unfold diagonalTarget
  have hp := anchored_output_pos (autonomousOrbit_anchored hA n) []
  omega

theorem orbitDiagonal_mem_iff_absoluteTargetBefore {Q0 : QState} : ∀ n h,
    h ∈ (autonomousOrbit Q0 n).diagonal ↔
      n + h ∈ absoluteTargetsBefore Q0 n := by
  intro n
  induction n with
  | zero =>
      intro h
      simp [autonomousOrbit, absoluteTargetsBefore]
  | succ n ih =>
      intro h
      rw [autonomousOrbit]
      change
        (h ∈ updateQueue (autonomousOrbit Q0 n).diagonal
            (qOutput [] (autonomousOrbit Q0 n)) ↔ _)
      rw [mem_updateQueue_iff]
      rw [ih (h + 1)]
      simp only [absoluteTargetsBefore, List.mem_append,
        List.mem_singleton]
      constructor
      · intro hs
        rcases hs with hold | hnew
        · left
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hold
        · right
          rcases hnew with ⟨_, heq⟩
          unfold diagonalTarget
          omega
      · intro hs
        rcases hs with hold | hnew
        · left
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hold
        · right
          have hk : qOutput [] (autonomousOrbit Q0 n) ≠ 0 := by
            unfold diagonalTarget at hnew
            omega
          refine ⟨hk, ?_⟩
          unfold diagonalTarget at hnew
          omega

theorem mem_absoluteTargetsBefore_iff {Q0 : QState} : ∀ n t,
    t ∈ absoluteTargetsBefore Q0 n ↔
      t ∈ Q0.diagonal ∨
        ∃ i, i < n ∧ diagonalTarget Q0 i = t := by
  intro n
  induction n with
  | zero =>
      intro t
      simp [absoluteTargetsBefore]
  | succ n ih =>
      intro t
      rw [absoluteTargetsBefore]
      simp only [List.mem_append, List.mem_singleton, ih t]
      constructor
      · intro hs
        rcases hs with hold | hlast
        · rcases hold with hinit | hprev
          · exact Or.inl hinit
          · rcases hprev with ⟨i, hi, heq⟩
            exact Or.inr ⟨i, by omega, heq⟩
        · exact Or.inr ⟨n, by omega, hlast.symm⟩
      · intro hs
        rcases hs with hinit | hout
        · exact Or.inl (Or.inl hinit)
        · rcases hout with ⟨i, hi, heq⟩
          by_cases hlt : i < n
          · exact Or.inl (Or.inr ⟨i, hlt, heq⟩)
          · have hieq : i = n := by omega
            subst i
            exact Or.inr heq.symm

theorem mem_absoluteTargetsBefore_clock_iff_fullRange {Q0 : QState}
    (hA : Anchored Q0) (n : Nat) :
    n ∈ absoluteTargetsBefore Q0 n ↔ AbsoluteDiagonalTarget Q0 n := by
  rw [mem_absoluteTargetsBefore_iff]
  unfold AbsoluteDiagonalTarget
  constructor
  · intro hs
    rcases hs with hinit | hout
    · exact Or.inl hinit
    · rcases hout with ⟨i, _, heq⟩
      exact Or.inr ⟨i, heq⟩
  · intro hs
    rcases hs with hinit | hout
    · exact Or.inl hinit
    · rcases hout with ⟨i, heq⟩
      right
      refine ⟨i, ?_, heq⟩
      have hgt := diagonalTarget_gt_index hA i
      omega

theorem diagonalTarget_not_mem_before {Q0 : QState} (n : Nat) :
    diagonalTarget Q0 n ∉ absoluteTargetsBefore Q0 n := by
  intro hmem
  have hledger := orbitDiagonal_mem_iff_absoluteTargetBefore (Q0 := Q0) n
    (qOutput [] (autonomousOrbit Q0 n))
  have hdiag :
      qOutput [] (autonomousOrbit Q0 n) ∈
        (autonomousOrbit Q0 n).diagonal := by
    apply hledger.mpr
    simpa [diagonalTarget]
  exact qOutput_absent_diagonal [] hdiag

theorem diagonalTarget_injective {Q0 : QState} :
    Function.Injective (diagonalTarget Q0) := by
  intro i j heq
  by_cases hij : i < j
  · have hmem : diagonalTarget Q0 i ∈ absoluteTargetsBefore Q0 j :=
      (mem_absoluteTargetsBefore_iff j _).mpr
        (Or.inr ⟨i, hij, rfl⟩)
    have hnot := diagonalTarget_not_mem_before (Q0 := Q0) j
    exact False.elim (hnot (by simpa [heq] using hmem))
  · by_cases hji : j < i
    · have hmem : diagonalTarget Q0 j ∈ absoluteTargetsBefore Q0 i :=
        (mem_absoluteTargetsBefore_iff i _).mpr
          (Or.inr ⟨j, hji, rfl⟩)
      have hnot := diagonalTarget_not_mem_before (Q0 := Q0) i
      exact False.elim (hnot (by simpa [heq] using hmem))
    · omega

theorem diagonalTarget_not_initial {Q0 : QState} (n : Nat) :
    diagonalTarget Q0 n ∉ Q0.diagonal := by
  intro hinit
  apply diagonalTarget_not_mem_before (Q0 := Q0) n
  exact (mem_absoluteTargetsBefore_iff n _).mpr (Or.inl hinit)

theorem absoluteTargetsBefore_nodup {Q0 : QState}
    (hN : Q0.diagonal.Nodup) :
    ∀ n, (absoluteTargetsBefore Q0 n).Nodup := by
  intro n
  induction n with
  | zero => simpa [absoluteTargetsBefore] using hN
  | succ n ih =>
      rw [absoluteTargetsBefore, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact fun heq =>
        diagonalTarget_not_mem_before (Q0 := Q0) n (heq ▸ ha)

theorem queueMex_eq_zero_iff_zero_absent (G : List Nat) :
    queueMex G = 0 ↔ 0 ∉ G := by
  constructor
  · intro hm hmem
    exact (queueMex_spec G).1 (by simpa [hm] using hmem)
  · intro hnot
    apply queueMex_eq_of_spec hnot
    intro k hk
    omega

def absoluteHoleBit (Q0 : QState) (n : Nat) : Nat :=
  if n ∈ absoluteTargetsBefore Q0 n then 0 else 1

def absoluteHoleCount (Q0 : QState) : Nat → Nat
  | 0 => 0
  | n + 1 => absoluteHoleCount Q0 n + absoluteHoleBit Q0 n

theorem orbitRecharge_eq_absoluteHoleBit {Q0 : QState} (n : Nat) :
    orbitRecharge Q0 n = absoluteHoleBit Q0 n := by
  have hledger := orbitDiagonal_mem_iff_absoluteTargetBefore (Q0 := Q0) n 0
  unfold orbitRecharge orbitLow absoluteHoleBit
  by_cases htarget : n ∈ absoluteTargetsBefore Q0 n
  · have hmem : 0 ∈ (autonomousOrbit Q0 n).diagonal :=
      hledger.mpr (by simpa using htarget)
    have hmex :
        queueMex (autonomousOrbit Q0 n).diagonal ≠ 0 := by
      intro heq
      exact (queueMex_eq_zero_iff_zero_absent _).mp heq hmem
    simp [htarget, hmex]
  · have hnot : 0 ∉ (autonomousOrbit Q0 n).diagonal := by
      intro hmem
      exact htarget (by simpa using hledger.mp hmem)
    have hmex : queueMex (autonomousOrbit Q0 n).diagonal = 0 :=
      (queueMex_eq_zero_iff_zero_absent _).mpr hnot
    simp [htarget, hmex]

theorem rechargeCount_eq_absoluteHoleCount {Q0 : QState} : ∀ N,
    rechargeCount (orbitRecharge Q0) N = absoluteHoleCount Q0 N := by
  intro N
  induction N with
  | zero => simp [rechargeCount, absoluteHoleCount]
  | succ N ih =>
      rw [rechargeCount, absoluteHoleCount, ih,
        orbitRecharge_eq_absoluteHoleBit N]

theorem absoluteHoleBit_eq_one_iff {Q0 : QState}
    (hA : Anchored Q0) (n : Nat) :
    absoluteHoleBit Q0 n = 1 ↔ ¬ AbsoluteDiagonalTarget Q0 n := by
  have hclock := mem_absoluteTargetsBefore_clock_iff_fullRange hA n
  by_cases htarget : n ∈ absoluteTargetsBefore Q0 n
  · have hrange : AbsoluteDiagonalTarget Q0 n := hclock.mp htarget
    simp [absoluteHoleBit, htarget, hrange]
  · have hrange : ¬ AbsoluteDiagonalTarget Q0 n := by
      intro hfull
      exact htarget (hclock.mpr hfull)
    simp [absoluteHoleBit, htarget, hrange]

theorem autonomousOrbit_absoluteHole_doubled_bound {Q0 : QState}
    (hA : Anchored Q0) (hN : Q0.diagonal.Nodup) (N : Nat) :
    2 * N ≤
      2 * absoluteHoleCount Q0 N +
        2 * (absoluteHoleCount Q0 N + 1) * Q0.diagonal.length +
          absoluteHoleCount Q0 N *
            (absoluteHoleCount Q0 N + 1) := by
  have hbound := autonomousOrbit_doubled_recharge_bound hA hN N
  rw [rechargeCount_eq_absoluteHoleCount (Q0 := Q0) N] at hbound
  exact hbound

#print axioms orbitDiagonal_mem_iff_absoluteTargetBefore
#print axioms mem_absoluteTargetsBefore_clock_iff_fullRange
#print axioms diagonalTarget_injective
#print axioms absoluteTargetsBefore_nodup
#print axioms orbitRecharge_eq_absoluteHoleBit
#print axioms rechargeCount_eq_absoluteHoleCount
#print axioms absoluteHoleBit_eq_one_iff
#print axioms autonomousOrbit_absoluteHole_doubled_bound

end OBUQ
end ChompLean
