import ChompLean.Proof
import Std

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean
namespace OBUQ

/-!
# The ordered blocker-union Mealy quotient

Work-ID: `X-OBUQ-GLOBAL-LEAN-AND-CONVOY-001`
Run-ID: `XOGC-20260812-2321-ROOT`

This file formalizes the algebraic active-frontier recurrence from Cycle 3
and its proper ordered blocker-union quotient.  Finite sets are represented
by lists but interpreted extensionally through `MemEq`; duplicates and source
overlap are therefore immaterial.  `queueMex` is the least missing natural
number starting at zero, so terminal service `0` is part of the model.

The frontier transition and the quotient transition are defined separately.
The main results prove decoder equality, one-step semiconjugacy, finite-run
semiconjugacy, and all-horizon future congruence under common forcing.

This is a theorem about the algebraic frontier recurrence.  It does not by
itself identify an arbitrary `gameF` table with a frontier orbit; such a
reconstruction bridge is a separate obligation.
-/

def MemEq (xs ys : List Nat) : Prop :=
  ∀ n, n ∈ xs ↔ n ∈ ys

theorem memEq_refl (xs : List Nat) : MemEq xs xs := by
  intro n
  rfl

theorem memEq_symm {xs ys : List Nat} (h : MemEq xs ys) : MemEq ys xs := by
  intro n
  exact (h n).symm

theorem memEq_trans {xs ys zs : List Nat}
    (hxy : MemEq xs ys) (hyz : MemEq ys zs) : MemEq xs zs := by
  intro n
  exact (hxy n).trans (hyz n)

theorem memEq_append {xs xs' ys ys' : List Nat}
    (hx : MemEq xs xs') (hy : MemEq ys ys') :
    MemEq (xs ++ ys) (xs' ++ ys') := by
  intro n
  simp only [List.mem_append]
  exact or_congr (hx n) (hy n)

def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => max x (listMax xs)

theorem mem_le_listMax {x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    x ≤ listMax xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [listMax]
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem listMax_le_of_mem_le {xs : List Nat} {b : Nat}
    (h : ∀ x, x ∈ xs → x ≤ b) : listMax xs ≤ b := by
  induction xs with
  | nil => simp [listMax]
  | cons x xs ih =>
      simp only [listMax]
      exact (Nat.max_le).2 ⟨h x (by simp), by
        apply ih
        intro y hy
        exact h y (by simp [hy])⟩

theorem listMax_eq_of_memEq {xs ys : List Nat} (h : MemEq xs ys) :
    listMax xs = listMax ys := by
  apply Nat.le_antisymm
  · apply listMax_le_of_mem_le
    intro x hx
    exact mem_le_listMax ((h x).mp hx)
  · apply listMax_le_of_mem_le
    intro y hy
    exact mem_le_listMax ((h y).mpr hy)

def seekMissing (xs : List Nat) (n : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n ∈ xs then seekMissing xs (n + 1) fuel else n

def queueMex (xs : List Nat) : Nat :=
  seekMissing xs 0 (listMax xs + 2)

theorem seekMissing_memEq {xs ys : List Nat} (h : MemEq xs ys)
    (n fuel : Nat) : seekMissing xs n fuel = seekMissing ys n fuel := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
      simp only [seekMissing]
      by_cases hx : n ∈ xs
      · have hy : n ∈ ys := (h n).mp hx
        simp [hx, hy, ih]
      · have hy : n ∉ ys := by
          intro hyn
          exact hx ((h n).mpr hyn)
        simp [hx, hy]

theorem queueMex_memEq {xs ys : List Nat} (h : MemEq xs ys) :
    queueMex xs = queueMex ys := by
  unfold queueMex
  rw [listMax_eq_of_memEq h]
  exact seekMissing_memEq h 0 (listMax ys + 2)

theorem not_mem_of_listMax_lt {xs : List Nat} {n : Nat}
    (h : listMax xs < n) : n ∉ xs := by
  intro hn
  have := mem_le_listMax hn
  omega

theorem seekMissing_spec {xs : List Nat} {n fuel : Nat}
    (hpast : ∀ k, k < n → k ∈ xs)
    (hbound : listMax xs < n + fuel) :
    let m := seekMissing xs n fuel
    m ∉ xs ∧ ∀ k, k < m → k ∈ xs := by
  induction fuel generalizing n with
  | zero =>
      simp only [seekMissing]
      constructor
      · exact not_mem_of_listMax_lt (by simpa using hbound)
      · exact hpast
  | succ fuel ih =>
      simp only [seekMissing]
      by_cases hn : n ∈ xs
      · rw [if_pos hn]
        apply ih
        · intro k hk
          by_cases hkn : k < n
          · exact hpast k hkn
          · have : k = n := by omega
            simpa [this] using hn
        · omega
      · rw [if_neg hn]
        exact ⟨hn, hpast⟩

theorem queueMex_spec (xs : List Nat) :
    queueMex xs ∉ xs ∧ ∀ k, k < queueMex xs → k ∈ xs := by
  unfold queueMex
  apply seekMissing_spec
  · intro k hk
    omega
  · omega

def shiftQueue : List Nat → List Nat
  | [] => []
  | 0 :: xs => shiftQueue xs
  | (x + 1) :: xs => x :: shiftQueue xs

theorem mem_shiftQueue_iff {n : Nat} {xs : List Nat} :
    n ∈ shiftQueue xs ↔ n + 1 ∈ xs := by
  induction xs with
  | nil => simp [shiftQueue]
  | cons x xs ih =>
      cases x with
      | zero => simpa [shiftQueue] using ih
      | succ x =>
          simp [shiftQueue, ih]

def updateQueue (xs : List Nat) (y : Nat) : List Nat :=
  shiftQueue xs ++ if y = 0 then [] else [y - 1]

theorem shiftQueue_memEq {xs ys : List Nat} (h : MemEq xs ys) :
    MemEq (shiftQueue xs) (shiftQueue ys) := by
  intro n
  rw [mem_shiftQueue_iff, mem_shiftQueue_iff]
  exact h (n + 1)

theorem updateQueue_memEq {xs ys : List Nat} (h : MemEq xs ys) (y : Nat) :
    MemEq (updateQueue xs y) (updateQueue ys y) := by
  unfold updateQueue
  apply memEq_append (shiftQueue_memEq h)
  exact memEq_refl _

inductive WordEq : List (List Nat) → List (List Nat) → Prop
  | nil : WordEq [] []
  | cons {q q' : List Nat} {qs qs' : List (List Nat)} :
      MemEq q q' → WordEq qs qs' → WordEq (q :: qs) (q' :: qs')

theorem wordEq_refl (qs : List (List Nat)) : WordEq qs qs := by
  induction qs with
  | nil => exact WordEq.nil
  | cons q qs ih => exact WordEq.cons (memEq_refl q) ih

theorem wordEq_append {as as' bs bs' : List (List Nat)}
    (ha : WordEq as as') (hb : WordEq bs bs') :
    WordEq (as ++ bs) (as' ++ bs') := by
  induction ha with
  | nil => simpa using hb
  | cons hq htail ih =>
      simp only [List.cons_append]
      exact WordEq.cons hq ih

structure ScanResult where
  outputs : List Nat
  survivors : List (List Nat)

def scanQueues (U R : List Nat) : List (List Nat) → ScanResult
  | [] => ⟨[], []⟩
  | q :: qs =>
      let y := queueMex (U ++ (q ++ R))
      let tail := scanQueues U (R ++ [y]) qs
      ⟨y :: tail.outputs,
        if y = 0 then tail.survivors else updateQueue q y :: tail.survivors⟩

theorem scanQueues_congruent {qs qs' : List (List Nat)}
    (hword : WordEq qs qs') (U R : List Nat) :
    (scanQueues U R qs).outputs = (scanQueues U R qs').outputs ∧
      WordEq (scanQueues U R qs).survivors
        (scanQueues U R qs').survivors := by
  induction hword generalizing R with
  | nil =>
      simp [scanQueues]
      exact WordEq.nil
  | @cons q q' qs qs' hq htail ih =>
      have hinput : MemEq (U ++ (q ++ R)) (U ++ (q' ++ R)) :=
        memEq_append (memEq_refl U) (memEq_append hq (memEq_refl R))
      have hy : queueMex (U ++ (q ++ R)) = queueMex (U ++ (q' ++ R)) :=
        queueMex_memEq hinput
      let y := queueMex (U ++ (q ++ R))
      have htail' := ih (R ++ [y])
      have hout :
          (scanQueues U (R ++ [y]) qs).outputs =
            (scanQueues U (R ++ [y]) qs').outputs := htail'.1
      have hsurv :
          WordEq (scanQueues U (R ++ [y]) qs).survivors
            (scanQueues U (R ++ [y]) qs').survivors := htail'.2
      dsimp [y] at hout hsurv
      rw [scanQueues, scanQueues]
      dsimp only
      rw [← hy]
      constructor
      · exact congrArg (fun tail => y :: tail) hout
      · by_cases hz : y = 0
        · have hz' : queueMex (U ++ (q ++ R)) = 0 := by
            simpa [y] using hz
          simp only [hz', ↓reduceIte]
          simpa [hz'] using hsurv
        · have hz' : queueMex (U ++ (q ++ R)) ≠ 0 := by
            simpa [y] using hz
          simp only [hz', ↓reduceIte]
          exact WordEq.cons
            (updateQueue_memEq hq (queueMex (U ++ (q ++ R)))) hsurv

structure QState where
  queues : List (List Nat)
  diagonal : List Nat

def QEq (Q Q' : QState) : Prop :=
  WordEq Q.queues Q'.queues ∧ MemEq Q.diagonal Q'.diagonal

theorem qEq_refl (Q : QState) : QEq Q Q :=
  ⟨wordEq_refl Q.queues, memEq_refl Q.diagonal⟩

theorem wordEq_symm {qs qs' : List (List Nat)} (h : WordEq qs qs') :
    WordEq qs' qs := by
  induction h with
  | nil => exact WordEq.nil
  | cons hq _ht ih => exact WordEq.cons (memEq_symm hq) ih

theorem wordEq_trans {a b c : List (List Nat)}
    (hab : WordEq a b) (hbc : WordEq b c) : WordEq a c := by
  induction hab generalizing c with
  | nil =>
      cases hbc
      exact WordEq.nil
  | cons hq _ht ih =>
      cases hbc with
      | cons hq' ht' => exact WordEq.cons (memEq_trans hq hq') (ih ht')

theorem qEq_symm {Q Q' : QState} (h : QEq Q Q') : QEq Q' Q :=
  ⟨wordEq_symm h.1, memEq_symm h.2⟩

theorem qEq_trans {Q Q' Q'' : QState}
    (h : QEq Q Q') (h' : QEq Q' Q'') : QEq Q Q'' :=
  ⟨wordEq_trans h.1 h'.1, memEq_trans h.2 h'.2⟩

def qOutput (U : List Nat) (Q : QState) : Nat :=
  let scan := scanQueues U [] Q.queues
  queueMex (U ++ (Q.diagonal ++ scan.outputs))

def qStep (U : List Nat) (Q : QState) : QState :=
  let scan := scanQueues U [] Q.queues
  let k := queueMex (U ++ (Q.diagonal ++ scan.outputs))
  let newborn := if k = 0 then [] else [updateQueue Q.diagonal k]
  ⟨scan.survivors ++ newborn, updateQueue Q.diagonal k⟩

theorem qOutput_eq_of_qEq {Q Q' : QState} (h : QEq Q Q') (U : List Nat) :
    qOutput U Q = qOutput U Q' := by
  have hscan := scanQueues_congruent h.1 U []
  unfold qOutput
  dsimp only
  rw [hscan.1]
  apply queueMex_memEq
  exact memEq_append
    (memEq_refl U)
    (memEq_append h.2 (memEq_refl (scanQueues U [] Q'.queues).outputs))

theorem qStep_congruent {Q Q' : QState} (h : QEq Q Q') (U : List Nat) :
    QEq (qStep U Q) (qStep U Q') := by
  have hscan := scanQueues_congruent h.1 U []
  have hk :
      queueMex (U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs)) =
        queueMex (U ++ (Q'.diagonal ++ (scanQueues U [] Q'.queues).outputs)) := by
    rw [hscan.1]
    apply queueMex_memEq
    exact memEq_append
      (memEq_refl U)
      (memEq_append h.2 (memEq_refl (scanQueues U [] Q'.queues).outputs))
  unfold qStep
  dsimp only
  rw [← hk]
  constructor
  · apply wordEq_append hscan.2
    by_cases hz :
        queueMex (U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs)) = 0
    · simpa [hz] using (WordEq.nil : WordEq [] [])
    · simpa [hz] using WordEq.cons
        (updateQueue_memEq h.2
          (queueMex (U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs))))
        WordEq.nil
  · exact updateQueue_memEq h.2
      (queueMex (U ++ (Q.diagonal ++ (scanQueues U [] Q.queues).outputs)))

def qRunOutputs : List (List Nat) → QState → List Nat
  | [], _Q => []
  | U :: Us, Q => qOutput U Q :: qRunOutputs Us (qStep U Q)

theorem qRunOutputs_eq_of_qEq {Q Q' : QState} (h : QEq Q Q')
    (forcing : List (List Nat)) :
    qRunOutputs forcing Q = qRunOutputs forcing Q' := by
  induction forcing generalizing Q Q' with
  | nil => rfl
  | cons U Us ih =>
      simp only [qRunOutputs]
      rw [qOutput_eq_of_qEq h U]
      exact congrArg (fun tail => qOutput U Q' :: tail)
        (ih (qStep_congruent h U))

structure HighRecord where
  age : Nat
  excess : Nat
deriving DecidableEq

structure LiveRecord where
  age : Nat
  column : List Nat
deriving DecidableEq

structure Frontier where
  live : List LiveRecord
  high : List HighRecord

def HighAgesPositive (Z : Frontier) : Prop :=
  ∀ h, h ∈ Z.high → 0 < h.age

def highValues : List HighRecord → List Nat
  | [] => []
  | h :: hs => h.excess :: highValues hs

def olderValues : List HighRecord → Nat → List Nat
  | [], _a => []
  | h :: hs, a =>
      if a < h.age then h.excess :: olderValues hs a else olderValues hs a

def projectLive (H : List HighRecord) (l : LiveRecord) : List Nat :=
  l.column ++ olderValues H l.age

def projectFrontier (Z : Frontier) : QState :=
  ⟨Z.live.map (projectLive Z.high), highValues Z.high⟩

def shiftHigh : List HighRecord → List HighRecord
  | [] => []
  | h :: hs =>
      if h.excess = 0 then shiftHigh hs
      else ⟨h.age + 1, h.excess - 1⟩ :: shiftHigh hs

def updateHigh (H : List HighRecord) (k : Nat) : List HighRecord :=
  shiftHigh H ++ if k = 0 then [] else [⟨1, k - 1⟩]

def updateLive (l : LiveRecord) (y : Nat) : LiveRecord :=
  ⟨l.age + 1, updateQueue l.column y⟩

structure FrontScanResult where
  outputs : List Nat
  survivors : List LiveRecord

def scanFrontier (U : List Nat) (H : List HighRecord) (R : List Nat) :
    List LiveRecord → FrontScanResult
  | [] => ⟨[], []⟩
  | l :: ls =>
      let y := queueMex (U ++ (projectLive H l ++ R))
      let tail := scanFrontier U H (R ++ [y]) ls
      ⟨y :: tail.outputs,
        if y = 0 then tail.survivors else updateLive l y :: tail.survivors⟩

def frontierOutput (U : List Nat) (Z : Frontier) : Nat :=
  let scan := scanFrontier U Z.high [] Z.live
  queueMex (U ++ (highValues Z.high ++ scan.outputs))

def frontierStep (U : List Nat) (Z : Frontier) : Frontier :=
  let scan := scanFrontier U Z.high [] Z.live
  let k := queueMex (U ++ (highValues Z.high ++ scan.outputs))
  let newborn := if k = 0 then [] else [LiveRecord.mk 1 [k - 1]]
  ⟨scan.survivors ++ newborn, updateHigh Z.high k⟩

theorem mem_highValues_iff {n : Nat} {H : List HighRecord} :
    n ∈ highValues H ↔ ∃ h, h ∈ H ∧ n = h.excess := by
  induction H with
  | nil => simp [highValues]
  | cons h H ih =>
      simp only [highValues, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨r, hr, rfl⟩)
        · exact ⟨h, by simp, rfl⟩
        · exact ⟨r, by simp [hr], rfl⟩
      · rintro ⟨r, rfl | hr, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r, hr, rfl⟩

theorem mem_olderValues_iff {n a : Nat} {H : List HighRecord} :
    n ∈ olderValues H a ↔
      ∃ h, h ∈ H ∧ a < h.age ∧ n = h.excess := by
  induction H with
  | nil => simp [olderValues]
  | cons h H ih =>
      simp only [olderValues]
      by_cases ha : a < h.age
      · simp only [ha, ↓reduceIte, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨r, hr, har, rfl⟩)
          · exact ⟨h, by simp, ha, rfl⟩
          · exact ⟨r, by simp [hr], har, rfl⟩
        · rintro ⟨r, rfl | hr, har, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨r, hr, har, rfl⟩
      · simp only [ha, ↓reduceIte, ih]
        constructor
        · rintro ⟨r, hr, har, rfl⟩
          exact ⟨r, by simp [hr], har, rfl⟩
        · rintro ⟨r, hr, har, rfl⟩
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact False.elim (ha har)
          · exact ⟨r, hr, har, rfl⟩

theorem mem_shiftHigh_iff {r : HighRecord} {H : List HighRecord} :
    r ∈ shiftHigh H ↔
      ∃ h, h ∈ H ∧ h.excess ≠ 0 ∧
        r = HighRecord.mk (h.age + 1) (h.excess - 1) := by
  induction H with
  | nil => simp [shiftHigh]
  | cons h H ih =>
      simp only [shiftHigh]
      by_cases hz : h.excess = 0
      · simp only [hz, ↓reduceIte, ih]
        constructor
        · rintro ⟨s, hs, hn, rfl⟩
          exact ⟨s, by simp [hs], hn, rfl⟩
        · rintro ⟨s, hs, hn, rfl⟩
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact False.elim (hn hz)
          · exact ⟨s, hs, hn, rfl⟩
      · simp only [hz, ↓reduceIte, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨s, hs, hn, rfl⟩)
          · exact ⟨h, by simp, hz, rfl⟩
          · exact ⟨s, by simp [hs], hn, rfl⟩
        · rintro ⟨s, rfl | hs, hn, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨s, hs, hn, rfl⟩

theorem highValues_shiftHigh_memEq (H : List HighRecord) :
    MemEq (highValues (shiftHigh H)) (shiftQueue (highValues H)) := by
  intro n
  rw [mem_shiftQueue_iff, mem_highValues_iff, mem_highValues_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases (mem_shiftHigh_iff.mp hr) with ⟨h, hh, hn, rfl⟩
    refine ⟨h, hh, ?_⟩
    dsimp only
    omega
  · rintro ⟨h, hh, heq⟩
    have hn : h.excess ≠ 0 := by omega
    refine ⟨HighRecord.mk (h.age + 1) (h.excess - 1), ?_, ?_⟩
    · exact mem_shiftHigh_iff.mpr ⟨h, hh, hn, rfl⟩
    · dsimp only
      omega

theorem olderValues_shiftHigh_memEq (H : List HighRecord) (a : Nat) :
    MemEq (olderValues (shiftHigh H) (a + 1))
      (shiftQueue (olderValues H a)) := by
  intro n
  rw [mem_shiftQueue_iff, mem_olderValues_iff, mem_olderValues_iff]
  constructor
  · rintro ⟨r, hr, har, rfl⟩
    rcases (mem_shiftHigh_iff.mp hr) with ⟨h, hh, hn, rfl⟩
    dsimp only at har ⊢
    refine ⟨h, hh, by omega, by omega⟩
  · rintro ⟨h, hh, hah, heq⟩
    have hn : h.excess ≠ 0 := by omega
    refine ⟨HighRecord.mk (h.age + 1) (h.excess - 1), ?_, ?_, ?_⟩
    · exact mem_shiftHigh_iff.mpr ⟨h, hh, hn, rfl⟩
    · dsimp only
      omega
    · dsimp only
      omega

theorem mem_updateHigh_iff {r : HighRecord} {H : List HighRecord} {k : Nat} :
    r ∈ updateHigh H k ↔
      r ∈ shiftHigh H ∨ (k ≠ 0 ∧ r = HighRecord.mk 1 (k - 1)) := by
  unfold updateHigh
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

theorem olderValues_updateHigh_memEq (H : List HighRecord) (a k : Nat) :
    MemEq (olderValues (updateHigh H k) (a + 1))
      (shiftQueue (olderValues H a)) := by
  intro n
  rw [mem_olderValues_iff, mem_shiftQueue_iff, mem_olderValues_iff]
  constructor
  · rintro ⟨r, hr, har, rfl⟩
    rcases (mem_updateHigh_iff.mp hr) with hr | ⟨_hk, rfl⟩
    · rcases (mem_shiftHigh_iff.mp hr) with ⟨h, hh, hn, rfl⟩
      dsimp only at har ⊢
      exact ⟨h, hh, by omega, by omega⟩
    · dsimp only at har
      omega
  · rintro ⟨h, hh, hah, heq⟩
    have hn : h.excess ≠ 0 := by omega
    let r := HighRecord.mk (h.age + 1) (h.excess - 1)
    refine ⟨r, ?_, ?_, ?_⟩
    · apply mem_updateHigh_iff.mpr
      exact Or.inl (mem_shiftHigh_iff.mpr ⟨h, hh, hn, rfl⟩)
    · dsimp [r]
      omega
    · dsimp [r]
      omega

theorem highValues_updateHigh_memEq (H : List HighRecord) (k : Nat) :
    MemEq (highValues (updateHigh H k)) (updateQueue (highValues H) k) := by
  intro n
  rw [mem_highValues_iff]
  unfold updateQueue
  simp only [List.mem_append]
  rw [mem_shiftQueue_iff]
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : r ∈ shiftHigh H := by
        exact (mem_updateHigh_iff.mp hr).resolve_right (by
          rintro ⟨hkne, _⟩
          exact hkne rfl)
      rcases (mem_shiftHigh_iff.mp hr') with ⟨h, hh, hn, rfl⟩
      apply mem_highValues_iff.mpr
      refine ⟨h, hh, ?_⟩
      dsimp only
      omega
    · intro hn
      rcases mem_highValues_iff.mp hn with ⟨h, hh, heq⟩
      have hne : h.excess ≠ 0 := by omega
      refine ⟨HighRecord.mk (h.age + 1) (h.excess - 1), ?_, ?_⟩
      exact mem_updateHigh_iff.mpr
        (Or.inl (mem_shiftHigh_iff.mpr ⟨h, hh, hne, rfl⟩))
      · dsimp only
        omega
  · simp only [hk, ↓reduceIte, List.mem_singleton]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rcases (mem_updateHigh_iff.mp hr) with hr | ⟨_hk, rfl⟩
      · left
        rcases (mem_shiftHigh_iff.mp hr) with ⟨h, hh, hn, rfl⟩
        apply mem_highValues_iff.mpr
        refine ⟨h, hh, ?_⟩
        dsimp only
        omega
      · right
        rfl
    · rintro (hn | heq)
      · rcases mem_highValues_iff.mp hn with ⟨h, hh, hval⟩
        have hne : h.excess ≠ 0 := by omega
        refine ⟨HighRecord.mk (h.age + 1) (h.excess - 1), ?_, ?_⟩
        exact mem_updateHigh_iff.mpr
          (Or.inl (mem_shiftHigh_iff.mpr ⟨h, hh, hne, rfl⟩))
        · dsimp only
          omega
      · refine ⟨HighRecord.mk 1 (k - 1), ?_, ?_⟩
        exact mem_updateHigh_iff.mpr (Or.inr ⟨hk, rfl⟩)
        · exact heq

theorem mem_updateQueue_iff {n y : Nat} {xs : List Nat} :
    n ∈ updateQueue xs y ↔
      n + 1 ∈ xs ∨ (y ≠ 0 ∧ n = y - 1) := by
  unfold updateQueue
  rw [List.mem_append, mem_shiftQueue_iff]
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy]

theorem project_updated_live_memEq (H : List HighRecord)
    (l : LiveRecord) (y k : Nat) :
    MemEq (projectLive (updateHigh H k) (updateLive l y))
      (updateQueue (projectLive H l) y) := by
  intro n
  rw [mem_updateQueue_iff]
  unfold projectLive updateLive
  dsimp only
  simp only [List.mem_append]
  rw [mem_updateQueue_iff]
  have hold := olderValues_updateHigh_memEq H l.age k n
  rw [mem_shiftQueue_iff] at hold
  constructor
  · rintro ((hcol | hins) | holdNew)
    · exact Or.inl (Or.inl hcol)
    · exact Or.inr hins
    · exact Or.inl (Or.inr ((hold).mp holdNew))
  · rintro (hsrc | hins)
    · rcases hsrc with hcol | holdOld
      · exact Or.inl (Or.inl hcol)
      · exact Or.inr ((hold).mpr holdOld)
    · exact Or.inl (Or.inr hins)

theorem highAgesPositive_updateHigh {H : List HighRecord} {k : Nat} :
    ∀ r, r ∈ updateHigh H k → 0 < r.age := by
  intro r hr
  rcases (mem_updateHigh_iff.mp hr) with hr | ⟨_hk, rfl⟩
  · rcases (mem_shiftHigh_iff.mp hr) with ⟨h, hh, _hne, rfl⟩
    dsimp only
    omega
  · dsimp only
    omega

theorem olderValues_updateHigh_one_memEq (H : List HighRecord) (k : Nat)
    (hpos : ∀ h, h ∈ H → 0 < h.age) :
    MemEq (olderValues (updateHigh H k) 1) (shiftQueue (highValues H)) := by
  intro n
  rw [mem_olderValues_iff, mem_shiftQueue_iff, mem_highValues_iff]
  constructor
  · rintro ⟨r, hr, har, rfl⟩
    rcases (mem_updateHigh_iff.mp hr) with hr | ⟨_hk, rfl⟩
    · rcases (mem_shiftHigh_iff.mp hr) with ⟨h, hh, hn, rfl⟩
      refine ⟨h, hh, ?_⟩
      dsimp only
      omega
    · dsimp only at har
      omega
  · rintro ⟨h, hh, heq⟩
    have hn : h.excess ≠ 0 := by omega
    let r := HighRecord.mk (h.age + 1) (h.excess - 1)
    refine ⟨r, ?_, ?_, ?_⟩
    · exact mem_updateHigh_iff.mpr
        (Or.inl (mem_shiftHigh_iff.mpr ⟨h, hh, hn, rfl⟩))
    · dsimp [r]
      exact Nat.succ_lt_succ (hpos h hh)
    · dsimp [r]
      omega

theorem project_newborn_memEq (H : List HighRecord) (k : Nat)
    (hpos : ∀ h, h ∈ H → 0 < h.age) (hk : k ≠ 0) :
    MemEq
      (projectLive (updateHigh H k) (LiveRecord.mk 1 [k - 1]))
      (updateQueue (highValues H) k) := by
  intro n
  unfold projectLive
  dsimp only
  rw [mem_updateQueue_iff]
  simp only [List.mem_append, List.mem_singleton]
  have hold := olderValues_updateHigh_one_memEq H k hpos n
  rw [mem_shiftQueue_iff] at hold
  constructor
  · rintro (heq | holdNew)
    · exact Or.inr ⟨hk, heq⟩
    · exact Or.inl (hold.mp holdNew)
  · rintro (holdOld | ⟨_hk, heq⟩)
    · exact Or.inr (hold.mpr holdOld)
    · exact Or.inl heq

theorem scanFrontier_project (U : List Nat) (H : List HighRecord) (R : List Nat)
    (ls : List LiveRecord)
    (k : Nat) :
    (scanFrontier U H R ls).outputs =
        (scanQueues U R (ls.map (projectLive H))).outputs ∧
      WordEq
        ((scanFrontier U H R ls).survivors.map
          (projectLive (updateHigh H k)))
        (scanQueues U R (ls.map (projectLive H))).survivors := by
  induction ls generalizing R with
  | nil =>
      simp [scanFrontier, scanQueues]
      exact WordEq.nil
  | cons l ls ih =>
      let y := queueMex (U ++ (projectLive H l ++ R))
      have htail := ih (R ++ [y])
      rw [scanFrontier, List.map, scanQueues]
      dsimp only
      constructor
      · exact congrArg (fun tail => y :: tail) htail.1
      · by_cases hy : y = 0
        · have hy' : queueMex (U ++ (projectLive H l ++ R)) = 0 := by
            simpa [y] using hy
          simp only [hy', ↓reduceIte]
          simpa [y, hy'] using htail.2
        · have hy' : queueMex (U ++ (projectLive H l ++ R)) ≠ 0 := by
            simpa [y] using hy
          simp only [hy', ↓reduceIte, List.map]
          apply WordEq.cons
          · exact project_updated_live_memEq H l y k
          · simpa [y] using htail.2

theorem frontierOutput_eq_qOutput (U : List Nat) (Z : Frontier) :
    frontierOutput U Z = qOutput U (projectFrontier Z) := by
  have hscan := scanFrontier_project U Z.high [] Z.live 0
  unfold frontierOutput qOutput projectFrontier
  dsimp only
  rw [hscan.1]

theorem frontierProject_step_qEq (U : List Nat) (Z : Frontier)
    (hpos : HighAgesPositive Z) :
    QEq (projectFrontier (frontierStep U Z))
      (qStep U (projectFrontier Z)) := by
  let scan := scanFrontier U Z.high [] Z.live
  let qscan := scanQueues U [] (Z.live.map (projectLive Z.high))
  let k := queueMex (U ++ (highValues Z.high ++ scan.outputs))
  have hscan := scanFrontier_project U Z.high [] Z.live k
  have hk :
      k = queueMex (U ++ (highValues Z.high ++ qscan.outputs)) := by
    dsimp [k, scan, qscan]
    rw [hscan.1]
  unfold frontierStep projectFrontier qStep
  dsimp only
  have hk0 :
      queueMex (U ++ (highValues Z.high ++ (scanFrontier U Z.high [] Z.live).outputs)) = k := by
    rfl
  have hk1 :
      queueMex (U ++ (highValues Z.high ++
        (scanQueues U [] (List.map (projectLive Z.high) Z.live)).outputs)) = k := by
    exact hk.symm
  rw [hk0, hk1]
  constructor
  · rw [List.map_append]
    apply wordEq_append
    · exact hscan.2
    · by_cases hk0 : k = 0
      · simpa [hk0] using (WordEq.nil : WordEq [] [])
      · simp only [hk0, ↓reduceIte, List.map]
        exact WordEq.cons
          (project_newborn_memEq Z.high k hpos hk0) WordEq.nil
  · exact highValues_updateHigh_memEq Z.high k

theorem highAgesPositive_frontierStep (U : List Nat) (Z : Frontier) :
    HighAgesPositive (frontierStep U Z) := by
  intro r hr
  unfold frontierStep at hr
  dsimp only at hr
  exact highAgesPositive_updateHigh r hr

structure FrontierRunResult where
  outputs : List Nat
  state : Frontier

def frontierRun : List (List Nat) → Frontier → FrontierRunResult
  | [], Z => ⟨[], Z⟩
  | U :: Us, Z =>
      let tail := frontierRun Us (frontierStep U Z)
      ⟨frontierOutput U Z :: tail.outputs, tail.state⟩

structure QRunResult where
  outputs : List Nat
  state : QState

def qRun : List (List Nat) → QState → QRunResult
  | [], Q => ⟨[], Q⟩
  | U :: Us, Q =>
      let tail := qRun Us (qStep U Q)
      ⟨qOutput U Q :: tail.outputs, tail.state⟩

theorem qRun_congruent (forcing : List (List Nat)) {Q Q' : QState}
    (h : QEq Q Q') :
    (qRun forcing Q).outputs = (qRun forcing Q').outputs ∧
      QEq (qRun forcing Q).state (qRun forcing Q').state := by
  induction forcing generalizing Q Q' with
  | nil =>
      simp [qRun]
      exact h
  | cons U Us ih =>
      simp only [qRun]
      have htail := ih (qStep_congruent h U)
      constructor
      · rw [qOutput_eq_of_qEq h U]
        exact congrArg (fun tail => qOutput U Q' :: tail) htail.1
      · exact htail.2

theorem frontierRun_project (forcing : List (List Nat)) (Z : Frontier)
    (hpos : HighAgesPositive Z) :
    (frontierRun forcing Z).outputs =
        (qRun forcing (projectFrontier Z)).outputs ∧
      QEq (projectFrontier (frontierRun forcing Z).state)
        (qRun forcing (projectFrontier Z)).state := by
  induction forcing generalizing Z with
  | nil =>
      simp [frontierRun, qRun]
      exact qEq_refl (projectFrontier Z)
  | cons U Us ih =>
      have hstep := frontierProject_step_qEq U Z hpos
      have hnext := ih (Z := frontierStep U Z)
        (highAgesPositive_frontierStep U Z)
      have hqrun :
          (qRun Us (qStep U (projectFrontier Z))).outputs =
              (qRun Us (projectFrontier (frontierStep U Z))).outputs ∧
            QEq (qRun Us (qStep U (projectFrontier Z))).state
              (qRun Us (projectFrontier (frontierStep U Z))).state := by
        exact qRun_congruent Us (qEq_symm hstep)
      simp only [frontierRun, qRun]
      constructor
      · rw [frontierOutput_eq_qOutput]
        exact congrArg (fun tail => qOutput U (projectFrontier Z) :: tail)
          (hnext.1.trans hqrun.1.symm)
      · exact qEq_trans hnext.2 (qEq_symm hqrun.2)

theorem frontier_future_congruence {Z W : Frontier}
    (hZ : HighAgesPositive Z) (hW : HighAgesPositive W)
    (hproj : QEq (projectFrontier Z) (projectFrontier W))
    (forcing : List (List Nat)) :
    (frontierRun forcing Z).outputs = (frontierRun forcing W).outputs ∧
      QEq (projectFrontier (frontierRun forcing Z).state)
        (projectFrontier (frontierRun forcing W).state) := by
  have hZrun := frontierRun_project forcing Z hZ
  have hWrun := frontierRun_project forcing W hW
  have hq := qRun_congruent forcing hproj
  constructor
  · exact hZrun.1.trans (hq.1.trans hWrun.1.symm)
  · exact qEq_trans hZrun.2 (qEq_trans hq.2 (qEq_symm hWrun.2))

#print axioms queueMex_spec
#print axioms qStep_congruent
#print axioms qRunOutputs_eq_of_qEq
#print axioms project_updated_live_memEq
#print axioms project_newborn_memEq
#print axioms frontierOutput_eq_qOutput
#print axioms frontierProject_step_qEq
#print axioms frontierRun_project
#print axioms frontier_future_congruence

end OBUQ
end ChompLean
