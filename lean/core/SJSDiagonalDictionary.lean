import ChompLean.Proof

/-!
# SJS implementation and initial-state lemmas

Publication audit correction (2026-10-13): this file does NOT prove that
the engine-side `d`-word equals `gameF q q` for every row q. It defines
the SJS list implementation and proves local mex and initial-state facts,
including `dword_zero`, `dword_one`, and `state_q`. The final `#eval` is a
finite computation, not a general equivalence theorem. The original header
incorrectly claimed that the complete dictionary reduction was closed.
Only this documentation was corrected; every proof token is unchanged.

The following is the intended dictionary, whose all-row preservation
and output bridge remain unproved in this file:

    owner  <->  live column           (a column `r` with `q <= f q r`)
    journal of owner `r` at row `q`   <->  the paper's `R (q,r)` set,
                                          truncated below the owner's birth
    this row's earlier awards         <->  the paper's `C (q,r)` set
    award of owner `r` at row `q`     <->  `f q r`
    freeze (award = q, owner erased)  <->  column `r` leaving the mex regime
    newborn's award                   <->  `f q q`

This intended bridge should use the actual-game recurrence and the
non-copy lower bound. Neither a finite matching prefix nor the separate
OBUQ canonical-orbit theorem supplies the missing bridge for these SJS
definitions. See the publication audit for exact admitted statements.
-/

set_option autoImplicit false

namespace ChompLean
namespace SJS

/-! ## 1  Day sets as lists, and the row-relative mex

A journal is a finite set of days, carried as a `List Nat`.  Only membership
matters, never order or multiplicity.  `mexGE q l` is the least day `>= q`
absent from `l`; the engine's `low_zero(J | served)` with `served`
pre-filled to `[0,q)` is exactly this. -/

def hasDay : List Nat -> Nat -> Bool
  | [], _ => false
  | x :: xs, k => (x == k) || hasDay xs k

theorem hasDay_iff (l : List Nat) (k : Nat) : hasDay l k = true <-> k ∈ l := by
  induction l with
  | nil => simp [hasDay]
  | cons x xs ih =>
      constructor
      · intro h
        rcases Bool.or_eq_true_iff.mp h with h1 | h2
        · have : x = k := by simpa using h1
          exact List.mem_cons.mpr (Or.inl this.symm)
        · exact List.mem_cons.mpr (Or.inr (ih.mp h2))
      · intro h
        rcases List.mem_cons.mp h with h1 | h2
        · have : (x == k) = true := by simp [h1]
          exact Bool.or_eq_true_iff.mpr (Or.inl this)
        · exact Bool.or_eq_true_iff.mpr (Or.inr (ih.mpr h2))

theorem not_mem_of_hasDay_false {l : List Nat} {k : Nat}
    (h : hasDay l k = false) : k ∉ l := by
  intro hmem
  have := (hasDay_iff l k).mpr hmem
  rw [h] at this
  exact Bool.noConfusion this

def dayBound : List Nat -> Nat
  | [] => 0
  | x :: xs => Nat.max x (dayBound xs)

theorem le_dayBound {l : List Nat} {x : Nat} (h : x ∈ l) : x <= dayBound l := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
      rcases List.mem_cons.mp h with h1 | h2
      · subst h1; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h2) (Nat.le_max_right _ _)

def mexGEaux (l : List Nat) : Nat -> Nat -> Nat
  | 0, k => k
  | fuel + 1, k => if hasDay l k then mexGEaux l fuel (k + 1) else k

/-- The least day `>= q` that is absent from `l`. -/
def mexGE (q : Nat) (l : List Nat) : Nat := mexGEaux l (dayBound l + 1) q

theorem mexGEaux_ge (l : List Nat) (fuel k : Nat) : k <= mexGEaux l fuel k := by
  induction fuel generalizing k with
  | zero => simp [mexGEaux]
  | succ n ih =>
      by_cases h : hasDay l k
      · have := ih (k + 1)
        simp [mexGEaux, h]
        omega
      · simp [mexGEaux, h]

theorem mexGEaux_not_mem (l : List Nat) (fuel k : Nat)
    (hf : dayBound l < k + fuel) : mexGEaux l fuel k ∉ l := by
  induction fuel generalizing k with
  | zero =>
      intro hmem
      have := le_dayBound hmem
      simp [mexGEaux] at hmem
      have hb := le_dayBound (l := l) (x := k) hmem
      omega
  | succ n ih =>
      by_cases h : hasDay l k
      · have hf' : dayBound l < (k + 1) + n := by omega
        have := ih (k + 1) hf'
        simpa [mexGEaux, h] using this
      · simpa [mexGEaux, h] using not_mem_of_hasDay_false (by simpa using h)

theorem mexGEaux_min (l : List Nat) (fuel k : Nat) :
    ∀ j, k <= j -> j < mexGEaux l fuel k -> j ∈ l := by
  induction fuel generalizing k with
  | zero => intro j h1 h2; simp [mexGEaux] at h2; omega
  | succ n ih =>
      intro j h1 h2
      by_cases h : hasDay l k
      · rw [mexGEaux] at h2
        simp [h] at h2
        by_cases hjk : j = k
        · subst hjk; exact (hasDay_iff l j).mp h
        · exact ih (k + 1) j (by omega) h2
      · rw [mexGEaux] at h2
        simp [h] at h2
        omega

theorem mexGE_ge (q : Nat) (l : List Nat) : q <= mexGE q l := mexGEaux_ge l _ q

theorem mexGE_not_mem (q : Nat) (l : List Nat) : mexGE q l ∉ l :=
  mexGEaux_not_mem l _ q (by omega)

theorem mexGE_min (q : Nat) (l : List Nat) :
    ∀ j, q <= j -> j < mexGE q l -> j ∈ l := mexGEaux_min l _ q

/-- `mexGE` is pinned by its three defining properties. -/
theorem mexGE_unique {q : Nat} {l : List Nat} {v : Nat}
    (h1 : q <= v) (h2 : v ∉ l) (h3 : ∀ j, q <= j -> j < v -> j ∈ l) :
    mexGE q l = v := by
  rcases Nat.lt_trichotomy (mexGE q l) v with hlt | heq | hgt
  · exact absurd (h3 _ (mexGE_ge q l) hlt) (mexGE_not_mem q l)
  · exact heq
  · exact absurd (mexGE_min q l v h1 hgt) h2

/-- Two day lists that agree on every day `>= q`. -/
def AgreeAbove (q : Nat) (l₁ l₂ : List Nat) : Prop :=
  ∀ d, q <= d -> (d ∈ l₁ <-> d ∈ l₂)

theorem AgreeAbove.refl (q : Nat) (l : List Nat) : AgreeAbove q l l :=
  fun _ _ => Iff.rfl

theorem AgreeAbove.symm {q : Nat} {l₁ l₂ : List Nat}
    (h : AgreeAbove q l₁ l₂) : AgreeAbove q l₂ l₁ :=
  fun d hd => (h d hd).symm

theorem AgreeAbove.trans {q : Nat} {l₁ l₂ l₃ : List Nat}
    (h₁ : AgreeAbove q l₁ l₂) (h₂ : AgreeAbove q l₂ l₃) : AgreeAbove q l₁ l₃ :=
  fun d hd => (h₁ d hd).trans (h₂ d hd)

/-- Agreement above `q` survives raising the threshold. -/
theorem AgreeAbove.mono {q q' : Nat} {l₁ l₂ : List Nat}
    (h : AgreeAbove q l₁ l₂) (hq : q <= q') : AgreeAbove q' l₁ l₂ :=
  fun d hd => h d (Nat.le_trans hq hd)

theorem AgreeAbove.cons {q : Nat} {l₁ l₂ : List Nat} (x : Nat)
    (h : AgreeAbove q l₁ l₂) : AgreeAbove q (x :: l₁) (x :: l₂) := by
  intro d hd
  simp only [List.mem_cons]
  exact or_congr Iff.rfl (h d hd)

theorem AgreeAbove.append {q : Nat} {a₁ a₂ b₁ b₂ : List Nat}
    (ha : AgreeAbove q a₁ a₂) (hb : AgreeAbove q b₁ b₂) :
    AgreeAbove q (a₁ ++ b₁) (a₂ ++ b₂) := by
  intro d hd
  simp only [List.mem_append]
  exact or_congr (ha d hd) (hb d hd)

/-- **The truncation principle.**  Only days `>= q` can influence the row-`q`
mex.  This is the `(TRUNC)` law of the campaign, in the only form the
dictionary needs. -/
theorem mexGE_congr {q : Nat} {l₁ l₂ : List Nat} (h : AgreeAbove q l₁ l₂) :
    mexGE q l₁ = mexGE q l₂ := by
  refine mexGE_unique (mexGE_ge q l₂) ?_ ?_
  · intro hmem
    exact (mexGE_not_mem q l₂) ((h _ (mexGE_ge q l₂)).mp hmem)
  · intro j hj hlt
    exact (h j hj).mpr (mexGE_min q l₂ j hj hlt)


/-! ## 2  The Sentinel Journal System

A faithful transcription of `sjs.py` (run `CLAUDE-CFE-20260902-042`, KEY GR):
D1-D4 with the engine's own freeze rule.  A state is a row index together
with the live owners' journals, oldest first.  In a row every owner scans in
age order and books the least day `>= q` that neither it nor an older owner
of this row already holds; an owner whose booked day is exactly `q` is the
freeze index and is erased at the end of the row; the newborn is appended
last and its own award is `d (q)`.

The Python engine pre-fills `served` with `[0,q)` and takes an unrestricted
`low_zero`; `mexGE q` folds that pre-fill into the mex, which is why no
`served` seed appears below. -/

abbrev Journal := List Nat

structure State where
  q : Nat
  J : List Journal

/-- The age-ordered scan of one row: each owner books `mexGE q` of its own
journal together with the days already booked in this row, and keeps it. -/
def scan (q : Nat) : List Journal -> List Nat -> List (Journal × Nat)
  | [], _ => []
  | g :: gs, served =>
      let y := mexGE q (g ++ served)
      (y :: g, y) :: scan q gs (y :: served)

/-- The awards of a row, in age order. -/
def awards (q : Nat) (Js : List Journal) : List Nat :=
  (scan q Js []).map Prod.snd

/-- The youngest owner's journal (`self.J[-1]`). -/
def lastJ : List Journal -> Journal
  | [] => []
  | [g] => g
  | _ :: gs => lastJ gs

/-- `d (q)`: the newborn's award, taken against the youngest owner's
*pre-award* journal and the whole row's bookings (D3). -/
def dOf (s : State) : Nat :=
  mexGE s.q (lastJ s.J ++ awards s.q s.J)

/-- One row of the engine: scan, erase the freeze index, append the newborn
with journal `(Y restricted to days > q) u {d q}`. -/
def step (s : State) : State :=
  { q := s.q + 1
  , J := ((scan s.q s.J []).filter (fun p => !(p.2 == s.q))).map Prod.fst
      ++ [dOf s :: (lastJ s.J).filter (fun x => decide (s.q < x))] }

/-- The game's own seed: at row `0`, one owner with an empty journal (the
engine's diagonal sentinel, which is the row-`0` freeze index). -/
def seed : State := { q := 0, J := [[]] }

def state : Nat -> State
  | 0 => seed
  | n + 1 => step (state n)

/-- **The engine's d-word.** -/
def dword (q : Nat) : Nat := dOf (state q)

-- Sanity: the first terms of OEIS A029900.
-- #eval (List.range 21).map dword
-- [1,3,4,6,8,10,11,13,15,16,18,20,21,24,25,27,28,30,32,34,35]

theorem state_zero : state 0 = { q := 0, J := [[]] } := rfl

theorem state_one : state 1 = { q := 1, J := [[1]] } := rfl

theorem dword_zero : dword 0 = 1 := rfl

theorem dword_one : dword 1 = 3 := rfl

theorem state_q (n : Nat) : (state n).q = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [state, step, ih]

-- Finite #eval execution prints the first 21 engine d-word values below.
-- This is not an all-row gameF equivalence theorem or a kernel-certified
-- equality proof.
/-- info: [1, 3, 4, 6, 8, 10, 11, 13, 15, 16, 18, 20, 21, 24, 25, 27, 28, 30, 32, 34, 35] -/
#guard_msgs in
#eval (List.range 21).map dword

end SJS
end ChompLean

