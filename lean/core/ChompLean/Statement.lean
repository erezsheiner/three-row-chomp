import Std

set_option autoImplicit false

namespace ChompLean

/-!
This is the mathematical interface file for the formalization.

To audit the theorem, read this file from top to bottom and check that these
definitions match the intended game. The long proof is deliberately kept in
the other files.

The definitions below are the formal model of three-row Chomp used by the
proof. A position `[p,q,r]` has nonincreasing row lengths `p >= q >= r`.
A legal move cuts one of the three rows and all rows below it. Cutting the
first row to `0` is not listed as a legal move, because that is the poisoned
move and is losing.

Reader guide:

* `Pos` is a three-row board state.
* `Move` is the legal non-poison move relation.
* `IsP` is the standard recursive definition of a previous-player win.
* `rectanglePos n` is the starting rectangle `[n,n,n]`.
* `UniqueActualWinningTargetClaim` says exactly: for every `n > 0`, there is
  exactly one legal move from `[n,n,n]` whose target is a `P`-position.

The proof file later checks:

```
ChompLean.uniqueActualWinningTarget_checked :
  ChompLean.UniqueActualWinningTargetClaim
```
-/

/--
A three-row Chomp position.

The fields `p`, `q`, and `r` are the row lengths, written in nonincreasing
order. The proof fields `hq` and `hr` are included only so Lean knows that
every `Pos` is a well-formed board.
-/
structure Pos where
  /-- Top-row length. -/
  p : Nat
  /-- Middle-row length. -/
  q : Nat
  /-- Bottom-row length. -/
  r : Nat
  /-- Well-formedness: the middle row is no longer than the top row. -/
  hq : q <= p
  /-- Well-formedness: the bottom row is no longer than the middle row. -/
  hr : r <= q

namespace Pos

/--
Lean bookkeeping: every legal move strictly decreases this number, so recursive
definitions over the game tree are accepted as terminating.
-/
def size (x : Pos) : Nat :=
  x.p + x.q + x.r

/--
Lean bookkeeping for `firstCut`: if `r <= q`, then after cutting both by the
same top-row bound `a`, the new bottom row is still no longer than the new
middle row. This lemma is not part of the mathematical statement.
-/
theorem min_mono_right {a r q : Nat} (h : r <= q) :
    Nat.min a r <= Nat.min a q := by
  by_cases har : a <= r
  · simp [Nat.min_eq_left har, Nat.min_eq_left (Nat.le_trans har h)]
  · have hra : r <= a := Nat.le_of_not_ge har
    simpa [Nat.min_eq_right hra] using Nat.le_min.mpr ⟨hra, h⟩

/--
Cut the first row to length `a`; rows below it are also truncated to at most
`a`. This models choosing a square in the first row.
-/
def firstCut (x : Pos) (a : Nat) : Pos where
  p := a
  q := Nat.min a x.q
  r := Nat.min a x.r
  hq := Nat.min_le_left a x.q
  hr := min_mono_right x.hr

/--
Cut the second row to length `a`; the third row is also truncated to at most
`a`, while the first row is unchanged.
-/
def secondCut (x : Pos) (a : Nat) (ha : a <= x.q) : Pos where
  p := x.p
  q := a
  r := Nat.min a x.r
  hq := Nat.le_trans ha x.hq
  hr := Nat.min_le_left a x.r

/--
Cut the third row to length `b`; the first two rows are unchanged.
-/
def thirdCut (x : Pos) (b : Nat) (hb : b <= x.r) : Pos where
  p := x.p
  q := x.q
  r := b
  hq := x.hq
  hr := Nat.le_trans hb x.hr

end Pos

/--
Legal non-poison Chomp moves.

The first-row case requires `0 < a`. Thus cutting the first row to `0`, i.e.
taking the poisoned square, is intentionally excluded from `Move`: it is the
losing move, not a move to a winning target.
-/
inductive Move : Pos -> Pos -> Prop where
  /-- Cut the first row to a positive smaller length. -/
  | first (x : Pos) (a : Nat) (ha0 : 0 < a) (ha : a < x.p) :
      Move x (Pos.firstCut x a)
  /-- Cut the second row to a smaller length, possibly `0`. -/
  | second (x : Pos) (a : Nat) (ha : a < x.q) :
      Move x (Pos.secondCut x a (Nat.le_of_lt ha))
  /-- Cut the third row to a smaller length, possibly `0`. -/
  | third (x : Pos) (b : Nat) (hb : b < x.r) :
      Move x (Pos.thirdCut x b (Nat.le_of_lt hb))

/--
Lean bookkeeping: a legal move makes the board strictly smaller. This justifies
the recursive definition of `IsP` below.
-/
theorem move_size_lt {x y : Pos} (h : Move x y) : y.size < x.size := by
  cases h with
  | first a ha0 ha =>
      simp [Pos.size, Pos.firstCut]
      have hq : Nat.min a x.q <= x.q := Nat.min_le_right a x.q
      have hr : Nat.min a x.r <= x.r := Nat.min_le_right a x.r
      omega
  | second a ha =>
      simp [Pos.size, Pos.secondCut]
      have hr : Nat.min a x.r <= x.r := Nat.min_le_right a x.r
      omega
  | third b hb =>
      simp [Pos.size, Pos.thirdCut]
      omega

/--
`IsP x` means that `x` is a `P`-position: the board is still nonempty
(`0 < x.p`), and every legal non-poison move from `x` goes to a non-`P`
position.

This is the usual finite-game recursive definition of a previous-player win.
-/
def IsP (x : Pos) : Prop :=
  0 < x.p ∧ ∀ y, Move x y -> ¬ IsP y
termination_by x.size
decreasing_by
  exact move_size_lt ‹Move x y›

/-- Constructor notation for a position `[p,q,r]`. -/
def mkPos (p q r : Nat) (hqp : q <= p) (hrq : r <= q) : Pos where
  p := p
  q := q
  r := r
  hq := hqp
  hr := hrq

/-- The position `[p,a,a]`. -/
def lowerSquarePos (p a : Nat) (hap : a <= p) : Pos :=
  mkPos p a a hap (Nat.le_refl a)

/-- The starting rectangle `[p,p,p]`. -/
def rectanglePos (p : Nat) : Pos :=
  lowerSquarePos p p (Nat.le_refl p)

/--
The audited theorem statement.

For every positive `n`, there is a legal move target `y` from the rectangle
`[n,n,n]` such that `y` is a `P`-position, and every other legal move target
that is a `P`-position is equal to `y`.

In ordinary game language: the `3 x n` Chomp rectangle has exactly one winning
opening move.
-/
def UniqueActualWinningTargetClaim : Prop :=
  ∀ {n : Nat}, 0 < n ->
    ∃ y, Move (rectanglePos n) y ∧ IsP y ∧
      ∀ y', Move (rectanglePos n) y' -> IsP y' -> y' = y

end ChompLean
