import ChompLean.Proof

set_option autoImplicit false

/-!
# FutureFreezeDiagonal, unconditionally

Work-ID: `AUG-CENTRAL-FIRST-EXIT-001`  ·  Run-ID: `CLAUDE-WX-20260918-010`, lane N.

The theorem: a blocker never reaches the diagonal of its own victim column,

`∀ q c, c < q → gameF q c = q → q < gameF c c`

(`gameF_futureFreezeDiagonal` below).  This is `FutureFreezeDiagonal` of
`projects/density-twohead/artifacts/FutureFreezeDiagonalReduction.lean:23-24`
and the atom of `RUN9/lane-F/FINAL.md` §1.1 ("`IMM = LIVE@d`": a column alive at
row `d(c)` never dies).

The proof follows REPORT-F1's chain as repaired in `RUN9/lane-F/FINAL.md` §1.1/§4,
with the cardinality bookkeeping replaced by one composite injection, because the
bank has no `Finset`:

* F1 step **(B)** = `hhost`/`wit` below: `rowStartPropagation` gives, for every row
  `b` strictly between the victim `c` and the blocker `q`, a column `e_b < c` of row
  `b` carrying the value `q`; the columns are pairwise distinct (no-repeat).
* F1 step **(A)** = `hgub` below, in pointwise form: each such column is still live
  at row `c` (`constant_step`, via `constant_from`), and its row-`c` value lies
  strictly between `c` and the diagonal value `gameF c c` (`diagonalMaximal` for
  `≤`, `fixed_q_injective` for `≠`).
* F1 step **(C)** (the disjointness bookkeeping) is absorbed: the two excluded
  values are `c` itself (excluded by liveness, which is strict) and `gameF c c`
  (excluded by row injectivity).
* F1 step **(D)** = `freezeDiagonal_le` + `futureFreezeDiagonal_of_model`: the two
  injections compose to an injection of the open interval `(c,q)` into the open
  interval `(c, gameF c c)`; `interval_inj_surj` (`ChompLean/FiniteInterval.lean`)
  turns that into `q ≤ gameF c c`, and `disjoint_D_S` into `q < gameF c c`.

The proof uses interval injections rather than explicit finite-set cardinality APIs: no `Finset` or separate `Nat` counting device,
and no `by_contra` is used.  The only input that is *not* a field or a theorem of
`RecurrenceModel` is the no-repeat fact `NoSameColumnRepeat`; it is supplied here
in two independent ways (`noSameColumnRepeat_of_encodes`, from the game encoding,
and `noSameColumnRepeat_of_recurrence`, from the mex branch of the Brouwer
recurrence), so the main theorem is `RecurrenceModel`-level plus one named
hypothesis that the actual game discharges twice over.
-/

namespace ChompLean

/--
`NoSameColumnRepeat f`: a fixed column never carries the same value on two
different rows that both lie strictly below that value.

This is `encoding_same_lower_no_repeat` (`ChompLean/Encoding.lean:289-292`) as a
predicate, so that the counting theorem below can be stated without the
`Encodes` scope.
-/
def NoSameColumnRepeat (f : Nat -> Nat -> Nat) : Prop :=
  ∀ {s t₁ t₂ p : Nat},
    s < t₁ -> t₁ < t₂ -> t₂ < p -> f t₁ s = p -> f t₂ s = p -> False

/-- The game encoding satisfies `NoSameColumnRepeat` (bank lemma, verbatim). -/
theorem noSameColumnRepeat_of_encodes {f : Nat -> Nat -> Nat} (hf : Encodes f) :
    NoSameColumnRepeat f := by
  intro s t₁ t₂ p hst₁ ht₁t₂ ht₂p h₁ h₂
  exact encoding_same_lower_no_repeat hf hst₁ ht₁t₂ ht₂p h₁ h₂

/--
`NoSameColumnRepeat` also follows from the recurrence alone, with no reference to
the game: the second occurrence is a mex cell whose own value would then be
blocked from the left by the first occurrence.  (This is FINAL §1.1's "replace
`(L6)`" repair; note that it needs the mex value to be *absent* from its blocked
set, i.e. `recurrence_mex_absent`, which is a consequence of
`BrouwerRecurrence` and is **not** one of `RecurrenceModel`'s fields.)
-/
theorem noSameColumnRepeat_of_recurrence {f : Nat -> Nat -> Nat}
    (hrec : BrouwerRecurrence f) :
    NoSameColumnRepeat f := by
  intro s t₁ t₂ p hst₁ ht₁t₂ ht₂p h₁ h₂
  have hlarge : t₂ < f t₂ s := by rw [h₂]; exact ht₂p
  have hnotB : ¬ B f t₂ s (f t₂ s) :=
    recurrence_mex_absent hrec (by omega) hlarge
  refine hnotB (Or.inl ⟨t₁, ht₁t₂, ?_⟩)
  rw [show min t₁ s = s from by omega, h₁, h₂]

/--
At most one column of a row carries the row index as its value: a row has at most
one freeze (death) event.  Immediate from `fixed_q_injective`; recorded because it
is what makes REPORT-F1's `eps` and `eps'` bounded by `1`.
-/
theorem death_column_unique
    (M : RecurrenceModel) {q r₁ r₂ : Nat}
    (hr₁ : r₁ ≤ q) (hr₂ : r₂ ≤ q)
    (h₁ : M.f q r₁ = q) (h₂ : M.f q r₂ = q) :
    r₁ = r₂ :=
  M.fixed_q_injective hr₁ hr₂ (h₁.trans h₂.symm)

/--
**Step (D), non-strict form.**  For a freeze `(q,c)` (`c < q`, `f q c = q`):
`q ≤ f c c`.

Hypotheses: the model, plus `NoSameColumnRepeat`.  Model inputs actually used:
`diagonal_gt`, `fixed_q_injective`, `constant_step` (through `constant_from`),
`rowStartPropagation`, `diagonalMaximal`.
-/
theorem freezeDiagonal_le
    (M : RecurrenceModel) (hnr : NoSameColumnRepeat M.f)
    {q c : Nat} (hcq : c < q) (hstart : M.f q c = q) :
    q ≤ M.f c c := by
  classical
  have hnr' : ∀ {s t₁ t₂ p : Nat},
      s < t₁ -> t₁ < t₂ -> t₂ < p -> M.f t₁ s = p -> M.f t₂ s = p -> False := hnr
  -- The adjacent freeze `q = c+1` is `diagonal_gt` alone (FINAL §1.1, repair 1).
  by_cases hadj : q ≤ c + 1
  · have hgt : c < M.f c c := M.diagonal_gt c
    omega
  have hgap : c + 1 < q := by omega
  -- Step (B): every intermediate row hosts `q` strictly left of the victim column.
  have hhost : ∀ b, c < b -> b < q -> ∃ e, e < c ∧ M.f b e = q := by
    intro b hcb hbq
    exact rowStartPropagation M hstart hcq hcb hbq
  let wit : Nat -> Nat :=
    fun b => if h : c < b ∧ b < q then Classical.choose (hhost b h.1 h.2) else 0
  have wit_spec : ∀ {b}, c < b -> b < q -> wit b < c ∧ M.f b (wit b) = q := by
    intro b hcb hbq
    have hmem := hhost b hcb hbq
    dsimp [wit]
    rw [dif_pos ⟨hcb, hbq⟩]
    exact Classical.choose_spec hmem
  -- Step (A), liveness half: the witness column is still live at row `c`.
  have hlive : ∀ {b}, c < b -> b < q -> c < M.f c (wit b) := by
    intro b hcb hbq
    obtain ⟨hwc, hval⟩ := wit_spec hcb hbq
    by_cases hsmall : M.f c (wit b) < c + 1
    · have hconst := constant_from M hwc hsmall (b - c)
      have hidx : c + (b - c) = b := by omega
      rw [hidx] at hconst
      omega
    · omega
  -- Step (A), ceiling half, with step (C) absorbed: the row-`c` value of the
  -- witness column is strictly below the diagonal value.
  have hgub : ∀ {b}, c < b -> b < q -> M.f c (wit b) < M.f c c := by
    intro b hcb hbq
    obtain ⟨hwc, _hval⟩ := wit_spec hcb hbq
    have hmax : M.f c (wit b) ≤ M.f c c := diagonalMaximal M (Nat.le_of_lt hwc)
    have hne : M.f c (wit b) ≠ M.f c c := by
      intro h
      have hweq : wit b = c := M.fixed_q_injective (Nat.le_of_lt hwc) (Nat.le_refl c) h
      omega
    omega
  -- Step (B), injectivity half, composed with row-`c` injectivity.
  have hinjg : ∀ x y, c < x -> x < q -> c < y -> y < q ->
      M.f c (wit x) = M.f c (wit y) -> x = y := by
    intro x y hcx hxq hcy hyq heq
    obtain ⟨hwx, hvx⟩ := wit_spec hcx hxq
    obtain ⟨hwy, hvy⟩ := wit_spec hcy hyq
    have hw : wit x = wit y :=
      M.fixed_q_injective (Nat.le_of_lt hwx) (Nat.le_of_lt hwy) heq
    by_cases hlt : x < y
    · have h1 : wit x < x := by omega
      have h2 : M.f y (wit x) = q := by rw [hw]; exact hvy
      exact False.elim (hnr' h1 hlt hyq hvx h2)
    by_cases hgt : y < x
    · have h1 : wit y < y := by omega
      have h2 : M.f x (wit y) = q := by rw [← hw]; exact hvx
      exact False.elim (hnr' h1 hgt hxq hvy h2)
    omega
  -- Step (D): the composite injection cannot fit if the diagonal were below `q`.
  apply Nat.le_of_not_gt
  intro hlt
  have hmapg : ∀ x, c < x -> x < q -> c < M.f c (wit x) ∧ M.f c (wit x) < q := by
    intro x hcx hxq
    have h1 := hlive hcx hxq
    have h2 := hgub hcx hxq
    exact ⟨h1, by omega⟩
  obtain ⟨x, hcx, hxq, hgx⟩ :=
    interval_inj_surj hcq (fun b => M.f c (wit b)) hmapg hinjg (q - 1)
      (by omega) (by omega)
  have hgx' : M.f c (wit x) = q - 1 := hgx
  have hub := hgub hcx hxq
  omega

/--
**The atom, over `RecurrenceModel` plus `NoSameColumnRepeat`.**
A blocker `q` frozen in column `c` is strictly below the diagonal value of its
own victim column.
-/
theorem futureFreezeDiagonal_of_model
    (M : RecurrenceModel) (hnr : NoSameColumnRepeat M.f)
    {q c : Nat} (hcq : c < q) (hstart : M.f q c = q) :
    q < M.f c c := by
  have hle := freezeDiagonal_le M hnr hcq hstart
  have hne : M.f c c ≠ q := by
    intro h
    exact disjoint_D_S M ⟨c, h⟩ ⟨c, hcq, hstart⟩
  omega

/--
**Prehost form**, over the same hypotheses: the blocker is already hosted in the
strict prefix of the row indexed by its own freeze column.  This is
`FreezeSeatPrehost` (`FutureFreezeDiagonalReduction.lean:28-29`).  The argument
is the reverse direction of `rowstart_hosted_iff_below_diagonal`
(`bank/formal-core/PrefreezeHostDiagonalCriterion.lean:24-47`), reproved here so
that this file depends on `ChompLean.Proof` only.
-/
theorem freezeSeatPrehost_of_model
    (M : RecurrenceModel) (hnr : NoSameColumnRepeat M.f)
    {q c : Nat} (hcq : c < q) (hstart : M.f q c = q) :
    C M.f c c q := by
  have hlt : q < M.f c c := futureFreezeDiagonal_of_model M hnr hcq hstart
  have hpos : 0 < q := by omega
  have hB : B M.f c c q :=
    M.mex_no_skip (Nat.le_refl c) (M.diagonal_gt c) hpos hlt
  rcases hB with hR | hC
  · rcases hR with ⟨a, hac, hvalue⟩
    rw [show min a c = a from by omega] at hvalue
    exact False.elim (disjoint_D_S M ⟨a, hvalue⟩ ⟨c, hcq, hstart⟩)
  · exact hC

/--
The Brouwer recurrence for the actual game (assembled from bank theorems).
Prior art, same statement and same proof: `gameF_brouwerRecurrence`,
`bank/formal-core/R56TopTwoHoles.lean:123` — repeated here under a distinct name
so that this file needs only `ChompLean.Proof` and can be imported alongside
`R56TopTwoHoles` without a duplicate declaration.
-/
theorem claude_gameF_brouwerRecurrence : BrouwerRecurrence gameF :=
  recurrence_of_encoding_and_mex game_encodes game_complete
    (mex_branch_of_encoding_and_lower game_encodes game_complete
      game_lower_blocked)

/--
**`FutureFreezeDiagonal` for the actual game, unconditionally.**

`∀ q c, c < q → gameF q c = q → q < gameF c c`.
-/
theorem gameF_futureFreezeDiagonal :
    ∀ q c : Nat, c < q -> gameF q c = q -> q < gameF c c := by
  intro q c hcq hstart
  exact futureFreezeDiagonal_of_model gameRecurrenceModel
    (noSameColumnRepeat_of_encodes game_encodes) hcq hstart

/-- The same theorem obtained through the recurrence-only no-repeat route. -/
theorem gameF_futureFreezeDiagonal_via_recurrence :
    ∀ q c : Nat, c < q -> gameF q c = q -> q < gameF c c := by
  intro q c hcq hstart
  exact futureFreezeDiagonal_of_model gameRecurrenceModel
    (noSameColumnRepeat_of_recurrence claude_gameF_brouwerRecurrence) hcq hstart

/-- `FreezeSeatPrehost` for the actual game, unconditionally. -/
theorem gameF_freezeSeatPrehost :
    ∀ q c : Nat, c < q -> gameF q c = q -> C gameF c c q := by
  intro q c hcq hstart
  exact freezeSeatPrehost_of_model gameRecurrenceModel
    (noSameColumnRepeat_of_encodes game_encodes) hcq hstart

/--
FINAL §1.3's sharper form `q ≤ d(c) − eps'` is **not** a strengthening of the
atom.  `eps' = #{e < c : f (c+1) e = c+1} ≤ 1` by `death_column_unique` (at most
one death per row), so the sharpened bound says `q + 1 ≤ d(c)` when `eps' = 1`,
which is exactly the atom; the proof below therefore never looks at `e` or at the
row-`(c+1)` death — the unused hypotheses are the content of the remark.
-/
theorem gameF_epsPrime_sharpening_is_implied
    {q c e : Nat} (hcq : c < q) (hstart : gameF q c = q)
    (_he : e < c + 1) (_hdeath : gameF (c + 1) e = c + 1) :
    q + 1 ≤ gameF c c := by
  have h := gameF_futureFreezeDiagonal q c hcq hstart
  omega

#print axioms ChompLean.freezeDiagonal_le
#print axioms ChompLean.futureFreezeDiagonal_of_model
#print axioms ChompLean.freezeSeatPrehost_of_model
#print axioms ChompLean.noSameColumnRepeat_of_encodes
#print axioms ChompLean.noSameColumnRepeat_of_recurrence
#print axioms ChompLean.gameF_futureFreezeDiagonal
#print axioms ChompLean.gameF_futureFreezeDiagonal_via_recurrence
#print axioms ChompLean.gameF_freezeSeatPrehost
#print axioms ChompLean.death_column_unique

end ChompLean
