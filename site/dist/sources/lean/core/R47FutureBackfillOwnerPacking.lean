import R44FutureFirstGapTripleBackfillCharge

set_option autoImplicit false

namespace ChompLean

/-!
R47: replace the row-seven base-case count by a quantitative packing law.

The underlying statement is independent of Chomp: a duplicate-free list of
integers lying strictly in the upper half of `[0,s)` has length at most half
the interval.  Applying it to all backfill owners, rather than selecting only
three of them, makes every additional backfill pay two units of row index.
-/

/-- A nodup list contained in `[lo,hi)` has at most `hi-lo` entries. -/
theorem nodup_interval_length_bound
    {xs : List Nat} {lo hi : Nat}
    (hlo : lo ≤ hi) (hnd : xs.Nodup)
    (hmem : ∀ x, x ∈ xs → lo ≤ x ∧ x < hi) :
    xs.length ≤ hi - lo := by
  have hsub : xs ⊆ List.range' lo (hi - lo) := by
    intro x hx
    apply List.mem_range'_1.mpr
    rcases hmem x hx with ⟨hlox, hxhi⟩
    constructor
    · exact hlox
    · omega
  have hcard := nodup_subset_length_le hnd hsub
  simpa using hcard

/-- Quantitative upper-half packing. For `s > 0`, a duplicate-free list of
`k` owners with every owner `i < s` and `s < 2*i` satisfies `2*k+1 <= s`.
The canonical future-first-gap application supplies at least three owners
and `s >= 7`. -/
theorem nodup_strict_upper_half_length_bound
    {xs : List Nat} {s : Nat}
    (hs : 0 < s) (hnd : xs.Nodup)
    (hmem : ∀ i, i ∈ xs → i < s ∧ s < i + i) :
    2 * xs.length + 1 ≤ s := by
  have hlo : s / 2 + 1 ≤ s := by omega
  have hcard := nodup_interval_length_bound
    (xs := xs) (lo := s / 2 + 1) (hi := s)
    hlo hnd (by
      intro i hi
      rcases hmem i hi with ⟨his, hhalf⟩
      constructor
      · omega
      · exact his)
  omega

private theorem r47_nodup_map_of_injective_on
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) (xs : List α)
    (hxs : xs.Nodup)
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.map_cons]
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hay⟩
        have hay' : a = y :=
          hinj a (by simp) y (by simp [hy]) hay.symm
        subst y
        exact hxs.1 hy
      · apply ih hxs.2
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

/-- Full quantitative version of the future-first-gap backfill charge.  The
witness list is the same concrete list of non-carry columns from R44, but now
its *entire* length is charged:

`2 * number_of_backfills + 1 ≤ s`.

Thus the previous `s≥7` theorem is only the `length≥3` corollary. -/
theorem game_future_first_gap_quantitative_backfill_charge
    {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    ∃ bs : List Nat,
      bs.Nodup ∧
      3 ≤ bs.length ∧
      2 * bs.length + 1 ≤ s ∧
      ∀ b, b ∈ bs →
        b < s + 1 ∧
        ¬ C gameF s s (gameF (s + 1) b) ∧
        ∃ i,
          b < i ∧ i < s ∧
          s + 1 < gameF i i ∧
          s < i + i ∧
          gameF i i = gameF (s + 1) b := by
  classical
  rcases game_future_first_gap_forces_three_strict_diagonal_backfills
      hFuture with ⟨bs, hbsNodup, hbsLen, hbs⟩
  have hownerExists : ∀ b, b ∈ bs →
      ∃ i,
        b < i ∧ i < s ∧
        s + 1 < gameF i i ∧
        s < i + i ∧
        gameF i i = gameF (s + 1) b := by
    intro b hb
    exact (hbs b hb).2.2
  let owner : Nat → Nat := fun b =>
    if hb : b ∈ bs then Classical.choose (hownerExists b hb) else 0
  have howner : ∀ b, b ∈ bs →
      b < owner b ∧ owner b < s ∧
      s + 1 < gameF (owner b) (owner b) ∧
      s < owner b + owner b ∧
      gameF (owner b) (owner b) = gameF (s + 1) b := by
    intro b hb
    dsimp [owner]
    rw [dif_pos hb]
    exact Classical.choose_spec (hownerExists b hb)
  have hownerInj : ∀ b₁, b₁ ∈ bs → ∀ b₂, b₂ ∈ bs →
      owner b₁ = owner b₂ → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ hEq
    have hvalue : gameF (s + 1) b₁ = gameF (s + 1) b₂ := by
      rw [← (howner b₁ hb₁).2.2.2.2,
        ← (howner b₂ hb₂).2.2.2.2, hEq]
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hbs b₁ hb₁).1)
      (Nat.le_of_lt (hbs b₂ hb₂).1) hvalue
  have hownersNodup : (bs.map owner).Nodup :=
    r47_nodup_map_of_injective_on owner bs hbsNodup hownerInj
  have hownersHalf : ∀ i, i ∈ bs.map owner → i < s ∧ s < i + i := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨b, hb, rfl⟩
    exact ⟨(howner b hb).2.1, (howner b hb).2.2.2.1⟩
  have hsPos : 0 < s := by
    have hthree :=
      (future_first_gap_source_capacity_collapse
        gameRecurrenceModel hFuture).1
    omega
  have hpack := nodup_strict_upper_half_length_bound
    hsPos hownersNodup hownersHalf
  simp only [List.length_map] at hpack
  exact ⟨bs, hbsNodup, hbsLen, hpack, hbs⟩

#print axioms nodup_interval_length_bound
#print axioms nodup_strict_upper_half_length_bound
#print axioms game_future_first_gap_quantitative_backfill_charge

end ChompLean
