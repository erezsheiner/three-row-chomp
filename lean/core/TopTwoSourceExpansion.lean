import ChompLean.Proof

set_option autoImplicit false

namespace ChompLean

/-- The common part of the sources at columns `r` and `r+1` of row `r+2`. -/
def TopTailCore (f : Nat -> Nat -> Nat) (r p : Nat) : Prop :=
  (Exists fun i => And (i < r + 1) (f i i = p)) \/
  (Exists fun b => And (b < r) (f (r + 2) b = p))

/-- Exact source of `V2(r+2)`: common core plus `V1(r+1)`. -/
theorem source_at_v2
    {f : Nat -> Nat -> Nat} {r p : Nat} :
    Iff (B f (r + 2) r p)
      (Or (TopTailCore f r p) (f (r + 1) r = p)) := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · rcases hR with ⟨i, hi, hfi⟩
      by_cases hir : i < r + 1
      · left
        left
        refine ⟨i, hir, ?_⟩
        have hirle : i <= r := by omega
        simpa [Nat.min_eq_left hirle] using hfi
      · right
        have hieq : i = r + 1 := by omega
        subst i
        simpa using hfi
    · left
      right
      exact hC
  · intro h
    rcases h with hK | hx
    · rcases hK with hD | hP
      · rcases hD with ⟨i, hi, hfi⟩
        left
        refine ⟨i, by omega, ?_⟩
        have hirle : i <= r := by omega
        simpa [Nat.min_eq_left hirle] using hfi
      · right
        exact hP
    · left
      refine ⟨r + 1, by omega, ?_⟩
      simpa using hx

/--
If a diagonal value with owner before row `r+2` is absent from the `V2` source,
its owner must be the immediately preceding diagonal `r+1`.
-/
theorem absent_v2_diagonal_owner_is_last
    {f : Nat -> Nat -> Nat} {r p i : Nat}
    (hi : i < r + 2) (hdiag : f i i = p)
    (habs : Not (B f (r + 2) r p)) :
    i = r + 1 := by
  by_cases hir : i <= r
  · have hB : B f (r + 2) r p := by
      left
      refine ⟨i, hi, ?_⟩
      simpa [Nat.min_eq_left hir] using hdiag
    exact False.elim (habs hB)
  · omega

/-- Exact source of `V1(r+2)`: common core plus `d(r+1)` and `V2(r+2)`. -/
theorem source_at_v1
    {f : Nat -> Nat -> Nat} {r p : Nat} :
    Iff (B f (r + 2) (r + 1) p)
      (Or (TopTailCore f r p)
        (Or (f (r + 1) (r + 1) = p) (f (r + 2) r = p))) := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · rcases hR with ⟨i, hi, hfi⟩
      have hirle : i <= r + 1 := by omega
      have hfii : f i i = p := by
        simpa [Nat.min_eq_left hirle] using hfi
      by_cases hir : i < r + 1
      · left
        left
        exact ⟨i, hir, hfii⟩
      · right
        left
        have hieq : i = r + 1 := by omega
        simpa [hieq] using hfii
    · rcases hC with ⟨b, hb, hfb⟩
      by_cases hbr : b < r
      · left
        right
        exact ⟨b, hbr, hfb⟩
      · right
        right
        have hbeq : b = r := by omega
        simpa [hbeq] using hfb
  · intro h
    rcases h with hK | hl | hy
    · rcases hK with hD | hP
      · rcases hD with ⟨i, hi, hfi⟩
        left
        refine ⟨i, by omega, ?_⟩
        have hirle : i <= r + 1 := by omega
        simpa [Nat.min_eq_left hirle] using hfi
      · right
        rcases hP with ⟨b, hb, hfb⟩
        exact ⟨b, by omega, hfb⟩
    · left
      refine ⟨r + 1, by omega, ?_⟩
      simpa using hl
    · right
      exact ⟨r, by omega, hy⟩

/-- The diagonal source is the `V1` source with only `V1` itself adjoined. -/
theorem source_at_diagonal
    {f : Nat -> Nat -> Nat} {r p : Nat} :
    Iff (B f (r + 2) (r + 2) p)
      (Or (B f (r + 2) (r + 1) p) (f (r + 2) (r + 1) = p)) := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · left
      left
      rcases hR with ⟨i, hi, hfi⟩
      refine ⟨i, hi, ?_⟩
      have hirle1 : i <= r + 1 := by omega
      have hirle2 : i <= r + 2 := by omega
      simpa [Nat.min_eq_left hirle1, Nat.min_eq_left hirle2] using hfi
    · rcases hC with ⟨b, hb, hfb⟩
      by_cases hbr : b < r + 1
      · left
        right
        exact ⟨b, hbr, hfb⟩
      · right
        have hbeq : b = r + 1 := by omega
        simpa [hbeq] using hfb
  · intro h
    rcases h with hB | hq
    · rcases hB with hR | hC
      · left
        rcases hR with ⟨i, hi, hfi⟩
        refine ⟨i, hi, ?_⟩
        have hirle1 : i <= r + 1 := by omega
        have hirle2 : i <= r + 2 := by omega
        simpa [Nat.min_eq_left hirle1, Nat.min_eq_left hirle2] using hfi
      · right
        rcases hC with ⟨b, hb, hfb⟩
        exact ⟨b, by omega, hfb⟩
    · right
      exact ⟨r + 1, by omega, hq⟩

/-- The preceding diagonal source is its `V1` source with that `V1` adjoined. -/
theorem previous_diagonal_source
    {f : Nat -> Nat -> Nat} {r p : Nat} :
    Iff (B f (r + 1) (r + 1) p)
      (Or (B f (r + 1) r p) (f (r + 1) r = p)) := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · left
      left
      rcases hR with ⟨i, hi, hfi⟩
      refine ⟨i, hi, ?_⟩
      have hirle0 : i <= r := by omega
      have hirle1 : i <= r + 1 := by omega
      simpa [Nat.min_eq_left hirle0, Nat.min_eq_left hirle1] using hfi
    · rcases hC with ⟨b, hb, hfb⟩
      by_cases hbr : b < r
      · left
        right
        exact ⟨b, hbr, hfb⟩
      · right
        have hbeq : b = r := by omega
        simpa [hbeq] using hfb
  · intro h
    rcases h with hB | hx
    · rcases hB with hR | hC
      · left
        rcases hR with ⟨i, hi, hfi⟩
        refine ⟨i, hi, ?_⟩
        have hirle0 : i <= r := by omega
        have hirle1 : i <= r + 1 := by omega
        simpa [Nat.min_eq_left hirle0, Nat.min_eq_left hirle1] using hfi
      · right
        rcases hC with ⟨b, hb, hfb⟩
        exact ⟨b, by omega, hfb⟩
    · right
      exact ⟨r, by omega, hx⟩

end ChompLean
