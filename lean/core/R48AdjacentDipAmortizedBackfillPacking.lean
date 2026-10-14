import R47ReusablePrefixBackfillCharge
import R44FutureFirstGapTripleBackfillCharge

set_option autoImplicit false

namespace ChompLean

/-!
R48: amortized packing for every adjacent dip in the actual game.

R47 turns `k` forbidden old-prefix values into at least `k+1` distinct
new-only values, each with a past diagonal owner.  Actual-game encoding says
that a past diagonal value re-emitted on row `q+1` is larger than `q+1`.
Together with diagonal source capacity `d(i)<=2*i+1`, every selected owner
lies in the strict upper half `q<2*i`.

Distinct backfill values have distinct owners.  Packing `m` distinct upper-
half indices below `q` gives `2*m+1<=q`.  Since `m>=k+1`, every forbidden
packet across an adjacent dip pays the unconditional amortized bound

`2*k+3 <= q`.

No FutureFirstGap, RM2, or UnitDip assumption is used.
-/

private theorem r48_nodup_map_of_injective_on
    (f : Nat -> Nat) (xs : List Nat)
    (hxs : xs.Nodup)
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
      f x = f y -> x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      change (f a :: as.map f).Nodup
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

/-- Pure packing lemma.  A nonempty duplicate-free list of indices strictly
below `q` and strictly above its half-capacity has size at most `(q-1)/2`. -/
theorem strict_upper_half_owner_packing
    {q : Nat} {owners : List Nat}
    (howners : owners.Nodup)
    (hnonempty : 0 < owners.length)
    (hband : forall i, i ∈ owners -> i < q /\ q < i + i) :
    2 * owners.length + 1 <= q := by
  have hqPos : 0 < q := by
    cases owners with
    | nil => simp at hnonempty
    | cons i is =>
        have hi := hband i (by simp)
        omega
  let rank : Nat -> Nat := fun i => q - 1 - i
  have hrankNodup : (owners.map rank).Nodup := by
    apply r48_nodup_map_of_injective_on rank owners howners
    intro i hi j hj hEq
    have hiBand := hband i hi
    have hjBand := hband j hj
    dsimp [rank] at hEq
    omega
  have hrankSub : owners.map rank ⊆ List.range ((q - 1) / 2) := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
    apply List.mem_range.mpr
    have hiBand := hband i hi
    dsimp [rank]
    omega
  have hcap := nodup_subset_length_le hrankNodup hrankSub
  simp only [List.length_map, List.length_range] at hcap
  omega

/-- Across an actual-game adjacent dip, all new-only strict-prefix values
fit into distinct strict-upper-half diagonal owners. -/
theorem game_adjacent_dip_backfill_owner_packing
    {q : Nat}
    (hdip : gameF (q + 1) (q + 1) < gameF q q)
    (hnonempty :
      0 < (PrefixBackfillValues
        (StrictRowPrefixValues gameF q)
        (StrictRowPrefixValues gameF (q + 1))).length) :
    2 * (PrefixBackfillValues
        (StrictRowPrefixValues gameF q)
        (StrictRowPrefixValues gameF (q + 1))).length + 1 <= q := by
  let backfills := PrefixBackfillValues
    (StrictRowPrefixValues gameF q)
    (StrictRowPrefixValues gameF (q + 1))
  have hbackfillNodup : backfills.Nodup := by
    exact List.filter_sublist.nodup
      (strictRowPrefixValues_nodup gameRecurrenceModel (q + 1))
  have hownerExists : forall v, v ∈ backfills ->
      exists i, i < q /\ gameF i i = v := by
    intro v hv
    exact adjacent_dip_backfill_has_past_diagonal_owner
      gameRecurrenceModel hdip hv
  let owner : Nat -> Nat := fun v =>
    if hv : v ∈ backfills then Classical.choose (hownerExists v hv)
    else 0
  have howner : forall v, v ∈ backfills ->
      owner v < q /\ gameF (owner v) (owner v) = v := by
    intro v hv
    dsimp [owner]
    rw [dif_pos hv]
    exact Classical.choose_spec (hownerExists v hv)
  have hownerInjective : forall v₁, v₁ ∈ backfills ->
      forall v₂, v₂ ∈ backfills ->
      owner v₁ = owner v₂ -> v₁ = v₂ := by
    intro v₁ hv₁ v₂ hv₂ hEq
    have h₁ := (howner v₁ hv₁).2
    have h₂ := (howner v₂ hv₂).2
    rw [hEq] at h₁
    exact h₁.symm.trans h₂
  have hownersNodup : (backfills.map owner).Nodup :=
    r48_nodup_map_of_injective_on owner backfills
      hbackfillNodup hownerInjective
  have hownerBand : forall i, i ∈ backfills.map owner ->
      i < q /\ q < i + i := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨v, hv, rfl⟩
    have hvFilter := List.mem_filter.mp hv
    have hvNew : v ∈ StrictRowPrefixValues gameF (q + 1) :=
      hvFilter.1
    rcases mem_strictRowPrefixValues_iff_C.mp hvNew with
      ⟨b, hb, hcell⟩
    have hhigh : q + 1 < gameF (owner v) (owner v) := by
      apply game_past_diagonal_reemission_is_high
        (i := owner v) (t := q + 1) (b := b)
        (Nat.le_of_lt hb)
      exact (howner v hv).2.trans hcell.symm
    have hsourceCap := recurrence_diagonal_source_capacity
      gameRecurrenceModel (owner v)
    change gameF (owner v) (owner v) <=
      owner v + owner v + 1 at hsourceCap
    exact ⟨(howner v hv).1, by omega⟩
  have hpack := strict_upper_half_owner_packing
    hownersNodup (by simpa [backfills] using hnonempty) hownerBand
  simpa [backfills] using hpack

/-- Main amortized theorem.  A duplicate-free packet of `k` old-prefix
values which all disappear across an adjacent dip can exist only at rows
`q >= 2*k+3`. -/
theorem game_adjacent_dip_forbidden_amortized_bound
    {q : Nat} {forbidden : List Nat}
    (hdip : gameF (q + 1) (q + 1) < gameF q q)
    (hforbidden : forbidden.Nodup)
    (hsub : forbidden ⊆ StrictRowPrefixValues gameF q)
    (hmissing : forall v, v ∈ forbidden ->
      v ∉ StrictRowPrefixValues gameF (q + 1)) :
    2 * forbidden.length + 3 <= q := by
  let backfills := PrefixBackfillValues
    (StrictRowPrefixValues gameF q)
    (StrictRowPrefixValues gameF (q + 1))
  have hpkg := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    gameRecurrenceModel hdip hforbidden hsub hmissing
  change forbidden.length + 1 <= backfills.length /\
      backfills.Nodup /\
      forall v, v ∈ backfills ->
        exists i, i < q /\ gameF i i = v at hpkg
  have hnonempty : 0 < backfills.length := by omega
  have hpack := game_adjacent_dip_backfill_owner_packing
    hdip (by simpa [backfills] using hnonempty)
  change 2 * backfills.length + 1 <= q at hpack
  omega

/-- Empty-packet base case: even without a named forbidden value, unit
prefix growth across a genuine adjacent dip creates one high backfill, so
no adjacent dip occurs before row three. -/
theorem game_adjacent_dip_requires_row_three
    {q : Nat}
    (hdip : gameF (q + 1) (q + 1) < gameF q q) :
    3 <= q := by
  have h := game_adjacent_dip_forbidden_amortized_bound
    (q := q) (forbidden := []) hdip
    (by simp) (by simp) (by simp)
  simpa using h

#print axioms strict_upper_half_owner_packing
#print axioms game_adjacent_dip_backfill_owner_packing
#print axioms game_adjacent_dip_forbidden_amortized_bound
#print axioms game_adjacent_dip_requires_row_three

end ChompLean
