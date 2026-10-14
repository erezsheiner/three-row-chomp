import R50EventETwoEdgeSurvivorLowerBound
import R48AdjacentDipAmortizedBackfillPacking

set_option autoImplicit false

namespace ChompLean

/-!
R51: cross-edge owner packing for two consecutive adjacent dips.

The backfills on the first edge occur in the middle strict prefix.  The
backfills on the second edge are, by definition, absent from that same
middle prefix.  Hence the two backfill packets are disjoint.  Their past
diagonal owners are therefore globally distinct and must fit together in
one weak upper-half interval.
-/

private theorem r51_nodup_map_of_injective_on
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

/-- Weak-upper-half packing with the right endpoint included. -/
theorem weak_upper_half_owner_packing
    {q : Nat} {owners : List Nat}
    (howners : owners.Nodup)
    (hband : forall i, i ∈ owners -> i <= q /\ q < i + i) :
    2 * owners.length <= q + 1 := by
  let rank : Nat -> Nat := fun i => q - i
  have hrankNodup : (owners.map rank).Nodup := by
    apply r51_nodup_map_of_injective_on rank owners howners
    intro i hi j hj hEq
    have hiBand := hband i hi
    have hjBand := hband j hj
    dsimp [rank] at hEq
    omega
  have hrankSub : owners.map rank ⊆ List.range ((q + 1) / 2) := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
    apply List.mem_range.mpr
    have hiBand := hband i hi
    dsimp [rank]
    omega
  have hcap := nodup_subset_length_le hrankNodup hrankSub
  simp only [List.length_map, List.length_range] at hcap
  omega

/-- Backfill values on consecutive edges are disjoint because the first
packet is present in the middle prefix and the second packet is absent from
that prefix. -/
theorem consecutive_prefix_backfill_packets_disjoint
    (q : Nat) :
    forall v,
      v ∈ PrefixBackfillValues
        (StrictRowPrefixValues gameF q)
        (StrictRowPrefixValues gameF (q + 1)) ->
      v ∈ PrefixBackfillValues
        (StrictRowPrefixValues gameF (q + 1))
        (StrictRowPrefixValues gameF (q + 2)) ->
      False := by
  intro v hvFirst hvSecond
  have hvMiddle := (List.mem_filter.mp hvFirst).1
  have hvNotMiddle :
      v ∉ StrictRowPrefixValues gameF (q + 1) := by
    have hfilter := (List.mem_filter.mp hvSecond).2
    simpa [PrefixBackfillValues] using hfilter
  exact hvNotMiddle hvMiddle

/-- The complete backfill packets from two consecutive dips share one
owner budget. -/
theorem game_consecutive_dips_combined_backfill_owner_packing
    {q : Nat}
    (hdip0 : gameF (q + 1) (q + 1) < gameF q q)
    (hdip1 : gameF (q + 2) (q + 2) < gameF (q + 1) (q + 1)) :
    let back0 := PrefixBackfillValues
      (StrictRowPrefixValues gameF q)
      (StrictRowPrefixValues gameF (q + 1))
    let back1 := PrefixBackfillValues
      (StrictRowPrefixValues gameF (q + 1))
      (StrictRowPrefixValues gameF (q + 2))
    2 * (back0.length + back1.length) <= q + 1 := by
  dsimp only
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF q)
    (StrictRowPrefixValues gameF (q + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (q + 1))
    (StrictRowPrefixValues gameF (q + 2))
  let values := back0 ++ back1

  have hback0Nodup : back0.Nodup := by
    exact List.filter_sublist.nodup
      (strictRowPrefixValues_nodup gameRecurrenceModel (q + 1))
  have hback1Nodup : back1.Nodup := by
    exact List.filter_sublist.nodup
      (strictRowPrefixValues_nodup gameRecurrenceModel (q + 2))
  have hcross : forall a, a ∈ back0 -> forall b, b ∈ back1 -> a ≠ b := by
    intro a ha b hb hEq
    subst b
    exact consecutive_prefix_backfill_packets_disjoint q a ha hb
  have hvaluesNodup : values.Nodup := by
    exact List.nodup_append.mpr ⟨hback0Nodup, hback1Nodup, hcross⟩

  have hownerExists : forall v, v ∈ values ->
      exists i, i <= q /\ q < i + i /\ gameF i i = v := by
    intro v hv
    rcases List.mem_append.mp hv with hv0 | hv1
    · rcases adjacent_dip_backfill_has_past_diagonal_owner
        gameRecurrenceModel hdip0 hv0 with ⟨i, hiq, hdiag⟩
      have hvNew := (List.mem_filter.mp hv0).1
      rcases mem_strictRowPrefixValues_iff_C.mp hvNew with
        ⟨b, hb, hcell⟩
      have hhigh := game_past_diagonal_reemission_is_high
        (i := i) (t := q + 1) (b := b)
        (Nat.le_of_lt hb) (hdiag.trans hcell.symm)
      have hcap := recurrence_diagonal_source_capacity
        gameRecurrenceModel i
      change gameF i i <= i + i + 1 at hcap
      exact ⟨i, by omega, by omega, hdiag⟩
    · rcases adjacent_dip_backfill_has_past_diagonal_owner
        gameRecurrenceModel hdip1 hv1 with ⟨i, hiq, hdiag⟩
      have hvNew := (List.mem_filter.mp hv1).1
      rcases mem_strictRowPrefixValues_iff_C.mp hvNew with
        ⟨b, hb, hcell⟩
      have hhigh := game_past_diagonal_reemission_is_high
        (i := i) (t := q + 2) (b := b)
        (Nat.le_of_lt hb) (hdiag.trans hcell.symm)
      have hcap := recurrence_diagonal_source_capacity
        gameRecurrenceModel i
      change gameF i i <= i + i + 1 at hcap
      exact ⟨i, by omega, by omega, hdiag⟩

  let owner : Nat -> Nat := fun v =>
    if hv : v ∈ values then Classical.choose (hownerExists v hv) else 0
  have howner : forall v, v ∈ values ->
      owner v <= q /\ q < owner v + owner v /\
        gameF (owner v) (owner v) = v := by
    intro v hv
    dsimp [owner]
    rw [dif_pos hv]
    exact Classical.choose_spec (hownerExists v hv)
  have hownerInj : forall v, v ∈ values -> forall w, w ∈ values ->
      owner v = owner w -> v = w := by
    intro v hv w hw hEq
    have hvDiag := (howner v hv).2.2
    have hwDiag := (howner w hw).2.2
    rw [hEq] at hvDiag
    exact hvDiag.symm.trans hwDiag
  have hownersNodup : (values.map owner).Nodup :=
    r51_nodup_map_of_injective_on owner values hvaluesNodup hownerInj
  have hownersBand : forall i, i ∈ values.map owner ->
      i <= q /\ q < i + i := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨v, hv, rfl⟩
    exact ⟨(howner v hv).1, (howner v hv).2.1⟩
  have hpack := weak_upper_half_owner_packing hownersNodup hownersBand
  simp only [List.length_map] at hpack
  change 2 * values.length <= q + 1 at hpack
  simpa [values, back0, back1] using hpack

/-- Cross-edge amortization.  Forbidden packets on both consecutive dips
pay one common owner budget, rather than two independent half-budgets. -/
theorem game_consecutive_dips_two_forbidden_packets_amortized_bound
    {q : Nat} {forbidden0 forbidden1 : List Nat}
    (hdip0 : gameF (q + 1) (q + 1) < gameF q q)
    (hdip1 : gameF (q + 2) (q + 2) < gameF (q + 1) (q + 1))
    (hforbidden0 : forbidden0.Nodup)
    (hsub0 : forbidden0 ⊆ StrictRowPrefixValues gameF q)
    (hmissing0 : forall v, v ∈ forbidden0 ->
      v ∉ StrictRowPrefixValues gameF (q + 1))
    (hforbidden1 : forbidden1.Nodup)
    (hsub1 : forbidden1 ⊆ StrictRowPrefixValues gameF (q + 1))
    (hmissing1 : forall v, v ∈ forbidden1 ->
      v ∉ StrictRowPrefixValues gameF (q + 2)) :
    2 * (forbidden0.length + forbidden1.length) + 3 <= q := by
  let back0 := PrefixBackfillValues
    (StrictRowPrefixValues gameF q)
    (StrictRowPrefixValues gameF (q + 1))
  let back1 := PrefixBackfillValues
    (StrictRowPrefixValues gameF (q + 1))
    (StrictRowPrefixValues gameF (q + 2))
  have hpkg0 := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    gameRecurrenceModel hdip0 hforbidden0 hsub0 hmissing0
  change forbidden0.length + 1 <= back0.length /\ _ at hpkg0
  have hpkg1 := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    gameRecurrenceModel hdip1 hforbidden1 hsub1 hmissing1
  change forbidden1.length + 1 <= back1.length /\ _ at hpkg1
  have hpack := game_consecutive_dips_combined_backfill_owner_packing
    hdip0 hdip1
  change 2 * (back0.length + back1.length) <= q + 1 at hpack
  omega

#print axioms weak_upper_half_owner_packing
#print axioms consecutive_prefix_backfill_packets_disjoint
#print axioms game_consecutive_dips_combined_backfill_owner_packing
#print axioms game_consecutive_dips_two_forbidden_packets_amortized_bound

end ChompLean
