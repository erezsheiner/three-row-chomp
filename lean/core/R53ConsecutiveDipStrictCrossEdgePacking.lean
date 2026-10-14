import R51ConsecutiveDipCrossEdgeBackfillPacking

set_option autoImplicit false

namespace ChompLean

/-!
R53: remove the spurious right endpoint from the two-edge backfill budget.

R51 placed the owners of the two consecutive backfill packets in the weak
upper half `i <= q`, because a past owner for the second edge is initially
known only to satisfy `i < q+1`.  The endpoint `i=q` is in fact impossible:
its value is the old diagonal `d(q)`, while every value in the second new
prefix is at most `d(q+2) < d(q)`.  Thus the combined packet fits in the
strict upper half `i < q` and gains one full unit of packing strength.
-/

private theorem r53_nodup_map_of_injective_on
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

/-- The second-edge packet cannot use the apparent endpoint owner `q`.
The two consecutive diagonal drops put `d(q)` strictly above the whole
row-`q+2` prefix. -/
theorem second_consecutive_dip_backfill_owner_lt_first_row
    {q i v : Nat}
    (hdip0 : gameF (q + 1) (q + 1) < gameF q q)
    (hdip1 : gameF (q + 2) (q + 2) < gameF (q + 1) (q + 1))
    (hv : v ∈ PrefixBackfillValues
      (StrictRowPrefixValues gameF (q + 1))
      (StrictRowPrefixValues gameF (q + 2)))
    (hi : i < q + 1)
    (hdiag : gameF i i = v) :
    i < q := by
  have hvNew := (List.mem_filter.mp hv).1
  rcases mem_strictRowPrefixValues_iff_C.mp hvNew with
    ⟨b, hb, hcell⟩
  have hrowMax := game_diagonal_maximal
    (q := q + 2) (s := b) (Nat.le_of_lt hb)
  have htwoDrop : gameF (q + 2) (q + 2) < gameF q q :=
    Nat.lt_trans hdip1 hdip0
  have hiLe : i <= q := by omega
  have hiNe : Not (i = q) := by
    intro hiEq
    subst i
    have hEq : gameF q q = gameF (q + 2) b :=
      hdiag.trans hcell.symm
    omega
  omega

/-- The complete backfill packets of two consecutive dips share the strict
upper-half owner budget below the first row. -/
theorem game_consecutive_dips_combined_backfill_owner_strict_packing
    {q : Nat}
    (hdip0 : gameF (q + 1) (q + 1) < gameF q q)
    (hdip1 : gameF (q + 2) (q + 2) < gameF (q + 1) (q + 1)) :
    let back0 := PrefixBackfillValues
      (StrictRowPrefixValues gameF q)
      (StrictRowPrefixValues gameF (q + 1))
    let back1 := PrefixBackfillValues
      (StrictRowPrefixValues gameF (q + 1))
      (StrictRowPrefixValues gameF (q + 2))
    2 * (back0.length + back1.length) + 1 <= q := by
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
    exact List.nodup_append.mpr
      ⟨hback0Nodup, hback1Nodup, hcross⟩

  have hownerExists : forall v, v ∈ values ->
      exists i, i < q /\ q < i + i /\ gameF i i = v := by
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
      exact ⟨i, hiq, by omega, hdiag⟩
    · rcases adjacent_dip_backfill_has_past_diagonal_owner
        gameRecurrenceModel hdip1 hv1 with ⟨i, hiq, hdiag⟩
      have hiqStrict := second_consecutive_dip_backfill_owner_lt_first_row
        hdip0 hdip1 hv1 hiq hdiag
      have hvNew := (List.mem_filter.mp hv1).1
      rcases mem_strictRowPrefixValues_iff_C.mp hvNew with
        ⟨b, hb, hcell⟩
      have hhigh := game_past_diagonal_reemission_is_high
        (i := i) (t := q + 2) (b := b)
        (Nat.le_of_lt hb) (hdiag.trans hcell.symm)
      have hcap := recurrence_diagonal_source_capacity
        gameRecurrenceModel i
      change gameF i i <= i + i + 1 at hcap
      exact ⟨i, hiqStrict, by omega, hdiag⟩

  let owner : Nat -> Nat := fun v =>
    if hv : v ∈ values then Classical.choose (hownerExists v hv) else 0
  have howner : forall v, v ∈ values ->
      owner v < q /\ q < owner v + owner v /\
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
    r53_nodup_map_of_injective_on owner values hvaluesNodup hownerInj
  have hownersBand : forall i, i ∈ values.map owner ->
      i < q /\ q < i + i := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨v, hv, rfl⟩
    exact ⟨(howner v hv).1, (howner v hv).2.1⟩
  have hback0Positive : 0 < back0.length := by
    have hpkg := adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
      gameRecurrenceModel (forbidden := []) hdip0
        (by simp) (by simp) (by simp)
    change 1 <= back0.length /\ _ at hpkg
    omega
  have hvaluesPositive : 0 < values.length := by
    simp only [values, List.length_append]
    omega
  have hpack := strict_upper_half_owner_packing
    hownersNodup (by simpa using hvaluesPositive) hownersBand
  simp only [List.length_map] at hpack
  change 2 * values.length + 1 <= q at hpack
  simpa [values, back0, back1] using hpack

/-- Strict cross-edge amortization for two forbidden packets. -/
theorem game_consecutive_dips_two_forbidden_packets_strict_amortized_bound
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
    2 * (forbidden0.length + forbidden1.length) + 5 <= q := by
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
  have hpack := game_consecutive_dips_combined_backfill_owner_strict_packing
    hdip0 hdip1
  change 2 * (back0.length + back1.length) + 1 <= q at hpack
  omega

/-- Event-E specialization of the strict two-edge budget.  The two named
diagonal values add one forbidden value on each edge, so the generic `+5`
becomes `+9` for the two missing-slot populations. -/
theorem gameF_eventE_strict_cross_edge_missing_bound
    {s delta z c b0 b1 : Nat}
    (hdip0 : gameF (s + 1) (s + 1) < gameF s s)
    (hdip1 : gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1))
    (hc : c < s) (hSucc : gameF s c = z + 1)
    (hNextDiag : gameF (s + 1) (s + 1) = z + 1)
    (hb1 : b1 < s + 1) (hHost1 : gameF (s + 1) b1 = z)
    (hEmit : gameF (s + 2) (s + 2) = z)
    (hslotsNodup : (EventEDefectBandSlots s delta c b0).Nodup)
    (hslotsData : forall g, g ∈ EventEDefectBandSlots s delta c b0 ->
      g < s /\ gameF s g < z) :
    2 * ((EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length) + 9 <= s := by
  let slots := EventEDefectBandSlots s delta c b0
  let missing0 := EventEMissingBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let missing1 := EventESecondMissingBandSlots s delta c b0
  let low0 := missing0.map (fun g => gameF s g)
  let low1 := missing1.map (fun g => gameF s g)
  let forbidden0 := low0 ++ [z + 1]
  let forbidden1 := low1 ++ [z]

  have hmissing0Nodup : missing0.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hsurvivorsNodup : survivors.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hmissing1Nodup : missing1.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hlow0Nodup : low0.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) missing0 hmissing0Nodup
    intro g hg k hk heq
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hk).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) heq
  have hlow1Nodup : low1.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) missing1 hmissing1Nodup
    intro g hg k hk heq
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hkSurv : k ∈ survivors := (List.mem_filter.mp hk).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) heq

  have hdisjoint0 : forall v, v ∈ low0 -> forall w, w ∈ [z + 1] ->
      v ≠ w := by
    intro v hv w hw hEq
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hLower := (hslotsData g hgSlots).2
    omega
  have hdisjoint1 : forall v, v ∈ low1 -> forall w, w ∈ [z] ->
      v ≠ w := by
    intro v hv w hw hEq
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hLower := (hslotsData g hgSlots).2
    omega
  have hforbidden0Nodup : forbidden0.Nodup :=
    List.nodup_append.mpr ⟨hlow0Nodup, by simp, hdisjoint0⟩
  have hforbidden1Nodup : forbidden1.Nodup :=
    List.nodup_append.mpr ⟨hlow1Nodup, by simp, hdisjoint1⟩

  have hsub0 : forbidden0 ⊆ StrictRowPrefixValues gameF s := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
      exact List.mem_map.mpr
        ⟨g, List.mem_range.mpr (hslotsData g hgSlots).1, rfl⟩
    · simp only [List.mem_singleton] at hvHigh
      subst v
      exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, hSucc⟩
  have hmissing0 : forall v, v ∈ forbidden0 ->
      v ∉ StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing0, EventEMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      rw [← hNextDiag]
      exact diagonal_value_absent_strict_prefix
        gameRecurrenceModel (s + 1)

  have hsub1 : forbidden1 ⊆ StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
      have hfilter := (List.mem_filter.mp hgSurv).2
      simpa [survivors, EventESurvivingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      exact List.mem_map.mpr
        ⟨b1, List.mem_range.mpr hb1, hHost1⟩
  have hmissing1 : forall v, v ∈ forbidden1 ->
      v ∉ StrictRowPrefixValues gameF (s + 2) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing1, EventESecondMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      rw [← hEmit]
      exact diagonal_value_absent_strict_prefix
        gameRecurrenceModel (s + 2)

  have hbound :=
    game_consecutive_dips_two_forbidden_packets_strict_amortized_bound
      hdip0 hdip1 hforbidden0Nodup hsub0 hmissing0
        hforbidden1Nodup hsub1 hmissing1
  have hlen0 : forbidden0.length = missing0.length + 1 := by
    simp [forbidden0, low0]
  have hlen1 : forbidden1.length = missing1.length + 1 := by
    simp [forbidden1, low1]
  change 2 * (missing0.length + missing1.length) + 9 <= s
  omega

#print axioms second_consecutive_dip_backfill_owner_lt_first_row
#print axioms game_consecutive_dips_combined_backfill_owner_strict_packing
#print axioms game_consecutive_dips_two_forbidden_packets_strict_amortized_bound
#print axioms gameF_eventE_strict_cross_edge_missing_bound

end ChompLean
