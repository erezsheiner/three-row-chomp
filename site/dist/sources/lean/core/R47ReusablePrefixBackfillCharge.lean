import R43FutureDiagonalSourceCapacityCollapse

set_option autoImplicit false

namespace ChompLean

/-!
R47: reusable prefix-exchange and diagonal-backfill charge.

The combinatorial core is independent of Chomp and of the recurrence.  If
`old` is a duplicate-free list, `new` is a duplicate-free list at least one
entry longer, and `forbidden` is a duplicate-free subfamily of `old` which
is disjoint from `new`, then at least `forbidden.length+1` entries of `new`
are absent from `old`.

The recurrence wrapper applies this to strict row prefixes across an
adjacent diagonal dip.  Every new-only value is positive and below the old
diagonal; old exact MEX puts it in the old blocked source, while new-only
excludes the row-prefix channel.  It therefore has a past diagonal owner.

No FutureFirstGap, RM2, or UnitDip assumption is used.
-/

/-- Values in `new` which already occur in `old`. -/
def PrefixCarryValues (old new : List Nat) : List Nat :=
  new.filter (fun v => decide (v ∈ old))

/-- Values in `new` which do not occur in `old`. -/
def PrefixBackfillValues (old new : List Nat) : List Nat :=
  new.filter (fun v => !(decide (v ∈ old)))

/-- The exact finite balance behind prefix backfill counting.  The displayed
inequality is useful even when the new list grows by more than one. -/
theorem prefix_exchange_forbidden_balance
    {old new forbidden : List Nat}
    (hnew : new.Nodup)
    (hforbidden : forbidden.Nodup)
    (hsub : forbidden ⊆ old)
    (hmissing : forall v, v ∈ forbidden -> v ∉ new) :
    forbidden.length + new.length <=
      old.length + (PrefixBackfillValues old new).length := by
  let carries := PrefixCarryValues old new
  have hcarryNodup : carries.Nodup := by
    exact List.filter_sublist.nodup hnew
  have hcross : forall a, a ∈ forbidden ->
      forall b, b ∈ carries -> a ≠ b := by
    intro a ha b hb hEq
    have hbNew : b ∈ new := (List.mem_filter.mp hb).1
    subst b
    exact hmissing a ha hbNew
  have hunionNodup : (forbidden ++ carries).Nodup := by
    exact List.nodup_append.mpr
      ⟨hforbidden, hcarryNodup, hcross⟩
  have hunionSub : forbidden ++ carries ⊆ old := by
    intro v hv
    rcases List.mem_append.mp hv with hvForbidden | hvCarry
    · exact hsub hvForbidden
    · have hmem := (List.mem_filter.mp hvCarry).2
      simpa [carries, PrefixCarryValues] using hmem
  have hcapacity := nodup_subset_length_le hunionNodup hunionSub
  have hcarryCap : forbidden.length + carries.length <= old.length := by
    simpa using hcapacity
  have hpartition :
      new.length = carries.length + (PrefixBackfillValues old new).length := by
    have hraw := List.length_eq_countP_add_countP
      (fun v => decide (v ∈ old)) (l := new)
    simp only [List.countP_eq_length_filter] at hraw
    simpa [carries, PrefixCarryValues, PrefixBackfillValues] using hraw
  omega

/-- Unit-growth corollary: `k` forbidden old values force at least `k+1`
new-only values. -/
theorem prefix_exchange_k_forbidden_force_k_succ_backfills
    {old new forbidden : List Nat}
    (hnew : new.Nodup)
    (hforbidden : forbidden.Nodup)
    (hsub : forbidden ⊆ old)
    (hmissing : forall v, v ∈ forbidden -> v ∉ new)
    (hgrowth : old.length + 1 <= new.length) :
    forbidden.length + 1 <= (PrefixBackfillValues old new).length := by
  have hbalance := prefix_exchange_forbidden_balance
    hnew hforbidden hsub hmissing
  omega

/-- Strict row-prefix values, in column order. -/
def StrictRowPrefixValues (f : Nat -> Nat -> Nat) (q : Nat) : List Nat :=
  (List.range q).map (fun b => f q b)

/-- List membership is exactly strict row-prefix membership `C(f,q,q)`. -/
theorem mem_strictRowPrefixValues_iff_C
    {f : Nat -> Nat -> Nat} {q v : Nat} :
    v ∈ StrictRowPrefixValues f q <-> C f q q v := by
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨b, hb, hvalue⟩
    exact ⟨b, List.mem_range.mp hb, hvalue⟩
  · rintro ⟨b, hb, hvalue⟩
    exact List.mem_map.mpr
      ⟨b, List.mem_range.mpr hb, hvalue⟩

private theorem r47_nodup_map_of_injective_on
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

/-- Column-indexed form of the pure exchange theorem.  An old prefix has
`n` cells, a new prefix has `n+1`, and `reserved` names `k` distinct old
columns whose values cannot occur in any new cell.  Injectivity of both
prefixes turns these into `k` distinct forbidden values and yields at least
`k+1` new-only cells. -/
theorem prefix_columns_k_reserved_force_k_succ_backfills
    {n : Nat} {oldValue newValue : Nat -> Nat}
    {reserved : List Nat}
    (holdInjective : forall c₁, c₁ < n -> forall c₂, c₂ < n ->
      oldValue c₁ = oldValue c₂ -> c₁ = c₂)
    (hnewInjective : forall b₁, b₁ < n + 1 ->
      forall b₂, b₂ < n + 1 ->
      newValue b₁ = newValue b₂ -> b₁ = b₂)
    (hreservedNodup : reserved.Nodup)
    (hreservedRange : reserved ⊆ List.range n)
    (hreservedMissing : forall c, c ∈ reserved ->
      forall b, b < n + 1 -> newValue b ≠ oldValue c) :
    reserved.length + 1 <=
      (PrefixBackfillValues
        ((List.range n).map oldValue)
        ((List.range (n + 1)).map newValue)).length := by
  let old := (List.range n).map oldValue
  let new := (List.range (n + 1)).map newValue
  let forbidden := reserved.map oldValue
  have hnewNodup : new.Nodup := by
    apply r47_nodup_map_of_injective_on
    · exact List.nodup_range
    · intro b₁ hb₁ b₂ hb₂ hEq
      exact hnewInjective b₁ (List.mem_range.mp hb₁)
        b₂ (List.mem_range.mp hb₂) hEq
  have hforbiddenNodup : forbidden.Nodup := by
    apply r47_nodup_map_of_injective_on
    · exact hreservedNodup
    · intro c₁ hc₁ c₂ hc₂ hEq
      exact holdInjective c₁
        (List.mem_range.mp (hreservedRange hc₁)) c₂
        (List.mem_range.mp (hreservedRange hc₂)) hEq
  have hforbiddenSub : forbidden ⊆ old := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨c, hc, rfl⟩
    exact List.mem_map.mpr ⟨c, hreservedRange hc, rfl⟩
  have hforbiddenMissing : forall v, v ∈ forbidden -> v ∉ new := by
    intro v hv hnewMem
    rcases List.mem_map.mp hv with ⟨c, hc, hcv⟩
    rcases List.mem_map.mp hnewMem with ⟨b, hb, hbv⟩
    apply hreservedMissing c hc b (List.mem_range.mp hb)
    exact hbv.trans hcv.symm
  have hgrowth : old.length + 1 <= new.length := by
    simp [old, new]
  have hcount := prefix_exchange_k_forbidden_force_k_succ_backfills
    hnewNodup hforbiddenNodup hforbiddenSub hforbiddenMissing hgrowth
  simpa [old, new, forbidden] using hcount

/-- Every recurrence-model strict row prefix is duplicate-free. -/
theorem strictRowPrefixValues_nodup
    (M : RecurrenceModel) (q : Nat) :
    (StrictRowPrefixValues M.f q).Nodup := by
  apply r47_nodup_map_of_injective_on
  · exact List.nodup_range
  · intro b₁ hb₁ b₂ hb₂ hEq
    exact M.fixed_q_injective
      (Nat.le_of_lt (List.mem_range.mp hb₁))
      (Nat.le_of_lt (List.mem_range.mp hb₂)) hEq

/-- MEX-to-owner conversion in its most reusable form.  A positive value
below an old diagonal which is absent from that row's strict prefix must be
supplied by the other diagonal-source channel. -/
theorem old_diagonal_mex_backfill_has_past_owner
    (M : RecurrenceModel) {q v : Nat}
    (hvPos : 0 < v)
    (hvBelow : v < M.f q q)
    (hvNotOld : v ∉ StrictRowPrefixValues M.f q) :
    exists i, i < q /\ M.f i i = v := by
  have hvB : B M.f q q v :=
    M.mex_no_skip (Nat.le_refl q) (M.diagonal_gt q)
      hvPos hvBelow
  have hvR : R M.f q q v := by
    rcases hvB with hR | hC
    · exact hR
    · exact False.elim
        (hvNotOld (mem_strictRowPrefixValues_iff_C.mpr hC))
  rcases hvR with ⟨i, hiq, hdiag⟩
  have hmin : min i q = i := Nat.min_eq_left (Nat.le_of_lt hiq)
  rw [hmin] at hdiag
  exact ⟨i, hiq, hdiag⟩

/-- Reusable recurrence wrapper.  Across any adjacent diagonal dip, every
new strict-prefix value which was not carried from the old strict prefix has
a diagonal owner strictly before the old row. -/
theorem adjacent_dip_backfill_has_past_diagonal_owner
    (M : RecurrenceModel) {q v : Nat}
    (hdip : M.f (q + 1) (q + 1) < M.f q q)
    (hvBackfill :
      v ∈ PrefixBackfillValues
        (StrictRowPrefixValues M.f q)
        (StrictRowPrefixValues M.f (q + 1))) :
    exists i,
      i < q /\ M.f i i = v := by
  have hvFilter := List.mem_filter.mp hvBackfill
  have hvNew : v ∈ StrictRowPrefixValues M.f (q + 1) :=
    hvFilter.1
  have hvNotOld : v ∉ StrictRowPrefixValues M.f q := by
    simpa [PrefixBackfillValues] using hvFilter.2
  rcases (mem_strictRowPrefixValues_iff_C.mp hvNew) with
    ⟨b, hb, hvalue⟩
  have hvPos : 0 < v := by
    have hgt := M.value_gt_index
      (q := q + 1) (r := b) (Nat.le_of_lt hb)
    rw [hvalue] at hgt
    omega
  have hvLeNext : v <= M.f (q + 1) (q + 1) := by
    have hmax := diagonalMaximal M
      (q := q + 1) (s := b) (Nat.le_of_lt hb)
    rw [hvalue] at hmax
    exact hmax
  have hvOld : v < M.f q q := by omega
  exact old_diagonal_mex_backfill_has_past_owner
    M hvPos hvOld hvNotOld

/-- Full `k -> k+1` diagonal-backfill package for an adjacent dip.  The
forbidden family can be any duplicate-free old-prefix subfamily absent from
the new prefix; it need not arise from a first-gap episode. -/
theorem adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills
    (M : RecurrenceModel) {q : Nat} {forbidden : List Nat}
    (hdip : M.f (q + 1) (q + 1) < M.f q q)
    (hforbidden : forbidden.Nodup)
    (hsub : forbidden ⊆ StrictRowPrefixValues M.f q)
    (hmissing : forall v, v ∈ forbidden ->
      v ∉ StrictRowPrefixValues M.f (q + 1)) :
    let backfills := PrefixBackfillValues
      (StrictRowPrefixValues M.f q)
      (StrictRowPrefixValues M.f (q + 1))
    forbidden.length + 1 <= backfills.length /\
      backfills.Nodup /\
      forall v, v ∈ backfills ->
        exists i, i < q /\ M.f i i = v := by
  dsimp only
  let old := StrictRowPrefixValues M.f q
  let new := StrictRowPrefixValues M.f (q + 1)
  let backfills := PrefixBackfillValues old new
  have hnew : new.Nodup := strictRowPrefixValues_nodup M (q + 1)
  have hgrowth : old.length + 1 <= new.length := by
    simp [old, new, StrictRowPrefixValues]
  have hcount : forbidden.length + 1 <= backfills.length := by
    apply prefix_exchange_k_forbidden_force_k_succ_backfills
      hnew hforbidden
    · exact hsub
    · intro v hv
      exact hmissing v hv
    · exact hgrowth
  have hbackfillNodup : backfills.Nodup := by
    exact List.filter_sublist.nodup hnew
  refine ⟨hcount, hbackfillNodup, ?_⟩
  intro v hv
  exact adjacent_dip_backfill_has_past_diagonal_owner M hdip hv

#print axioms prefix_exchange_forbidden_balance
#print axioms prefix_exchange_k_forbidden_force_k_succ_backfills
#print axioms prefix_columns_k_reserved_force_k_succ_backfills
#print axioms mem_strictRowPrefixValues_iff_C
#print axioms strictRowPrefixValues_nodup
#print axioms old_diagonal_mex_backfill_has_past_owner
#print axioms adjacent_dip_backfill_has_past_diagonal_owner
#print axioms adjacent_dip_k_forbidden_force_k_succ_diagonal_backfills

end ChompLean
