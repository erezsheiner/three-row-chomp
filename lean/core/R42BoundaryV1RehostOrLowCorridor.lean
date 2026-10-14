import R40UnitDipBoundaryV1StrictCharge

set_option autoImplicit false

namespace ChompLean

/-!
R42: one more pre-freeze rehost, or a complete low-diagonal corridor.

R40 leaves `z < 2*r` in the boundary-`V1` branch.  If `z` is hosted on
even one additional row `s+1<y<=r`, that host joins the preview and all
post-freeze hosts in the no-repeat charge.  Column `s` is still forbidden
by the boundary constant tail.  Hence `z-r+1` objects fit into `r-1`
columns and `z+2 <= 2*r`.

If there is no such rehost, the exact prefreeze host/diagonal criterion
forces `d(y)<z` on every row from `s+1` through the freeze.  Thus the R40
residue reduces to a strictly stronger capacity branch or one named
low-diagonal-corridor atom.  No RM2 or UnitDip is assumed.
-/

private theorem r42_nodup_map_of_injective_on
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) (xs : List alpha)
    (hxs : xs.Nodup)
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs -> f x = f y -> x = y) :
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

/-- Strict charge with one additional pre-freeze rehost. -/
theorem gameF_boundary_preview_rehost_plus_active_hosts_capacity
    {s b y c r z : Nat}
    (hbs : b < s)
    (hty : s + 1 < y) (hyr : y <= r) (hrz : r < z)
    (hpreview : gameF s b = z)
    (hrehCol : c < y) (hrehost : gameF y c = z)
    (hstart : gameF z r = z)
    (hboundary : gameF (s + 1) s = s + 1) :
    z + 2 <= r + r := by
  classical
  let xs := s :: y :: List.range' (r + 1) (z - r - 1)
  have hclass : forall x, x ∈ xs ->
      x = s \/ x = y \/ (r < x /\ x < z) := by
    intro x hx
    change x ∈ s :: y :: List.range' (r + 1) (z - r - 1) at hx
    rcases List.mem_cons.mp hx with hxsEq | hxrest
    · exact Or.inl hxsEq
    · rcases List.mem_cons.mp hxrest with hxyEq | hxrange
      · exact Or.inr (Or.inl hxyEq)
      · right
        right
        have hrange := List.mem_range'_1.mp hxrange
        omega
  have hxs : xs.Nodup := by
    change (s :: y :: List.range' (r + 1) (z - r - 1)).Nodup
    rw [List.nodup_cons, List.nodup_cons]
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with hEq | hrange
      · omega
      · have hrange := List.mem_range'_1.mp hrange
        omega
    · constructor
      · intro hrange
        have hrange := List.mem_range'_1.mp hrange
        omega
      · exact List.nodup_range' 1
  have hex : forall x, x ∈ xs ->
      exists k, k < r /\ k < x /\ gameF x k = z := by
    intro x hx
    rcases hclass x hx with rfl | rfl | hxActive
    · exact ⟨b, by omega, hbs, hpreview⟩
    · exact ⟨c, by omega, hrehCol, hrehost⟩
    · rcases rowStartPropagation gameRecurrenceModel hstart hrz
        hxActive.1 hxActive.2 with ⟨k, hkr, hhost⟩
      exact ⟨k, hkr, by omega, hhost⟩
  have hupper : forall x, x ∈ xs -> x < z := by
    intro x hx
    rcases hclass x hx with rfl | rfl | hxActive
    · omega
    · omega
    · exact hxActive.2
  let host : Nat -> Nat := fun x =>
    if hx : x ∈ xs then Classical.choose (hex x hx) else 0
  have hhost : forall x, x ∈ xs ->
      host x < r /\ host x < x /\ gameF x (host x) = z := by
    intro x hx
    dsimp [host]
    rw [dif_pos hx]
    exact Classical.choose_spec (hex x hx)
  have hinj : forall x, x ∈ xs -> forall x', x' ∈ xs ->
      host x = host x' -> x = x' := by
    intro x hx x' hx' hsame
    by_cases hEq : x = x'
    · exact hEq
    have hxHost := hhost x hx
    have hx'Host := hhost x' hx'
    by_cases hlt : x < x'
    · exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hxHost.2.1 hlt (hupper x' hx') hxHost.2.2
          (by simpa [hsame] using hx'Host.2.2))
    · have hx'x : x' < x := by omega
      exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hx'Host.2.1 hx'x (hupper x hx) hx'Host.2.2
          (by simpa [hsame] using hxHost.2.2))
  have havoid : forall x, x ∈ xs -> host x ≠ s := by
    intro x hx hEq
    have hxHost := hhost x hx
    rcases hclass x hx with rfl | rfl | hxActive
    · omega
    · have hconst := gameF_boundary_v1_constant_column hboundary x (by omega)
      rw [hEq, hconst] at hxHost
      omega
    · have hconst := gameF_boundary_v1_constant_column hboundary x (by omega)
      rw [hEq, hconst] at hxHost
      omega
  have hmapNodup : (xs.map host).Nodup :=
    r42_nodup_map_of_injective_on host xs hxs hinj
  let cols := List.range' 0 s ++ List.range' (s + 1) (r - s - 1)
  have hsubset : xs.map host ⊆ cols := by
    intro k hk
    rcases List.mem_map.mp hk with ⟨x, hx, rfl⟩
    apply List.mem_append.mpr
    by_cases hks : host x < s
    · left
      apply List.mem_range'_1.mpr
      exact ⟨Nat.zero_le _, by simpa using hks⟩
    · right
      apply List.mem_range'_1.mpr
      constructor
      · have hne := havoid x hx
        omega
      · have hkr := (hhost x hx).1
        omega
  have hbound := nodup_subset_length_le hmapNodup hsubset
  have hxsLen : xs.length = z - r + 1 := by
    dsimp [xs]
    simp
    omega
  have hcolsLen : cols.length = r - 1 := by
    dsimp [cols]
    simp
    omega
  have hraw : xs.length <= cols.length := by simpa using hbound
  rw [hxsLen, hcolsLen] at hraw
  omega

/-- Complete boundary residue after the strengthened charge. -/
theorem gameF_late_blocker_boundary_v1_rehost_or_low_diagonal_corridor
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1) :
    exists b r,
      b < s /\ s + 1 <= r /\
      r < DipFirstGap gameRecurrenceModel s /\
      gameF s b = DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      DipFirstGap gameRecurrenceModel s < r + r /\
      (((exists y,
          s + 1 < y /\ y <= r /\
          C gameF y y (DipFirstGap gameRecurrenceModel s)) /\
        DipFirstGap gameRecurrenceModel s + 2 <= r + r) \/
       (forall y, s + 1 <= y -> y <= r ->
          gameF y y < DipFirstGap gameRecurrenceModel s)) := by
  rcases hLate with
    ⟨_hgap, r, hrLate, hrz, hstart, hOldC, hNewMissing⟩
  rcases hOldC with ⟨b, hbs, hpreview⟩
  have hstrict := gameF_boundary_preview_plus_active_hosts_strict_capacity
    hbs hrLate hrz hpreview hstart hboundary
  have hhalf : DipFirstGap gameRecurrenceModel s < r + r := by omega
  by_cases hRehost : exists y,
      s + 1 < y /\ y <= r /\
      C gameF y y (DipFirstGap gameRecurrenceModel s)
  · rcases hRehost with ⟨y, hty, hyr, c, hcy, hhost⟩
    have hstrong := gameF_boundary_preview_rehost_plus_active_hosts_capacity
      hbs hty hyr hrz hpreview hcy hhost hstart hboundary
    exact ⟨b, r, hbs, hrLate, hrz, hpreview, hstart, hhalf,
      Or.inl ⟨⟨y, hty, hyr, ⟨c, hcy, hhost⟩⟩, hstrong⟩⟩
  · have hcorridor : forall y, s + 1 <= y -> y <= r ->
        gameF y y < DipFirstGap gameRecurrenceModel s := by
      intro y hty hyr
      have hNoHost :
          Not (C gameF y y (DipFirstGap gameRecurrenceModel s)) := by
        by_cases hyEq : y = s + 1
        · subst y
          intro hC
          apply hNewMissing
          exact Or.inr hC
        · intro hC
          exact hRehost ⟨y, by omega, hyr, hC⟩
      exact (rowstart_missing_iff_above_diagonal
        gameRecurrenceModel hrz hstart).1 hNoHost
    exact ⟨b, r, hbs, hrLate, hrz, hpreview, hstart, hhalf,
      Or.inr hcorridor⟩

/-- The near-midpoint class `z=2*r-1` cannot afford a pre-freeze rehost;
it therefore forces the complete low-diagonal corridor. -/
theorem gameF_boundary_v1_near_midpoint_forces_low_diagonal_corridor
    {s r : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1)
    (hrz : r < DipFirstGap gameRecurrenceModel s)
    (hstart : gameF (DipFirstGap gameRecurrenceModel s) r =
      DipFirstGap gameRecurrenceModel s)
    (hnear : DipFirstGap gameRecurrenceModel s + 1 = r + r) :
    forall y, s + 1 <= y -> y <= r ->
      gameF y y < DipFirstGap gameRecurrenceModel s := by
  rcases gameF_late_blocker_boundary_v1_rehost_or_low_diagonal_corridor
      hLate hboundary with
    ⟨_b, r0, _hbs, _hrLate, hr0z, _hpreview, hstart0,
      _hhalf, hcase⟩
  have hrEq : r0 = r :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hr0z) (Nat.le_of_lt hrz)
      (hstart0.trans hstart.symm)
  subst r0
  rcases hcase with hRehost | hcorridor
  · omega
  · exact hcorridor

end ChompLean
