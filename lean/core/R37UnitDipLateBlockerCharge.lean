import R33UnitDipFirstGapTrichotomy
import R27ActualGameGapCharge

set_option autoImplicit false

namespace ChompLean

/-!
R37: actual-game sharpening of R33's late-blocker first-gap atom.

R33 supplies an exceptional preview host `gameF s b = z` strictly before a
freeze `s < r < z`, while row `s+1` has lost `z`.  After the freeze, every
row `r<x<z` has a row-start-propagation host below `r`.  Actual encoding
no-repeat makes all of those host columns pairwise distinct and also keeps
them distinct from the old preview column `b`.

This is the R27 finite charge with one extra, already-consumed column.  The
`z-r-1` active rows plus the preview occupy distinct columns in `[0,r)`, so
`z-r <= r`, equivalently `z <= 2*r`.  Thus an entire early-freeze class is
eliminated without RM2 or UnitDip.
-/

/-- Local list helper used by the augmented charge. -/
private theorem r37_nodup_map_of_injective_on
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

/-- Augmented R27 charge.  One pre-freeze preview host plus all post-freeze
row-start-propagation hosts fit injectively into the `r` columns below the
freeze. -/
theorem gameF_preview_plus_active_hosts_capacity
    {s b r z : Nat}
    (hbs : b < s) (hsr : s < r) (hrz : r < z)
    (hpreview : gameF s b = z)
    (hstart : gameF z r = z) :
    z - r <= r := by
  classical
  let xs := s :: List.range' (r + 1) (z - r - 1)
  have hclass : forall x, x ∈ xs -> x = s \/ (r < x /\ x < z) := by
    intro x hx
    change x ∈ s :: List.range' (r + 1) (z - r - 1) at hx
    rcases List.mem_cons.mp hx with hxsEq | hxrange
    · exact Or.inl hxsEq
    · right
      have hrange := List.mem_range'_1.mp hxrange
      omega
  have hxs : xs.Nodup := by
    change (s :: List.range' (r + 1) (z - r - 1)).Nodup
    rw [List.nodup_cons]
    constructor
    · intro hmem
      have hrange := List.mem_range'_1.mp hmem
      omega
    · exact List.nodup_range' 1
  have hex : forall x, x ∈ xs ->
      exists c, c < r /\ c < x /\ gameF x c = z := by
    intro x hx
    rcases hclass x hx with rfl | hxActive
    · exact ⟨b, by omega, hbs, hpreview⟩
    · rcases rowStartPropagation gameRecurrenceModel hstart hrz
        hxActive.1 hxActive.2 with ⟨c, hcr, hhost⟩
      exact ⟨c, hcr, by omega, hhost⟩
  have hupper : forall x, x ∈ xs -> x < z := by
    intro x hx
    rcases hclass x hx with rfl | hxActive
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
  have hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
      host x = host y -> x = y := by
    intro x hx y hy hxy
    by_cases hEq : x = y
    · exact hEq
    have hxHost := hhost x hx
    have hyHost := hhost y hy
    by_cases hlt : x < y
    · exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hxHost.2.1 hlt (hupper y hy) hxHost.2.2
          (by simpa [hxy] using hyHost.2.2))
    · have hyx : y < x := by omega
      exact False.elim
        (encoding_same_lower_no_repeat game_encodes
          hyHost.2.1 hyx (hupper x hx) hyHost.2.2
          (by simpa [hxy] using hxHost.2.2))
  have hmapNodup : (xs.map host).Nodup :=
    r37_nodup_map_of_injective_on host xs hxs hinj
  have hsubset : xs.map host ⊆ List.range' 0 r := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨x, hx, rfl⟩
    apply List.mem_range'_1.mpr
    exact ⟨Nat.zero_le _, by simpa using (hhost x hx).1⟩
  have hbound := nodup_subset_length_le hmapNodup hsubset
  have hlen : xs.length = z - r := by
    dsimp [xs]
    simp
    omega
  have hraw : xs.length <= r := by
    simpa using hbound
  rw [hlen] at hraw
  exact hraw

/-- Every active post-freeze row has a unique host below `r`, and actual
no-repeat forbids reuse of the exceptional preview column. -/
theorem gameF_active_hosts_unique_and_avoid_preview
    {s b r z : Nat}
    (hbs : b < s) (hsr : s < r) (hrz : r < z)
    (hpreview : gameF s b = z)
    (hstart : gameF z r = z) :
    forall x, r < x -> x < z ->
      exists c,
        c < r /\ c ≠ b /\ gameF x c = z /\
        forall c', c' < r -> gameF x c' = z -> c' = c := by
  intro x hrx hxz
  rcases rowStartPropagation gameRecurrenceModel hstart hrz hrx hxz with
    ⟨c, hcr, hhost⟩
  have hcb : c ≠ b := by
    intro hEq
    subst c
    exact encoding_same_lower_no_repeat game_encodes
      hbs (by omega) hxz hpreview hhost
  refine ⟨c, hcr, hcb, hhost, ?_⟩
  intro c' hc'r hc'host
  exact gameRecurrenceModel.fixed_q_injective
    (by omega) (by omega) (hc'host.trans hhost.symm)

/-- Sharp actual-game coordinates of R33's late-blocker atom.  Besides the
preview/freeze chain, this packages the improved finite charge and the
unique moved-host corridor. -/
theorem gameF_dip_first_gap_late_blocker_sharp_coordinates
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    exists b r,
      b < s /\ s + 1 <= r /\
      r < DipFirstGap gameRecurrenceModel s /\
      gameF s b = DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      Not (B gameF (s + 1) (s + 1)
        (DipFirstGap gameRecurrenceModel s)) /\
      DipFirstGap gameRecurrenceModel s - r <= r /\
      DipFirstGap gameRecurrenceModel s <= r + r /\
      (forall x, r < x -> x < DipFirstGap gameRecurrenceModel s ->
        exists c,
          c < r /\ c ≠ b /\
          gameF x c = DipFirstGap gameRecurrenceModel s /\
          forall c', c' < r ->
            gameF x c' = DipFirstGap gameRecurrenceModel s -> c' = c) := by
  rcases hLate with
    ⟨_hgap, r, hrLate, hrz, hstart, hOldC, hNewMissing⟩
  rcases hOldC with ⟨b, hbs, hpreview⟩
  have hsr : s < r := by omega
  have hcap := gameF_preview_plus_active_hosts_capacity
    hbs hsr hrz hpreview hstart
  have hhalf : DipFirstGap gameRecurrenceModel s <= r + r := by
    omega
  have hcorridor := gameF_active_hosts_unique_and_avoid_preview
    hbs hsr hrz hpreview hstart
  exact ⟨b, r, hbs, hrLate, hrz, hpreview, hstart,
    hNewMissing, hcap, hhalf, hcorridor⟩

/-- Explicit eliminated class: the first-gap blocker cannot have any
row-start/freeze witness strictly below the halfway point.  Fixed-row
injectivity identifies any proposed witness with the charged witness. -/
theorem gameF_dip_first_gap_late_blocker_has_no_early_freeze
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    Not (exists r,
      r < DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      r + r < DipFirstGap gameRecurrenceModel s) := by
  rcases gameF_dip_first_gap_late_blocker_sharp_coordinates hLate with
    ⟨_b, r, _hbs, _hrLate, hrz, _hpreview, hstart,
      _hMissing, _hcap, hhalf, _hcorridor⟩
  rintro ⟨r', hr'z, hstart', hearly⟩
  have hrr' : r = r' :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hrz) (Nat.le_of_lt hr'z)
      (hstart.trans hstart'.symm)
  omega

/-- The dip-row `V1` has only two possibilities.  It is the boundary value
`s+1`, or it is high; in the high case the R27 future-gap normal form starts
immediately at prefix `s`. -/
theorem gameF_late_blocker_first_gap_v1_boundary_or_R27_gap
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    let z := DipFirstGap gameRecurrenceModel s
    let q := gameF (s + 1) s
    exists r,
      r < z /\ gameF z r = z /\
      (q = s + 1 \/
        (s + 1 < q /\ q < z /\
          exists x,
            s + 1 < x /\ x < z /\ Not (C gameF x s z) /\
            (x <= r \/
              Not (B gameF x s z) \/
              exists a, s < a /\ a < x /\ gameF a s = z))) := by
  dsimp only
  rcases hLate with
    ⟨_hgap, r, _hrLate, hrz, hstart, _hOldC, hNewMissing⟩
  let z := DipFirstGap gameRecurrenceModel s
  let q := gameF (s + 1) s
  have hqLower : s < q := by
    exact gameRecurrenceModel.value_gt_index (by omega)
  have hqMax : q <= gameF (s + 1) (s + 1) := by
    exact diagonalMaximal gameRecurrenceModel (by omega)
  have hqz : q < z := by
    change q < gameRecurrenceModel.f (s + 1) (s + 1) + 1
    change q <= gameRecurrenceModel.f (s + 1) (s + 1) at hqMax
    omega
  by_cases hboundary : q = s + 1
  · exact ⟨r, hrz, hstart, Or.inl hboundary⟩
  · refine ⟨r, hrz, hstart, Or.inr ?_⟩
    have htq : s + 1 < q := by omega
    have hgapC : Not (C gameF (s + 1) s z) := by
      rintro ⟨b, hbs, hhost⟩
      apply hNewMissing
      right
      exact ⟨b, by omega, hhost⟩
    rcases gameF_future_gap_prefreeze_or_source_gap_or_boundary_owner
        (c := s) (t := s + 1) (q := q) (z := z) (r := r)
        (by omega) rfl htq hqz hgapC hrz hstart with
      ⟨x, htx, hxz, hxgap, hxcase⟩
    refine ⟨htq, hqz, x, htx, hxz, hxgap, ?_⟩
    simpa using hxcase

/-- Owner-free non-unit dips inherit the sharp late-freeze bound.  This
eliminates the entire class in which the only first-gap opening is a
blocker with `2*r < z`. -/
theorem gameF_owner_free_nonunit_dip_has_halfway_late_freeze
    {s : Nat}
    (hgap : DipFirstGap gameRecurrenceModel s < gameF s s)
    (hNoDiagonal : forall a,
      gameF a a ≠ DipFirstGap gameRecurrenceModel s) :
    exists b r,
      b < s /\ s + 1 <= r /\
      r < DipFirstGap gameRecurrenceModel s /\
      gameF s b = DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      DipFirstGap gameRecurrenceModel s <= r + r := by
  have hLate :=
    nonunit_dip_without_diagonal_first_gap_is_late_blocker_loss
      gameRecurrenceModel hgap hNoDiagonal
  rcases gameF_dip_first_gap_late_blocker_sharp_coordinates hLate with
    ⟨b, r, hbs, hrLate, hrz, hpreview, hstart,
      _hMissing, _hcap, hhalf, _hcorridor⟩
  exact ⟨b, r, hbs, hrLate, hrz, hpreview, hstart, hhalf⟩

/-- Owner-free form of the eliminated class. -/
theorem gameF_owner_free_nonunit_dip_has_no_early_freeze
    {s : Nat}
    (hgap : DipFirstGap gameRecurrenceModel s < gameF s s)
    (hNoDiagonal : forall a,
      gameF a a ≠ DipFirstGap gameRecurrenceModel s) :
    Not (exists r,
      r < DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      r + r < DipFirstGap gameRecurrenceModel s) := by
  have hLate :=
    nonunit_dip_without_diagonal_first_gap_is_late_blocker_loss
      gameRecurrenceModel hgap hNoDiagonal
  exact gameF_dip_first_gap_late_blocker_has_no_early_freeze hLate

end ChompLean
