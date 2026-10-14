import R37UnitDipLateBlockerCharge

set_option autoImplicit false

namespace ChompLean

/-!
R40: the boundary `V1` branch of R37 is strictly more expensive.

Assume `q = gameF (s+1) s = s+1`.  The constant branch then fixes column
`s` to the value `s+1` forever.  In particular, none of the post-freeze
hosts of the first-gap blocker `z` can use column `s`.

R37 already charged the exceptional preview plus every active row to
distinct columns below `r`.  Removing the unavailable column `s` improves
the weak capacity `z-r <= r` to `z-r < r`, hence `z < 2*r`.  This removes
the midpoint case `z=2*r` as well as all earlier freezes, without RM2 or
UnitDip.
-/

/-- A boundary `V1` is frozen in its column by the constant branch. -/
theorem gameF_boundary_v1_constant_column
    {s : Nat} (hboundary : gameF (s + 1) s = s + 1) :
    forall y, s + 1 <= y -> gameF y s = s + 1 := by
  intro y hty
  have hsmall : gameF (s + 1) s < (s + 1) + 1 := by
    rw [hboundary]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := s + 1) (r := s) (by omega) hsmall (y - (s + 1))
  have hsum : s + 1 + (y - (s + 1)) = y := by omega
  change gameRecurrenceModel.f (s + 1) s = s + 1 at hboundary
  change gameRecurrenceModel.f y s = s + 1
  simpa [hsum, hboundary] using hconst

/-- Exact source normal form in the boundary branch.  The `V1` source has
MEX `s+1`; after adjoining that boundary output, the diagonal source has
MEX `d(s+1)`.  Below the diagonal, the only missing positive value from the
`V1` source is `s+1` itself.  Both the diagonal and its successor first gap
are absent from the `V1` source. -/
def DipBoundaryV1SourceNormalForm (s : Nat) : Prop :=
  let t := s + 1
  let x := gameF t t
  let z := DipFirstGap gameRecurrenceModel s
  IsMex (B gameF t s) t /\
  IsMex (B gameF t t) x /\
  (forall v, 0 < v -> v < x ->
    (B gameF t s v <-> v ≠ t)) /\
  Not (B gameF t s x) /\
  Not (B gameF t s z) /\
  (forall y, t <= y -> gameF y s = t)

theorem gameF_late_blocker_boundary_v1_exact_source_normal_form
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1) :
    DipBoundaryV1SourceNormalForm s := by
  dsimp only [DipBoundaryV1SourceNormalForm]
  rcases hLate with
    ⟨_hgap, _r, _hrLate, _hrz, _hstart, _hOldC, hzMissingDiag⟩
  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  have hmexSeat :
      IsMex (B gameF (s + 1) s) (s + 1) :=
    recurrence_host_at_least_row_is_mex hrec (by omega)
      (Nat.le_refl (s + 1)) hboundary
  have hmexDiag :
      IsMex (B gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1)) := by
    apply hrec.2 (Nat.le_refl (s + 1))
    omega
  have hbelow : forall v, 0 < v ->
      v < gameF (s + 1) (s + 1) ->
      (B gameF (s + 1) s v <-> v ≠ s + 1) := by
    intro v hvPos hvDiag
    constructor
    · intro hB hvEq
      subst v
      exact hmexSeat.2.1 hB
    · intro hvNe
      have hBDiag : B gameF (s + 1) (s + 1) v :=
        hmexDiag.2.2 v hvPos hvDiag
      rcases (previous_diagonal_source
          (f := gameF) (r := s) (p := v)).1 hBDiag with hB | hlast
      · exact hB
      · have hEq : s + 1 = v := hboundary.symm.trans hlast
        exact False.elim (hvNe hEq.symm)
  have hxMissingSeat :
      Not (B gameF (s + 1) s (gameF (s + 1) (s + 1))) := by
    intro hB
    apply hmexDiag.2.1
    exact (previous_diagonal_source
      (f := gameF) (r := s)
      (p := gameF (s + 1) (s + 1))).2 (Or.inl hB)
  have hzMissingDiagGame :
      Not (B gameF (s + 1) (s + 1)
        (DipFirstGap gameRecurrenceModel s)) := by
    simpa using hzMissingDiag
  have hzMissingSeat :
      Not (B gameF (s + 1) s
        (DipFirstGap gameRecurrenceModel s)) := by
    intro hB
    apply hzMissingDiagGame
    exact (previous_diagonal_source
      (f := gameF) (r := s)
      (p := DipFirstGap gameRecurrenceModel s)).2 (Or.inl hB)
  exact ⟨hmexSeat, hmexDiag, hbelow, hxMissingSeat, hzMissingSeat,
    gameF_boundary_v1_constant_column hboundary⟩

/-- Local list helper for the strict charge. -/
private theorem r40_nodup_map_of_injective_on
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

/-- Strict augmented charge with one constant column removed. -/
theorem gameF_boundary_preview_plus_active_hosts_strict_capacity
    {s b r z : Nat}
    (hbs : b < s) (htR : s + 1 <= r) (hrz : r < z)
    (hpreview : gameF s b = z)
    (hstart : gameF z r = z)
    (hboundary : gameF (s + 1) s = s + 1) :
    z - r < r := by
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
  have havoid : forall x, x ∈ xs -> host x ≠ s := by
    intro x hx hEq
    have hxHost := hhost x hx
    rcases hclass x hx with rfl | hxActive
    · omega
    · have hconst := gameF_boundary_v1_constant_column hboundary x (by omega)
      rw [hEq, hconst] at hxHost
      omega
  have hmapNodup : (xs.map host).Nodup :=
    r40_nodup_map_of_injective_on host xs hxs hinj
  let cols := List.range' 0 s ++ List.range' (s + 1) (r - s - 1)
  have hsubset : xs.map host ⊆ cols := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨x, hx, rfl⟩
    apply List.mem_append.mpr
    by_cases hcs : host x < s
    · left
      apply List.mem_range'_1.mpr
      exact ⟨Nat.zero_le _, by simpa using hcs⟩
    · right
      apply List.mem_range'_1.mpr
      constructor
      · have hne := havoid x hx
        omega
      · have hcr := (hhost x hx).1
        omega
  have hbound := nodup_subset_length_le hmapNodup hsubset
  have hxsLen : xs.length = z - r := by
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

/-- Sharp boundary package: the freeze lies strictly above the midpoint. -/
theorem gameF_late_blocker_boundary_v1_has_strict_half_freeze
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1) :
    exists b r,
      b < s /\ s + 1 <= r /\
      r < DipFirstGap gameRecurrenceModel s /\
      gameF s b = DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      DipFirstGap gameRecurrenceModel s - r < r /\
      DipFirstGap gameRecurrenceModel s < r + r := by
  rcases hLate with
    ⟨_hgap, r, hrLate, hrz, hstart, hOldC, _hNewMissing⟩
  rcases hOldC with ⟨b, hbs, hpreview⟩
  have hstrict := gameF_boundary_preview_plus_active_hosts_strict_capacity
    hbs hrLate hrz hpreview hstart hboundary
  have hhalf : DipFirstGap gameRecurrenceModel s < r + r := by omega
  exact ⟨b, r, hbs, hrLate, hrz, hpreview, hstart, hstrict, hhalf⟩

/-- Eliminated boundary class: no freeze witness can lie at or below the
midpoint.  This includes both `2*r<z` and the formerly open equality
`2*r=z`. -/
theorem gameF_late_blocker_boundary_v1_has_no_lower_half_freeze
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1) :
    Not (exists r,
      r < DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      r + r <= DipFirstGap gameRecurrenceModel s) := by
  rcases gameF_late_blocker_boundary_v1_has_strict_half_freeze
      hLate hboundary with
    ⟨_b, r, _hbs, _hrLate, hrz, _hpreview, hstart,
      _hstrict, hhalf⟩
  rintro ⟨r', hr'z, hstart', hlower⟩
  have hrr' : r = r' :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hrz) (Nat.le_of_lt hr'z)
      (hstart.trans hstart'.symm)
  omega

/-- Owner-free non-unit-dip specialization. -/
theorem gameF_owner_free_nonunit_dip_boundary_v1_has_strict_half_freeze
    {s : Nat}
    (hgap : DipFirstGap gameRecurrenceModel s < gameF s s)
    (hNoDiagonal : forall a,
      gameF a a ≠ DipFirstGap gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1) :
    exists b r,
      b < s /\ s + 1 <= r /\
      r < DipFirstGap gameRecurrenceModel s /\
      gameF s b = DipFirstGap gameRecurrenceModel s /\
      gameF (DipFirstGap gameRecurrenceModel s) r =
        DipFirstGap gameRecurrenceModel s /\
      DipFirstGap gameRecurrenceModel s < r + r := by
  have hLate :=
    nonunit_dip_without_diagonal_first_gap_is_late_blocker_loss
      gameRecurrenceModel hgap hNoDiagonal
  rcases gameF_late_blocker_boundary_v1_has_strict_half_freeze
      hLate hboundary with
    ⟨b, r, hbs, hrLate, hrz, hpreview, hstart, _hstrict, hhalf⟩
  exact ⟨b, r, hbs, hrLate, hrz, hpreview, hstart, hhalf⟩

end ChompLean
