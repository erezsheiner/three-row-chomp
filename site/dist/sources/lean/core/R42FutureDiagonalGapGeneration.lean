import R40FutureDiagonalPrehostCharge

set_option autoImplicit false

namespace ChompLean

/-!
R42: automatic prefix-gap generation for future diagonal prehosts.

For a fixed future diagonal value `x=d(a)`, same-lower no-repeat injects all
pre-owner rows which host `x` before a fixed prefix `c` into the `c` columns
`[0,c)`.  Hence more than `c` such rows force an actual prefix gap.  If an
old prehost row `q` is already known, its host consumes one of those columns,
so only `q-1` later rows can continue to host `x` before prefix `q`.

Exact diagonal MEX then turns the forced prefix gap into a concrete shifted
host at a column at least `q`, provided `x` remains below that row's
diagonal.  No RM2 or UnitDip assumption is used.
-/

private theorem r42_nodup_map_of_injective_on
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) (xs : List alpha)
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

/-- At most `c` distinct pre-owner rows can host the same future diagonal
value in columns strictly before `c`. -/
theorem game_future_diagonal_prefix_host_capacity
    {c a x : Nat} {xs : List Nat}
    (haOwner : gameF a a = x)
    (hxs : xs.Nodup)
    (hrows : forall r, r ∈ xs ->
      c <= r /\ r < a /\ C gameF r c x) :
    xs.length <= c := by
  classical
  have hex : forall r, r ∈ xs ->
      exists b, b < c /\ b < r /\ gameF r b = x := by
    intro r hr
    rcases hrows r hr with ⟨hcr, _hra, b, hbc, hhost⟩
    exact ⟨b, hbc, Nat.lt_of_lt_of_le hbc hcr, hhost⟩
  let host : Nat -> Nat := fun r =>
    if hr : r ∈ xs then Classical.choose (hex r hr) else 0
  have hhost : forall r, r ∈ xs ->
      host r < c /\ host r < r /\ gameF r (host r) = x := by
    intro r hr
    dsimp [host]
    rw [dif_pos hr]
    exact Classical.choose_spec (hex r hr)
  have hax : a < x := by
    have hgt := gameRecurrenceModel.diagonal_gt a
    change a < gameF a a at hgt
    rw [haOwner] at hgt
    exact hgt
  have hinj : forall r₁, r₁ ∈ xs -> forall r₂, r₂ ∈ xs ->
      host r₁ = host r₂ -> r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ heq
    by_cases hrs : r₁ = r₂
    · exact hrs
    have h₁ := hhost r₁ hr₁
    have h₂ := hhost r₂ hr₂
    have hd₁ := hrows r₁ hr₁
    have hd₂ := hrows r₂ hr₂
    by_cases hlt : r₁ < r₂
    · exact False.elim (encoding_same_lower_no_repeat game_encodes
        h₁.2.1 hlt (by omega) h₁.2.2
        (by simpa [heq] using h₂.2.2))
    · have hgt : r₂ < r₁ := by omega
      exact False.elim (encoding_same_lower_no_repeat game_encodes
        h₂.2.1 hgt (by omega) h₂.2.2
        (by simpa [heq] using h₁.2.2))
  have hmapNodup : (xs.map host).Nodup :=
    r42_nodup_map_of_injective_on host xs hxs hinj
  have hsubset : xs.map host ⊆ List.range c := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
    exact List.mem_range.mpr (hhost r hr).1
  have hlen := nodup_subset_length_le hmapNodup hsubset
  simpa using hlen

/-- More than `c` distinct pre-owner rows automatically force a row on
which `x` is absent from prefix `c`. -/
theorem game_many_preowner_rows_force_prefix_gap
    {c a x : Nat} {xs : List Nat}
    (haOwner : gameF a a = x)
    (hxs : xs.Nodup)
    (hrows : forall r, r ∈ xs -> c <= r /\ r < a)
    (hmany : c < xs.length) :
    exists r, r ∈ xs /\ Not (C gameF r c x) := by
  classical
  apply Classical.byContradiction
  intro hnoGap
  have hAll : forall r, r ∈ xs -> C gameF r c x := by
    intro r hr
    apply Classical.byContradiction
    intro hgap
    exact hnoGap ⟨r, hr, hgap⟩
  have hcap := game_future_diagonal_prefix_host_capacity
    haOwner hxs (fun r hr => ⟨(hrows r hr).1, (hrows r hr).2, hAll r hr⟩)
  omega

/--
An existing prehost at row `q` consumes one prefix column.  Therefore `q`
later high rows already suffice to force a prefix-`q` gap; exact MEX then
places `x` at a shifted host column `b>=q` on that row.
-/
theorem game_futurePrehost_many_high_rows_force_shifted_host
    {q a x : Nat} {xs : List Nat}
    (hloss : FutureDiagonalPrehostLoss gameRecurrenceModel q a x)
    (hxs : xs.Nodup)
    (hrows : forall r, r ∈ xs ->
      q < r /\ r < a /\ x < gameF r r)
    (hmany : q <= xs.length) :
    exists r b,
      r ∈ xs /\ q <= b /\ b < r /\ gameF r b = x /\
      Not (C gameF r q x) := by
  classical
  have hqNotMem : q ∉ xs := by
    intro hq
    have := (hrows q hq).1
    omega
  have hconsNodup : (q :: xs).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hqNotMem, hxs⟩
  have hgap : exists r, r ∈ xs /\ Not (C gameF r q x) := by
    apply Classical.byContradiction
    intro hnoGap
    have hAll : forall r, r ∈ xs -> C gameF r q x := by
      intro r hr
      apply Classical.byContradiction
      intro hnot
      exact hnoGap ⟨r, hr, hnot⟩
    have hconsRows : forall r, r ∈ q :: xs ->
        q <= r /\ r < a /\ C gameF r q x := by
      intro r hr
      rcases List.mem_cons.mp hr with hEq | hr
      · subst r
        exact ⟨Nat.le_refl _, hloss.1, hloss.2.2.1⟩
      · have hrdata := hrows r hr
        exact ⟨Nat.le_of_lt hrdata.1, hrdata.2.1, hAll r hr⟩
    have hcap := game_future_diagonal_prefix_host_capacity
      (by
        change gameF a a = x
        exact hloss.2.1)
      hconsNodup hconsRows
    simp only [List.length_cons] at hcap
    omega
  rcases hgap with ⟨r, hr, hprefixGap⟩
  have hrdata := hrows r hr
  rcases game_future_diagonal_below_row_has_interior_host
      hrdata.2.1 (by
        change gameF a a = x
        exact hloss.2.1) hrdata.2.2 with
    ⟨b, hbr, hhost⟩
  have hqb : q <= b := by
    by_cases h : q <= b
    · exact h
    · exact False.elim (hprefixGap ⟨b, by omega, hhost⟩)
  exact ⟨r, b, hr, hqb, hbr, hhost, hprefixGap⟩

/-- Owner-distance specialization.  If the owner is beyond `2*q` and every
intermediate row keeps `x` below its diagonal, a shifted host is forced
automatically. -/
theorem game_long_futurePrehost_high_interval_forces_shifted_host
    {q a x : Nat}
    (hloss : FutureDiagonalPrehostLoss gameRecurrenceModel q a x)
    (hlong : q + q + 1 <= a)
    (hhigh : forall r, q < r -> r < a -> x < gameF r r) :
    exists r b,
      q < r /\ r < a /\ q <= b /\ b < r /\
      gameF r b = x /\ Not (C gameF r q x) := by
  let xs := List.range' (q + 1) (a - q - 1)
  have hxs : xs.Nodup := by
    dsimp [xs]
    exact List.nodup_range' 1
  have hrows : forall r, r ∈ xs ->
      q < r /\ r < a /\ x < gameF r r := by
    intro r hr
    have hrange := List.mem_range'_1.mp hr
    exact ⟨by omega, by omega, hhigh r (by omega) (by omega)⟩
  have hmany : q <= xs.length := by
    dsimp [xs]
    simp
    omega
  rcases game_futurePrehost_many_high_rows_force_shifted_host
      hloss hxs hrows hmany with
    ⟨r, b, hr, hqb, hbr, hhost, hgap⟩
  have hrdata := hrows r hr
  exact ⟨r, b, hrdata.1, hrdata.2.1, hqb, hbr, hhost, hgap⟩

/--
Unconditional future-first-gap trichotomy.  A future owner is either in the
near band `a<=2*s+1`, or some tail row drops below the future value, or the
high tail is long enough to force a concrete host shifted to column `>=s`.
-/
theorem game_future_first_gap_near_owner_or_tail_downcross_or_shifted_host
    {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    exists a,
      s + 2 <= a /\
      a <= gameF (s + 1) (s + 1) /\
      gameF a a = DipFirstGap gameRecurrenceModel s /\
      (a <= s + s + 1 \/
        (exists r,
          s + 1 < r /\ r < a /\
          gameF r r < DipFirstGap gameRecurrenceModel s) \/
        exists r b,
          s + 1 < r /\ r < a /\ s <= b /\ b < r /\
          gameF r b = DipFirstGap gameRecurrenceModel s /\
          Not (C gameF r s (DipFirstGap gameRecurrenceModel s))) := by
  rcases future_first_gap_is_future_prehost_loss
      gameRecurrenceModel hFuture with ⟨a, ha, hloss⟩
  have hband := futureDiagonalPrehost_owner_band
    gameRecurrenceModel hloss
  have haUpper : a <= gameF (s + 1) (s + 1) := by
    change a <= gameRecurrenceModel.f (s + 1) (s + 1)
    dsimp [DipFirstGap] at hband
    omega
  refine ⟨a, by omega, haUpper, ?_, ?_⟩
  · change gameF a a = DipFirstGap gameRecurrenceModel s
    exact hloss.2.1
  · by_cases hnear : a <= s + s + 1
    · exact Or.inl hnear
    · by_cases hdown : exists r,
          s + 1 < r /\ r < a /\
            gameF r r < DipFirstGap gameRecurrenceModel s
      · exact Or.inr (Or.inl hdown)
      · have hhigh : forall r, s + 1 < r -> r < a ->
            DipFirstGap gameRecurrenceModel s < gameF r r := by
          intro r htail hra
          apply Nat.lt_of_not_ge
          intro hle
          have hne : gameF r r ≠ DipFirstGap gameRecurrenceModel s := by
            intro heq
            have hdiagEq :
                gameRecurrenceModel.f r r =
                  gameRecurrenceModel.f a a := by
              change gameF r r = gameF a a
              rw [heq]
              exact hloss.2.1.symm
            have hidx := diagonal_injective gameRecurrenceModel hdiagEq
            omega
          have hlt : gameF r r < DipFirstGap gameRecurrenceModel s := by
            omega
          exact hdown ⟨r, htail, hra, hlt⟩
        let xs := List.range' (s + 2) (a - s - 2)
        have hxs : xs.Nodup := by
          dsimp [xs]
          exact List.nodup_range' 1
        have hrows : forall r, r ∈ xs ->
            s < r /\ r < a /\
              DipFirstGap gameRecurrenceModel s < gameF r r := by
          intro r hr
          have hrange := List.mem_range'_1.mp hr
          exact ⟨by omega, by omega, hhigh r (by omega) (by omega)⟩
        have hmany : s <= xs.length := by
          dsimp [xs]
          simp
          omega
        rcases game_futurePrehost_many_high_rows_force_shifted_host
            hloss hxs hrows hmany with
          ⟨r, b, hr, hsb, hbr, hhost, hgap⟩
        have hrTail : s + 1 < r := by
          have hrange := List.mem_range'_1.mp hr
          omega
        have hra := (hrows r hr).2.1
        exact Or.inr (Or.inr
          ⟨r, b, hrTail, hra, hsb, hbr, hhost, hgap⟩)

#print axioms game_future_diagonal_prefix_host_capacity
#print axioms game_futurePrehost_many_high_rows_force_shifted_host
#print axioms game_future_first_gap_near_owner_or_tail_downcross_or_shifted_host

end ChompLean
