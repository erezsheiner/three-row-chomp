import R38DiagonalFirstGapChronologyAudit
import R14FrontierLaw

set_option autoImplicit false

namespace ChompLean

/-!
R40: owner-distance and no-repeat consequences of the diagonal prehost loss
isolated in R38.

No RM2 assumption is used.  A future diagonal owner `a` satisfies `a<x`.
If `x` was already hosted in row `q`, strict row maximality also gives
`x<d(q)`.  Thus a delayed owner (`q+2<=a`) consumes at least four units of
diagonal slack at the old host row.  In the actual encoding, the old host
column is then forbidden from carrying `x` on every intermediate row by
same-lower no-repeat.
-/

/-- Basic owner band for every diagonal prehost loss. -/
theorem futureDiagonalPrehost_owner_band
    (M : RecurrenceModel) {q a x : Nat}
    (hloss : FutureDiagonalPrehostLoss M q a x) :
    q < a /\ a < x /\ x < M.f q q := by
  rcases hloss with ⟨hqa, haOwner, hC, _hAbsent⟩
  rcases hC with ⟨b, hbq, hhost⟩
  have hax : a < x := by
    have hgt := M.diagonal_gt a
    rw [haOwner] at hgt
    exact hgt
  have hxle : x <= M.f q q := by
    have hle := diagonalMaximal M (q := q) (s := b) (Nat.le_of_lt hbq)
    rw [hhost] at hle
    exact hle
  have hxne : x ≠ M.f q q := by
    intro heq
    have hcols := M.fixed_q_injective
      (q := q) (b₁ := b) (b₂ := q)
      (Nat.le_of_lt hbq) (Nat.le_refl q) (hhost.trans heq)
    omega
  exact ⟨hqa, hax, by omega⟩

/-- A prehost whose diagonal owner is delayed by at least two rows forces
`d(q)>=q+4`.  This is the first unconditional owner-distance exclusion:
rows of diagonal slack at most three cannot start such an episode. -/
theorem delayed_futureDiagonalPrehost_forces_slack_four
    (M : RecurrenceModel) {q a x : Nat}
    (hloss : FutureDiagonalPrehostLoss M q a x)
    (hdelay : q + 2 <= a) :
    q + 4 <= M.f q q := by
  have hband := futureDiagonalPrehost_owner_band M hloss
  omega

/-- Consequently a delayed prehost is impossible at a row whose diagonal
slack is at most three. -/
theorem no_delayed_futureDiagonalPrehost_of_slack_at_most_three
    (M : RecurrenceModel) {q a x : Nat}
    (hslack : M.f q q <= q + 3)
    (hdelay : q + 2 <= a) :
    Not (FutureDiagonalPrehostLoss M q a x) := by
  intro hloss
  have hfour := delayed_futureDiagonalPrehost_forces_slack_four
    M hloss hdelay
  omega

/-- R33 future first gaps have a sharply bounded owner:
`s+2 <= a <= d(s+1)`, and force four units of slack at row `s`. -/
theorem future_first_gap_owner_band_and_slack_four
    (M : RecurrenceModel) {s : Nat}
    (hFuture : DipFirstGapFutureDiagonalLoss M s) :
    exists a,
      s + 2 <= a /\
      a <= M.f (s + 1) (s + 1) /\
      s + 4 <= M.f s s := by
  rcases future_first_gap_is_future_prehost_loss M hFuture with
    ⟨a, ha, hloss⟩
  have hband := futureDiagonalPrehost_owner_band M hloss
  have hfour := delayed_futureDiagonalPrehost_forces_slack_four
    M hloss (by omega)
  refine ⟨a, by omega, ?_, hfour⟩
  dsimp [DipFirstGap] at hband
  omega

/-- The past branch has the same slack-four cost, but at its earlier
diagonal owner rather than necessarily at the dip row. -/
theorem past_first_gap_old_owner_has_slack_four
    (M : RecurrenceModel) {s : Nat}
    (hPast : DipFirstGapPastDiagonal M s) :
    exists q,
      q < s /\
      M.f q q = DipFirstGap M s /\
      q + 4 <= M.f q q := by
  rcases past_first_gap_forces_predecessor_future_prehost_loss
      M hPast with ⟨q, hqs, hqOwner, hloss⟩
  have hfour := delayed_futureDiagonalPrehost_forces_slack_four
    M hloss (by omega)
  exact ⟨q, hqs, hqOwner, hfour⟩

/-- At a low-slack row the R33 future-diagonal branch is impossible. -/
theorem no_future_first_gap_of_slack_at_most_three
    (M : RecurrenceModel) {s : Nat}
    (hslack : M.f s s <= s + 3) :
    Not (DipFirstGapFutureDiagonalLoss M s) := by
  intro hFuture
  rcases future_first_gap_owner_band_and_slack_four M hFuture with
    ⟨_a, _halower, _haupper, hfour⟩
  omega

/-- Combining the non-circular settled-row elimination from R38 with the
slack bound removes both diagonal branches.  Only the late blocker remains. -/
theorem nonunit_dip_at_settled_low_slack_row_is_late_blocker
    (M : RecurrenceModel) {j : Nat}
    (hSettled : RMax M j < M.f (j + 2) (j + 2))
    (hslack : M.f (j + 1) (j + 1) <= j + 4)
    (hgap : DipFirstGap M (j + 1) < M.f (j + 1) (j + 1)) :
    DipFirstGapLateBlockerLoss M (j + 1) := by
  rcases nonunit_dip_at_previously_settled_row_is_future_or_late
      M hSettled hgap with hFuture | hLate
  · exact False.elim
      (no_future_first_gap_of_slack_at_most_three
        M (s := j + 1) (by omega) hFuture)
  · exact hLate

/-! ## Actual-game no-repeat consequences -/

/-- In the genuine encoding, the original host column of a future diagonal
prehost episode is a desert for that value until its diagonal owner. -/
theorem game_futureDiagonalPrehost_has_column_desert
    {q a x : Nat}
    (hloss : FutureDiagonalPrehostLoss gameRecurrenceModel q a x) :
    exists b,
      b < q /\ gameF q b = x /\
      forall t, q < t -> t < a -> gameF t b ≠ x := by
  rcases hloss with ⟨hqa, haOwner, hC, _hAbsent⟩
  rcases hC with ⟨b, hbq, hhost⟩
  have hax : a < x := by
    have hgt := gameRecurrenceModel.diagonal_gt a
    rw [haOwner] at hgt
    exact hgt
  refine ⟨b, hbq, hhost, ?_⟩
  intro t hqt hta htHost
  exact encoding_same_lower_no_repeat game_encodes
    hbq hqt (by omega) hhost htHost

/-- Every future diagonal value lying below an earlier diagonal is hosted
in that earlier row; the diagonal `R` branch is impossible because the
unique owner lies in the future. -/
theorem game_future_diagonal_below_row_has_interior_host
    {r a x : Nat}
    (hra : r < a) (haOwner : gameF a a = x)
    (hxBelow : x < gameF r r) :
    exists b, b < r /\ gameF r b = x := by
  have hxPos : 0 < x := by
    have hgt := gameRecurrenceModel.diagonal_gt a
    change a < gameF a a at hgt
    rw [haOwner] at hgt
    omega
  have hB : B gameF r r x :=
    (recurrence_diagonal_exact_mex gameRecurrenceModel r).2.2
      x hxPos hxBelow
  rcases hB with hR | hC
  · rcases hR with ⟨i, hi, hvalue⟩
    have hiOwner : gameF i i = x := by
      simpa [Nat.min_eq_left (Nat.le_of_lt hi)] using hvalue
    have hiOwner' :
        gameRecurrenceModel.f i i = gameRecurrenceModel.f a a := by
      change gameF i i = gameF a a
      exact hiOwner.trans haOwner.symm
    have hidx : i = a :=
      diagonal_injective gameRecurrenceModel hiOwner'
    omega
  · exact hC

/-- Hosts of the same future diagonal value on two distinct pre-owner rows
must use different lower columns.  This is the two-row charge primitive. -/
theorem game_future_diagonal_preowner_hosts_use_distinct_columns
    {r₁ r₂ a x b₁ b₂ : Nat}
    (hb₁ : b₁ < r₁) (hr₁r₂ : r₁ < r₂)
    (hr₂a : r₂ < a) (haOwner : gameF a a = x)
    (hhost₁ : gameF r₁ b₁ = x)
    (hhost₂ : gameF r₂ b₂ = x) :
    b₁ ≠ b₂ := by
  intro hbeq
  subst b₂
  have hax : a < x := by
    have hgt := gameRecurrenceModel.diagonal_gt a
    change a < gameF a a at hgt
    rw [haOwner] at hgt
    exact hgt
  exact encoding_same_lower_no_repeat game_encodes
    hb₁ hr₁r₂ (by omega) hhost₁ hhost₂

/-- Local list helper for the finite charge below. -/
private theorem r40_nodup_map_of_injective_on
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

/--
Finite no-repeat charge for a future diagonal value.  Consider rows below a
common horizon `u<=a` on which `x=d(a)` lies below the row diagonal but is
missing from prefix `c`.  Exact MEX gives a host in each row, the prefix gap
puts it in `[c,u)`, and no-repeat makes the host columns distinct.
-/
theorem game_future_diagonal_prefix_gap_charge_bound
    {c u a x : Nat} {xs : List Nat}
    (haOwner : gameF a a = x) (hua : u <= a)
    (hxs : xs.Nodup)
    (hrows : forall r, r ∈ xs ->
      r < u /\ x < gameF r r /\ Not (C gameF r c x)) :
    xs.length <= u - c := by
  classical
  have hex : forall r, r ∈ xs ->
      exists b, c <= b /\ b < r /\ b < u /\ gameF r b = x := by
    intro r hr
    have hrdata := hrows r hr
    have hra : r < a := by omega
    rcases game_future_diagonal_below_row_has_interior_host
        hra haOwner hrdata.2.1 with ⟨b, hbr, hhost⟩
    have hcb : c <= b := by
      by_cases h : c <= b
      · exact h
      · exact False.elim (hrdata.2.2 ⟨b, by omega, hhost⟩)
    exact ⟨b, hcb, hbr, by omega, hhost⟩
  let host : Nat -> Nat := fun r =>
    if hr : r ∈ xs then Classical.choose (hex r hr) else 0
  have hhost : forall r, r ∈ xs ->
      c <= host r /\ host r < r /\ host r < u /\
        gameF r (host r) = x := by
    intro r hr
    dsimp [host]
    rw [dif_pos hr]
    exact Classical.choose_spec (hex r hr)
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
        h₁.2.1 hlt
        (by
          have hax := gameRecurrenceModel.diagonal_gt a
          change a < gameF a a at hax
          rw [haOwner] at hax
          omega)
        h₁.2.2.2 (by simpa [heq] using h₂.2.2.2))
    · have hgt : r₂ < r₁ := by omega
      exact False.elim (encoding_same_lower_no_repeat game_encodes
        h₂.2.1 hgt
        (by
          have hax := gameRecurrenceModel.diagonal_gt a
          change a < gameF a a at hax
          rw [haOwner] at hax
          omega)
        h₂.2.2.2 (by simpa [heq] using h₁.2.2.2))
  have hmapNodup : (xs.map host).Nodup :=
    r40_nodup_map_of_injective_on host xs hxs hinj
  have hsubset : xs.map host ⊆ List.range' c (u - c) := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
    have hs := hhost r hr
    apply List.mem_range'_1.mpr
    exact ⟨hs.1, by omega⟩
  have hlen := nodup_subset_length_le hmapNodup hsubset
  simpa using hlen

/-- Both diagonal branches of an actual-game first gap therefore contain a
concrete host column which cannot carry the charged value again before its
future diagonal owner. -/
theorem game_diagonal_first_gap_branch_has_column_desert
    {s : Nat}
    (hDiagonal :
      DipFirstGapPastDiagonal gameRecurrenceModel s \/
        DipFirstGapFutureDiagonalLoss gameRecurrenceModel s) :
    exists q a x b,
      q < a /\ b < q /\ gameF q b = x /\
      forall t, q < t -> t < a -> gameF t b ≠ x := by
  rcases diagonal_first_gap_branch_forces_future_prehost_loss
      gameRecurrenceModel hDiagonal with ⟨q, a, x, hloss⟩
  rcases game_futureDiagonalPrehost_has_column_desert hloss with
    ⟨b, hbq, hhost, hdesert⟩
  exact ⟨q, a, x, b, hloss.1, hbq, hhost, hdesert⟩

#print axioms delayed_futureDiagonalPrehost_forces_slack_four
#print axioms nonunit_dip_at_settled_low_slack_row_is_late_blocker
#print axioms game_diagonal_first_gap_branch_has_column_desert
#print axioms game_future_diagonal_prefix_gap_charge_bound

end ChompLean
