import R42BoundaryV1RehostOrLowCorridor

set_option autoImplicit false

namespace ChompLean

/-!
R43: a low-diagonal corridor has finite preview capacity.

Suppose the R42 boundary residue has no pre-freeze rehost, so every
diagonal `d(y)` for `s+1<=y<=r` is below the first-gap blocker `z`, while
`z<d(s)`.  Each such future diagonal value is covered by the old diagonal
MEX at row `s`.  It cannot enter through the historical-diagonal channel,
because its diagonal owner is the future row `y`; hence it has a strict
current-row host before column `s`.

The same old row also hosts the two distinct row-start species `s+1` and
`z`.  Thus `r-s` future diagonals plus these two row starts inject into the
`s` columns below the old diagonal.  This gives `r+2<=2*s`, excluding every
corridor with `r>=2*s-1`.

The last theorem also records the honest first transition inside a
nontrivial corridor: it is a genuine dip, and R33 gives its exact unit/past
diagonal/future loss/late-blocker split.  No RM2 or UnitDip is used.
-/

/-- A future diagonal below an old diagonal is necessarily hosted in the
strict prefix of the old row. -/
theorem future_diagonal_below_old_diagonal_has_old_row_host
    (M : RecurrenceModel) {s y : Nat}
    (hsy : s < y) (hbelow : M.f y y < M.f s s) :
    C M.f s s (M.f y y) := by
  have hyPos : 0 < M.f y y := by
    have := M.diagonal_gt y
    omega
  have hB : B M.f s s (M.f y y) :=
    M.mex_no_skip (Nat.le_refl s) (M.diagonal_gt s) hyPos hbelow
  rcases hB with hR | hC
  · rcases hR with ⟨a, has, hvalue⟩
    have haLe : a <= s := Nat.le_of_lt has
    have haOwner : M.f a a = M.f y y := by
      simpa [Nat.min_eq_left haLe] using hvalue
    have hay : a = y := diagonal_injective M haOwner
    omega
  · exact hC

private theorem r43_nodup_map_of_injective_on
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

/-- Host-capacity theorem for the full low-diagonal corridor. -/
theorem gameF_boundary_low_diagonal_corridor_capacity
    {s r : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1)
    (hrLate : s + 1 <= r)
    (hcorridor : forall y, s + 1 <= y -> y <= r ->
      gameF y y < DipFirstGap gameRecurrenceModel s) :
    r + 2 <= s + s := by
  classical
  rcases hLate with
    ⟨hgap, _r0, _hrLate0, _hrz0, _hstart0, hOldC, _hNewMissing⟩
  let z := DipFirstGap gameRecurrenceModel s
  let t := s + 1
  let rows := List.range' t (r - s)
  let diagVals := rows.map (fun y => gameF y y)
  let vals := z :: t :: diagVals
  have htz : t < z := by
    dsimp [t, z, DipFirstGap]
    have hdiag := gameRecurrenceModel.diagonal_gt (s + 1)
    omega
  have htHost : C gameF s s t := by
    have hstartT : gameF t s = t := by
      simpa [t] using hboundary
    have htBelowOld : t <= gameF s s := by
      change t <= gameRecurrenceModel.f s s
      change z < gameRecurrenceModel.f s s at hgap
      omega
    exact (rowstart_hosted_iff_below_diagonal
      gameRecurrenceModel (by omega) hstartT).2 htBelowOld
  have hrowsNodup : rows.Nodup := by
    dsimp [rows]
    exact List.nodup_range' 1
  have hdiagNodup : diagVals.Nodup := by
    apply r43_nodup_map_of_injective_on (fun y => gameF y y) rows
      hrowsNodup
    intro y _hy y' _hy' heq
    exact diagonal_injective gameRecurrenceModel heq
  have hzNotDiag : z ∉ diagVals := by
    intro hzMem
    rcases List.mem_map.mp hzMem with ⟨y, hyRows, hyz⟩
    have hyRange := List.mem_range'_1.mp (by simpa [rows] using hyRows)
    have hyLow := hcorridor y (by omega) (by omega)
    change gameRecurrenceModel.f y y < z at hyLow
    change gameRecurrenceModel.f y y = z at hyz
    rw [hyz] at hyLow
    omega
  have htNotDiag : t ∉ diagVals := by
    intro htMem
    rcases List.mem_map.mp htMem with ⟨y, hyRows, hyt⟩
    have hyRange := List.mem_range'_1.mp (by simpa [rows] using hyRows)
    have hstartT : gameF t s = t := by
      simpa [t] using hboundary
    exact disjoint_D_S gameRecurrenceModel
      ⟨y, hyt⟩ ⟨s, by omega, hstartT⟩
  have hvalsNodup : vals.Nodup := by
    change (z :: t :: diagVals).Nodup
    rw [List.nodup_cons, List.nodup_cons]
    constructor
    · intro hzMem
      rcases List.mem_cons.mp hzMem with hztEq | hzDiag
      · omega
      · exact hzNotDiag hzDiag
    · exact ⟨htNotDiag, hdiagNodup⟩
  have hex : forall v, v ∈ vals ->
      exists c, c < s /\ gameF s c = v := by
    intro v hv
    change v ∈ z :: t :: diagVals at hv
    rcases List.mem_cons.mp hv with hvz | hvrest
    · subst v
      rcases hOldC with ⟨b, hbs, hhost⟩
      exact ⟨b, hbs, by simpa [z] using hhost⟩
    · rcases List.mem_cons.mp hvrest with hvt | hvDiag
      · subst v
        rcases htHost with ⟨c, hcs, hhost⟩
        exact ⟨c, hcs, hhost⟩
      · rcases List.mem_map.mp hvDiag with ⟨y, hyRows, hyv⟩
        have hyRange := List.mem_range'_1.mp (by simpa [rows] using hyRows)
        have hyLow := hcorridor y (by omega) (by omega)
        have hyBelowOld : gameF y y < gameF s s := by
          change gameRecurrenceModel.f y y < gameRecurrenceModel.f s s
          change z < gameRecurrenceModel.f s s at hgap
          change gameRecurrenceModel.f y y < z at hyLow
          omega
        rcases future_diagonal_below_old_diagonal_has_old_row_host
            gameRecurrenceModel (by omega) hyBelowOld with
          ⟨c, hcs, hhost⟩
        change gameF s c = gameF y y at hhost
        exact ⟨c, hcs, hhost.trans hyv⟩
  let host : Nat -> Nat := fun v =>
    if hv : v ∈ vals then Classical.choose (hex v hv) else 0
  have hhost : forall v, v ∈ vals ->
      host v < s /\ gameF s (host v) = v := by
    intro v hv
    dsimp [host]
    rw [dif_pos hv]
    exact Classical.choose_spec (hex v hv)
  have hinj : forall v, v ∈ vals -> forall w, w ∈ vals ->
      host v = host w -> v = w := by
    intro v hv w hw hsame
    have hvHost := hhost v hv
    have hwHost := hhost w hw
    calc
      v = gameF s (host v) := hvHost.2.symm
      _ = gameF s (host w) := by rw [hsame]
      _ = w := hwHost.2
  have hmapNodup : (vals.map host).Nodup :=
    r43_nodup_map_of_injective_on host vals hvalsNodup hinj
  have hsubset : vals.map host ⊆ List.range' 0 s := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨v, hv, rfl⟩
    apply List.mem_range'_1.mpr
    exact ⟨Nat.zero_le _, by simpa using (hhost v hv).1⟩
  have hbound := nodup_subset_length_le hmapNodup hsubset
  have hvalsLen : vals.length = r - s + 2 := by
    dsimp [vals, diagVals, rows]
    simp
  have hraw : vals.length <= s := by simpa using hbound
  rw [hvalsLen] at hraw
  omega

/-- A nontrivial low corridor starts with a genuine dip.  Its first step has
exactly the R33 four-way normal form; this is a transition theorem, not an
assumption of UnitDip. -/
theorem gameF_boundary_low_corridor_first_transition
    {s r : Nat}
    (hnext : s + 2 <= r)
    (hcorridor : forall y, s + 1 <= y -> y <= r ->
      gameF y y < DipFirstGap gameRecurrenceModel s) :
    gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1) /\
      (gameF (s + 2) (s + 2) + 1 = gameF (s + 1) (s + 1) \/
       DipFirstGapPastDiagonal gameRecurrenceModel (s + 1) \/
       DipFirstGapFutureDiagonalLoss gameRecurrenceModel (s + 1) \/
       DipFirstGapLateBlockerLoss gameRecurrenceModel (s + 1)) := by
  have hbelow := hcorridor (s + 2) (by omega) hnext
  have hne : gameF (s + 2) (s + 2) ≠ gameF (s + 1) (s + 1) := by
    intro heq
    have hidx := diagonal_injective gameRecurrenceModel heq
    omega
  have hdip : gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1) := by
    change gameRecurrenceModel.f (s + 2) (s + 2) <
      gameRecurrenceModel.f (s + 1) (s + 1) + 1 at hbelow
    change gameRecurrenceModel.f (s + 2) (s + 2) ≠
      gameRecurrenceModel.f (s + 1) (s + 1) at hne
    change gameRecurrenceModel.f (s + 2) (s + 2) <
      gameRecurrenceModel.f (s + 1) (s + 1)
    omega
  exact ⟨hdip, dip_is_unit_or_first_gap_trichotomy
    gameRecurrenceModel hdip⟩

/-- Near-midpoint specialization: the forced low corridor is also short in
row coordinates. -/
theorem gameF_boundary_v1_near_midpoint_forces_short_low_corridor
    {s r : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s)
    (hboundary : gameF (s + 1) s = s + 1)
    (hrLate : s + 1 <= r)
    (hrz : r < DipFirstGap gameRecurrenceModel s)
    (hstart : gameF (DipFirstGap gameRecurrenceModel s) r =
      DipFirstGap gameRecurrenceModel s)
    (hnear : DipFirstGap gameRecurrenceModel s + 1 = r + r) :
    r + 2 <= s + s /\
      forall y, s + 1 <= y -> y <= r ->
        gameF y y < DipFirstGap gameRecurrenceModel s := by
  have hcorridor :=
    gameF_boundary_v1_near_midpoint_forces_low_diagonal_corridor
      hLate hboundary hrz hstart hnear
  have hcap := gameF_boundary_low_diagonal_corridor_capacity
    hLate hboundary hrLate hcorridor
  exact ⟨hcap, hcorridor⟩

end ChompLean
