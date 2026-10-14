import R26ActualGameFutureGap
import R14FrontierLaw

set_option autoImplicit false

namespace ChompLean

/-!
R27: a finite charge for the actual-game future-prefix gaps from R26.

Let `gameF z r = z` be a row-start blocker and fix a shorter prefix `c`.
For every row `x` strictly between the freeze `r` and the blocker row `z`,
row-start propagation gives a host `gameF x b = z` with `b<r`.  If `z` is
still missing from prefix `c` on that row, then necessarily `c<=b`.

The actual Chomp encoding supplies one more fact which is not part of the
abstract `RecurrenceModel`: the same lower column cannot host the same value
on two distinct intermediate rows.  Consequently post-freeze prefix gaps
inject into the finite column strip `[c,r)`.  This is the finite charge
needed to make an iterated R26 argument non-circular.
-/

/-- Two distinct post-freeze prefix-gap rows have distinct middle-band
hosts.  This is the two-witness form of the charge invariant. -/
theorem gameF_two_postfreeze_gaps_have_distinct_hosts
    {c r x y z : Nat}
    (hstart : gameF z r = z) (hrz : r < z)
    (hrx : r < x) (hxy : x < y) (hyz : y < z)
    (hxgap : Not (C gameF x c z))
    (hygap : Not (C gameF y c z)) :
    exists bx bY,
      c <= bx /\ bx < r /\ gameF x bx = z /\
      c <= bY /\ bY < r /\ gameF y bY = z /\ Not (bx = bY) := by
  have hxz : x < z := Nat.lt_trans hxy hyz
  rcases rowStartPropagation gameRecurrenceModel hstart hrz hrx hxz with
    ⟨bx, hbxr, hxb⟩
  rcases rowStartPropagation gameRecurrenceModel hstart hrz
      (Nat.lt_trans hrx hxy) hyz with ⟨byHost, hbyr, hyb⟩
  have hcbx : c <= bx := by
    by_cases h : c <= bx
    · exact h
    · exact False.elim (hxgap ⟨bx, by omega, hxb⟩)
  have hcby : c <= byHost := by
    by_cases h : c <= byHost
    · exact h
    · exact False.elim (hygap ⟨byHost, by omega, hyb⟩)
  have hne : Not (bx = byHost) := by
    intro heq
    subst byHost
    exact encoding_same_lower_no_repeat game_encodes
      (Nat.lt_trans hbxr hrx) hxy hyz hxb hyb
  exact ⟨bx, byHost, hcbx, hbxr, hxb, hcby, hbyr, hyb, hne⟩

/-- A `C`-gap which is nevertheless covered by the full source can only be
covered by a genuinely later boundary-column owner.  A diagonal owner at or
left of `c` is impossible because `z` already has a row-start opening.

This is the exact endpoint needed when an R26 `C`-gap fails to remain a
full `B`-gap. -/
theorem rowstart_C_gap_is_source_gap_or_boundary_owner
    (M : RecurrenceModel) {c r x z : Nat}
    (hrz : r < z) (hstart : M.f z r = z)
    (hxgap : Not (C M.f x c z)) :
    Not (B M.f x c z) \/
      exists a, c < a /\ a < x /\ M.f a c = z := by
  by_cases hB : B M.f x c z
  · right
    rcases hB with hR | hC
    · rcases hR with ⟨a, hax, hvalue⟩
      have hca : c < a := by
        by_cases hac : a <= c
        · have hdiag : M.f a a = z := by
            simpa [Nat.min_eq_left hac] using hvalue
          exact False.elim
            (disjoint_D_S M ⟨a, hdiag⟩ ⟨r, hrz, hstart⟩)
        · omega
      have hboundary : M.f a c = z := by
        simpa [Nat.min_eq_right (Nat.le_of_lt hca)] using hvalue
      exact ⟨a, hca, hax, hboundary⟩
    · exact False.elim (hxgap hC)
  · exact Or.inl hB

/-- A full source gap has an exact cell-level iteration trichotomy.  The
cell is low/non-live, serves `z`, or emits a new high value strictly between
the row index and `z`.  In the last case the same R26 argument can be
started again from this later row. -/
theorem source_gap_cell_low_or_service_or_high_lower
    (M : RecurrenceModel) {c x z : Nat}
    (hcx : c <= x) (hz : 0 < z)
    (hgap : Not (B M.f x c z)) :
    M.f x c <= x \/ M.f x c = z \/
      (x < M.f x c /\ M.f x c < z) := by
  by_cases hlow : M.f x c <= x
  · exact Or.inl hlow
  · have hxout : x < M.f x c := by omega
    have houtle : M.f x c <= z := by
      apply Nat.le_of_not_gt
      intro hzout
      exact hgap (M.mex_no_skip hcx hxout hz hzout)
    by_cases heq : M.f x c = z
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr ⟨hxout, by omega⟩)

/-- R26 plus the source/boundary classification.  A forced future prefix
gap has one of three non-circular outcomes: it is at/before the freeze, it
remains a full source gap after the freeze, or it reaches a concrete owner
on the boundary column `c`. -/
theorem gameF_future_gap_prefreeze_or_source_gap_or_boundary_owner
    {c t q z r : Nat}
    (hct : c < t)
    (hq : gameF t c = q)
    (htq : t < q) (hqz : q < z)
    (hgap : Not (C gameF t c z))
    (hrz : r < z) (hstart : gameF z r = z) :
    exists x,
      t < x /\ x < z /\ Not (C gameF x c z) /\
      (x <= r \/
        Not (B gameF x c z) \/
        exists a, c < a /\ a < x /\ gameF a c = z) := by
  rcases rightmost_hole_forces_future_prefix_gap
      gameRecurrenceModel hct hq htq hqz hgap with
    ⟨x, htx, hxz, hxgap⟩
  refine ⟨x, htx, hxz, hxgap, ?_⟩
  by_cases hxr : x <= r
  · exact Or.inl hxr
  · have hs := rowstart_C_gap_is_source_gap_or_boundary_owner
      gameRecurrenceModel hrz hstart hxgap
    exact Or.inr hs

/-- Fully iteration-facing form.  Unless R26 reaches the freeze side or a
boundary owner, it produces a full source gap.  At that source gap the cell
is either low, serves `z`, or gives the strictly later/high/lower seed needed
for another R26 step. -/
theorem gameF_future_gap_iteration_normal_form
    {c t q z r : Nat}
    (hct : c < t)
    (hq : gameF t c = q)
    (htq : t < q) (hqz : q < z)
    (hgap : Not (C gameF t c z))
    (hrz : r < z) (hstart : gameF z r = z) :
    exists x,
      t < x /\ x < z /\ Not (C gameF x c z) /\
      (x <= r \/
        (exists a, c < a /\ a < x /\ gameF a c = z) \/
        (Not (B gameF x c z) /\
          (gameF x c <= x \/ gameF x c = z \/
            (x < gameF x c /\ gameF x c < z)))) := by
  rcases gameF_future_gap_prefreeze_or_source_gap_or_boundary_owner
      hct hq htq hqz hgap hrz hstart with
    ⟨x, htx, hxz, hxgap, hxcase⟩
  refine ⟨x, htx, hxz, hxgap, ?_⟩
  rcases hxcase with hpre | hrest
  · exact Or.inl hpre
  · rcases hrest with hsource | howner
    · have hcell := source_gap_cell_low_or_service_or_high_lower
        gameRecurrenceModel (by omega) (by omega) hsource
      exact Or.inr (Or.inr ⟨hsource, hcell⟩)
    · exact Or.inr (Or.inl howner)

/-- Local helper: mapping a duplicate-free list through a function which is
injective on that list preserves duplicate-freeness. -/
private theorem nodup_map_of_injective_on
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

/-- Finite-charge theorem.  Any duplicate-free list of post-freeze rows on
which `z` is missing from the fixed prefix `c` has length at most `r-c`.
Each row consumes a distinct host column in `[c,r)`. -/
theorem gameF_postfreeze_prefix_gap_charge_bound
    {c r z : Nat} {xs : List Nat}
    (hstart : gameF z r = z) (hrz : r < z)
    (hxs : xs.Nodup)
    (hrows : forall x, x ∈ xs ->
      r < x /\ x < z /\ Not (C gameF x c z)) :
    xs.length <= r - c := by
  classical
  have hex : forall x, x ∈ xs ->
      exists b, c <= b /\ b < r /\ gameF x b = z := by
    intro x hx
    have hxdata := hrows x hx
    rcases rowStartPropagation gameRecurrenceModel hstart hrz
        hxdata.1 hxdata.2.1 with ⟨b, hbr, hb⟩
    have hcb : c <= b := by
      by_cases h : c <= b
      · exact h
      · exact False.elim (hxdata.2.2 ⟨b, by omega, hb⟩)
    exact ⟨b, hcb, hbr, hb⟩
  let host : Nat -> Nat := fun x =>
    if hx : x ∈ xs then Classical.choose (hex x hx) else 0
  have hhost : forall x, x ∈ xs ->
      c <= host x /\ host x < r /\ gameF x (host x) = z := by
    intro x hx
    dsimp [host]
    rw [dif_pos hx]
    exact Classical.choose_spec (hex x hx)
  have hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
      host x = host y -> x = y := by
    intro x hx y hy hxy
    by_cases hEq : x = y
    · exact hEq
    have hxdata := hrows x hx
    have hydata := hrows y hy
    have hxh := hhost x hx
    have hyh := hhost y hy
    by_cases hlt : x < y
    · exact False.elim (encoding_same_lower_no_repeat game_encodes
        (Nat.lt_trans hxh.2.1 hxdata.1) hlt hydata.2.1
        hxh.2.2 (by simpa [hxy] using hyh.2.2))
    · have hyx : y < x := by omega
      exact False.elim (encoding_same_lower_no_repeat game_encodes
        (Nat.lt_trans hyh.2.1 hydata.1) hyx hxdata.2.1
        hyh.2.2 (by simpa [hxy] using hxh.2.2))
  have hmapNodup : (xs.map host).Nodup :=
    nodup_map_of_injective_on host xs hxs hinj
  have hsubset : xs.map host ⊆ List.range' c (r - c) := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
    have hs := hhost x hx
    apply List.mem_range'_1.mpr
    constructor
    · exact hs.1
    · omega
  have hlen := nodup_subset_length_le hmapNodup hsubset
  simpa using hlen

/-- If the active row interval `(r,z)` is longer than the middle-band
charge strip `[c,r)`, not every active row can remain a prefix gap.  Hence
there is an actual row on which `z` crosses back into prefix `c`.

This conclusion is unconditional on MEX/backstop hypotheses; it is a direct
actual-game consequence of row-start propagation and no-repeat. -/
theorem gameF_long_active_interval_forces_prefix_return
    {c r z : Nat}
    (hstart : gameF z r = z) (hrz : r < z)
    (hlong : r - c < z - r - 1) :
    exists x, r < x /\ x < z /\ C gameF x c z := by
  classical
  by_cases hex : exists x, r < x /\ x < z /\ C gameF x c z
  · exact hex
  · let xs := List.range' (r + 1) (z - r - 1)
    have hxs : xs.Nodup := by
      dsimp [xs]
      exact List.nodup_range' 1
    have hrows : forall x, x ∈ xs ->
        r < x /\ x < z /\ Not (C gameF x c z) := by
      intro x hx
      have hxrange := List.mem_range'_1.mp (by simpa [xs] using hx)
      have hrx : r < x := by omega
      have hxz : x < z := by omega
      have hxgap : Not (C gameF x c z) := by
        intro hC
        exact hex ⟨x, hrx, hxz, hC⟩
      exact ⟨hrx, hxz, hxgap⟩
    have hbound := gameF_postfreeze_prefix_gap_charge_bound
      (xs := xs) hstart hrz hxs hrows
    have hlength : xs.length = z - r - 1 := by
      simp [xs]
    rw [hlength] at hbound
    exact False.elim (by omega)

/-- Endpoint form of the charge.  A duplicate-free family of more than
`r-c` future prefix gaps cannot remain entirely post-freeze: one row must
lie at or before the freeze.  Thus any chain construction that produces
fresh rows has a certified finite stopping alternative. -/
theorem gameF_long_prefix_gap_chain_hits_prefreeze
    {c r z : Nat} {xs : List Nat}
    (hstart : gameF z r = z) (hrz : r < z)
    (hxs : xs.Nodup)
    (hrows : forall x, x ∈ xs ->
      x < z /\ Not (C gameF x c z))
    (hlong : r - c < xs.length) :
    exists x, x ∈ xs /\ x <= r := by
  classical
  by_cases hex : exists x, x ∈ xs /\ x <= r
  · exact hex
  · have hpost : forall x, x ∈ xs ->
        r < x /\ x < z /\ Not (C gameF x c z) := by
      intro x hx
      have hxdata := hrows x hx
      have hrx : r < x := by
        by_cases hle : x <= r
        · exact False.elim (hex ⟨x, hx, hle⟩)
        · omega
      exact ⟨hrx, hxdata.1, hxdata.2⟩
    have hbound := gameF_postfreeze_prefix_gap_charge_bound
      hstart hrz hxs hpost
    exact False.elim (by omega)

end ChompLean
