import R22L3PastRangeEscape

set_option autoImplicit false

namespace ChompLean

/-!
R23: exact escape normal form for the tail from an already covered source
to the rescue backstop.

There are two independent pieces.

* Pure source algebra: if a value is present at an earlier source but absent
  at a later source, then it was already supported only by the column tail
  at the earlier source, and some intervening edge performs an exact parked
  swap with none of the three replacement channels.
* Actual Chomp geometry: a row-start opening whose start column is strictly
  left of a source column is always present at that source.  Combining this
  with R22 shows that a sub-`u` rescue value missing at the final source is
  either a late row-start (`r >= c`) or a future diagonal (`a >= c+3`).

Thus an element of `B2` can escape the backstop only if both obstructions
occur: it begins in the transient `ColTail` channel, suffers an exact swap
on the tail, and belongs to one of the two late opening species.
-/

/-- Permanent channels at an earlier source survive to every later source.
Consequently, a value present at `e` but absent at `c >= e` was already
`ParkedOnly` at `e`; this conclusion does not require the value to disappear
on the first edge. -/
theorem source_member_missing_later_is_parkedOnly
    {f : Nat -> Nat -> Nat} {t e c z : Nat}
    (hec : e <= c)
    (hhere : B f t e z)
    (hmissing : Not (B f t c z)) :
    ParkedOnly f t e z := by
  have hnotDiag : Not (DiagPrefix f t e z) := by
    rintro ⟨a, hat, hae, hval⟩
    apply hmissing
    left
    exact R_iff_diagPrefix_or_colTail.mpr
      (Or.inl ⟨a, hat, Nat.le_trans hae hec, hval⟩)
  have hnotRow : Not (C f t e z) := by
    rintro ⟨b, hbe, hval⟩
    apply hmissing
    right
    exact ⟨b, Nat.lt_of_lt_of_le hbe hec, hval⟩
  have hcol : ColTail f t e z := by
    rcases hhere with hR | hC
    · rcases R_iff_diagPrefix_or_colTail.mp hR with hDiag | hCol
      · exact False.elim (hnotDiag hDiag)
      · exact hCol
    · exact False.elim (hnotRow hC)
  exact ⟨hcol, hnotDiag, hnotRow⟩

/-- A finite covered-to-missing interval contains an actual one-edge loss. -/
theorem exists_loss_edge_before_later_missing
    {S : Nat -> Prop} {p c : Nat}
    (hpc : p < c) (hp : S p) (hc : Not (S c)) :
    exists k, p <= k /\ k < c /\ S k /\ Not (S (k + 1)) := by
  induction c with
  | zero => omega
  | succ c ih =>
      by_cases hprev : S c
      · exact ⟨c, by omega, by omega, hprev, by simpa using hc⟩
      · by_cases hpc' : p < c
        · rcases ih hpc' hprev with ⟨k, hpk, hkc, hk, hknext⟩
          exact ⟨k, hpk, by omega, hk, hknext⟩
        · have hpeq : p = c := by omega
          exact False.elim (hprev (by simpa [hpeq] using hp))

/-- Exact swap edge forced by loss somewhere before a later missing source.
The three negated terms are respectively the entering diagonal, the new
column tail, and the fresh current-row cell. -/
theorem source_member_missing_later_has_exact_swap_edge
    {f : Nat -> Nat -> Nat} {t p c z : Nat}
    (hpc : p < c)
    (hp : B f t p z)
    (hc : Not (B f t c z)) :
    exists k,
      p <= k /\ k < c /\
      B f t k z /\ Not (B f t (k + 1) z) /\
      ParkedOnly f t k z /\
      Not (k + 1 < t /\ f (k + 1) (k + 1) = z) /\
      Not (ColTail f t (k + 1) z) /\
      f t k ≠ z := by
  rcases exists_loss_edge_before_later_missing
      (S := fun r => B f t r z) (p := p) (c := c)
      hpc hp hc with ⟨k, hpk, hkc, hk, hknext⟩
  have hnormal :=
    (source_loss_iff_parked_and_no_replacement
      (f := f) (t := t) (e := k) (z := z)).mp ⟨hk, hknext⟩
  exact ⟨k, hpk, hkc, hk, hknext, hnormal.1,
    hnormal.2.1, hnormal.2.2.1, hnormal.2.2.2⟩

/-- Actual-Chomp row-start cover.  If `[z,z,r]` is a P-position and its
start column lies strictly left of `c<t`, then `z` is in `B(t,c)`.

For `z <= t`, the constant branch propagates the row-start cell to row `t`.
For `t < z`, `rowStartPropagation` supplies an even earlier current-row
cell.  These two cases cover every relative order of `z` and `t`. -/
theorem rowstart_before_column_enters_source
    (M : RecurrenceModel) {t c z r : Nat}
    (hct : c < t)
    (hstart : M.f z r = z)
    (hrz : r < z)
    (hrc : r < c) :
    B M.f t c z := by
  by_cases hzt : z <= t
  · have hsmall : M.f z r < z + 1 := by
      rw [hstart]
      omega
    have hconst := constant_from M hrz hsmall (t - z)
    have hsum : z + (t - z) = t := Nat.add_sub_of_le hzt
    rw [hsum] at hconst
    right
    exact ⟨r, hrc, hconst.trans hstart⟩
  · have htz : t < z := Nat.lt_of_not_ge hzt
    have hprop : C M.f t r z :=
      rowStartPropagation M hstart hrz (by omega) htz
    rcases hprop with ⟨b, hbr, hval⟩
    right
    exact ⟨b, by omega, hval⟩

/-- A global lower-prefix fact for every recurrence model: source column
`c` contains every positive value at most `c`, in every later row `t`.
Diagonal openings enter the diagonal prefix; row-start openings enter by
`rowstart_before_column_enters_source`. -/
theorem source_covers_positive_up_to_column
    (M : RecurrenceModel) {t c z : Nat}
    (hct : c < t) (hz : 0 < z) (hzc : z <= c) :
    B M.f t c z := by
  rcases M.opening_cover hz with hDiagonal | hRowStart
  · left
    rcases hDiagonal with ⟨a, haz, haOwner⟩
    exact R_iff_diagPrefix_or_colTail.mpr
      (Or.inl ⟨a, by omega, by omega, haOwner⟩)
  · rcases hRowStart with ⟨r, hrz, hstart⟩
    exact rowstart_before_column_enters_source
      M hct hstart hrz (by omega)

/-- Therefore every positive value missing from `B(t,c)` lies strictly
above the source column. -/
theorem missing_source_value_is_above_column
    (M : RecurrenceModel) {t c z : Nat}
    (hct : c < t) (hz : 0 < z)
    (hmissing : Not (B M.f t c z)) :
    c < z := by
  by_cases hzc : z <= c
  · exact False.elim
      (hmissing (source_covers_positive_up_to_column M hct hz hzc))
  · omega

/-- R22's residual dichotomy sharpened by the row-start cover theorem.
A blocker missing from the final rescue source cannot start before the
backstop column; hence it is genuinely a late blocker. -/
theorem missing_rescue_final_is_late_rowstart_or_future_diagonal
    (M : RecurrenceModel) {c u z : Nat}
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hz : 0 < z) (hzu : z < u)
    (hzMissingFinal : Not (B M.f (c + 3) c z)) :
    (exists r, c <= r /\ r < z /\ M.f z r = z) \/
      (exists a, c + 3 <= a /\ a < z /\ M.f a a = z) := by
  rcases missing_final_sub_u_is_rowstart_or_future_diagonal
      M huSeat hPrevDiagonalAbove hz hzu hzMissingFinal with
      hRowStart | hFuture
  · left
    rcases hRowStart with ⟨r, hrz, hstart⟩
    refine ⟨r, ?_, hrz, hstart⟩
    by_cases hrc : r < c
    · exact False.elim (hzMissingFinal
        (rowstart_before_column_enters_source
          M (by omega) hstart hrz hrc))
    · omega
  · exact Or.inr hFuture

/-- Complete necessary normal form for a value that is covered at an
earlier rescue source `p` but escapes the final source `B(c+3,c)`.

It is transient already at `p`, an exact no-replacement swap occurs on some
edge `k -> k+1` of the tail, and its unique opening species is either a
row-start at/after `c` or a diagonal owner at/after the current row `c+3`.
-/
theorem rescue_tail_escape_normal_form
    (M : RecurrenceModel) {p c u z : Nat}
    (hpc : p < c)
    (huSeat : M.f (c + 2) (c + 1) = u)
    (hPrevDiagonalAbove : u < M.f (c + 1) (c + 1))
    (hz : 0 < z) (hzu : z < u)
    (hp : B M.f (c + 3) p z)
    (hzMissingFinal : Not (B M.f (c + 3) c z)) :
    ParkedOnly M.f (c + 3) p z /\
    (exists k,
      p <= k /\ k < c /\
      B M.f (c + 3) k z /\ Not (B M.f (c + 3) (k + 1) z) /\
      ParkedOnly M.f (c + 3) k z /\
      Not (k + 1 < c + 3 /\ M.f (k + 1) (k + 1) = z) /\
      Not (ColTail M.f (c + 3) (k + 1) z) /\
      M.f (c + 3) k ≠ z) /\
    ((exists r, c <= r /\ r < z /\ M.f z r = z) \/
      (exists a, c + 3 <= a /\ a < z /\ M.f a a = z)) := by
  refine ⟨source_member_missing_later_is_parkedOnly
      (Nat.le_of_lt hpc) hp hzMissingFinal, ?_, ?_⟩
  · exact source_member_missing_later_has_exact_swap_edge
      hpc hp hzMissingFinal
  · exact missing_rescue_final_is_late_rowstart_or_future_diagonal
      M huSeat hPrevDiagonalAbove hz hzu hzMissingFinal

/-- The preceding theorem in the R20--R22 coordinates.  For `L>2`, every
value of `B2=B(t,e+2)` that is absent at the backstop `B(t,e+L)` has the
exact transient/swap/late-opening normal form. -/
theorem rescue_B2_escape_normal_form
    (M : RecurrenceModel) {e L u z : Nat}
    (hL : 2 < L)
    (huSeat : M.f (e + L + 2) (e + L + 1) = u)
    (hPrevDiagonalAbove : u < M.f (e + L + 1) (e + L + 1))
    (hz : 0 < z) (hzu : z < u)
    (hB2 : B M.f (e + L + 3) (e + 2) z)
    (hzMissingBackstop : Not (B M.f (e + L + 3) (e + L) z)) :
    ParkedOnly M.f (e + L + 3) (e + 2) z /\
    (exists k,
      e + 2 <= k /\ k < e + L /\
      B M.f (e + L + 3) k z /\
      Not (B M.f (e + L + 3) (k + 1) z) /\
      ParkedOnly M.f (e + L + 3) k z /\
      Not (k + 1 < e + L + 3 /\ M.f (k + 1) (k + 1) = z) /\
      Not (ColTail M.f (e + L + 3) (k + 1) z) /\
      M.f (e + L + 3) k ≠ z) /\
    ((exists r, e + L <= r /\ r < z /\ M.f z r = z) \/
      (exists a, e + L + 3 <= a /\ a < z /\ M.f a a = z)) := by
  have huSeat' : M.f ((e + L) + 2) ((e + L) + 1) = u := by
    simpa [Nat.add_assoc] using huSeat
  have hPrev' : u < M.f ((e + L) + 1) ((e + L) + 1) := by
    simpa [Nat.add_assoc] using hPrevDiagonalAbove
  have hB2' : B M.f ((e + L) + 3) (e + 2) z := by
    simpa [Nat.add_assoc] using hB2
  have hmissing' : Not (B M.f ((e + L) + 3) (e + L) z) := by
    simpa [Nat.add_assoc] using hzMissingBackstop
  have hnormal := rescue_tail_escape_normal_form
    M (p := e + 2) (c := e + L)
      (by omega) huSeat' hPrev' hz hzu hB2' hmissing'
  simpa [Nat.add_assoc] using hnormal

/-- Unconditional safe range of the long tail.  At the backstop column
`c=e+L`, every positive value `z <= c` is covered, whether or not it was in
`B2`.  Hence a tail escape can only occur in the strict upper strip
`e+L < z < u`. -/
theorem rescue_backstop_covers_below_its_column
    (M : RecurrenceModel) {e L z : Nat}
    (hz : 0 < z) (hzColumn : z <= e + L) :
    B M.f (e + L + 3) (e + L) z := by
  exact source_covers_positive_up_to_column
    M (by omega) hz hzColumn

/-- Proof-facing tail seal after R23.  Full `B2` preservation no longer
needs a black-box `LAST-EDGE-SEAL`: it follows from exclusion of exactly the
two late opening species isolated above. -/
theorem rescue_B2_tail_preservation_of_no_late_openings
    (M : RecurrenceModel) {e L u : Nat}
    (hL : 2 < L)
    (huSeat : M.f (e + L + 2) (e + L + 1) = u)
    (hPrevDiagonalAbove : u < M.f (e + L + 1) (e + L + 1))
    (hNoLateRowStart :
      forall z, 0 < z -> z < u ->
        Not (exists r, e + L <= r /\ r < z /\ M.f z r = z))
    (hNoFutureDiagonal :
      forall z, 0 < z -> z < u ->
        Not (exists a,
          e + L + 3 <= a /\ a < z /\ M.f a a = z)) :
    forall z, 0 < z -> z < u ->
      B M.f (e + L + 3) (e + 2) z ->
      B M.f (e + L + 3) (e + L) z := by
  intro z hz hzu hB2
  by_cases hfinal : B M.f (e + L + 3) (e + L) z
  · exact hfinal
  · have hnormal := rescue_B2_escape_normal_form
      M hL huSeat hPrevDiagonalAbove hz hzu hB2 hfinal
    rcases hnormal.2.2 with hLate | hFuture
    · exact False.elim (hNoLateRowStart z hz hzu hLate)
    · exact False.elim (hNoFutureDiagonal z hz hzu hFuture)

end ChompLean
