import R48LateBlockerWellFoundedDescent

set_option autoImplicit false

namespace ChompLean

/-!
R49: finite packing for the general high-`q` terminal certificate.

R48 bounds the number of recursive smaller-late-blocker transitions by the
initial blocker value.  If that recursion ends in the high-`q` R27 packet,
the row-start witness in the packet gives a second, independent finite
charge: duplicate-free post-freeze prefix gaps inject into the columns
between the terminal prefix and the freeze.

Thus the high-`q` terminal is no longer opaque.  Its whole post-freeze gap
family has finite capacity, and the full active interval is either short or
contains an actual prefix return.  Combining this with R48 gives one bound
for the recursive prefix plus the terminal gap family.  No boundary,
near-midpoint, RM2, or `UnitDip` hypothesis is used.
-/

/-- The high-`q` R47 packet together with its exact R27 finite charge and
the resulting short-interval-or-prefix-return stopping alternative. -/
def LateBlockerHighQChargeNormalForm (s : Nat) : Prop :=
  let z := LateBlockerValue s
  LateBlockerHighQGapPacket s /\
    exists r,
      s + 1 <= r /\ r < z /\ gameF z r = z /\
      (forall xs : List Nat, xs.Nodup ->
        (forall y, y ∈ xs ->
          r < y /\ y < z /\ Not (C gameF y s z)) ->
        xs.length <= r - s) /\
      (z - r - 1 <= r - s \/
        exists y, r < y /\ y < z /\ C gameF y s z)

/-- Every high-`q` terminal packet carries the exact finite charge. -/
theorem gameF_high_q_terminal_charge_normal_form
    {s : Nat}
    (hHigh : LateBlockerHighQGapPacket s) :
    LateBlockerHighQChargeNormalForm s := by
  dsimp only [LateBlockerHighQChargeNormalForm, LateBlockerValue]
  refine ⟨hHigh, ?_⟩
  dsimp only [LateBlockerHighQGapPacket] at hHigh
  rcases hHigh with
    ⟨b, r, x, hbs, hrLate, hrz, hpreview, hstart, hhalf,
      hqHigh, hqz, hxLate, hxz, hxgap, hxcase⟩
  refine ⟨r, hrLate, hrz, hstart, ?_, ?_⟩
  · intro xs hxs hrows
    exact gameF_postfreeze_prefix_gap_charge_bound
      (c := s) (r := r) (z := DipFirstGap gameRecurrenceModel s)
      (xs := xs) hstart hrz hxs hrows
  · by_cases hshort :
        DipFirstGap gameRecurrenceModel s - r - 1 <= r - s
    · exact Or.inl hshort
    · right
      apply gameF_long_active_interval_forces_prefix_return
        (c := s) (r := r)
        (z := DipFirstGap gameRecurrenceModel s) hstart hrz
      omega

/-- Numerical form of the stopping alternative: unless the blocker returns
to prefix `s` on an active post-freeze row, the terminal geometry satisfies
`z+s <= 2*r+1`. -/
theorem gameF_high_q_terminal_linear_short_or_prefix_return
    {s : Nat}
    (hHigh : LateBlockerHighQGapPacket s) :
    exists r,
      s + 1 <= r /\ r < LateBlockerValue s /\
      gameF (LateBlockerValue s) r = LateBlockerValue s /\
      (LateBlockerValue s + s <= r + r + 1 \/
        exists y,
          r < y /\ y < LateBlockerValue s /\
          C gameF y s (LateBlockerValue s)) := by
  have hNF := gameF_high_q_terminal_charge_normal_form hHigh
  dsimp only [LateBlockerHighQChargeNormalForm] at hNF
  rcases hNF with
    ⟨_hPacket, r, hrLate, hrz, hstart, _hpack, hstop⟩
  refine ⟨r, hrLate, hrz, hstart, ?_⟩
  rcases hstop with hshort | hreturn
  · left
    omega
  · exact Or.inr hreturn

/-- R49 opens precisely the high-`q` branch of every R48 terminal
certificate; the nonrecursive boundary branch is preserved verbatim. -/
theorem gameF_late_blocker_terminal_certificate_R49_reduction
    {s : Nat}
    (hTerminal : LateBlockerTerminalCertificate s) :
    LateBlockerHighQChargeNormalForm s \/
      (BoundaryLateBlockerParametricNormalForm s /\
        Not (BoundaryCorridorSmallerLateBlocker s)) := by
  dsimp only [LateBlockerTerminalCertificate] at hTerminal
  rcases hTerminal with hHigh | hBoundary
  · exact Or.inl (gameF_high_q_terminal_charge_normal_form hHigh)
  · exact Or.inr hBoundary

/-- An R48 descent prefix followed by an R49 terminal has a bounded
recursive part and an opened high-`q` branch. -/
theorem gameF_late_blocker_descent_to_terminal_R49_reduction
    {s n : Nat}
    (hrun : LateBlockerDescentRun s n)
    (hTerminal : LateBlockerTerminalCertificate (s + n)) :
    n <= LateBlockerValue s /\
      (LateBlockerHighQChargeNormalForm (s + n) \/
        (BoundaryLateBlockerParametricNormalForm (s + n) /\
          Not (BoundaryCorridorSmallerLateBlocker (s + n)))) := by
  exact ⟨gameF_late_blocker_descent_run_length_bound n s hrun,
    gameF_late_blocker_terminal_certificate_R49_reduction hTerminal⟩

/-- Exact two-resource packing bound.  After `n` recursive late-blocker
steps, every duplicate-free family of terminal post-freeze prefix gaps has
size at most `r-(s+n)`.  Hence recursive steps plus terminal gaps fit in the
sum of the initial blocker budget and the terminal column-strip budget. -/
theorem gameF_descent_to_high_q_gap_family_total_charge_bound
    {s n : Nat}
    (hrun : LateBlockerDescentRun s n)
    (hHigh : LateBlockerHighQGapPacket (s + n)) :
    exists r,
      s + n + 1 <= r /\
      r < LateBlockerValue (s + n) /\
      gameF (LateBlockerValue (s + n)) r =
        LateBlockerValue (s + n) /\
      forall xs : List Nat, xs.Nodup ->
        (forall y, y ∈ xs ->
          r < y /\ y < LateBlockerValue (s + n) /\
          Not (C gameF y (s + n) (LateBlockerValue (s + n)))) ->
        n + xs.length <=
          LateBlockerValue s + (r - (s + n)) := by
  have hn := gameF_late_blocker_descent_run_length_bound n s hrun
  have hNF := gameF_high_q_terminal_charge_normal_form hHigh
  dsimp only [LateBlockerHighQChargeNormalForm] at hNF
  rcases hNF with
    ⟨_hPacket, r, hrLate, hrz, hstart, hpack, _hstop⟩
  refine ⟨r, hrLate, hrz, hstart, ?_⟩
  intro xs hxs hrows
  have hm := hpack xs hxs hrows
  exact Nat.add_le_add hn hm

/-- Full-active-interval form of the combined R48+R27 packing.  At the
high-`q` terminal, either a genuine prefix return occurs, or the recursive
descent length plus every active post-freeze row obeys one additive bound. -/
theorem gameF_descent_to_high_q_terminal_short_or_return
    {s n : Nat}
    (hrun : LateBlockerDescentRun s n)
    (hHigh : LateBlockerHighQGapPacket (s + n)) :
    exists r,
      s + n + 1 <= r /\
      r < LateBlockerValue (s + n) /\
      gameF (LateBlockerValue (s + n)) r =
        LateBlockerValue (s + n) /\
      (n + (LateBlockerValue (s + n) - r - 1) <=
          LateBlockerValue s + (r - (s + n)) \/
        exists y,
          r < y /\ y < LateBlockerValue (s + n) /\
          C gameF y (s + n) (LateBlockerValue (s + n))) := by
  have hn := gameF_late_blocker_descent_run_length_bound n s hrun
  have hNF := gameF_high_q_terminal_charge_normal_form hHigh
  dsimp only [LateBlockerHighQChargeNormalForm] at hNF
  rcases hNF with
    ⟨_hPacket, r, hrLate, hrz, hstart, _hpack, hstop⟩
  refine ⟨r, hrLate, hrz, hstart, ?_⟩
  rcases hstop with hshort | hreturn
  · exact Or.inl (Nat.add_le_add hn hshort)
  · exact Or.inr hreturn

end ChompLean

