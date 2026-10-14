import R15ParkedValueSwap

set_option autoImplicit false

namespace ChompLean

/-!
R16: bookkeeping for a value that moves one column right while moving one
row down.  The substantive schedule assertion is the second cell equality;
once it is supplied, membership in the new column tail is definitional.

The strict-depth hypothesis `e < r` is essential.  Without it, the new host
may lie on (or to the left of) the new column rather than in `ColTail`.
-/

/-- A fixed positive-depth lane move supplies the omitted successor-column
tail channel.  The old-host equality is retained to express the observed
handoff pattern, although the conclusion itself uses only the new host. -/
theorem adjacent_lane_handoff_enters_colTail
    {f : Nat -> Nat -> Nat} {t r e z : Nat}
    (_hold : f r e = z)
    (hnext : f (r + 1) (e + 1) = z)
    (hdepth : e < r)
    (ht : r + 1 < t) :
    ColTail f t (e + 1) z := by
  exact ⟨r + 1, ht, by omega, hnext⟩

/-- With only weak depth, the translated hosting still enters the full
`R` source.  Equality `e = r` is the boundary case: the witness enters the
diagonal channel rather than `ColTail`. -/
theorem adjacent_lane_handoff_enters_R_of_weak_depth
    {f : Nat -> Nat -> Nat} {t r e z : Nat}
    (hnext : f (r + 1) (e + 1) = z)
    (hdepth : e <= r)
    (ht : r + 1 < t) :
    R f t (e + 1) z := by
  refine ⟨r + 1, ht, ?_⟩
  have hcol : e + 1 <= r + 1 := by omega
  simpa [Nat.min_eq_right hcol] using hnext

/-- General-gap form: translating row and column by the same amount
preserves strict depth and puts the translated host in the translated
column tail. -/
theorem lane_host_enters_colTail_general
    {f : Nat -> Nat -> Nat} {t r e g z : Nat}
    (hhost : f (r + g) (e + g) = z)
    (hdepth : e < r)
    (ht : r + g < t) :
    ColTail f t (e + g) z := by
  exact ⟨r + g, ht, by omega, hhost⟩

/-- General-gap weak-depth form for the full fixed-source channel. -/
theorem lane_host_enters_R_general_of_weak_depth
    {f : Nat -> Nat -> Nat} {t r e g z : Nat}
    (hhost : f (r + g) (e + g) = z)
    (hdepth : e <= r)
    (ht : r + g < t) :
    R f t (e + g) z := by
  refine ⟨r + g, ht, ?_⟩
  have hcol : e + g <= r + g := by omega
  simpa [Nat.min_eq_right hcol] using hhost

/-- Pair-shaped general-gap version matching the empirical lane language.
The first hosting records the start of the lane; source membership at the
endpoint follows from the translated hosting. -/
theorem lane_handoff_enters_colTail_general
    {f : Nat -> Nat -> Nat} {t r e g z : Nat}
    (_hold : f r e = z)
    (hnext : f (r + g) (e + g) = z)
    (hdepth : e < r)
    (ht : r + g < t) :
    ColTail f t (e + g) z :=
  lane_host_enters_colTail_general hnext hdepth ht

/-- An adjacent lane re-emission is therefore an actual replacement channel
in the successor source. -/
theorem adjacent_lane_handoff_enters_successor_source
    {f : Nat -> Nat -> Nat} {t r e z : Nat}
    (hold : f r e = z)
    (hnext : f (r + 1) (e + 1) = z)
    (hdepth : e < r)
    (ht : r + 1 < t) :
    B f t (e + 1) z := by
  left
  exact R_iff_diagPrefix_or_colTail.mpr
    (Or.inr
      (adjacent_lane_handoff_enters_colTail hold hnext hdepth ht))

/-- In particular, if `z` was parked-only in the old column, a supplied
lane re-emission prevents swap-out.  No MEX or Chomp recurrence fact is
needed for this bookkeeping implication. -/
theorem adjacent_lane_handoff_prevents_source_loss
    {f : Nat -> Nat -> Nat} {t r e z : Nat}
    (hpark : ParkedOnly f t e z)
    (hold : f r e = z)
    (hnext : f (r + 1) (e + 1) = z)
    (hdepth : e < r)
    (ht : r + 1 < t) :
    B f t e z /\ B f t (e + 1) z := by
  exact ⟨parkedOnly_mem_current_source hpark,
    adjacent_lane_handoff_enters_successor_source
      hold hnext hdepth ht⟩

/-! ## Range-owner bridge

For the observed range-value handoffs the owner is the very next row after
the handoff host: old host `(e+1,e)`, new host `(e+2,e+1)`, and diagonal
owner `(e+2,e+2)`.  The diagonal equality changes the bookkeeping after
column `e+1`: from column `e+2` onward the value is permanently in the
monotone diagonal-prefix channel.
-/

/-- A diagonal owner at `e+2` enters the diagonal prefix at its own column. -/
theorem next_range_owner_enters_diagPrefix
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (howner : f (e + 2) (e + 2) = z)
    (ht : e + 2 < t) :
    DiagPrefix f t (e + 2) z := by
  exact ⟨e + 2, ht, Nat.le_refl _, howner⟩

/-- Once its owner is in the time horizon, the same diagonal witness remains
in every source column at or to the right of the owner.  No condition
`q < t` is needed; only the owner row itself must be below `t`. -/
theorem next_range_owner_persists_diagPrefix
    {f : Nat -> Nat -> Nat} {t e q z : Nat}
    (howner : f (e + 2) (e + 2) = z)
    (ht : e + 2 < t)
    (hq : e + 2 <= q) :
    DiagPrefix f t q z := by
  exact ⟨e + 2, ht, hq, howner⟩

/-- Hence the range owner closes `z` in every later full source. -/
theorem next_range_owner_closes_all_later_sources
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (howner : f (e + 2) (e + 2) = z)
    (ht : e + 2 < t) :
    forall {q}, e + 2 <= q -> B f t q z := by
  intro q hq
  left
  exact R_iff_diagPrefix_or_colTail.mpr
    (Or.inl (next_range_owner_persists_diagPrefix howner ht hq))

/-- Exact depth-one handoff-to-owner bridge.  A parked value is present in
the old source, the off-diagonal re-emission keeps it in the successor
source, and its next-row diagonal owner makes that coverage permanent from
column `e+2` onward. -/
theorem depth_one_handoff_to_range_owner_closure
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hpark : ParkedOnly f t e z)
    (hold : f (e + 1) e = z)
    (hhandoff : f (e + 2) (e + 1) = z)
    (howner : f (e + 2) (e + 2) = z)
    (ht : e + 2 < t) :
    B f t e z /\
    B f t (e + 1) z /\
    (forall {q}, e + 2 <= q -> B f t q z) := by
  refine ⟨parkedOnly_mem_current_source hpark, ?_, ?_⟩
  · exact adjacent_lane_handoff_enters_successor_source
      (r := e + 1) hold (by simpa [Nat.add_assoc] using hhandoff)
      (by omega) (by omega)
  · exact next_range_owner_closes_all_later_sources howner ht

/-! ## The missing depth hypothesis cannot be deleted -/

def laneDepthCounter (a b : Nat) : Nat :=
  if (a = 1 /\ b = 1) \/ (a = 2 /\ b = 2) then 7 else 0

theorem laneDepthCounter_two_hostings :
    laneDepthCounter 1 1 = 7 /\ laneDepthCounter 2 2 = 7 := by
  simp [laneDepthCounter]

theorem laneDepthCounter_not_colTail :
    Not (ColTail laneDepthCounter 3 2 7) := by
  rintro ⟨a, ha3, h2a, _hval⟩
  omega

/-- Concrete counterframe to the statement as written without `e < r`:
take `r=e=1`, `t=3`, and two diagonal hostings.  Both advertised equalities
and `r+1<t` hold, but the new hosting is diagonal, not in the column tail. -/
theorem lane_handoff_without_positive_depth_is_false :
    laneDepthCounter 1 1 = 7 /\
    laneDepthCounter (1 + 1) (1 + 1) = 7 /\
    1 + 1 < 3 /\
    Not (ColTail laneDepthCounter 3 (1 + 1) 7) := by
  refine ⟨laneDepthCounter_two_hostings.1,
    laneDepthCounter_two_hostings.2, by omega, ?_⟩
  simpa using laneDepthCounter_not_colTail

end ChompLean
