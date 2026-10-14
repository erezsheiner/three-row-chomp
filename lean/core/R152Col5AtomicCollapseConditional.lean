import R151FSyndeticNearG

set_option autoImplicit false

namespace ChompLean

/-!
R152: conditional consequences of the column-5 linear rail.

The only new input in this file is the proposed theorem

`gameF t 5 = t + 4` for `7 <= t`.

At a lag-four R151 boundary, the terminal burn lies in row `q-1` and
has value `q+3`.  The proposed rail has exactly the same value in that
row.  Fixed-row injectivity therefore pins the terminal-burn column to
`5`.  In the atomic subcase this says `g+1=5`, hence `g=4`; more
generally it says `r-1=5`, hence `r=6`.  The latter already contradicts
the midpoint lower bound and the failed-rail inequality, so atomicity is
not actually needed for the lag-four closure.
-/

/-- Abstract form of the proposed column-5 theorem.  Keeping it as an
argument lets this file compile before the rail itself is banked. -/
def GameFCol5RailFrom7 : Prop :=
  forall t, 7 <= t -> gameF t 5 = t + 4

/-- A lag-four terminal burn is forced to column `5`. -/
theorem gameF_col5_lag4_terminal_pins_r
    {q r : Nat}
    (hrail : GameFCol5RailFrom7)
    (hq8 : 8 <= q)
    (hra : r <= q - 1)
    (hburn : gameF (q - 1) (r - 1) = q + 3) :
    r = 6 := by
  have h5 : gameF (q - 1) 5 = (q - 1) + 4 :=
    hrail (q - 1) (by omega)
  have heq : gameF (q - 1) 5 = gameF (q - 1) (r - 1) := by
    rw [h5, hburn]
    omega
  have hc : 5 = r - 1 := gameRecurrenceModel.fixed_q_injective
    (q := q - 1) (by omega) (by omega) heq
  omega

/-- In the atomic subcase `r=g+2`, the same collision pins `g=4`.
This is the exact abstract consequence requested by the R151 audit. -/
theorem gameF_col5_atomic_terminal_pins_g
    {q g : Nat}
    (hrail : GameFCol5RailFrom7)
    (hq8 : 8 <= q)
    (hra : g + 2 <= q - 1)
    (hburn : gameF (q - 1) (g + 1) = q + 3) :
    g = 4 := by
  have h5 : gameF (q - 1) 5 = (q - 1) + 4 :=
    hrail (q - 1) (by omega)
  have heq : gameF (q - 1) 5 = gameF (q - 1) (g + 1) := by
    rw [h5, hburn]
    omega
  have hc : 5 = g + 1 := gameRecurrenceModel.fixed_q_injective
    (q := q - 1) (by omega) (by omega) heq
  omega

/-- The weak midpoint lower bound already excludes the pinned value
`g=4` for `q>=8`.  No ledger, syndeticity, owner coverage, or preview
analysis is needed. -/
theorem gameF_col5_kills_atomic_midpoint
    {q g : Nat}
    (hrail : GameFCol5RailFrom7)
    (hq8 : 8 <= q)
    (hra : g + 2 <= q - 1)
    (hburn : gameF (q - 1) (g + 1) = q + 3)
    (hmid : q + 2 <= 2 * g) :
    False := by
  have hg := gameF_col5_atomic_terminal_pins_g hrail hq8 hra hburn
  omega

/-- Wrapper in the exact midpoint form used by the R151 first-failure
ledger.  The nonnegative correction count only strengthens `hmid`. -/
theorem gameF_col5_kills_atomic_first_failure_midpoint
    {A : Nat -> Nat} {q g : Nat}
    (hrail : GameFCol5RailFrom7)
    (hq8 : 8 <= q)
    (hra : g + 2 <= q - 1)
    (hburn : gameF (q - 1) (g + 1) = q + 3)
    (hgdef : q + 2 + A (q + 2) <= 2 * g) :
    False := by
  exact gameF_col5_kills_atomic_midpoint hrail hq8 hra hburn (by omega)

/-- Stronger than the atomic result: every lag-four first-failure
boundary is impossible.  The collision gives `r=6`; the failed rail
then gives `g<=4`, while the midpoint lower bound and `q>=8` give
`g>=5`. -/
theorem gameF_col5_kills_lag4_first_failure
    {q r g : Nat}
    (hrail : GameFCol5RailFrom7)
    (hq8 : 8 <= q)
    (hra : r <= q - 1)
    (hfailure : g + 1 < r)
    (hburn : gameF (q - 1) (r - 1) = q + 3)
    (hmid : q + 2 <= 2 * g) :
    False := by
  have hr := gameF_col5_lag4_terminal_pins_r hrail hq8 hra hburn
  omega

/-- Exact R151 ledger-midpoint wrapper for the full lag-four closure. -/
theorem gameF_col5_kills_lag4_first_failure_midpoint
    {A : Nat -> Nat} {q r g : Nat}
    (hrail : GameFCol5RailFrom7)
    (hq8 : 8 <= q)
    (hra : r <= q - 1)
    (hfailure : g + 1 < r)
    (hburn : gameF (q - 1) (r - 1) = q + 3)
    (hgdef : q + 2 + A (q + 2) <= 2 * g) :
    False := by
  exact gameF_col5_kills_lag4_first_failure hrail hq8 hra hfailure
    hburn (by omega)

/-! The following two corollaries locate the precise missing actual-game
content in the arithmetic interface frames from
`R151SparseCapsAtomicSeparation`: they cannot realize their advertised
terminal burn once the column-5 rail is available. -/

/-- The whole dense atomic interface family is excluded at its terminal
burn cell. -/
theorem gameF_col5_excludes_dense_atomic_terminal
    {m : Nat}
    (hrail : GameFCol5RailFrom7)
    (hm : 5 <= m)
    (hburn : gameF (4 * m) (3 * m + 2) = 4 * m + 4) :
    False := by
  have h5 : gameF (4 * m) 5 = 4 * m + 4 := by
    simpa using hrail (4 * m) (by omega)
  have hc : 5 = 3 * m + 2 := gameRecurrenceModel.fixed_q_injective
    (q := 4 * m) (by omega) (by omega) (h5.trans hburn.symm)
  omega

/-- The repaired rank-30 atomic interface (`v=60`, `g=44`) is likewise
excluded: its terminal burn would duplicate value `60` in columns `5`
and `45` of row `56`. -/
theorem gameF_col5_excludes_repaired_rank30_atomic_terminal
    (hrail : GameFCol5RailFrom7)
    (hburn : gameF 56 45 = 60) :
    False := by
  have h5 : gameF 56 5 = 60 := by
    simpa using hrail 56 (by omega)
  have hc : (5 : Nat) = 45 := gameRecurrenceModel.fixed_q_injective
    (q := 56) (by omega) (by omega) (h5.trans hburn.symm)
  omega

#print axioms gameF_col5_lag4_terminal_pins_r
#print axioms gameF_col5_atomic_terminal_pins_g
#print axioms gameF_col5_kills_atomic_midpoint
#print axioms gameF_col5_kills_lag4_first_failure
#print axioms gameF_col5_excludes_dense_atomic_terminal
#print axioms gameF_col5_excludes_repaired_rank30_atomic_terminal

end ChompLean
