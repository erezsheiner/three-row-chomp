import R31TerminalStripQueueTrace
import R18ParkedVanishBoundary

set_option autoImplicit false

namespace ChompLean

/-!
R32: exact depth-four reduction for terminal sub-seat backfill.

Let `e=t-4`.  If a row-start value `z` is hosted in one of the final
three cells of row `t`, then its membership in `B f t e` has no diagonal
or current-row-prefix ambiguity:

* the row-start witness excludes every diagonal owner by `D`/`S`
  disjointness;
* fixed-row injectivity excludes a second copy strictly before `e`;
* consequently the only possible source channel is the depth-four column
  tail, whose three possible rows can be enumerated exactly.

The final section names the still-open actual-game scheduler statement as
`TerminalSubUBackfillLaw` and proves that this one law closes the R29/R31
residual.  No proof of that law is claimed here.
-/

/-- In `e`-coordinates, a terminally hosted blocker is in the depth-four
source exactly when one of the three intervening rows hosted it in column
`e`. -/
theorem blocker_terminal_host_depth4_source_iff_recent_column_hosts
    (M : RecurrenceModel) {e z r b : Nat}
    (hrz : r < z) (hstart : M.f z r = z)
    (heb : e + 1 <= b) (hbt : b < e + 4)
    (hhost : M.f (e + 4) b = z) :
    B M.f (e + 4) e z <->
      M.f (e + 1) e = z \/
      M.f (e + 2) e = z \/
      M.f (e + 3) e = z := by
  constructor
  · intro hB
    rcases hB with hR | hC
    · rcases R_iff_diagPrefix_or_colTail.mp hR with hDiag | hCol
      · rcases hDiag with ⟨a, _hat, _hae, hdiag⟩
        exact False.elim
          (disjoint_D_S M ⟨a, hdiag⟩ ⟨r, hrz, hstart⟩)
      · exact colTail_depth4_cases hCol
    · rcases hC with ⟨b', hb'e, hb'host⟩
      have hb'row : b' <= e + 4 := by omega
      have hbrow : b <= e + 4 := by omega
      have hbb' : b' = b :=
        M.fixed_q_injective hb'row hbrow (hb'host.trans hhost.symm)
      omega
  · intro hrecent
    left
    apply R_iff_diagPrefix_or_colTail.mpr
    right
    rcases hrecent with h1 | h2 | h3
    · exact ⟨e + 1, by omega, by omega, h1⟩
    · exact ⟨e + 2, by omega, by omega, h2⟩
    · exact ⟨e + 3, by omega, by omega, h3⟩

/-- The same exact reduction in row coordinates.  The condition
`t-3 <= b < t` says precisely that the given host is in the terminal
three-cell strip. -/
theorem blocker_terminal_host_source_depth4_iff_recent_column_hosts
    (M : RecurrenceModel) {t z r b : Nat}
    (ht : 4 <= t)
    (hrz : r < z) (hstart : M.f z r = z)
    (hbTerminal : t - 3 <= b) (hbt : b < t)
    (hhost : M.f t b = z) :
    B M.f t (t - 4) z <->
      M.f (t - 3) (t - 4) = z \/
      M.f (t - 2) (t - 4) = z \/
      M.f (t - 1) (t - 4) = z := by
  have ht4 : t - 4 + 4 = t := by omega
  have ht3 : t - 4 + 1 = t - 3 := by omega
  have ht2 : t - 4 + 2 = t - 2 := by omega
  have ht1 : t - 4 + 3 = t - 1 := by omega
  have hbLower : t - 4 + 1 <= b := by omega
  have h :=
    blocker_terminal_host_depth4_source_iff_recent_column_hosts
      M hrz hstart hbLower (by simpa only [ht4] using hbt)
        (by simpa only [ht4] using hhost)
  simpa only [ht4, ht3, ht2, ht1] using h

/-- The proposed actual-game scheduler law isolated by the R32 audit.
After a rescue (`u` is the preceding `V1` and lies below the preceding
diagonal), every terminal-strip output below `u` is already present in the
depth-four source.

This is deliberately a definition, not a theorem of `RecurrenceModel`.
The rescue inequality is essential in the empirical dropped-hypothesis
audit. -/
def TerminalSubUBackfillLaw (M : RecurrenceModel) : Prop :=
  forall {t u b : Nat},
    6 <= t ->
    M.f (t - 1) (t - 2) = u ->
    u < M.f (t - 2) (t - 2) ->
    t - 3 <= b -> b < t ->
    M.f t b < u ->
    B M.f t (t - 4) (M.f t b)

/-- On the blocker branch, `TerminalSubUBackfillLaw` does more than assert
abstract source membership: the exact depth-four reduction converts it to
one of the three concrete recent same-column equalities. -/
theorem terminal_sub_u_backfill_blocker_has_recent_column_host
    (M : RecurrenceModel) (hLaw : TerminalSubUBackfillLaw M)
    {t u z r b : Nat}
    (ht : 6 <= t)
    (huSeat : M.f (t - 1) (t - 2) = u)
    (hPrevDiagonalAbove : u < M.f (t - 2) (t - 2))
    (hzu : z < u)
    (hrz : r < z) (hstart : M.f z r = z)
    (hbTerminal : t - 3 <= b) (hbt : b < t)
    (hhost : M.f t b = z) :
    M.f (t - 3) (t - 4) = z \/
      M.f (t - 2) (t - 4) = z \/
      M.f (t - 1) (t - 4) = z := by
  have hbackfill : B M.f t (t - 4) z := by
    have h := hLaw ht huSeat hPrevDiagonalAbove hbTerminal hbt
      (by simpa only [hhost] using hzu)
    simpa only [hhost] using h
  exact
    (blocker_terminal_host_source_depth4_iff_recent_column_hosts
      M (by omega) hrz hstart hbTerminal hbt hhost).mp hbackfill

/-- Minimal closure interface for the R29/R31 residual.  Once the terminal
host has been produced, the backfill law contradicts the already-assumed
absence from the preceding (`t-4`) source. -/
theorem terminal_sub_u_backfill_law_excludes_terminal_residual
    (M : RecurrenceModel) (hLaw : TerminalSubUBackfillLaw M)
    {t u z b : Nat}
    (ht : 6 <= t)
    (huSeat : M.f (t - 1) (t - 2) = u)
    (hPrevDiagonalAbove : u < M.f (t - 2) (t - 2))
    (hzu : z < u)
    (hbTerminal : t - 3 <= b) (hbt : b < t)
    (hhost : M.f t b = z)
    (hzMissingDepth4 : Not (B M.f t (t - 4) z)) : False := by
  apply hzMissingDepth4
  have h := hLaw ht huSeat hPrevDiagonalAbove hbTerminal hbt
    (by simpa only [hhost] using hzu)
  simpa only [hhost] using h

/-- `L=3` specialization matching the residual coordinates of R29/R31:
`t=e+6`, the earlier missing source is `e+2=t-4`, and the terminal host is
one of `e+3,e+4,e+5`.  The final-backstop absence at `e+3` is the upstream
fact used by R29 to produce this host; after the host is available, it is
not needed again in the contradiction. -/
theorem gameF_terminal_sub_u_backfill_closes_r29_r31_residual
    (hLaw : TerminalSubUBackfillLaw gameRecurrenceModel)
    {e u z b : Nat}
    (huSeat : gameF (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < gameF (e + 4) (e + 4))
    (hzu : z < u)
    (hb : b = e + 3 \/ b = e + 4 \/ b = e + 5)
    (hhost : gameF (e + 6) b = z)
    (hzMissingTwo : Not (B gameF (e + 6) (e + 2) z)) : False := by
  have hbTerminal : e + 6 - 3 <= b := by
    rcases hb with rfl | rfl | rfl <;> omega
  have hbt : b < e + 6 := by
    rcases hb with rfl | rfl | rfl <;> omega
  apply terminal_sub_u_backfill_law_excludes_terminal_residual
    gameRecurrenceModel hLaw (t := e + 6) (u := u) (z := z) (b := b)
      (by omega)
  · simpa only [show e + 6 - 1 = e + 5 by omega,
      show e + 6 - 2 = e + 4 by omega] using huSeat
  · simpa only [show e + 6 - 2 = e + 4 by omega] using
      hPrevDiagonalAbove
  · exact hzu
  · exact hbTerminal
  · exact hbt
  · exact hhost
  · simpa only [show e + 6 - 4 = e + 2 by omega] using hzMissingTwo

end ChompLean
