import R17OrderedLoss

set_option autoImplicit false

namespace ChompLean

/-!
R18 scale correction: the upper value in a same-edge double loss need not
be the next diagonal owner.  The ordered-loss induction only needs it to be
back in the source two columns after the old source.  Under the fact that it
was absent at the intervening source, the three channels below are the exact
ways this can happen.
-/

/-- The exact new channels by which a value absent at source `e+1` can be
present again at source `e+2`.  The `ColTail` branch is intentionally kept:
it is transient coverage, but transient one-step recovery is sufficient for
the ordered-loss induction. -/
def ImmediateRecoveryChannels
    (f : Nat -> Nat -> Nat) (t e z : Nat) : Prop :=
  (e + 2 < t /\ f (e + 2) (e + 2) = z) \/
  ColTail f t (e + 2) z \/
  f t (e + 1) = z

/-- Once `z` is missing at source `e+1`, its membership at source `e+2` is
equivalent to one of the new diagonal, new column-tail, or fresh-row-cell
channels.  Old diagonal-prefix and old row-prefix membership are ruled out
by the missing-source hypothesis. -/
theorem lost_then_recovered_iff_immediate_channels
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hlost : Not (B f t (e + 1) z)) :
    B f t (e + 2) z <-> ImmediateRecoveryChannels f t e z := by
  have hstep : e + 2 = (e + 1) + 1 := by omega
  rw [hstep, B_successor_exact_delta]
  constructor
  · intro h
    rcases h with hOldDiag | hNewDiag | hNewCol | hOldRow | hFresh
    · exact False.elim (hlost (Or.inl
        (R_iff_diagPrefix_or_colTail.mpr (Or.inl hOldDiag))))
    · exact Or.inl hNewDiag
    · exact Or.inr (Or.inl hNewCol)
    · exact False.elim (hlost (Or.inr hOldRow))
    · exact Or.inr (Or.inr hFresh)
  · intro h
    rcases h with hNewDiag | hNewCol | hFresh
    · exact Or.inr (Or.inl hNewDiag)
    · exact Or.inr (Or.inr (Or.inl hNewCol))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hFresh)))

/-- Proof-facing corrected specialization of `ordered_B_window_closure`.
For two losses on one edge, it asks for exact immediate recovery channels
for the upper value, rather than the refuted diagonal-only classifier. -/
theorem ordered_B_window_closure_of_upper_recovery_channels
    {f : Nat -> Nat -> Nat} {t lo n u : Nat}
    (hn : 1 <= n)
    (hbase :
      forall z, 0 < z -> z < u ->
        Not (B f t lo z) -> B f t (lo + 1) z)
    (hmex :
      forall k, k + 2 <= n ->
        IsMex (B f t (lo + (k + 1))) (f t (lo + (k + 1))))
    (hupperRecovery :
      forall k y z, k + 2 <= n ->
        0 < y -> y < z -> z < u ->
        B f t (lo + k) y -> Not (B f t (lo + (k + 1)) y) ->
        B f t (lo + k) z -> Not (B f t (lo + (k + 1)) z) ->
        ImmediateRecoveryChannels f t (lo + k) z)
    (hlast :
      forall z, 0 < z -> z < u ->
        B f t (lo + (n - 1)) z -> B f t (lo + n) z) :
    forall z, 0 < z -> z < u -> B f t (lo + n) z := by
  apply ordered_B_window_closure hn hbase hmex ?_ hlast
  intro k y z hk hy hyz hzu hky hmissingY hkz hmissingZ
  have hchannels := hupperRecovery k y z hk hy hyz hzu
    hky hmissingY hkz hmissingZ
  have hlost : Not (B f t ((lo + k) + 1) z) := by
    simpa [Nat.add_assoc] using hmissingZ
  have hrecovered :=
    (lost_then_recovered_iff_immediate_channels hlost).2 hchannels
  simpa [Nat.add_assoc] using hrecovered

/-!
The `s=20829` scale witness does not satisfy immediate upper recovery.  It
instead exhibits the exact two-cell MEX queue: the lower missing value is
served at `e+1`, and, after it is restored and every value below the upper
one is covered, the upper value is served at `e+2`.  The next theorem is the
minimal mechanical core of that route.  The hypotheses deliberately expose
the only substantive step: coverage of every value below `z` at source
`e+2`.
-/

/-- Two ordered debts can be served in consecutive cells.  No recovery or
permanent-channel hypothesis for the upper value is used. -/
theorem entry_double_two_step
    {f : Nat -> Nat -> Nat} {t e y z : Nat}
    (hy : 0 < y) (hyz : y < z)
    (hmexY : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hyMissing : Not (B f t (e + 1) y))
    (hlowerY : forall w, 0 < w -> w < y -> B f t (e + 1) w)
    (hmexZ : IsMex (B f t (e + 2)) (f t (e + 2)))
    (hzMissing : Not (B f t (e + 2) z))
    (hlowerZ : forall w, 0 < w -> w < z -> B f t (e + 2) w) :
    f t (e + 1) = y /\
      B f t (e + 2) y /\
      f t (e + 2) = z /\
      B f t (e + 3) z := by
  have hserveY : f t (e + 1) = y :=
    mex_serves_only_low_hole hmexY hyMissing hy hlowerY
  have hyCovered : B f t (e + 2) y := by
    simpa [Nat.add_assoc] using
      (fresh_emission_closes_next (e := e + 1) hserveY)
  have hz : 0 < z := by omega
  have hserveZ : f t (e + 2) = z :=
    mex_serves_only_low_hole hmexZ hzMissing hz hlowerZ
  have hzCovered : B f t (e + 3) z := by
    simpa [Nat.add_assoc] using
      (fresh_emission_closes_next (e := e + 2) hserveZ)
  exact ⟨hserveY, hyCovered, hserveZ, hzCovered⟩

/-- At a final edge, a penultimate source with at most one sub-`u` hole is
enough: the MEX cell closes that hole, while `hseal` preserves every value
that was already present.  This is the proof-facing `n=3` fallback once the
two-step analysis establishes the one-hole penultimate state. -/
theorem penultimate_one_hole_mex_closure
    {f : Nat -> Nat -> Nat} {t e u : Nat}
    (hmex : IsMex (B f t e) (f t e))
    (hone :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hseal :
      forall z, 0 < z -> z < u -> B f t e z -> B f t (e + 1) z) :
    forall z, 0 < z -> z < u -> B f t (e + 1) z := by
  intro z hz hzu
  by_cases hcurrent : B f t e z
  · exact hseal z hz hzu hcurrent
  · exact one_hole_mex_seals_base hmex hone hz hzu hcurrent

end ChompLean
