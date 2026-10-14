import R17HandoffSink

set_option autoImplicit false

namespace ChompLean

/-!
R17: abstract rolling-debt induction.

`S k z` means that value `z` is covered at the `k`-th source of a finite
window.  The theorem isolates three local inputs:

* every hole at the first source is sealed at the next source;
* every value lost on an interior edge is restored one source later;
* the final edge creates no new loss.

No bound on the number of simultaneous holes is used.  In particular, the
finite receipts `holes <= 2` and the offset alphabets are not hypotheses.
-/

theorem rolling_debt_closure
    {S : Nat -> Nat -> Prop} {n u : Nat}
    (hn : 1 <= n)
    (hbase :
      forall z, 0 < z -> z < u ->
        Not (S 0 z) -> S 1 z)
    (hrecover :
      forall k z, k + 2 <= n -> 0 < z -> z < u ->
        S k z -> Not (S (k + 1) z) -> S (k + 2) z)
    (hlast :
      forall z, 0 < z -> z < u ->
        S (n - 1) z -> S n z) :
    forall z, 0 < z -> z < u -> S n z := by
  have hinvariant :
      forall k, k < n -> forall z, 0 < z -> z < u ->
        Not (S (k + 1) z) -> S k z := by
    intro k hk
    induction k with
    | zero =>
        intro z hz hzu hmissing
        by_cases h0 : S 0 z
        · exact h0
        · exact False.elim (hmissing (by simpa using hbase z hz hzu h0))
    | succ k ih =>
        intro z hz hzu hmissing
        have hklt : k < n := by omega
        by_cases hprev : S (k + 1) z
        · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hprev
        · have hcoveredK : S k z := ih hklt z hz hzu hprev
          have hrestored : S (k + 2) z :=
            hrecover k z (by omega) hz hzu hcoveredK hprev
          exact False.elim (hmissing (by simpa [Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using hrestored))
  intro z hz hzu
  by_cases hfinal : S n z
  · exact hfinal
  · have hprev : S (n - 1) z := by
      apply hinvariant (n - 1) (by omega) z hz hzu
      simpa [Nat.sub_add_cancel hn] using hfinal
    exact False.elim (hfinal (hlast z hz hzu hprev))

/-!
Instantiation for the Chomp source `B` on columns `lo, ..., lo+n`.
The index arithmetic is kept in the statement so later proof files can feed
the three local window lemmas directly into the abstract induction.
-/

theorem rolling_B_window_closure
    {f : Nat -> Nat -> Nat} {t lo n u : Nat}
    (hn : 1 <= n)
    (hbase :
      forall z, 0 < z -> z < u ->
        Not (B f t lo z) -> B f t (lo + 1) z)
    (hrecover :
      forall k z, k + 2 <= n -> 0 < z -> z < u ->
        B f t (lo + k) z ->
        Not (B f t (lo + (k + 1)) z) ->
        B f t (lo + (k + 2)) z)
    (hlast :
      forall z, 0 < z -> z < u ->
        B f t (lo + (n - 1)) z -> B f t (lo + n) z) :
    forall z, 0 < z -> z < u -> B f t (lo + n) z := by
  let S : Nat -> Nat -> Prop := fun k z => B f t (lo + k) z
  exact rolling_debt_closure (S := S) hn hbase hrecover hlast

/--
The concrete reduction used by the R17 program.  Once every actual loss has
the fresh-or-next-diagonal sink, `R17HandoffSink` supplies the recovery
hypothesis of the abstract rolling-debt theorem.
-/
theorem rolling_B_window_closure_of_death_dichotomy
    {f : Nat -> Nat -> Nat} {t lo n u : Nat}
    (hn : 1 <= n)
    (hbase :
      forall z, 0 < z -> z < u ->
        Not (B f t lo z) -> B f t (lo + 1) z)
    (hdeath :
      forall k z, k + 2 <= n -> 0 < z -> z < u ->
        B f t (lo + k) z ->
        Not (B f t (lo + (k + 1)) z) ->
        (f t ((lo + k) + 1) = z \/
          ((lo + k) + 2 < t /\
            f ((lo + k) + 2) ((lo + k) + 2) = z)))
    (hlast :
      forall z, 0 < z -> z < u ->
        B f t (lo + (n - 1)) z -> B f t (lo + n) z) :
    forall z, 0 < z -> z < u -> B f t (lo + n) z := by
  apply rolling_B_window_closure hn hbase ?_ hlast
  intro k z hk hz hzu hcurrent hlost
  have hsink := hdeath k z hk hz hzu hcurrent hlost
  have hcovered := death_dichotomy_covers_later_source
    (e := lo + k) (r := lo + (k + 2)) hsink (by omega)
  simpa [Nat.add_assoc] using hcovered

end ChompLean
