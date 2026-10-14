import R17RollingDebt

set_option autoImplicit false

namespace ChompLean

/-!
R17: ordered-loss reduction.

This is a sharper replacement for assuming the full death dichotomy.  At an
interior edge, the least newly lost value is served by the next MEX cell.  A
new hypothesis is needed only when another, smaller value is lost on the same
edge: the larger loss must already be restored by the next source (in the
observed Chomp windows, it is exactly the new diagonal owner).
-/

/-- A genuine MEX cell serves a missing value when there is no lower hole. -/
theorem mex_serves_only_low_hole
    {f : Nat -> Nat -> Nat} {t e z : Nat}
    (hmex : IsMex (B f t e) (f t e))
    (hzMissing : Not (B f t e z))
    (hzPos : 0 < z)
    (hlower : forall y, 0 < y -> y < z -> B f t e y) :
    f t e = z := by
  have hle : f t e <= z := by
    by_cases h : f t e <= z
    · exact h
    · have hzlt : z < f t e := by omega
      exact False.elim (hzMissing (hmex.2.2 z hzPos hzlt))
  have hge : z <= f t e := by
    by_cases h : z <= f t e
    · exact h
    · have hflt : f t e < z := by omega
      exact False.elim (hmex.2.1 (hlower (f t e) hmex.1 hflt))
  exact Nat.le_antisymm hle hge

/-- At most one sub-`u` hole plus a MEX cell gives the base seal. -/
theorem one_hole_mex_seals_base
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (hmex : IsMex (B f t e) (f t e))
    (hone :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hz : 0 < z) (hzu : z < u)
    (hmissing : Not (B f t e z)) :
    B f t (e + 1) z := by
  have hlower : forall y, 0 < y -> y < z -> B f t e y := by
    intro y hy hyz
    by_cases hcovered : B f t e y
    · exact hcovered
    · have heq := hone y z hy (by omega) hz hzu hcovered hmissing
      omega
  have heq : f t e = z :=
    mex_serves_only_low_hole hmex hmissing hz hlower
  exact fresh_emission_closes_next heq

/--
If every old-column-only value on the final edge is its newly arriving
diagonal owner, that edge creates no loss.
-/
theorem final_parked_owner_implies_no_loss
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (howner :
      forall w, 0 < w -> w < u -> ParkedOnly f t e w ->
        (e + 1 < t /\ f (e + 1) (e + 1) = w))
    (hz : 0 < z) (hzu : z < u)
    (hcurrent : B f t e z) :
    B f t (e + 1) z := by
  by_cases hnext : B f t (e + 1) z
  · exact hnext
  · have hpark := source_loss_implies_parkedOnly hcurrent hnext
    rcases howner z hz hzu hpark with ⟨ht, hdiag⟩
    exact False.elim (hnext (B_successor_exact_delta.mpr
      (Or.inr (Or.inl ⟨ht, hdiag⟩))))

/--
Abstract rolling closure from same-edge loss ordering.  `hupper` says that
if `y<z` are both lost on edge `k -> k+1`, then the upper loss `z` is already
restored at source `k+2`.  Values with no lower simultaneous loss are served
by `hserve`.
-/
theorem ordered_loss_closure
    {S : Nat -> Nat -> Prop} {n u : Nat}
    (hn : 1 <= n)
    (hbase :
      forall z, 0 < z -> z < u ->
        Not (S 0 z) -> S 1 z)
    (hserve :
      forall k z, k + 2 <= n -> 0 < z -> z < u ->
        Not (S (k + 1) z) ->
        (forall y, 0 < y -> y < z -> S (k + 1) y) ->
        S (k + 2) z)
    (hupper :
      forall k y z, k + 2 <= n ->
        0 < y -> y < z -> z < u ->
        S k y -> Not (S (k + 1) y) ->
        S k z -> Not (S (k + 1) z) ->
        S (k + 2) z)
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
        intro z hz hzu hmissingNext
        have hklt : k < n := by omega
        by_cases hprev : S (k + 1) z
        · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hprev
        · have hcoveredK : S k z := ih hklt z hz hzu hprev
          have hrestored : S (k + 2) z := by
            by_cases hlossBelow :
                exists y, 0 < y /\ y < z /\
                  S k y /\ Not (S (k + 1) y)
            · rcases hlossBelow with ⟨y, hy, hyz, hky, hmissingY⟩
              exact hupper k y z (by omega) hy hyz hzu
                hky hmissingY hcoveredK hprev
            · have hlowerCovered :
                  forall y, 0 < y -> y < z -> S (k + 1) y := by
                intro y hy hyz
                by_cases hyCovered : S (k + 1) y
                · exact hyCovered
                · have hky : S k y := ih hklt y hy (by omega) hyCovered
                  exact False.elim
                    (hlossBelow ⟨y, hy, hyz, hky, hyCovered⟩)
              exact hserve k z (by omega) hz hzu hprev hlowerCovered
          exact False.elim (hmissingNext (by simpa [Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using hrestored))
  intro z hz hzu
  by_cases hfinal : S n z
  · exact hfinal
  · have hprev : S (n - 1) z := by
      apply hinvariant (n - 1) (by omega) z hz hzu
      simpa [Nat.sub_add_cancel hn] using hfinal
    exact False.elim (hfinal (hlast z hz hzu hprev))

/--
Concrete Chomp-source form.  The MEX service is discharged mechanically;
the only interior content left in `hupper` is the same-edge ordering law.
-/
theorem ordered_B_window_closure
    {f : Nat -> Nat -> Nat} {t lo n u : Nat}
    (hn : 1 <= n)
    (hbase :
      forall z, 0 < z -> z < u ->
        Not (B f t lo z) -> B f t (lo + 1) z)
    (hmex :
      forall k, k + 2 <= n ->
        IsMex (B f t (lo + (k + 1))) (f t (lo + (k + 1))))
    (hupper :
      forall k y z, k + 2 <= n ->
        0 < y -> y < z -> z < u ->
        B f t (lo + k) y -> Not (B f t (lo + (k + 1)) y) ->
        B f t (lo + k) z -> Not (B f t (lo + (k + 1)) z) ->
        B f t (lo + (k + 2)) z)
    (hlast :
      forall z, 0 < z -> z < u ->
        B f t (lo + (n - 1)) z -> B f t (lo + n) z) :
    forall z, 0 < z -> z < u -> B f t (lo + n) z := by
  let S : Nat -> Nat -> Prop := fun k z => B f t (lo + k) z
  apply ordered_loss_closure (S := S) hn hbase ?_ hupper hlast
  intro k z hk hz hzu hmissing hlower
  have hcell := hmex k hk
  have heq : f t (lo + (k + 1)) = z :=
    mex_serves_only_low_hole hcell hmissing hz hlower
  simpa [S, Nat.add_assoc] using
    (fresh_emission_closes_next (e := lo + (k + 1)) heq)

/--
Final proof-facing form: when two ordered values are lost on the same edge,
the larger one is the diagonal owner two columns later.  The diagonal-source
membership is discharged here, leaving that classifier as the only interior
window hypothesis.
-/
theorem ordered_B_window_closure_of_upper_diagonal
    {f : Nat -> Nat -> Nat} {t lo n u : Nat}
    (hn : 1 <= n)
    (hbase :
      forall z, 0 < z -> z < u ->
        Not (B f t lo z) -> B f t (lo + 1) z)
    (hmex :
      forall k, k + 2 <= n ->
        IsMex (B f t (lo + (k + 1))) (f t (lo + (k + 1))))
    (hupperDiag :
      forall k y z, k + 2 <= n ->
        0 < y -> y < z -> z < u ->
        B f t (lo + k) y -> Not (B f t (lo + (k + 1)) y) ->
        B f t (lo + k) z -> Not (B f t (lo + (k + 1)) z) ->
        (lo + k + 2 < t /\
          f (lo + k + 2) (lo + k + 2) = z))
    (hlast :
      forall z, 0 < z -> z < u ->
        B f t (lo + (n - 1)) z -> B f t (lo + n) z) :
    forall z, 0 < z -> z < u -> B f t (lo + n) z := by
  apply ordered_B_window_closure hn hbase hmex ?_ hlast
  intro k y z hk hy hyz hzu hky hmissingY hkz hmissingZ
  rcases hupperDiag k y z hk hy hyz hzu
    hky hmissingY hkz hmissingZ with ⟨ht, hdiag⟩
  have hpermanent :
      PermanentCover f t (lo + k + 2) z :=
    next_diagonal_enters_permanent ht hdiag
  simpa [Nat.add_assoc] using permanentCover_mem_source hpermanent

end ChompLean
