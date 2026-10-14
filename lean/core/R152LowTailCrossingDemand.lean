import R151FAtomicPreview

set_option autoImplicit false

namespace ChompLean

/-!
R152: extend the preview-supplier crossing law from the lag-three preview
to every high host in the low tail of the R151 first-failure normal form.

The proof uses only actual-game recurrence, persistence of a completed
row-start, fixed-row injectivity, and diagonal/row-start disjointness.  In
particular, the value need not be `t+3`: any host `F(t,H)=v` with
`H<t<v` has the same crossing obligation.
-/

/-- A completed blocker frozen strictly to the right of a high-host column
must visit that column strictly before its own row-start.  This is the
generic form of `gameF_preview_crossing_blocker_prefreeze_visit`. -/
theorem gameF_high_host_crossing_blocker_prefreeze_visit
    {t H v k rk : Nat}
    (hhost : gameF t H = v)
    (hHt : H < t)
    (htv : t < v)
    (hkt : k <= t)
    (hrkH : H < rk)
    (hrkk : rk < k)
    (hstartk : gameF k rk = k) :
    exists a, H < a /\ a < k /\ gameF a H = k := by
  have hkpos : 0 < k := by omega
  have hnotfirst : Not (H < t /\ gameF (t - 1) H < t) := by
    rintro ⟨hHt', hsmall⟩
    have hconst := gameF_brouwerRecurrence.1 (q := t) (r := H) hHt' hsmall
    rw [hhost] at hconst
    omega
  have hmex := gameF_brouwerRecurrence.2 (q := t) (r := H)
    (by omega) hnotfirst
  have hkB : B gameF t H k :=
    hmex.2.2 k hkpos (by rw [hhost]; omega)
  have hpersist : gameF t rk = k :=
    gameF_freeze_persists hrkk hstartk hkt
  cases hkB with
  | inr hC =>
      rcases hC with ⟨b, hbH, hbval⟩
      have hbrk : b = rk := gameRecurrenceModel.fixed_q_injective
        (by omega) (by omega) (hbval.trans hpersist.symm)
      omega
  | inl hR =>
      rcases hR with ⟨a, hat, haval⟩
      by_cases haH : a <= H
      · have hdiag : gameF a a = k := by
          simpa [Nat.min_eq_left haH] using haval
        exact False.elim (disjoint_D_S gameRecurrenceModel
          ⟨a, hdiag⟩ ⟨rk, hrkk, hstartk⟩)
      · have hHa : H < a := Nat.lt_of_not_ge haH
        have hcol : gameF a H = k := by
          simpa [Nat.min_eq_right (Nat.le_of_lt hHa)] using haval
        by_cases hak : a < k
        · exact ⟨a, hHa, hak, hcol⟩
        · exfalso
          have hrow := gameF_low_cell_has_rowstart (q := a) (c := H)
            (by omega) (by omega)
          rw [hcol] at hrow
          have hHrk : H = rk := gameRecurrenceModel.fixed_q_injective
            (q := k) (by omega) (by omega) (hrow.2.trans hstartk.symm)
          omega

/-- A high-host column cannot already be the freeze column of any blocker
at or below the host row. -/
theorem gameF_high_host_column_freeze_free
    {t H v k rk : Nat}
    (hhost : gameF t H = v)
    (htv : t < v)
    (hkt : k <= t)
    (hrkk : rk < k)
    (hstartk : gameF k rk = k) :
    rk ≠ H := by
  intro heq
  subst rk
  have hpersist : gameF t H = k :=
    gameF_freeze_persists hrkk hstartk hkt
  omega

/-- Distinct pre-target rows hosting the same high value must use distinct
columns.  Thus the all-low tail in R151 supplies genuinely different
crossing columns, not repeated copies of one obligation. -/
theorem gameF_same_high_target_hosts_have_distinct_columns
    {t1 t2 H1 H2 v : Nat}
    (hH1t1 : H1 < t1)
    (ht12 : t1 < t2)
    (ht2v : t2 < v)
    (hhost1 : gameF t1 H1 = v)
    (hhost2 : gameF t2 H2 = v) :
    H1 ≠ H2 := by
  intro hcols
  subst H2
  exact encoding_same_lower_no_repeat game_encodes
    (s := H1) (t₁ := t1) (t₂ := t2) (p := v)
    hH1t1 ht12 ht2v hhost1 hhost2

/-- The crossing supplier is itself a saturated MEX cell, now stated as
an immediate generic-host consequence. -/
theorem gameF_high_host_crossing_supplier_is_saturated
    {t H v k rk : Nat}
    (hhost : gameF t H = v)
    (hHt : H < t)
    (htv : t < v)
    (hkt : k <= t)
    (hrkH : H < rk)
    (hrkk : rk < k)
    (hstartk : gameF k rk = k) :
    exists a, H < a /\ a < k /\ gameF a H = k /\
      forall j, 0 < j -> j < k -> B gameF a H j := by
  rcases gameF_high_host_crossing_blocker_prefreeze_visit
      hhost hHt htv hkt hrkH hrkk hstartk with ⟨a, hHa, hak, hval⟩
  exact ⟨a, hHa, hak, hval,
    gameF_crossing_supplier_is_saturated hHa hak hval⟩

#print axioms gameF_high_host_crossing_blocker_prefreeze_visit
#print axioms gameF_high_host_column_freeze_free
#print axioms gameF_same_high_target_hosts_have_distinct_columns
#print axioms gameF_high_host_crossing_supplier_is_saturated

end ChompLean
