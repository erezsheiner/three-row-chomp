import R152Col11Lag7Collapse
import R154Lag8TerminalSiblingAudit
import R138StrictPreLag3HostCeilingReduction

set_option autoImplicit false

namespace ChompLean

/-!
# Fixed-lag HOST-OLD reduction

The first non-rail endpoint after the compiled lag-four through lag-seven
pairs is the row `v-8`.  The F8000 receipt suggests the sharp slice of
HOST-OLD below: every actual lag-eight host lies strictly before the
assignment midpoint.  This file records exactly what that atom buys and
shows why the existing order/scalar interface cannot prove it.
-/

/-- The fixed-lag-eight slice of strict HOST-OLD. -/
def FixedLag8HostCeiling (v g : Nat) : Prop :=
  forall c, c <= v - 8 -> gameF (v - 8) c = v -> c < g

/-- Full strict pre-lag-three HOST-OLD contains the fixed-lag-eight slice. -/
theorem fixedLag8HostCeiling_of_strictPreLag3HostCeiling
    {v g : Nat}
    (hv : 8 <= v)
    (hhostOld : StrictPreLag3HostCeiling v g) :
    FixedLag8HostCeiling v g := by
  intro c hca hhost
  exact hhostOld (v - 8) c hca (by omega) hhost

/-- The fixed-lag atom removes exactly the adaptive endpoint `a=q-5` from
the strengthened R151 normal form, pushing the terminal burn to lag at
least nine.  No midpoint or low-sibling premise is used. -/
theorem gameF_firstFailure_burn_ladder_pre_lag9_actual_of_fixedLag8
    {q r g H : Nat}
    (hq : 23 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hlag8 : FixedLag8HostCeiling (q + 3) g) :
    exists a, r <= a /\ a < q - 5 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_pre_lag8_actual
      hq hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 5
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have ha : a = q - 5 := by omega
    subst a
    have hburn' : gameF ((q + 3) - 8) (r - 1) = q + 3 := by
      have hidx : (q + 3) - 8 = q - 5 := by omega
      rw [hidx]
      exact hburn
    have hc : r - 1 < g := hlag8 (r - 1) (by omega) hburn'
    omega

/-! ## Exact interface separation

At parameter `k=7`, the arithmetic R151F frame has target 70, terminal
burn row 62 (`70-8`), terminal predecessor 55, and midpoint 49.  It obeys
the exported first-failure/order/scalar geometry while placing the lag-eight
terminal host strictly to the right of the midpoint.  Thus the new fixed-lag
atom needs actual source content beyond that interface.
-/

theorem r151f_k7_fixed_lag8_countergeometry :
    r151fV 7 = 70 /\
    r151fA 7 = r151fV 7 - 8 /\
    r151fR 7 - 1 = 55 /\
    r151fG 7 = 49 /\
    r151fG 7 < r151fR 7 - 1 /\
    r151fBurnRow 7 (r151fR 7 - 1) = r151fA 7 := by
  simp [r151fV, r151fA, r151fR, r151fG, r151fBurnRow]

/-- The same fixed-lag-eight countergeometry also carries every packaged
scalar first-failure constraint of the R151F interface. -/
theorem r151f_k7_fixed_lag8_interface_survives :
    (1 <= r151fQ 7 /\
      r151fR 7 < r151fQ 7 + 3 /\
      r151fV 7 = r151fQ 7 + 3 /\
      r151fG 7 + 1 < r151fR 7 /\
      2 < r151fG 7 + 1 /\
      r151fH 7 <= r151fQ 7 /\
      r151fH 7 <= r151fG 7 /\
      r151fR 7 - (r151fG 7 + 1) = 7 - 1) /\
    (r151fV 7 + 4 * 7 = 2 * r151fG 7 /\
      r151fR 7 + 1 = 2 * (4 * 7 + 1) - 1 /\
      r151fV 7 = 6 * 7 + 4 * 7 /\
      r151fV 7 + 4 * 7 <= 2 * r151fR 7 + 1 /\
      (r151fV 7 - r151fR 7 - 1) + 4 * 7 <= r151fR 7) := by
  exact ⟨r151f_first_failure_frame (by omega),
    r151f_scalar_interfaces (by omega)⟩

#print axioms fixedLag8HostCeiling_of_strictPreLag3HostCeiling
#print axioms gameF_firstFailure_burn_ladder_pre_lag9_actual_of_fixedLag8
#print axioms r151f_k7_fixed_lag8_countergeometry
#print axioms r151f_k7_fixed_lag8_interface_survives

end ChompLean
