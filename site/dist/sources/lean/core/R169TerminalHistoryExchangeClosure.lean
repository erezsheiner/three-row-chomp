import R168DeepTerminalLeftRelayNormalForm

set_option autoImplicit false

namespace ChompLean

/-!
# Terminal-history exchange closes the upper rail

`R168DeepTerminalLeftRelayNormalForm` isolated the exact surviving global
debt.  In the live terminal edit class where `q = v - 3` is absent from both
adjacent completed histories, it is enough to exclude an older occurrence
of `v` below row `q` in the predecessor column.  The existing depth-three
causal decomposition then forces the row-`q` occurrence.

This file records the end-to-end consequence: that single exchange law is
already sufficient for the all-depth owner descent and hence for the upper
rail.  No unrestricted terminal age law is needed on this route.
-/

/-- The minimal adjacent-history exchange exclusion implies the all-depth
preview-owner descent used by the terminal upper-rail proof. -/
theorem liveDeepTerminalPreviewOwnerNotLeft_of_exchange
    (hexchange : LiveTerminalPreviewAbsentExcludesOldTargetHistory) :
    LiveDeepTerminalPreviewOwnerNotLeft :=
  liveDeepTerminalPreviewOwnerNotLeft_of_previewAbsentHistoryForcesLag3
    (liveTerminalPreviewAbsentHistoryForcesLag3_iff_exchange.mpr hexchange)

/-- End-to-end closure statement.  The only additional global hypothesis is
the restricted adjacent-history exchange exclusion isolated in R168. -/
theorem gameF_upperRail_of_liveTerminalPreviewAbsentExchange
    {q r g H : Nat}
    (hq : 4 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3)
    (hexchange : LiveTerminalPreviewAbsentExcludesOldTargetHistory) :
    r <= g + 1 := by
  exact gameF_upperRail_of_liveDeepTerminalPreviewOwnerNotLeft
    hq hrv hstart howners hinterior hpreviewLe hpreviewLeft hpreview
    (liveDeepTerminalPreviewOwnerNotLeft_of_exchange hexchange)

#print axioms liveDeepTerminalPreviewOwnerNotLeft_of_exchange
#print axioms gameF_upperRail_of_liveTerminalPreviewAbsentExchange

end ChompLean
