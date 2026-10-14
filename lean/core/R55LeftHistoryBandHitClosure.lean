import R55BandHitFourthClosure
import R55OverlapLedgerEventEEchoStaircase

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
R55: LEFT-HISTORY LAW and its Event-E band-hit specialization.

The generic law is a direct exact-source consequence.  Suppose a high,
non-past value `v` is hosted at column `c` in row `t`.  If a column `b<c`
has output above `v`, MEX forces `v` into the source of `(t,b)`.  It cannot
come from the row prefix (its unique current host is to the right), and it
cannot come from a diagonal source (non-pastness).  Thus column `b` already
hosted `v` on a strictly earlier row.

For the third-dip Event-E hit, `v=z-1` is the future diagonal value at
`s+3`, hence non-past.  Consequently, if both named higher packet columns
`c,b0` lie left of its row-`s` host, they force two distinct prior rides of
`z-1`.  Combined with the two-extra-source bound and the exact overlap
envelope, this gives a sharpened order/history normal form and locates the
whole hit atom beyond the corridor `ell < delta+11`.
-/

private theorem r55_pred_lt_self {z : Nat} (hz : 0 < z) :
    z - 1 < z := by
  omega

/-- LEFT-HISTORY LAW in the recurrence-model API. -/
theorem left_history_of_higher_left_column
    (M : RecurrenceModel) {t v c b : Nat}
    (hct : c <= t) (hbc : b < c)
    (htv : t < v) (hhost : M.f t c = v)
    (hhigher : v < M.f t b)
    (hnotPast : forall a, a < t -> M.f a a ≠ v) :
    exists a, b < a /\ a < t /\ M.f a b = v := by
  have hB : B M.f t b v := by
    apply M.mex_no_skip (by omega)
    · omega
    · omega
    · exact hhigher
  rcases hB with hR | hC
  · rcases hR with ⟨a, hat, hvalue⟩
    by_cases hab : a <= b
    · have hmin : min a b = a := Nat.min_eq_left hab
      rw [hmin] at hvalue
      exact False.elim ((hnotPast a hat) hvalue)
    · have hba : b < a := by omega
      have hmin : min a b = b := Nat.min_eq_right (by omega)
      rw [hmin] at hvalue
      exact ⟨a, hba, hat, hvalue⟩
  · rcases hC with ⟨r, hrb, hvalue⟩
    have hrc : r = c :=
      M.fixed_q_injective (by omega) hct
        (hvalue.trans hhost.symm)
    omega

/-- Order-or-history form: a higher current-row host is either to the
right of the host of `v`, or its column contains a strict prior ride of
`v`. -/
theorem higher_column_right_or_left_history
    (M : RecurrenceModel) {t v c b : Nat}
    (hct : c <= t) (htv : t < v)
    (hhost : M.f t c = v) (hhigher : v < M.f t b)
    (hnotPast : forall a, a < t -> M.f a a ≠ v) :
    c < b \/ exists a, b < a /\ a < t /\ M.f a b = v := by
  by_cases hbc : b < c
  · exact Or.inr
      (left_history_of_higher_left_column M hct hbc htv hhost
        hhigher hnotPast)
  · left
    have hne : b ≠ c := by
      intro hEq
      subst b
      rw [hhost] at hhigher
      omega
    omega

/-- Strengthened third-dip hit certificate.  The final alternative is the
new content: when neither higher packet column is to the right of the
`z-1` host, both columns carry distinct strict prior rides of `z-1`. -/
def EventEThirdDipBandHitLeftHistoryCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBandHitCompressedCertificate s delta z c b0 /\
  2 * delta + 15 <= s /\
  delta + 11 <= s - delta - 4 /\
  exists g,
    g ∈ EventEThirdMissingBandSlots s delta c b0 /\
    gameF s g = z - 1 /\
    (g < c \/ g < b0 \/
      (s - delta - 1 <= g /\
       exists ac ab,
         c < ac /\ ac < s /\ gameF ac c = z - 1 /\
         b0 < ab /\ ab < s /\ gameF ab b0 = z - 1 /\
         ac ≠ ab))

/-- Event-E application of LEFT-HISTORY plus the R55 overlap envelope. -/
theorem gameF_nonmax_eventE_third_dip_band_hit_left_history
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hhit : EventEThirdDipBandHitCompressedCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventEThirdDipBandHitLeftHistoryCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  classical
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventEThirdDipBandHitCompressedCertificate
    s delta z c b0 at hhit
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists ce be, EventECrossEdgeSurvivorCertificate s delta z ce be
    at hresData
  rcases hresData with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨hdip0, hmargin, hdip1⟩
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzDiag : z + 1 = d := hInv.2.2.2.1
  have hdip2 := hhit.1.1
  have henv := gameF_margin_eventE_third_dip_env_defect_bound
    hU hdip0 hmargin hdip1 hdip2
  change delta + (s + 4) / 2 + 6 <= s /\
      2 * delta + 15 <= s at henv
  have hell : delta + 11 <= s - delta - 4 := by omega
  have horder := eventE_third_dip_band_hit_source_order
    hcross hhit (by omega : (z + 1) + delta = 2 * s)
  rcases horder with ⟨g, hgMissing, hgValue, horder⟩
  refine ⟨hhit, henv.2, hell, g, hgMissing, hgValue, ?_⟩
  by_cases hgc : g < c
  · exact Or.inl hgc
  by_cases hgb0 : g < b0
  · exact Or.inr (Or.inl hgb0)
  right
  right
  have hgDeep : s - delta - 1 <= g := by
    rcases horder with hgc' | hgb0' | hgDeep
    · exact False.elim (hgc hgc')
    · exact False.elim (hgb0 hgb0')
    · exact hgDeep
  refine ⟨hgDeep, ?_⟩
  have hgTriple : g ∈ EventETriplePrefixBandSlots s delta c b0 :=
    (List.mem_filter.mp hgMissing).1
  have hgSurv : g ∈ EventESurvivingBandSlots s delta c b0 :=
    (List.mem_filter.mp hgTriple).1
  have hgSlots : g ∈ EventEDefectBandSlots s delta c b0 :=
    (List.mem_filter.mp hgSurv).1
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨hc, hb0, hcNe, hSucc, hBase,
      _hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hgData := hslotsProps g hgSlots
  have hgcNe : g ≠ c := hgData.2.1
  have hgb0Ne : g ≠ b0 := hgData.2.2.1
  have hcg : c < g := by omega
  have hb0g : b0 < g := by omega
  have hstair := hhit.2.1
  have hdiag3 : gameF (s + 3) (s + 3) = z - 1 :=
    hstair.2.2.2.2.1
  have hpHigh : s < z - 1 := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    omega
  have hpNotPast : forall a, a < s -> gameF a a ≠ z - 1 := by
    intro a ha hEq
    have hdiagEq : gameF a a = gameF (s + 3) (s + 3) :=
      hEq.trans hdiag3.symm
    have haEq := diagonal_injective gameRecurrenceModel hdiagEq
    omega
  have hcHistory := left_history_of_higher_left_column
    gameRecurrenceModel
    (t := s) (v := z - 1) (c := g) (b := c)
    (Nat.le_of_lt hgData.1) hcg hpHigh hgValue
    (by change z - 1 < gameF s c; rw [hSucc]; omega) hpNotPast
  have hbHistory := left_history_of_higher_left_column
    gameRecurrenceModel
    (t := s) (v := z - 1) (c := g) (b := b0)
    (Nat.le_of_lt hgData.1) hb0g hpHigh hgValue
    (by change z - 1 < gameF s b0; rw [hBase]; omega) hpNotPast
  rcases hcHistory with ⟨ac, hcac, hacs, hacValue⟩
  rcases hbHistory with ⟨ab, hb0ab, habs, habValue⟩
  have hacab : ac ≠ ab := by
    intro hEq
    subst ab
    have hcb : c = b0 :=
      gameRecurrenceModel.fixed_q_injective
        (Nat.le_of_lt hcac) (Nat.le_of_lt hb0ab)
        (hacValue.trans habValue.symm)
    exact hcNe hcb
  exact ⟨ac, ab, hcac, hacs, hacValue,
    hb0ab, habs, habValue, hacab⟩

/-- The third-dip band-hit atom is absent throughout the entire corridor
`ell < delta+11`; in particular its slack is at least twelve. -/
theorem gameF_no_nonmax_eventE_third_dip_band_hit_below_env_corridor
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hcorridor :
      s - (2 * s - gameF (s + 1) (s + 1)) - 4 <
        (2 * s - gameF (s + 1) (s + 1)) + 11) :
    Not (EventEThirdDipBandHitCompressedCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) := by
  intro hhit
  have hcert := gameF_nonmax_eventE_third_dip_band_hit_left_history
    hU hres hcross hhit
  exact (Nat.not_lt_of_ge hcert.2.2.1) hcorridor

theorem gameF_nonmax_eventE_third_dip_band_hit_slack_twelve
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hhit : EventEThirdDipBandHitCompressedCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    12 <= s - (2 * s - gameF (s + 1) (s + 1)) - 4 := by
  have hcert := gameF_nonmax_eventE_third_dip_band_hit_left_history
    hU hres hcross hhit
  have hdeltaPos :
      1 <= 2 * s - gameF (s + 1) (s + 1) := hres.2.1.1
  have hbase :
      12 <= (2 * s - gameF (s + 1) (s + 1)) + 11 := by omega
  exact Nat.le_trans hbase hcert.2.2.1

/-- Pointwise LEFT-HISTORY audit for every named higher packet column in
the three-prehost staircase.  The first two clauses concern `z+1,z` on
row `s`; the third concerns the named `z` host on row `s+1`. -/
def EventEThirdDipEveryLeftColumnHistoryCertificate
    (s delta z c b0 : Nat) : Prop :=
  exists g r1 r2 bz,
    g ∈ EventEThirdMissingBandSlots s delta c b0 /\
    r1 < s + 1 /\ r2 < s + 2 /\ bz < s + 1 /\
    gameF s g = z - 1 /\
    gameF (s + 1) r1 = z - 1 /\
    gameF (s + 2) r2 = z - 1 /\
    gameF (s + 1) bz = z /\
    (g < c \/ exists a, c < a /\ a < s /\ gameF a c = z - 1) /\
    (g < b0 \/ exists a, b0 < a /\ a < s /\ gameF a b0 = z - 1) /\
    (r1 < bz \/
      exists a, bz < a /\ a < s + 1 /\ gameF a bz = z - 1)

theorem gameF_nonmax_eventE_third_dip_every_left_column_history
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hhit : EventEThirdDipBandHitCompressedCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventEThirdDipEveryLeftColumnHistoryCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  classical
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventEThirdDipBandHitCompressedCertificate
    s delta z c b0 at hhit
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\ _ at hresData
  have hInv := hresData.2.1
  rcases hInv with
    ⟨_deltaPos, _deltaUpper, _hsum, _hzDiag,
      _ci, _bi, bz, _dc, _d0, _d1,
      _hcI, _hbI, hbz, _hcNeI, _hbNeI,
      _hSuccI, _hBaseI, hHostZ, _rest⟩
  have hhitData := hhit
  rcases hhitData with
    ⟨_hpen, _hstair, _hlast, _hweight, _hfour,
      g, r1, r2, hgMissing, hr1, hr2,
      hgValue, hhost1, hhost2, _hgr1, _hr1r2, _hgr2⟩
  have hgTriple : g ∈ EventETriplePrefixBandSlots s delta c b0 :=
    (List.mem_filter.mp hgMissing).1
  have hgSurv : g ∈ EventESurvivingBandSlots s delta c b0 :=
    (List.mem_filter.mp hgTriple).1
  have hgSlots : g ∈ EventEDefectBandSlots s delta c b0 :=
    (List.mem_filter.mp hgSurv).1
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, hSucc, hBase,
      _slotsNodup, _slotsLen, hslotsProps, _weak⟩
  have hgLt : g < s := (hslotsProps g hgSlots).1
  have hstair := hhit.2.1
  have hdiag3 : gameF (s + 3) (s + 3) = z - 1 :=
    hstair.2.2.2.2.1
  have hpHigh : s + 1 < z - 1 := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    omega
  have hzPos : 0 < z := by
    have hpredPos : 0 < z - 1 :=
      Nat.lt_trans (Nat.zero_lt_succ s) hpHigh
    exact Nat.lt_of_lt_of_le hpredPos (Nat.sub_le z 1)
  have hzPred : z - 1 < z := r55_pred_lt_self hzPos
  have hnotPastS : forall a, a < s -> gameF a a ≠ z - 1 := by
    intro a ha hEq
    have haEq := diagonal_injective gameRecurrenceModel
      (hEq.trans hdiag3.symm)
    omega
  have hnotPastS1 : forall a, a < s + 1 -> gameF a a ≠ z - 1 := by
    intro a ha hEq
    have haEq := diagonal_injective gameRecurrenceModel
      (hEq.trans hdiag3.symm)
    omega
  have hcOrder := higher_column_right_or_left_history
    gameRecurrenceModel
    (t := s) (v := z - 1) (c := g) (b := c)
    (Nat.le_of_lt hgLt) (by omega) hgValue
    (by change z - 1 < gameF s c; rw [hSucc]; omega) hnotPastS
  have hb0Order := higher_column_right_or_left_history
    gameRecurrenceModel
    (t := s) (v := z - 1) (c := g) (b := b0)
    (Nat.le_of_lt hgLt) (by omega) hgValue
    (by change z - 1 < gameF s b0; rw [hBase]; omega) hnotPastS
  have hbzOrder := higher_column_right_or_left_history
    gameRecurrenceModel
    (t := s + 1) (v := z - 1) (c := r1) (b := bz)
    (Nat.le_of_lt hr1) hpHigh hhost1
    (by change z - 1 < gameF (s + 1) bz; rw [hHostZ]; exact hzPred)
    hnotPastS1
  exact ⟨g, r1, r2, bz, hgMissing, hr1, hr2, hbz,
    hgValue, hhost1, hhost2, hHostZ, hcOrder, hb0Order, hbzOrder⟩

#print axioms left_history_of_higher_left_column
#print axioms higher_column_right_or_left_history
#print axioms gameF_nonmax_eventE_third_dip_band_hit_left_history
#print axioms gameF_no_nonmax_eventE_third_dip_band_hit_below_env_corridor
#print axioms gameF_nonmax_eventE_third_dip_band_hit_slack_twelve
#print axioms gameF_nonmax_eventE_third_dip_every_left_column_history

end ChompLean
