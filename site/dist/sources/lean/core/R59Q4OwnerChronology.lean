import R58Q4FirstLoss

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
R59: chronology and owner collapse for a named certified Q4 loss edge.

No minimality of that edge is asserted. The conclusions below retain the
displayed previous-row presence/current-row absence and UnitDip/residual
hypotheses.

The R58 loss classification is sharpened in two independent ways.

* In the exact-capture arm, UnitDip gives a one-sided Lipschitz bound for
  the diagonal.  Since the Event-E diagonal at `s+3` is already above `z`,
  reaching the predecessor value `p+1` at `t-1` costs at least `z-p`
  rows.  In particular `t=s+4` is impossible.
* In the past-owner arm, the comparison `p<d(t)` is retained rather than
  discarded.  The no-recross barrier then eliminates every future owner
  below `z`, including both exact capture and the R58 late-owner arm.
  The only surviving chronology is an early owner, sharply localized by
  the defect-band and diagonal source-capacity bounds.
-/

/-- UnitDip is a one-sided Lipschitz condition on the diagonal: looking
backwards by `b-a` rows can increase the diagonal by at most `b-a`. -/
theorem unitDip_diagonal_reverse_lipschitz
    (M : RecurrenceModel) (hU : UnitDip M) :
    forall {a b : Nat}, a <= b ->
      M.f a a <= M.f b b + (b - a) := by
  intro a b hab
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  have hmain : forall n : Nat,
      M.f a a <= M.f (a + n) (a + n) + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep :
            M.f (a + n) (a + n) <=
              M.f (a + n + 1) (a + n + 1) + 1 := by
          by_cases hdip :
              M.f (a + n + 1) (a + n + 1) <
                M.f (a + n) (a + n)
          · have hu := hU (a + n) (by
              simpa [Nat.add_assoc] using hdip)
            simpa [Nat.add_assoc] using (show
              M.f (a + n) (a + n) <=
                M.f (a + n + 1) (a + n + 1) + 1 by omega)
          · omega
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (show M.f a a <=
              M.f (a + n + 1) (a + n + 1) + (n + 1) by omega)
  have h := hmain n
  simpa using h

/-- Once an injective UnitDip diagonal has left a value `z` upwards, it
can never return to `z` or cross below it.  Any downward crossing would
have to land on `z`, contradicting diagonal injectivity. -/
theorem unitDip_diagonal_no_recross_above
    (M : RecurrenceModel) (hU : UnitDip M)
    {a b z : Nat}
    (ha : M.f a a = z)
    (habove : z < M.f (a + 1) (a + 1))
    (hb : a + 1 <= b) :
    z < M.f b b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hmain : forall n : Nat,
      z < M.f (a + 1 + n) (a + 1 + n) := by
    intro n
    induction n with
    | zero => simpa using habove
    | succ n ih =>
        let q := a + 1 + n
        have ihq : z < M.f q q := by simpa [q] using ih
        have hnext : z < M.f (q + 1) (q + 1) := by
          by_cases hdip : M.f (q + 1) (q + 1) < M.f q q
          · have hu := hU q hdip
            by_cases hle : M.f (q + 1) (q + 1) <= z
            · have heq : M.f (q + 1) (q + 1) = z := by omega
              have hdiagEq : M.f (q + 1) (q + 1) = M.f a a :=
                heq.trans ha.symm
              have hidx := diagonal_injective M hdiagEq
              dsimp [q] at hidx
              omega
            · omega
          · omega
        simpa [q, Nat.add_assoc] using hnext
  exact hmain n

/-- Event-E specialization of the no-recross barrier.  No later row can
emit a diagonal value below `z`. -/
theorem gameF_eventE_post_nondip_diagonal_above_z
    (hU : UnitDip gameRecurrenceModel)
    {s z u : Nat}
    (hdiag2 : gameF (s + 2) (s + 2) = z)
    (hdiag3 : z < gameF (s + 3) (s + 3))
    (hu : s + 3 <= u) :
    z < gameF u u := by
  apply unitDip_diagonal_no_recross_above
    gameRecurrenceModel hU hdiag2
  · simpa [Nat.add_assoc] using hdiag3
  · omega

/-- Hence neither exact capture nor any future diagonal owner of a value
strictly below `z` can occur after the Event-E non-dip edge. -/
theorem gameF_eventE_future_below_z_owner_impossible
    (hU : UnitDip gameRecurrenceModel)
    {s z u p : Nat}
    (hdiag2 : gameF (s + 2) (s + 2) = z)
    (hdiag3 : z < gameF (s + 3) (s + 3))
    (hu : s + 3 <= u) (hpz : p < z) :
    gameF u u ≠ p := by
  have hbar := gameF_eventE_post_nondip_diagonal_above_z
    hU hdiag2 hdiag3 hu
  omega

/-- Exact capture after an already-above-`z` row has a quantitative
descent cost. -/
theorem unitDip_exact_capture_descent_budget
    (M : RecurrenceModel) (hU : UnitDip M)
    {s z p t : Nat}
    (ht : s + 4 <= t)
    (hpz : p < z)
    (hdiag3 : z < M.f (s + 3) (s + 3))
    (hpred : M.f (t - 1) (t - 1) = p + 1) :
    s + 5 <= t /\ s + z + 4 <= p + t := by
  have hindex : s + 3 <= t - 1 := by omega
  have hlip := unitDip_diagonal_reverse_lipschitz M hU hindex
  rw [hpred] at hlip
  constructor <;> omega

/-- If capture occurs at the earliest row allowed by the descent budget,
then every inequality is tight: the packet value is exactly `z-1`, the
row-`s+3` diagonal is `z+1`, and the intervening diagonal is `z`. -/
theorem unitDip_exact_capture_earliest_row_rigidity
    (M : RecurrenceModel) (hU : UnitDip M)
    {s z p t : Nat}
    (hpz : p < z)
    (hdiag3 : z < M.f (s + 3) (s + 3))
    (hpred : M.f (t - 1) (t - 1) = p + 1)
    (htExact : t = s + 5) :
    p + 1 = z /\
      M.f (s + 3) (s + 3) = z + 1 /\
      M.f (s + 4) (s + 4) = z := by
  subst t
  have hpred4 : M.f (s + 4) (s + 4) = p + 1 := by
    simpa using hpred
  have hdip : M.f (s + 4) (s + 4) < M.f (s + 3) (s + 3) := by
    omega
  have hu := hU (s + 3) (by
    simpa [Nat.add_assoc] using hdip)
  have hu' :
      M.f (s + 4) (s + 4) + 1 = M.f (s + 3) (s + 3) := by
    simpa [Nat.add_assoc] using hu
  exact ⟨by omega, by omega, by omega⟩

/-- Consequently exact capture either occurs no earlier than `s+6`, or
the unique earliest pattern above is forced. -/
theorem unitDip_exact_capture_later_or_rigid_earliest
    (M : RecurrenceModel) (hU : UnitDip M)
    {s z p t : Nat}
    (ht : s + 4 <= t)
    (hpz : p < z)
    (hdiag3 : z < M.f (s + 3) (s + 3))
    (hpred : M.f (t - 1) (t - 1) = p + 1) :
    s + 6 <= t \/
      (t = s + 5 /\ p + 1 = z /\
        M.f (s + 3) (s + 3) = z + 1 /\
        M.f (s + 4) (s + 4) = z) := by
  have hbudget := unitDip_exact_capture_descent_budget
    M hU ht hpz hdiag3 hpred
  by_cases hlater : s + 6 <= t
  · exact Or.inl hlater
  · right
    have htExact : t = s + 5 := by omega
    have hrigid := unitDip_exact_capture_earliest_row_rigidity
      M hU hpz hdiag3 hpred htExact
    exact ⟨htExact, hrigid.1, hrigid.2.1, hrigid.2.2⟩

/-- A value hosted in row `q` before its future diagonal owner is a
future-diagonal prehost loss. -/
theorem gameF_future_diagonal_host_is_prehost_loss
    {q r a p : Nat}
    (hrq : r < q) (hqa : q < a)
    (hhost : gameF q r = p)
    (howner : gameF a a = p) :
    FutureDiagonalPrehostLoss gameRecurrenceModel q a p := by
  have hC : C gameF q q p := ⟨r, hrq, hhost⟩
  have habsent : Not (B gameF a a p) := by
    rw [← howner]
    exact (recurrence_diagonal_exact_mex gameRecurrenceModel a).2.1
  exact ⟨hqa, howner, hC, habsent⟩

/-- R58 with the strict inequality in the past-owner arm retained. -/
theorem gameF_unitDip_prefix_loss_exact_capture_or_strict_left_echo
    (hU : UnitDip gameRecurrenceModel)
    {t p : Nat} (ht : 1 <= t)
    (hpresent : p ∈ StrictRowPrefixValues gameF (t - 1))
    (habsent : p ∉ StrictRowPrefixValues gameF t) :
    (gameF t t = p /\ gameF (t - 1) (t - 1) = p + 1) \/
      exists a b,
        p < gameF t t /\ b < a /\ a < t - 1 /\ b < t - 1 /\
        gameF a a = p /\ gameF (t - 1) b = p := by
  rcases mem_strictRowPrefixValues_iff_C.mp hpresent with
    ⟨b, hbt, hhost⟩
  have hpPos : 0 < p := by
    have hvalueGt := encoded_gt game_encodes (Nat.le_of_lt hbt)
    rw [hhost] at hvalueGt
    omega
  have hnotC : Not (C gameF t t p) := by
    intro hC
    exact habsent (mem_strictRowPrefixValues_iff_C.mpr hC)
  by_cases hdiagLe : gameF t t <= p
  · left
    have hpBand := gameF_strict_prefix_value_band hpresent
    have hdiagNe : gameF t t ≠ gameF (t - 1) (t - 1) := by
      intro hEq
      have hidx := diagonal_injective gameRecurrenceModel hEq
      omega
    have hdip : gameF t t < gameF (t - 1) (t - 1) := by
      omega
    have htStep : t - 1 + 1 = t := by omega
    have hunitRaw := hU (t - 1) (by
      rw [htStep]
      exact hdip)
    have hunit : gameF t t + 1 = gameF (t - 1) (t - 1) := by
      simpa [htStep] using hunitRaw
    omega
  · right
    have hpBelow : p < gameF t t := by omega
    have hpast : exists a, a < t /\ gameF a a = p := by
      by_cases hpast : exists a, a < t /\ gameF a a = p
      · exact hpast
      · exfalso
        apply hnotC
        apply recurrence_nonpast_below_diagonal_strict_prefix
          gameRecurrenceModel hpPos hpBelow
        simpa [PastDiagonalValueBefore, gameRecurrenceModel] using hpast
    rcases hpast with ⟨a, hat, howner⟩
    have haBefore : a < t - 1 := by
      have haLe : a <= t - 1 := by omega
      apply Nat.lt_of_le_of_ne haLe
      intro haEq
      have haEq' : a = t - 1 := by omega
      subst a
      have hcols : b = t - 1 :=
        gameRecurrenceModel.fixed_q_injective
          (Nat.le_of_lt hbt) (Nat.le_refl _)
          (hhost.trans howner.symm)
      omega
    have hleft : b < a :=
      gameF_past_diagonal_echo_strictly_left
        haBefore (Nat.le_of_lt hbt) (hhost.trans howner.symm)
    exact ⟨a, b, hpBelow, hleft, haBefore, hbt, howner, hhost⟩

/-- Full Q4 owner chronology under the actual R55 residual data.

The three arms are exact capture, an early past owner, and a late owner.
Exact capture carries the new descent budget.  An early owner lies in the
strict upper half forced by diagonal source capacity.  A late owner is a
future-diagonal prehost loss from row `s` and lies at least two rows before
the first-loss row. -/
theorem gameF_Q4_first_loss_R59_owner_trichotomy
    (hU : UnitDip gameRecurrenceModel)
    {s c b0 g t : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hstrict : EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hg : g ∈ EventEFourPrefixBandSlots
      s (2 * s - gameF (s + 1) (s + 1)) c b0)
    (htLower : s + 4 <= t)
    (htUpper : t <= gameF s g)
    (htz : t < gameF (s + 1) (s + 1) - 1)
    (hpresent : gameF s g ∈ StrictRowPrefixValues gameF (t - 1))
    (habsent : gameF s g ∉ StrictRowPrefixValues gameF t) :
    let p := gameF s g
    let z := gameF (s + 1) (s + 1) - 1
    t < z /\ p < z /\ p <= s + g + 1 /\
      ((gameF t t = p /\ gameF (t - 1) (t - 1) = p + 1 /\
        s + 5 <= t /\ s + z + 4 <= p + t /\
        s + z + 4 <= 2 * p /\
        FutureDiagonalPrehostLoss gameRecurrenceModel s t p) \/
      (exists a b,
        p < gameF t t /\ b < a /\ a < s /\ g < a /\
        b < t - 1 /\ s + 3 <= 2 * a /\
        gameF a a = p /\ gameF (t - 1) b = p) \/
      (exists a b,
        p < gameF t t /\ b < a /\ s + 4 <= a /\
        a + 2 <= t /\ t <= p /\ b < t - 1 /\
        gameF a a = p /\ gameF (t - 1) b = p /\
        FutureDiagonalPrehostLoss gameRecurrenceModel s a p)) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  let p := gameF s g
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipStrictSharedOwnerCertificate
    s delta z c b0 at hstrict
  change g ∈ EventEFourPrefixBandSlots s delta c b0 at hg
  change t <= p at htUpper
  change t < z at htz
  change p ∈ StrictRowPrefixValues gameF (t - 1) at hpresent
  change p ∉ StrictRowPrefixValues gameF t at habsent
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists ce be, EventECrossEdgeSurvivorCertificate
        s delta z ce be at hresData
  rcases hresData with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨hdip0, _hmargin, hdip1⟩
  have hzDiag1 : gameF (s + 1) (s + 1) = z + 1 := by
    have hz := hInv.2.2.2.1
    change z + 1 = d at hz
    omega
  have hunit0 := hU s hdip0
  change gameF (s + 1) (s + 1) + 1 = gameF s s at hunit0
  have hdiag0 : gameF s s = z + 2 := by omega
  have hunit1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hunit1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by omega
  have hnondip3 : Not
      (gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2)) :=
    hstrict.1.1.1
  have hdiag3Ne :
      gameF (s + 3) (s + 3) ≠ gameF (s + 2) (s + 2) := by
    intro hEq
    have hidx := diagonal_injective gameRecurrenceModel hEq
    omega
  have hdiag3 : z < gameF (s + 3) (s + 3) := by omega
  have hgTriple :
      g ∈ EventETriplePrefixBandSlots s delta c b0 :=
    (List.mem_filter.mp hg).1
  have hgSurvivor :
      g ∈ EventESurvivingBandSlots s delta c b0 :=
    (List.mem_filter.mp hgTriple).1
  have hgBand : g ∈ EventEDefectBandSlots s delta c b0 :=
    (List.mem_filter.mp hgSurvivor).1
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      _hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hgs : g < s := (hslotsProps g hgBand).1
  have hpz : p < z := by
    have htransition := (hslotsProps g hgBand).2.2.2
    simpa [p, EventELowerTransition] using htransition.2.1
  have hpSource : p <= s + g + 1 := by
    have hcap := high_cell_output_source_capacity
      gameRecurrenceModel (Nat.le_of_lt hgs) (by omega : s < p) rfl
    omega
  refine ⟨htz, hpz, hpSource, ?_⟩
  have htPos : 1 <= t := by omega
  rcases gameF_unitDip_prefix_loss_exact_capture_or_strict_left_echo
      hU htPos hpresent habsent with hcapture | heecho
  · left
    have hbudget := unitDip_exact_capture_descent_budget
      gameRecurrenceModel hU htLower hpz hdiag3 hcapture.2
    have hprehost :
        FutureDiagonalPrehostLoss gameRecurrenceModel s t p :=
      gameF_future_diagonal_host_is_prehost_loss
        hgs (by omega) rfl hcapture.1
    exact ⟨hcapture.1, hcapture.2, hbudget.1, hbudget.2,
      by omega, hprehost⟩
  · rcases heecho with
      ⟨a, b, hpBelow, hba, hat, hbt, howner, hhost⟩
    rcases gameF_packet_past_owner_interval
        hgs hpz hdiag0 hzDiag1 hdiag2 hdiag3 hat howner with
      hearly | hlate
    · right
      left
      have hcap := recurrence_diagonal_source_capacity
        gameRecurrenceModel a
      change gameF a a <= a + a + 1 at hcap
      rw [howner] at hcap
      exact ⟨a, b, hpBelow, hba, hearly.1, hearly.2, hbt,
        by omega, howner, hhost⟩
    · right
      right
      have hprehost :
          FutureDiagonalPrehostLoss gameRecurrenceModel s a p :=
        gameF_future_diagonal_host_is_prehost_loss
          hgs (by omega) rfl howner
      exact ⟨a, b, hpBelow, hba, hlate.1,
        by omega, htUpper, hbt, howner, hhost, hprehost⟩

/-- Final R59 collapse of the Q4 first-loss chronology.  The exact-capture
and late-owner arms of the preceding trichotomy are impossible: both would
put a future diagonal at the packet value `p<z`, while the no-recross
barrier keeps every diagonal from row `s+3` onward strictly above `z`.

Thus every Q4 loss has a genuinely early owner `a<s`.  Both the original
row-`s` host and the last pre-loss host lie left of `a`, they use distinct
columns, and diagonal source capacity gives `t <= 2*a+1`. -/
theorem gameF_Q4_first_loss_R59_early_owner_only
    (hU : UnitDip gameRecurrenceModel)
    {s c b0 g t : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hstrict : EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hg : g ∈ EventEFourPrefixBandSlots
      s (2 * s - gameF (s + 1) (s + 1)) c b0)
    (htLower : s + 4 <= t)
    (htUpper : t <= gameF s g)
    (htz : t < gameF (s + 1) (s + 1) - 1)
    (hpresent : gameF s g ∈ StrictRowPrefixValues gameF (t - 1))
    (habsent : gameF s g ∉ StrictRowPrefixValues gameF t) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    let p := gameF s g
    let z := gameF (s + 1) (s + 1) - 1
    t < z /\ p < z /\ p <= s + g + 1 /\
      s - delta - 2 <= g /\
      exists a b,
        p < gameF t t /\ b < a /\ a < s /\ g < a /\
        g ≠ b /\ b < t - 1 /\ t <= 2 * a + 1 /\
        s + 3 <= 2 * a /\
        gameF a a = p /\ gameF (t - 1) b = p := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  let p := gameF s g
  have htri := gameF_Q4_first_loss_R59_owner_trichotomy
    hU hres hcross hstrict hg htLower htUpper htz hpresent habsent
  change t < z /\ p < z /\ p <= s + g + 1 /\ _ at htri
  rcases htri with ⟨htz', hpz, hpSource, hchron⟩
  have hgData := hg
  change g ∈ EventEFourPrefixBandSlots s delta c b0 at hgData
  have hgTriple :
      g ∈ EventETriplePrefixBandSlots s delta c b0 :=
    (List.mem_filter.mp hgData).1
  have hgSurvivor :
      g ∈ EventESurvivingBandSlots s delta c b0 :=
    (List.mem_filter.mp hgTriple).1
  have hgBand : g ∈ EventEDefectBandSlots s delta c b0 :=
    (List.mem_filter.mp hgSurvivor).1
  have hgOuter := List.mem_of_mem_erase hgBand
  have hgInner := List.mem_of_mem_erase hgOuter
  have hgRange := List.mem_range'_1.mp hgInner
  have hgLower : s - delta - 2 <= g := hgRange.1
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\
      delta + 5 <= s /\
      exists ce be, EventECrossEdgeSurvivorCertificate
        s delta z ce be at hresData
  rcases hresData with ⟨hEvent, hInv, _hnonmax, _hexists⟩
  rcases hEvent with ⟨_hdip0, _hmargin, hdip1⟩
  have hzDiag1 : gameF (s + 1) (s + 1) = z + 1 := by
    have hz := hInv.2.2.2.1
    change z + 1 = d at hz
    omega
  have hunit1 := hU (s + 1) hdip1
  change gameF (s + 2) (s + 2) + 1 = d at hunit1
  have hdiag2 : gameF (s + 2) (s + 2) = z := by omega
  have hstrictData := hstrict
  change EventENonDipStrictSharedOwnerCertificate
    s delta z c b0 at hstrictData
  have hnondip3 : Not
      (gameF (s + 3) (s + 3) < gameF (s + 2) (s + 2)) :=
    hstrictData.1.1.1
  have hdiag3Ne :
      gameF (s + 3) (s + 3) ≠ gameF (s + 2) (s + 2) := by
    intro hEq
    have hidx := diagonal_injective gameRecurrenceModel hEq
    omega
  have hdiag3 : z < gameF (s + 3) (s + 3) := by omega
  refine ⟨htz', hpz, hpSource, hgLower, ?_⟩
  rcases hchron with hcapture | hearly | hlate
  · exact False.elim
      ((gameF_eventE_future_below_z_owner_impossible
        hU hdiag2 hdiag3 (by omega) hpz) hcapture.1)
  · rcases hearly with
      ⟨a, b, hpBelow, hba, has, hga, hbt,
        hhalf, howner, hhost⟩
    have hcap := recurrence_diagonal_source_capacity
      gameRecurrenceModel a
    change gameF a a <= a + a + 1 at hcap
    rw [howner] at hcap
    have hgb : g ≠ b := by
      intro hEq
      subst b
      exact encoding_same_lower_no_repeat game_encodes
        (s := g) (t₁ := s) (t₂ := t - 1) (p := p)
        (Nat.lt_trans hga has) (by omega) (by omega)
        rfl hhost
    exact ⟨a, b, hpBelow, hba, has, hga, hgb, hbt,
      by omega, hhalf, howner, hhost⟩
  · rcases hlate with
      ⟨a, _b, _hpBelow, _hba, haLower, _hat,
        _htp, _hbt, howner, _hhost, _hprehost⟩
    exact False.elim
      ((gameF_eventE_future_below_z_owner_impossible
        hU hdiag2 hdiag3 (by omega) hpz) howner)

#print axioms unitDip_diagonal_reverse_lipschitz
#print axioms unitDip_diagonal_no_recross_above
#print axioms gameF_eventE_post_nondip_diagonal_above_z
#print axioms gameF_eventE_future_below_z_owner_impossible
#print axioms unitDip_exact_capture_descent_budget
#print axioms unitDip_exact_capture_earliest_row_rigidity
#print axioms unitDip_exact_capture_later_or_rigid_earliest
#print axioms gameF_future_diagonal_host_is_prehost_loss
#print axioms gameF_unitDip_prefix_loss_exact_capture_or_strict_left_echo
#print axioms gameF_Q4_first_loss_R59_owner_trichotomy
#print axioms gameF_Q4_first_loss_R59_early_owner_only

end ChompLean
