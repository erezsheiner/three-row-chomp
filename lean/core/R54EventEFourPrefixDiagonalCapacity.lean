import R54EventEFourPrefixFifthEdgeFreeze
import R54NonmaxEventEQuietStrictOwnerReduction

set_option autoImplicit false

namespace ChompLean

/-!
R54: a genuinely new capacity bound for the four-prefix packet.

Put `ell = s-delta-4`, so the Event-E identities give

  `z = s+3+ell`  and  `1 <= ell`.

Every low four-prefix value (`p <= s+3`) has already completed a row start.
The margin hypothesis places all `s` previous diagonal values in `[1,z)`;
these diagonal values are distinct and disjoint from the low row starts.
Hence there are at most `ell+2` low values.  The high values lie in the
literal interval `[s+4,z)`, which has only `ell-1` places.  Therefore

  `|Q4| <= 2*ell+1`.

Combining this with the strict shared-owner lower bound `+9` gives the new
structural restriction `s <= 6*ell+1`.
-/

noncomputable def EventELowFourPrefixBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventEFourPrefixBandSlots s delta c b0).filter (fun g =>
    decide (gameF s g <= s + 3))

noncomputable def EventEHighFourPrefixBandSlots
    (s delta c b0 : Nat) : List Nat :=
  (EventEFourPrefixBandSlots s delta c b0).filter (fun g =>
    decide (s + 3 < gameF s g))

def EventEFourPrefixDiagonalCapacityCertificate
    (s delta z c b0 : Nat) : Prop :=
  let ell := s - delta - 4
  1 <= ell ∧
  z = s + 3 + ell ∧
  (EventEFourPrefixBandSlots s delta c b0).length =
    (EventELowFourPrefixBandSlots s delta c b0).length +
      (EventEHighFourPrefixBandSlots s delta c b0).length ∧
  (EventELowFourPrefixBandSlots s delta c b0).length <= ell + 2 ∧
  (EventEHighFourPrefixBandSlots s delta c b0).length + 1 <= ell ∧
  (EventEFourPrefixBandSlots s delta c b0).length <= 2 * ell + 1

private theorem r54d_nodup_map_of_injective_on
    (f : Nat -> Nat) (xs : List Nat)
    (hxs : xs.Nodup)
    (hinj : ∀ x, x ∈ xs -> ∀ y, y ∈ xs ->
      f x = f y -> x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      change (f a :: as.map f).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hay⟩
        have hay' : a = y :=
          hinj a (by simp) y (by simp [hy]) hay.symm
        subst y
        exact hxs.1 hy
      · apply ih hxs.2
        intro x hx y hy hxy
        exact hinj x (by simp [hx]) y (by simp [hy]) hxy

/-- The exact low/high capacity theorem.  Notice that it uses the margin
part of Event E but not the behavior of the fourth diagonal edge. -/
theorem gameF_nonmax_eventE_four_prefix_diagonal_capacity
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    EventEFourPrefixDiagonalCapacityCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0 := by
  classical
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  let ell := s - delta - 4
  change MarginEventECounterexample s ∧
      EventEDefectPacketInvariant s d delta z ∧
      delta + 5 <= s ∧
      ∃ c b0, EventECrossEdgeSurvivorCertificate s delta z c b0
    at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  rcases hres with ⟨hEvent, hInv, hnonmax, _hexists⟩
  rcases hEvent with ⟨_hdip0, hmargin, _hdip1⟩
  have hsum : d + delta = 2 * s := hInv.2.2.1
  have hzDiag : z + 1 = d := hInv.2.2.2.1
  have hellPos : 1 <= ell := by
    dsimp [ell]
    omega
  have hzExact : z = s + 3 + ell := by
    dsimp [ell]
    omega
  have hzWindow : s + 4 <= z := by omega

  let slots := EventEDefectBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let four := EventEFourPrefixBandSlots s delta c b0
  let low := EventELowFourPrefixBandSlots s delta c b0
  let high := EventEHighFourPrefixBandSlots s delta c b0
  let diagValues := (List.range s).map (fun i => gameF i i)
  let lowValues := low.map (fun g => gameF s g)
  let highValues := high.map (fun g => gameF s g)

  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hsurvivorsNodup : survivors.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have htripleNodup : triple.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hfourNodup : four.Nodup :=
    List.filter_sublist.nodup htripleNodup
  have hlowNodup : low.Nodup :=
    List.filter_sublist.nodup hfourNodup
  have hhighNodup : high.Nodup :=
    List.filter_sublist.nodup hfourNodup

  have hfourSlots : ∀ g, g ∈ four -> g ∈ slots := by
    intro g hg
    have hgTriple : g ∈ triple := (List.mem_filter.mp hg).1
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hgTriple).1
    exact (List.mem_filter.mp hgSurv).1
  have hlowFour : ∀ g, g ∈ low -> g ∈ four := by
    intro g hg
    exact (List.mem_filter.mp hg).1
  have hhighFour : ∀ g, g ∈ high -> g ∈ four := by
    intro g hg
    exact (List.mem_filter.mp hg).1

  have hdiagNodup : diagValues.Nodup := by
    apply r54d_nodup_map_of_injective_on
      (fun i => gameF i i) (List.range s) List.nodup_range
    intro i _hi j _hj hEq
    exact diagonal_injective gameRecurrenceModel hEq
  have hlowValuesNodup : lowValues.Nodup := by
    apply r54d_nodup_map_of_injective_on
      (fun g => gameF s g) low hlowNodup
    intro g hg k hk hEq
    have hgData := hslotsProps g (hfourSlots g (hlowFour g hg))
    have hkData := hslotsProps k (hfourSlots k (hlowFour k hk))
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hgData.1) (Nat.le_of_lt hkData.1) hEq
  have hhighValuesNodup : highValues.Nodup := by
    apply r54d_nodup_map_of_injective_on
      (fun g => gameF s g) high hhighNodup
    intro g hg k hk hEq
    have hgData := hslotsProps g (hfourSlots g (hhighFour g hg))
    have hkData := hslotsProps k (hfourSlots k (hhighFour k hk))
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hgData.1) (Nat.le_of_lt hkData.1) hEq

  have hPastBelow : ∀ i, i < s -> gameF i i < z := by
    intro i hi
    rcases hmargin with hs0 | ⟨j, hsj, hmarg⟩
    · omega
    · have hij : i <= j := by omega
      have hle := rmax_ge gameRecurrenceModel j i hij
      change gameF i i <= RMax gameRecurrenceModel j at hle
      change RMax gameRecurrenceModel j < z at hmarg
      omega

  have hlowCompleted : ∀ p, p ∈ lowValues ->
      ∃ r, r < p ∧ gameF p r = p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨g, hg, hgp⟩
    have hgFour := hlowFour g hg
    have hlowBound : gameF s g <= s + 3 := by
      have hfilter := (List.mem_filter.mp hg).2
      simpa [low, EventELowFourPrefixBandSlots] using hfilter
    have hnormal := gameF_eventE_four_prefix_value_rowstart_or_high
      hcross hgFour
    rcases hnormal with hstart | hhigh
    · rcases hstart with
        ⟨_p, r, hpEq, _hpBound, hr, hrowstart, _hstable⟩
      have hr' : r < p := by omega
      have hrowstart' : gameF p r = p := by
        rw [← hgp, ← hpEq]
        exact hrowstart
      exact ⟨r, hr', hrowstart'⟩
    · omega

  have hspeciesDisjoint : ∀ a, a ∈ diagValues ->
      ∀ p, p ∈ lowValues -> a ≠ p := by
    intro a ha p hp hEq
    rcases List.mem_map.mp ha with ⟨i, _hi, hiValue⟩
    rcases hlowCompleted p hp with ⟨r, hrp, hstart⟩
    exact disjoint_D_S gameRecurrenceModel
      ⟨i, hiValue.trans hEq⟩ ⟨r, hrp, hstart⟩
  have hunionNodup : (diagValues ++ lowValues).Nodup :=
    List.nodup_append.mpr
      ⟨hdiagNodup, hlowValuesNodup, hspeciesDisjoint⟩
  have hunionSub : diagValues ++ lowValues ⊆
      List.range' 1 (z - 1) := by
    intro v hv
    apply List.mem_range'_1.mpr
    rcases List.mem_append.mp hv with hvDiag | hvLow
    · rcases List.mem_map.mp hvDiag with ⟨i, hi, rfl⟩
      have hiS : i < s := List.mem_range.mp hi
      have hpos := gameRecurrenceModel.diagonal_gt i
      change i < gameF i i at hpos
      exact ⟨by omega, by have := hPastBelow i hiS; omega⟩
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgFour := hlowFour g hg
      have hgData := hslotsProps g (hfourSlots g hgFour)
      have hvPos : 0 < gameF s g := by
        simpa [EventELowerTransition] using hgData.2.2.2.1
      have hvBelow : gameF s g < z := by
        simpa [EventELowerTransition] using hgData.2.2.2.2.1
      exact ⟨by omega, by omega⟩
  have hunionCap := nodup_subset_length_le hunionNodup hunionSub
  have hlowCap : low.length <= ell + 2 := by
    have hdiagLen : diagValues.length = s := by simp [diagValues]
    have hlowLen : lowValues.length = low.length := by simp [lowValues]
    have hrangeLen : (List.range' 1 (z - 1)).length = z - 1 := by simp
    rw [List.length_append, hdiagLen, hlowLen, hrangeLen] at hunionCap
    omega

  have hhighValuesSub : highValues ⊆
      List.range' (s + 4) (z - (s + 4)) := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgFour := hhighFour g hg
    have hfilter := (List.mem_filter.mp hg).2
    have hvHigh : s + 4 <= gameF s g := by
      simpa [high, EventEHighFourPrefixBandSlots] using hfilter
    have hgData := hslotsProps g (hfourSlots g hgFour)
    have hvBelow : gameF s g < z := by
      simpa [EventELowerTransition] using hgData.2.2.2.2.1
    apply List.mem_range'_1.mpr
    constructor <;> omega
  have hhighIntervalCap :=
    nodup_subset_length_le hhighValuesNodup hhighValuesSub
  have hhighCap : high.length + 1 <= ell := by
    have hcap : high.length <= z - (s + 4) := by
      simpa [highValues] using hhighIntervalCap
    omega

  have hpartitionRaw := List.length_eq_countP_add_countP
    (fun g => decide (gameF s g <= s + 3)) (l := four)
  simp only [List.countP_eq_length_filter] at hpartitionRaw
  have hpartition : four.length = low.length + high.length := by
    simpa [low, high, EventELowFourPrefixBandSlots,
      EventEHighFourPrefixBandSlots] using hpartitionRaw
  have htotalCap : four.length <= 2 * ell + 1 := by
    omega
  have hresult : EventEFourPrefixDiagonalCapacityCertificate
      s delta z c b0 :=
    ⟨hellPos, hzExact, hpartition, hlowCap, hhighCap, htotalCap⟩
  simpa [delta, z, d] using hresult

/-- Strict `+9` owner packing and the diagonal/row-start capacity imply
that a nonmaximal quiet Event E must stay at least `(s-1)/6` away from the
maximal defect face. -/
theorem gameF_nonmax_eventE_strict_four_prefix_slack_bound
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hstrict : EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    let ell := s - delta - 4
    s <= 6 * ell + 1 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let ell := s - delta - 4
  have hcap := gameF_nonmax_eventE_four_prefix_diagonal_capacity
    (s := s) (c := c) (b0 := b0) hres hcross
  change EventEFourPrefixDiagonalCapacityCertificate
    s delta (d - 1) c b0 at hcap
  change EventENonDipStrictSharedOwnerCertificate
    s delta (d - 1) c b0 at hstrict
  have hQCap := hcap.2.2.2.2.2
  have hstrictBound := hstrict.2.2.2
  have hresData := hres.2
  have hsum : d + delta = 2 * s := hresData.1.2.2.1
  change (EventEFourPrefixBandSlots s delta c b0).length <=
      2 * ell + 1 at hQCap
  change 2 * delta + 9 <= s +
      2 * (EventEFourPrefixBandSlots s delta c b0).length at hstrictBound
  omega

/-- The entire next-to-maximal quiet layer is empty.  Capacity gives
`s <= 6*1+1 = 7`, while the strict absorbed-owner inequality already has
the form `2*N+9 <= s`, hence `9 <= s`. -/
theorem gameF_no_nonmax_eventE_next_to_max_nondip
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hstrict : EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hell : let delta := 2 * s - gameF (s + 1) (s + 1)
      s - delta - 4 = 1) : False := by
  dsimp only at hell
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let ell := s - delta - 4
  have hslack := gameF_nonmax_eventE_strict_four_prefix_slack_bound
    (s := s) (c := c) (b0 := b0) hres hcross hstrict
  change s <= 6 * ell + 1 at hslack
  change ell = 1 at hell
  have habsorbed := hstrict.2.2.1
  change 2 * ((EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length +
      (EventEThirdMissingBandSlots s delta c b0).length) + 9 <= s
    at habsorbed
  omega

/-- Equivalent reusable form of the previous closure: every strict quiet
nonmaximal branch has at least two units of slack beyond the maximal face.
Thus the old nonmaximal bound `delta+5 <= s` improves to `delta+6 <= s`. -/
theorem gameF_nonmax_eventE_nondip_strict_defect_gap
    {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hstrict : EventENonDipStrictSharedOwnerCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    let ell := s - delta - 4
    2 <= ell ∧ delta + 6 <= s := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let ell := s - delta - 4
  have hslack := gameF_nonmax_eventE_strict_four_prefix_slack_bound
    (s := s) (c := c) (b0 := b0) hres hcross hstrict
  change s <= 6 * ell + 1 at hslack
  have habsorbed := hstrict.2.2.1
  change 2 * ((EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length +
      (EventEThirdMissingBandSlots s delta c b0).length) + 9 <= s
    at habsorbed
  have hellTwo : 2 <= ell := by omega
  exact ⟨hellTwo, by omega⟩

#print axioms gameF_nonmax_eventE_four_prefix_diagonal_capacity
#print axioms gameF_nonmax_eventE_strict_four_prefix_slack_bound
#print axioms gameF_no_nonmax_eventE_next_to_max_nondip
#print axioms gameF_nonmax_eventE_nondip_strict_defect_gap

end ChompLean
