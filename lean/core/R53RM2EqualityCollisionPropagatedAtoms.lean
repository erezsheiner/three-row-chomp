import R52RM2SaturatedPropagationResidual
import R53ConsecutiveDipStrictCrossEdgePacking
import R53EventEMaximalBackfillOwnerEquality
import R53NonmaxEventENonDipSharedOwnerSaturation

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R53: replace the saturated R52 certificates by explicit equality and
propagation atoms.

At maximal defect, the diagonal species and the triple-prefix row-start
species have exactly the same cardinality as the whole interval
[1,s+3]. Their inclusion is therefore an exact permutation. Applying
this equality to the distinguished value s+2 gives one collision atom:
s+2 is either an early diagonal value or the unique R52 high survivor,
which carries the seven predecessor configurations.

In the nonmaximal branch, the third-edge trichotomy is split once more.
The no-third-dip packet is either below its explicit 3/4 threshold or
contains a concrete four-prefix survivor. Thus only four finite propagated
atoms remain.
-/

private theorem r53_perm_of_nodup_subset_length_le
    {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : xs ⊆ ys)
    (hlen : ys.length <= xs.length) :
    xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact List.Perm.nil
      | cons y ys => simp at hlen
  | cons a xs ih =>
      have hndParts := List.nodup_cons.mp hnd
      have ha : a ∈ ys := hsub (by simp)
      have hsubErase : xs ⊆ ys.erase a := by
        intro x hx
        have hxy : x ∈ ys := hsub (by simp [hx])
        have hxa : x ≠ a := by
          intro hxa
          apply hndParts.1
          simpa [hxa] using hx
        exact (List.mem_erase_of_ne hxa).mpr hxy
      have hlenErase : (ys.erase a).length <= xs.length := by
        have herase := List.length_erase_of_mem ha
        simp only [List.length_cons] at hlen
        omega
      have htail : xs.Perm (ys.erase a) :=
        ih hndParts.2 hsubErase hlenErase
      exact (htail.cons a).trans (List.perm_cons_erase ha).symm

private theorem r53_nodup_map_of_injective_on
    (f : Nat -> Nat) (xs : List Nat)
    (hxs : xs.Nodup)
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
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

/-- Exact equality case behind the maximal diagonal squeeze. -/
def EventEMaximalEqualitySaturationCertificate
    (s delta z c b0 : Nat) : Prop :=
  let horizon := (s + 3) / 2 + 1
  let diagValues :=
    ((List.range horizon).map (fun i => gameF i i)) ++ [z]
  let startValues :=
    (EventETriplePrefixBandSlots s delta c b0).map
      (fun g => gameF s g)
  EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z c b0 /\
  (EventETriplePrefixBandSlots s delta c b0).length = s / 2 /\
  (diagValues ++ startValues).Perm (List.range' 1 (s + 3))

/-- Maximal equality saturation upgrades the cardinal squeeze to a complete
species permutation of [1,s+3]. -/
theorem gameF_margin_eventE_maximal_equality_saturation
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    delta + 4 = s ->
      exists c b0,
        EventEMaximalEqualitySaturationCertificate s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change delta + 4 = s ->
    exists c b0,
      EventEMaximalEqualitySaturationCertificate s delta z c b0
  intro hmax
  have hExact := gameF_margin_eventE_maximal_survivor_count_exact
    hU hdip hmargin hnextDip hmax
  change exists c b0,
    EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z c b0 /\
    (EventETriplePrefixBandSlots s delta c b0).length = s / 2
    at hExact
  rcases hExact with ⟨c, b0, hSqueeze, hTripleExact⟩

  let slots := EventEDefectBandSlots s delta c b0
  let triple := EventETriplePrefixBandSlots s delta c b0
  let horizon := (s + 3) / 2 + 1
  let earlyDiag := (List.range horizon).map (fun i => gameF i i)
  let diagValues := earlyDiag ++ [z]
  let startValues := triple.map (fun g => gameF s g)

  have hcross := hSqueeze.1
  have hzExact := hSqueeze.2.1
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, _hslotsLen, hslotsProps, _hweak⟩
  have hsurvivorsNodup :
      (EventESurvivingBandSlots s delta c b0).Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have htripleNodup : triple.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hstartValuesNodup : startValues.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) triple htripleNodup
    intro g hg k hk hEq
    have hgSurv := (List.mem_filter.mp hg).1
    have hkSurv := (List.mem_filter.mp hk).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsProps g hgSlots).1)
      (Nat.le_of_lt (hslotsProps k hkSlots).1) hEq

  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  have hdeltaSum := hInv.2.2.1
  have hzSucc := hInv.2.2.2.1
  have hunitNext := hU (s + 1) hnextDip
  change gameF (s + 2) (s + 2) + 1 = d at hunitNext
  have hEmit : gameF (s + 2) (s + 2) = z := by omega

  have hearlyNodup : earlyDiag.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun i => gameF i i) (List.range horizon) List.nodup_range
    intro i hi j hj hEq
    exact diagonal_injective gameRecurrenceModel hEq
  have hzNotEarly : z ∉ earlyDiag := by
    intro hzMem
    rcases List.mem_map.mp hzMem with ⟨i, hi, hiValue⟩
    have hiRange : i < horizon := List.mem_range.mp hi
    have hiEq : i = s + 2 :=
      diagonal_injective gameRecurrenceModel
        (hiValue.trans hEmit.symm)
    dsimp [horizon] at hiRange
    omega
  have hdiagValuesNodup : diagValues.Nodup := by
    exact List.nodup_append.mpr
      ⟨hearlyNodup, by simp, by
        intro a ha b hb hEq
        simp only [List.mem_singleton] at hb
        have haZ : a = z := hEq.trans hb
        rw [haZ] at ha
        exact hzNotEarly ha⟩

  have hcompleted : forall p, p ∈ startValues ->
      exists r, r < p /\ gameF p r = p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨g, hgTriple, rfl⟩
    have hgSurv :
        g ∈ EventESurvivingBandSlots s delta c b0 :=
      (List.mem_filter.mp hgTriple).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hmem1 : gameF s g ∈
        StrictRowPrefixValues gameF (s + 1) := by
      simpa [EventESurvivingBandSlots] using
        (List.mem_filter.mp hgSurv).2
    have hmem2 : gameF s g ∈
        StrictRowPrefixValues gameF (s + 2) := by
      simpa [triple, EventETriplePrefixBandSlots] using
        (List.mem_filter.mp hgTriple).2
    have htransition := (hslotsProps g hgSlots).2.2.2
    have hpz : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    rcases gameF_three_prefix_value_has_completed_rowstart
        (hslotsProps g hgSlots).1 rfl
        (mem_strictRowPrefixValues_iff_C.mp hmem1)
        (mem_strictRowPrefixValues_iff_C.mp hmem2)
        (by omega) with ⟨r, hr, hstart, _hregime⟩
    exact ⟨r, hr, hstart⟩
  have hspeciesDisjoint : forall a, a ∈ diagValues ->
      forall p, p ∈ startValues -> a ≠ p := by
    intro a ha p hp hEq
    rcases hcompleted p hp with ⟨r, hrp, hstart⟩
    rcases List.mem_append.mp ha with haEarly | haZ
    · rcases List.mem_map.mp haEarly with ⟨i, _hi, hiValue⟩
      exact disjoint_D_S gameRecurrenceModel
        ⟨i, hiValue.trans hEq⟩ ⟨r, hrp, hstart⟩
    · simp only [List.mem_singleton] at haZ
      have hzP : z = p := haZ.symm.trans hEq
      exact disjoint_D_S gameRecurrenceModel
        ⟨s + 2, hEmit.trans hzP⟩ ⟨r, hrp, hstart⟩
  have hunionNodup : (diagValues ++ startValues).Nodup :=
    List.nodup_append.mpr
      ⟨hdiagValuesNodup, hstartValuesNodup, hspeciesDisjoint⟩

  have hunionSub : diagValues ++ startValues ⊆
      List.range' 1 (s + 3) := by
    intro v hv
    rcases List.mem_append.mp hv with hvDiag | hvStart
    · rcases List.mem_append.mp hvDiag with hvEarly | hvZ
      · rcases List.mem_map.mp hvEarly with ⟨i, hi, rfl⟩
        have hiRange : i < horizon := List.mem_range.mp hi
        have hpos := gameRecurrenceModel.diagonal_gt i
        have hcap := recurrence_diagonal_source_capacity
          gameRecurrenceModel i
        change i < gameF i i at hpos
        change gameF i i <= i + i + 1 at hcap
        have hneTop : gameF i i ≠ d := by
          intro hEq
          have hiEq : i = s + 1 :=
            diagonal_injective gameRecurrenceModel hEq
          dsimp [horizon] at hiRange
          omega
        apply List.mem_range'_1.mpr
        dsimp [horizon] at hiRange
        constructor <;> omega
      · simp only [List.mem_singleton] at hvZ
        subst v
        apply List.mem_range'_1.mpr
        constructor <;> omega
    · rcases List.mem_map.mp hvStart with ⟨g, hgTriple, rfl⟩
      have hgSurv := (List.mem_filter.mp hgTriple).1
      have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
      have htransition := (hslotsProps g hgSlots).2.2.2
      have hpPos : 0 < gameF s g := by
        simpa [EventELowerTransition] using htransition.1
      have hpz : gameF s g < z := by
        simpa [EventELowerTransition] using htransition.2.1
      apply List.mem_range'_1.mpr
      constructor <;> omega

  have hlen : (List.range' 1 (s + 3)).length <=
      (diagValues ++ startValues).length := by
    have hdiagLen : diagValues.length = horizon + 1 := by
      simp [diagValues, earlyDiag]
    have hstartLen : startValues.length = triple.length := by
      simp [startValues]
    have hrangeLen : (List.range' 1 (s + 3)).length = s + 3 := by
      simp
    rw [List.length_append, hdiagLen, hstartLen, hrangeLen]
    change triple.length = s / 2 at hTripleExact
    dsimp [horizon]
    omega
  have hperm : (diagValues ++ startValues).Perm
      (List.range' 1 (s + 3)) :=
    r53_perm_of_nodup_subset_length_le hunionNodup hunionSub hlen
  refine ⟨c, b0, ?_⟩
  dsimp only [EventEMaximalEqualitySaturationCertificate]
  change EventEMaximalSurvivorDiagonalSqueezeCertificate
      s delta z c b0 /\
    triple.length = s / 2 /\
    (diagValues ++ startValues).Perm (List.range' 1 (s + 3))
  exact ⟨hSqueeze, hTripleExact, hperm⟩

/-- The equality-saturation collision at value s+2: it is either consumed
by the early diagonal species, or by the unique high row-start atom. -/
def EventEMaximalEqualityCollisionAtom
    (s delta z c b0 : Nat) : Prop :=
  EventEMaximalEqualitySaturationCertificate s delta z c b0 /\
  let horizon := (s + 3) / 2 + 1
  (exists i, i < horizon /\ gameF i i = s + 2) \/
  exists g bz b1 b2,
    g ∈ EventEHighTripleBandSlots s delta c b0 /\
    bz < s + 1 /\ b1 < s + 1 /\ b2 < s + 2 /\
    gameF (s + 1) bz = z /\
    gameF (s + 1) b1 = gameF s g /\
    gameF (s + 2) b2 = gameF s g /\
    MaximalEventEHighSurvivorAtom s c b0 bz g b1 b2 b2 /\
    MaximalEventEHighSevenConfiguration s c b0 bz b1 b2

/-- Equality saturation at maximal defect forces the explicit collision
atom at the distinguished value s+2. -/
theorem gameF_margin_eventE_maximal_equality_collision_atom
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    delta + 4 = s ->
      exists c b0,
        EventEMaximalEqualityCollisionAtom s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change delta + 4 = s ->
    exists c b0,
      EventEMaximalEqualityCollisionAtom s delta z c b0
  intro hmax
  have hSat := gameF_margin_eventE_maximal_equality_saturation
    hU hdip hmargin hnextDip hmax
  change exists c b0,
    EventEMaximalEqualitySaturationCertificate s delta z c b0 at hSat
  rcases hSat with ⟨c, b0, hSat⟩
  have hSeven := gameF_margin_eventE_maximal_R52_bulk_seven_atom_residual
    hU hdip hmargin hnextDip hmax
  change exists c' b0',
    EventEMaximalBulkSevenAtomCertificate s delta z c' b0' at hSeven
  rcases hSeven with ⟨c', b0', hSeven⟩

  have hbaseSat := hSat.1.1.1.1.1
  have hbaseSeven := hSeven.1.1.1.1.1
  rcases hbaseSat with
    ⟨hc, hb0, _hne, hSucc, hBase, _hSatRest⟩
  rcases hbaseSeven with
    ⟨hc', hb0', _hne', hSucc', hBase', _hSevenRest⟩
  have hcEq : c = c' :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hc) (Nat.le_of_lt hc')
      (hSucc.trans hSucc'.symm)
  have hbEq : b0 = b0' :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hb0) (Nat.le_of_lt hb0')
      (hBase.trans hBase'.symm)
  subst c'
  subst b0'

  let horizon := (s + 3) / 2 + 1
  let earlyDiag := (List.range horizon).map (fun i => gameF i i)
  let diagValues := earlyDiag ++ [z]
  let triple := EventETriplePrefixBandSlots s delta c b0
  let startValues := triple.map (fun g => gameF s g)
  change EventEMaximalSurvivorDiagonalSqueezeCertificate
      s delta z c b0 /\
    triple.length = s / 2 /\
    (diagValues ++ startValues).Perm (List.range' 1 (s + 3))
    at hSat
  have hSatFull := hSat
  rcases hSat with ⟨hSqueeze, _hTripleExact, hperm⟩
  have hzExact := hSqueeze.2.1
  dsimp only [EventEMaximalBulkSevenAtomCertificate] at hSeven
  let next := EventENextOwnerTripleBandSlots s delta c b0
  let high := EventEHighTripleBandSlots s delta c b0
  change EventEMaximalBulkFrozenCarryCertificate s delta z c b0 /\
    next.length <= 1 /\ high.length <= 1 /\
    (forall g, g ∈ triple ->
      g ∈ EventEFrozenTripleBandSlots s delta c b0 \/
      g ∈ next \/ g ∈ high) /\
    (forall g, g ∈ next ->
      EventENextOwnerGapTerminal s z g (gameF s g)) /\
    (forall g, g ∈ high ->
      exists bz b1 b2,
        bz < s + 1 /\ b1 < s + 1 /\ b2 < s + 2 /\
        gameF (s + 1) bz = z /\
        gameF (s + 1) b1 = gameF s g /\
        gameF (s + 2) b2 = gameF s g /\
        MaximalEventEHighSurvivorAtom
          s c b0 bz g b1 b2 b2 /\
        MaximalEventEHighSevenConfiguration s c b0 bz b1 b2)
    at hSeven
  rcases hSeven with
    ⟨_hBulk, _hNextBound, _hHighBound, _hclass,
      _hnextTerminals, hhighAtoms⟩

  have hs2Range : s + 2 ∈ List.range' 1 (s + 3) := by
    apply List.mem_range'_1.mpr
    constructor <;> omega
  have hs2Union : s + 2 ∈ diagValues ++ startValues :=
    hperm.mem_iff.mpr hs2Range
  refine ⟨c, b0, ?_⟩
  dsimp only [EventEMaximalEqualityCollisionAtom]
  refine ⟨hSatFull, ?_⟩
  rcases List.mem_append.mp hs2Union with hs2Diag | hs2Start
  · rcases List.mem_append.mp hs2Diag with hs2Early | hs2Z
    · left
      rcases List.mem_map.mp hs2Early with ⟨i, hi, hiValue⟩
      exact ⟨i, List.mem_range.mp hi, hiValue⟩
    · simp only [List.mem_singleton] at hs2Z
      omega
  · right
    rcases List.mem_map.mp hs2Start with ⟨g, hgTriple, hgValue⟩
    have hgHigh : g ∈ high := by
      apply List.mem_filter.mpr
      refine ⟨hgTriple, ?_⟩
      simpa [high, EventEHighTripleBandSlots] using hgValue
    rcases hhighAtoms g hgHigh with
      ⟨bz, b1, b2, hbz, hb1, hb2,
        hHostZ, hHost1, hHost2, hAtom, hSevenCases⟩
    exact ⟨g, bz, b1, b2, hgHigh, hbz, hb1, hb2,
      hHostZ, hHost1, hHost2, hAtom, hSevenCases⟩

/-- Strict event-E cross-edge certificate. -/
def EventEStrictCrossEdgeSurvivorCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventECrossEdgeSurvivorCertificate s delta z c b0 /\
  2 * ((EventEMissingBandSlots s delta c b0).length +
    (EventESecondMissingBandSlots s delta c b0).length) + 9 <= s /\
  2 * delta + 9 <= s +
    2 * (EventETriplePrefixBandSlots s delta c b0).length

/-- The strict owner budget improves the local event-E cross-edge constant
from 7 to 9. -/
theorem gameF_eventE_strict_cross_edge_missing_bound_R53_local
    {s delta z c b0 b1 : Nat}
    (hdip0 : gameF (s + 1) (s + 1) < gameF s s)
    (hdip1 : gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1))
    (hc : c < s) (hSucc : gameF s c = z + 1)
    (hNextDiag : gameF (s + 1) (s + 1) = z + 1)
    (hb1 : b1 < s + 1) (hHost1 : gameF (s + 1) b1 = z)
    (hEmit : gameF (s + 2) (s + 2) = z)
    (hslotsNodup : (EventEDefectBandSlots s delta c b0).Nodup)
    (hslotsData : forall g, g ∈ EventEDefectBandSlots s delta c b0 ->
      g < s /\ gameF s g < z) :
    2 * ((EventEMissingBandSlots s delta c b0).length +
      (EventESecondMissingBandSlots s delta c b0).length) + 9 <= s := by
  let slots := EventEDefectBandSlots s delta c b0
  let missing0 := EventEMissingBandSlots s delta c b0
  let survivors := EventESurvivingBandSlots s delta c b0
  let missing1 := EventESecondMissingBandSlots s delta c b0
  let low0 := missing0.map (fun g => gameF s g)
  let low1 := missing1.map (fun g => gameF s g)
  let forbidden0 := low0 ++ [z + 1]
  let forbidden1 := low1 ++ [z]

  have hmissing0Nodup : missing0.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hsurvivorsNodup : survivors.Nodup :=
    List.filter_sublist.nodup hslotsNodup
  have hmissing1Nodup : missing1.Nodup :=
    List.filter_sublist.nodup hsurvivorsNodup
  have hlow0Nodup : low0.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) missing0 hmissing0Nodup
    intro g hg k hk heq
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hk).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) heq
  have hlow1Nodup : low1.Nodup := by
    apply r53_nodup_map_of_injective_on
      (fun g => gameF s g) missing1 hmissing1Nodup
    intro g hg k hk heq
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hkSurv : k ∈ survivors := (List.mem_filter.mp hk).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hkSlots : k ∈ slots := (List.mem_filter.mp hkSurv).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsData g hgSlots).1)
      (Nat.le_of_lt (hslotsData k hkSlots).1) heq

  have hforbidden0Nodup : forbidden0.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hlow0Nodup, by simp, ?_⟩
    intro v hv w hw hEq
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
    have hLower := (hslotsData g hgSlots).2
    omega
  have hforbidden1Nodup : forbidden1.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hlow1Nodup, by simp, ?_⟩
    intro v hv w hw hEq
    simp only [List.mem_singleton] at hw
    subst w
    rcases List.mem_map.mp hv with ⟨g, hg, rfl⟩
    have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
    have hgSlots : g ∈ slots := (List.mem_filter.mp hgSurv).1
    have hLower := (hslotsData g hgSlots).2
    omega

  have hsub0 : forbidden0 ⊆ StrictRowPrefixValues gameF s := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgSlots : g ∈ slots := (List.mem_filter.mp hg).1
      exact List.mem_map.mpr
        ⟨g, List.mem_range.mpr (hslotsData g hgSlots).1, rfl⟩
    · simp only [List.mem_singleton] at hvHigh
      subst v
      exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, hSucc⟩
  have hmissing0 : forall v, v ∈ forbidden0 ->
      v ∉ StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing0, EventEMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      rw [← hNextDiag]
      exact diagonal_value_absent_strict_prefix
        gameRecurrenceModel (s + 1)
  have hsub1 : forbidden1 ⊆ StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgSurv : g ∈ survivors := (List.mem_filter.mp hg).1
      have hfilter := (List.mem_filter.mp hgSurv).2
      simpa [survivors, EventESurvivingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      exact List.mem_map.mpr
        ⟨b1, List.mem_range.mpr hb1, hHost1⟩
  have hmissing1 : forall v, v ∈ forbidden1 ->
      v ∉ StrictRowPrefixValues gameF (s + 2) := by
    intro v hv
    rcases List.mem_append.mp hv with hvLow | hvHigh
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing1, EventESecondMissingBandSlots] using hfilter
    · simp only [List.mem_singleton] at hvHigh
      subst v
      rw [← hEmit]
      exact diagonal_value_absent_strict_prefix
        gameRecurrenceModel (s + 2)

  have hbound :=
    game_consecutive_dips_two_forbidden_packets_strict_amortized_bound
      hdip0 hdip1 hforbidden0Nodup hsub0 hmissing0
        hforbidden1Nodup hsub1 hmissing1
  have hlen0 : forbidden0.length = missing0.length + 1 := by
    simp [forbidden0, low0]
  have hlen1 : forbidden1.length = missing1.length + 1 := by
    simp [forbidden1, low1]
  change 2 * (missing0.length + missing1.length) + 9 <= s
  omega

/-- Every event E carries the strict global survivor inequality. -/
theorem gameF_margin_eventE_strict_cross_edge_survivor_bound
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventEStrictCrossEdgeSurvivorCertificate s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hcross := gameF_margin_eventE_cross_edge_survivor_bound
    hU hdip hmargin hnextDip
  change exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  rcases hcross with ⟨c, b0, hcross⟩
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨hc, hb0, _hne, hSucc, hBase,
      hslotsNodup, hslotsLen, hslotsProps, _hweak⟩
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  rcases hInv with
    ⟨_hdeltaPos, _hdeltaUpper, _hdeltaSum, hzDiag,
      ci, bi, b1, _dc, _d0, _d1,
      hci, hbi, hb1, _hneCB, _hneB,
      hSuccI, hBaseI, hHost1, _hrest⟩
  have hciEq : ci = c :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hci) (Nat.le_of_lt hc)
      (hSuccI.trans hSucc.symm)
  have hbiEq : bi = b0 :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hbi) (Nat.le_of_lt hb0)
      (hBaseI.trans hBase.symm)
  subst ci
  subst bi
  have hslotsData : forall g,
      g ∈ EventEDefectBandSlots s delta c b0 ->
      g < s /\ gameF s g < z := by
    intro g hg
    have hdata := hslotsProps g hg
    have htransition := hdata.2.2.2
    have hLower : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    exact ⟨hdata.1, hLower⟩
  have hunitNext := hU (s + 1) hnextDip
  change gameF (s + 2) (s + 2) + 1 = d at hunitNext
  have hEmit : gameF (s + 2) (s + 2) = z := by omega
  have hstrict := gameF_eventE_strict_cross_edge_missing_bound_R53_local
    hdip hnextDip hc hSucc (by omega) hb1 hHost1 hEmit
      hslotsNodup hslotsData
  have hpartition := hcross.1.2.2.1
  have hglobal : 2 * delta + 9 <= s +
      2 * (EventETriplePrefixBandSlots s delta c b0).length := by
    change (EventEDefectBandSlots s delta c b0).length =
        (EventEMissingBandSlots s delta c b0).length +
        (EventESecondMissingBandSlots s delta c b0).length +
        (EventETriplePrefixBandSlots s delta c b0).length at hpartition
    change (EventEDefectBandSlots s delta c b0).length = delta at hslotsLen
    omega
  exact ⟨c, b0, hcross, hstrict, hglobal⟩

/-- Equality saturation and strict cross-edge packing are incompatible.
Hence maximal event E is impossible. -/
theorem gameF_no_margin_eventE_maximal_defect
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 \/
      exists j, s = j + 1 /\
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    Not (delta + 4 = s) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hmax
  have hstrict := gameF_margin_eventE_strict_cross_edge_survivor_bound
    hU hdip hmargin hnextDip
  change exists c b0,
    EventEStrictCrossEdgeSurvivorCertificate s delta z c b0 at hstrict
  rcases hstrict with ⟨c, b0, hstrict⟩
  have hglobal := hstrict.2.2
  have hExact := gameF_margin_eventE_maximal_survivor_count_exact
    hU hdip hmargin hnextDip hmax
  change exists ce be,
    EventEMaximalSurvivorDiagonalSqueezeCertificate s delta z ce be /\
    (EventETriplePrefixBandSlots s delta ce be).length = s / 2
    at hExact
  rcases hExact with ⟨ce, be, hSqueeze, htriple⟩
  have hbaseStrict := hstrict.1.1.1.1
  have hbaseExact := hSqueeze.1.1.1.1
  rcases hbaseStrict with
    ⟨hc, hb0, _hne, hSucc, hBase, _hrest⟩
  rcases hbaseExact with
    ⟨hce, hbe, _hneE, hSuccE, hBaseE, _hrestE⟩
  have hcEq : c = ce :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hc) (Nat.le_of_lt hce)
      (hSucc.trans hSuccE.symm)
  have hbEq : b0 = be :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hb0) (Nat.le_of_lt hbe)
      (hBase.trans hBaseE.symm)
  subst ce
  subst be
  omega

/-- Four finite atoms obtained after one more propagation of a nonmaximal
event E. -/
def EventENonmaxFinitePropagatedAtom
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipPenultimateHitCertificate s delta z c b0 \/
  EventEThirdDipExtraForbiddenCertificate s delta z c b0 \/
  (EventENonDipSharedOwnerSaturationCertificate s delta z c b0 /\
    2 * delta + 7 <= s) \/
  (EventENonDipSharedOwnerSaturationCertificate s delta z c b0 /\
    exists g, g ∈ EventEFourPrefixBandSlots s delta c b0)

def NonmaxMarginEventER53FiniteResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  NonmaxMarginEventECrossEdgeResidual s /\
  exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 /\
    EventENonmaxFinitePropagatedAtom s delta z c b0

/-- The R52 third-edge trichotomy sharpens to four finite atoms; in the
high-defect no-dip case a concrete four-prefix survivor is selected. -/
theorem gameF_nonmax_eventE_R53_finite_propagated_atoms
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 /\
      EventENonmaxFinitePropagatedAtom s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hprop := gameF_nonmax_eventE_R53_shared_owner_trichotomy
    hU hres
  change exists c b0,
    EventECrossEdgeSurvivorCertificate s delta z c b0 /\
    (EventEThirdDipPenultimateHitCertificate s delta z c b0 \/
     EventEThirdDipExtraForbiddenCertificate s delta z c b0 \/
     EventENonDipSharedOwnerSaturationCertificate s delta z c b0)
    at hprop
  rcases hprop with ⟨c, b0, hcross, hcase⟩
  refine ⟨c, b0, hcross, ?_⟩
  rcases hcase with hHit | hExtra | hNoDip
  · exact Or.inl hHit
  · exact Or.inr (Or.inl hExtra)
  · by_cases hlarge : s < 2 * delta + 7
    · have hfour :=
        eventE_nondip_shared_owner_forces_four_prefix_value
          hNoDip hlarge
      exact Or.inr (Or.inr (Or.inr ⟨hNoDip, hfour⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hNoDip, by omega⟩))

def MaximalMarginEventER53CollisionResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  MarginEventECounterexample s /\
  delta + 4 = s /\
  exists c b0,
    EventEMaximalEqualityCollisionAtom s delta z c b0

/-- The explicit equality-collision residual is empty under UnitDip. -/
theorem gameF_no_R53_maximal_equality_collision_residual
    (hU : UnitDip gameRecurrenceModel) :
    Not (exists s, MaximalMarginEventER53CollisionResidual s) := by
  rintro ⟨s, hres⟩
  rcases hres with ⟨hEvent, hmax, _hAtom⟩
  rcases hEvent with ⟨hdip, hmargin, hnextDip⟩
  exact gameF_margin_eventE_maximal_defect_impossible
    hU hdip hmargin hnextDip hmax

/-- Final R53 reduction: after the equality collision eliminates maximal
event E, RM2 failure under UnitDip is equivalent to one finite propagated
nonmaximal residual. -/
theorem gameF_unitDip_not_RM2_iff_R53_nonmax_finite_residual
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      exists s, NonmaxMarginEventER53FiniteResidual s := by
  constructor
  · intro hNotRM2
    rcases (gameF_unitDip_not_RM2_iff_exists_eventE hU).mp hNotRM2 with
      ⟨s, hEvent⟩
    rcases hEvent with ⟨hdip, hmargin, hnextDip⟩
    have hEvent' : MarginEventECounterexample s :=
      ⟨hdip, hmargin, hnextDip⟩
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    have hInv := gameF_margin_eventE_parametric_defect_invariant
      hU hdip hmargin hnextDip
    change EventEDefectPacketInvariant s d delta z at hInv
    have hNotMax : Not (delta + 4 = s) :=
      gameF_margin_eventE_maximal_defect_impossible
        hU hdip hmargin hnextDip
    have hnonmax : delta + 5 <= s := by
      have hupper := hInv.2.1
      omega
    have hcross := gameF_margin_eventE_cross_edge_survivor_bound
      hU hdip hmargin hnextDip
    change exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
    have hCrossResidual : NonmaxMarginEventECrossEdgeResidual s := by
      dsimp only [NonmaxMarginEventECrossEdgeResidual]
      exact ⟨hEvent', hInv, hnonmax, hcross⟩
    have hfinite := gameF_nonmax_eventE_R53_finite_propagated_atoms
      hU hCrossResidual
    change exists c b0,
      EventECrossEdgeSurvivorCertificate s delta z c b0 /\
      EventENonmaxFinitePropagatedAtom s delta z c b0 at hfinite
    rcases hfinite with ⟨c, b0, hcrossFinite, hAtom⟩
    refine ⟨s, ?_⟩
    dsimp only [NonmaxMarginEventER53FiniteResidual]
    exact ⟨hCrossResidual, c, b0, hcrossFinite, hAtom⟩
  · rintro ⟨s, hres⟩
    apply (gameF_unitDip_not_RM2_iff_exists_eventE hU).mpr
    exact ⟨s, hres.1.1⟩

/-- Positive dual of the final reduction. -/
theorem gameF_unitDip_RM2_iff_no_R53_nonmax_finite_residual
    (hU : UnitDip gameRecurrenceModel) :
    TwoStepDiagonalRecordLaw gameRecurrenceModel <->
      Not (exists s, NonmaxMarginEventER53FiniteResidual s) := by
  constructor
  · intro hRM2 hResidual
    exact ((gameF_unitDip_not_RM2_iff_R53_nonmax_finite_residual hU).mpr
      hResidual) hRM2
  · intro hNoResidual
    apply Classical.byContradiction
    intro hNotRM2
    exact hNoResidual
      ((gameF_unitDip_not_RM2_iff_R53_nonmax_finite_residual hU).mp
        hNotRM2)

/-- Unconditional audit, retaining the first-gap layer only when UnitDip
fails. -/
theorem gameF_RM2_counterexample_R53_complete_audit
    (hNotRM2 : Not (TwoStepDiagonalRecordLaw gameRecurrenceModel)) :
    (exists s, R51FirstGapResidual s) \/
    (exists s, NonmaxMarginEventER53FiniteResidual s) := by
  classical
  by_cases hU : UnitDip gameRecurrenceModel
  · exact Or.inr
      ((gameF_unitDip_not_RM2_iff_R53_nonmax_finite_residual hU).mp
        hNotRM2)
  · exact Or.inl
      (gameF_not_unitDip_has_R51_first_gap_residual hU)

end ChompLean
