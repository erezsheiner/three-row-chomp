import R35RM2LocalObstructionPackage
import R50Integration

set_option autoImplicit false

namespace ChompLean

/-!
R51: direct residual audit for RM2.

Under `UnitDip`, failure of RM2 is exactly a numerical-margin consecutive
dip (event E).  The parametric Event-E invariant and the R50 two-edge/host
theorems then leave four sharply named cases: a nonmaximal defect with a
strict finite defect budget, or one of the three exact owner-time freeze
regimes in the maximal defect case.

Without assuming `UnitDip`, there is one additional first-gap layer.  The
past- and future-diagonal species remain named explicitly.  The late-blocker
species is opened by R48--R50 into a high-`q` iterative terminal with finite
measures, a nonrecursive boundary terminal, or a strict successor descent.
No hypothesis is left implicit and no RM2 premise is used in a reduction
which is meant to audit failure of RM2.
-/

/-- The exact pointwise failure of `MarginNoConsecutiveDips`. -/
def MarginEventECounterexample (s : Nat) : Prop :=
  gameF (s + 1) (s + 1) < gameF s s /\
  (s = 0 \/
    exists j, s = j + 1 /\
      RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1) /\
  gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)

/-- The three possible owner times for the maximal-defect survivor. -/
inductive EventEFreezeRegimeTag
  | alreadyFrozen
  | freezesAtNext
  | freezesAtSecond
  deriving DecidableEq

/-- A nonmaximal event-E residual.  Besides the strict defect inequality,
it retains both the full parametric packet and the exact two-edge survivor
count certificate. -/
def NonmaxMarginEventEResidual (s : Nat) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  MarginEventECounterexample s /\
  EventEDefectPacketInvariant s d delta z /\
  delta + 5 <= s /\
  exists c b0,
    EventETwoEdgeSurvivorCountCertificate s delta z c b0

/-- Maximal event E with its exact three-row host geometry, completed lower
row start, exact distinct-column count, two-edge finite certificate, and a
specified owner-time freeze regime. -/
def MaximalMarginEventEFreezeResidual
    (s : Nat) (tag : EventEFreezeRegimeTag) : Prop :=
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  MarginEventECounterexample s /\
  delta + 4 = s /\
  (exists cf bf,
    EventETwoEdgeSurvivorCountCertificate s delta z cf bf) /\
  exists c b0 bz g b1 b2 r,
    z = s + 3 /\
    c < s /\ b0 < s /\ bz < s + 1 /\
    gameF s c = z + 1 /\ gameF s b0 = z /\
    gameF (s + 1) bz = z /\
    g ∈ EventEDefectBandSlots s delta c b0 /\
    g < s /\ g ≠ c /\ g ≠ b0 /\
    b1 < s + 1 /\ b2 < s + 2 /\
    gameF (s + 1) b1 = gameF s g /\
    gameF (s + 2) b2 = gameF s g /\
    0 < gameF s g /\ gameF s g < z /\
    r < gameF s g /\ gameF (gameF s g) r = gameF s g /\
    ([g, b1, b2].eraseDups).length = gameF s g - s + 1 /\
    ThreeConsecutiveHostGeometry s (gameF s g) g b1 b2 /\
    (match tag with
      | .alreadyFrozen =>
          gameF s g <= s /\ g = b1 /\ b1 = b2
      | .freezesAtNext =>
          gameF s g = s + 1 /\ g ≠ b1 /\ b1 = b2
      | .freezesAtSecond =>
          gameF s g = s + 2 /\ g ≠ b1 /\ b1 ≠ b2 /\ g ≠ b2)

/-- The exact R48--R50 residual of a late first-gap blocker. -/
def R51LateBlockerResidual (s : Nat) : Prop :=
  LateBlockerHighQIterativeNormalForm s \/
  (BoundaryLateBlockerParametricNormalForm s /\
    Not (BoundaryCorridorSmallerLateBlocker s)) \/
  LateBlockerDescentStep (s + 1) s

/-- Complete first-gap residual when `UnitDip` itself fails. -/
def R51FirstGapResidual (s : Nat) : Prop :=
  DipFirstGapPastDiagonal gameRecurrenceModel s \/
  DipFirstGapFutureDiagonalLoss gameRecurrenceModel s \/
  R51LateBlockerResidual s

/-- Failure of the margin law is exactly existence of an event-E witness. -/
theorem gameF_not_marginNoConsecutiveDips_iff_exists_eventE :
    Not (MarginNoConsecutiveDips gameRecurrenceModel) <->
      exists s, MarginEventECounterexample s := by
  classical
  constructor
  · intro hNotMargin
    by_cases hEvent : exists s, MarginEventECounterexample s
    · exact hEvent
    · exact False.elim (hNotMargin (by
        intro s hdip hmargin hnextDip
        apply hEvent
        exact ⟨s, hdip, hmargin, hnextDip⟩))
  · rintro ⟨s, hEvent⟩ hNoConsecutive
    rcases hEvent with ⟨hdip, hmargin, hnextDip⟩
    exact hNoConsecutive s hdip hmargin hnextDip

/-- Under `UnitDip`, the RM2 counterexamples and event-E witnesses coincide
exactly.  The reverse direction is direct: two consecutive dips contradict
the two-step record comparison from `s` to `s+2`. -/
theorem gameF_unitDip_not_RM2_iff_exists_eventE
    (hU : UnitDip gameRecurrenceModel) :
    Not (TwoStepDiagonalRecordLaw gameRecurrenceModel) <->
      exists s, MarginEventECounterexample s := by
  constructor
  · intro hNotRM2
    apply gameF_not_marginNoConsecutiveDips_iff_exists_eventE.mp
    intro hMargin
    exact hNotRM2
      (game_twoStepRecordLaw_of_unitDip_marginNoConsecutiveDips
        hU hMargin)
  · rintro ⟨s, hdip, hmargin, hnextDip⟩ hRM2
    have hrecord : gameF s s < gameF (s + 2) (s + 2) :=
      hRM2 (i := s) (a := s + 2) (by omega)
    omega

/-- Exact four-way Event-E residual.  The nonmaximal case has
`delta+5<=s`; equality `delta+4=s` yields precisely one of the three R50
freeze regimes. -/
theorem gameF_margin_eventE_R51_exact_residual_normal_form
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hEvent : MarginEventECounterexample s) :
    NonmaxMarginEventEResidual s \/
    MaximalMarginEventEFreezeResidual s .alreadyFrozen \/
    MaximalMarginEventEFreezeResidual s .freezesAtNext \/
    MaximalMarginEventEFreezeResidual s .freezesAtSecond := by
  rcases hEvent with ⟨hdip, hmargin, hnextDip⟩
  have hEvent' : MarginEventECounterexample s :=
    ⟨hdip, hmargin, hnextDip⟩
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hInv := gameF_margin_eventE_parametric_defect_invariant
    hU hdip hmargin hnextDip
  change EventEDefectPacketInvariant s d delta z at hInv
  have hCount := gameF_margin_eventE_two_edge_survivor_lower_bound
    hU hdip hmargin hnextDip
  change exists c b0,
    EventETwoEdgeSurvivorCountCertificate s delta z c b0 at hCount
  by_cases hmax : delta + 4 = s
  · have hGeometry :=
      gameF_margin_eventE_maximal_defect_triple_host_geometry
        hU hdip hmargin hnextDip
    change delta + 4 = s ->
      exists c b0 bz g b1 b2 r,
        z = s + 3 /\
        c < s /\ b0 < s /\ bz < s + 1 /\
        gameF s c = z + 1 /\ gameF s b0 = z /\
        gameF (s + 1) bz = z /\
        g ∈ EventEDefectBandSlots s delta c b0 /\
        g < s /\ g ≠ c /\ g ≠ b0 /\
        b1 < s + 1 /\ b2 < s + 2 /\
        gameF (s + 1) b1 = gameF s g /\
        gameF (s + 2) b2 = gameF s g /\
        0 < gameF s g /\ gameF s g < z /\
        r < gameF s g /\ gameF (gameF s g) r = gameF s g /\
        ([g, b1, b2].eraseDups).length = gameF s g - s + 1 /\
        ThreeConsecutiveHostGeometry s (gameF s g) g b1 b2
      at hGeometry
    rcases hGeometry hmax with
      ⟨c, b0, bz, g, b1, b2, r,
        hzMax, hc, hb0, hbz, hSucc, hBase, hHostZ,
        hgBand, hgs, hgc, hgb0, hb1, hb2, hHost1, hHost2,
        hpPos, hpz, hrp, hstart, hcount, hgeometry⟩
    have hgeometryFull := hgeometry
    rcases hgeometry with
      ⟨_hpUpper, _hgp, _hb1p, _hb2p,
        _hfirstIff, _hsecondIff, _hspanIff, hregime⟩
    have hBuild : forall tag : EventEFreezeRegimeTag,
        (match tag with
          | .alreadyFrozen =>
              gameF s g <= s /\ g = b1 /\ b1 = b2
          | .freezesAtNext =>
              gameF s g = s + 1 /\ g ≠ b1 /\ b1 = b2
          | .freezesAtSecond =>
              gameF s g = s + 2 /\ g ≠ b1 /\ b1 ≠ b2 /\ g ≠ b2) ->
        MaximalMarginEventEFreezeResidual s tag := by
      intro tag htag
      dsimp only [MaximalMarginEventEFreezeResidual]
      refine ⟨hEvent', hmax, hCount,
        c, b0, bz, g, b1, b2, r,
        hzMax, hc, hb0, hbz, hSucc, hBase, hHostZ,
        hgBand, hgs, hgc, hgb0, hb1, hb2, hHost1, hHost2,
        hpPos, hpz, hrp, hstart, hcount, hgeometryFull, htag⟩
    rcases hregime with hPast | hNext | hSecond
    · exact Or.inr (Or.inl (hBuild .alreadyFrozen hPast))
    · exact Or.inr (Or.inr
        (Or.inl (hBuild .freezesAtNext hNext)))
    · exact Or.inr (Or.inr
        (Or.inr (hBuild .freezesAtSecond hSecond)))
  · left
    dsimp only [NonmaxMarginEventEResidual]
    refine ⟨hEvent', hInv, ?_, hCount⟩
    have hupper := hInv.2.1
    omega

/-- The four-case residual is the complete UnitDip counterexample audit. -/
theorem gameF_unitDip_RM2_counterexample_R51_normal_form
    (hU : UnitDip gameRecurrenceModel)
    (hNotRM2 : Not (TwoStepDiagonalRecordLaw gameRecurrenceModel)) :
    (exists s, NonmaxMarginEventEResidual s) \/
    (exists s,
      MaximalMarginEventEFreezeResidual s .alreadyFrozen) \/
    (exists s,
      MaximalMarginEventEFreezeResidual s .freezesAtNext) \/
    (exists s,
      MaximalMarginEventEFreezeResidual s .freezesAtSecond) := by
  rcases (gameF_unitDip_not_RM2_iff_exists_eventE hU).mp hNotRM2 with
    ⟨s, hEvent⟩
  rcases gameF_margin_eventE_R51_exact_residual_normal_form
      hU hEvent with hNonmax | hPast | hNext | hSecond
  · exact Or.inl ⟨s, hNonmax⟩
  · exact Or.inr (Or.inl ⟨s, hPast⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨s, hNext⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨s, hSecond⟩))

/-- R48--R50 opening of every late-blocker obstruction: finite high-`q`
iteration, nonrecursive boundary terminal, or strict smaller successor. -/
theorem gameF_late_blocker_R51_residual
    {s : Nat}
    (hLate : DipFirstGapLateBlockerLoss gameRecurrenceModel s) :
    R51LateBlockerResidual s := by
  rcases gameF_late_blocker_terminal_or_successor_descent hLate with
    hTerminal | hDescent
  · rcases gameF_late_blocker_terminal_certificate_R50_reduction
      hTerminal with hHigh | hBoundary
    · exact Or.inl hHigh
    · exact Or.inr (Or.inl hBoundary)
  · exact Or.inr (Or.inr hDescent)

/-- Every non-unit dip receives the fully opened R51 first-gap residual. -/
theorem gameF_nonunit_dip_R51_first_gap_residual
    {s : Nat}
    (hgap : DipFirstGap gameRecurrenceModel s < gameF s s) :
    R51FirstGapResidual s := by
  rcases nonunit_dip_first_gap_trichotomy
      gameRecurrenceModel hgap with hPast | hFuture | hLate
  · exact Or.inl hPast
  · exact Or.inr (Or.inl hFuture)
  · exact Or.inr (Or.inr
      (gameF_late_blocker_R51_residual hLate))

/-- Negation of `UnitDip` produces a concrete first-gap residual, with its
late-blocker branch already carrying the R48--R50 finite measures. -/
theorem gameF_not_unitDip_has_R51_first_gap_residual
    (hNotU : Not (UnitDip gameRecurrenceModel)) :
    exists s, R51FirstGapResidual s := by
  classical
  by_cases hGap : exists s,
      DipFirstGap gameRecurrenceModel s < gameF s s
  · rcases hGap with ⟨s, hgap⟩
    exact ⟨s, gameF_nonunit_dip_R51_first_gap_residual hgap⟩
  · exact False.elim (hNotU (by
      intro s hdip
      change gameF (s + 1) (s + 1) < gameF s s at hdip
      by_cases hUnit : gameF (s + 1) (s + 1) + 1 = gameF s s
      · exact hUnit
      · have hgap : DipFirstGap gameRecurrenceModel s < gameF s s := by
          change gameF (s + 1) (s + 1) + 1 < gameF s s
          omega
        exact False.elim (hGap ⟨s, hgap⟩)))

/-- Unconditional RM2 failure audit.  Either `UnitDip` already fails at a
named first-gap residual (whose late-blocker case is fully reduced), or the
counterexample is one of the exact four Event-E residuals above. -/
theorem gameF_RM2_counterexample_R51_complete_audit
    (hNotRM2 : Not (TwoStepDiagonalRecordLaw gameRecurrenceModel)) :
    (exists s, R51FirstGapResidual s) \/
    ((exists s, NonmaxMarginEventEResidual s) \/
      (exists s,
        MaximalMarginEventEFreezeResidual s .alreadyFrozen) \/
      (exists s,
        MaximalMarginEventEFreezeResidual s .freezesAtNext) \/
      (exists s,
        MaximalMarginEventEFreezeResidual s .freezesAtSecond)) := by
  classical
  by_cases hU : UnitDip gameRecurrenceModel
  · right
    exact gameF_unitDip_RM2_counterexample_R51_normal_form hU hNotRM2
  · left
    exact gameF_not_unitDip_has_R51_first_gap_residual hU

end ChompLean
