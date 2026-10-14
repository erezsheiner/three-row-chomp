import R55DeepQuietFullGeometry
import R55OverlapLedgerEventEEchoStaircase

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
R55: import the exact overlap ledger into the deep-quiet geometry.

The forward-owner theorem from `R55DeepQuietFullGeometry` says that every
canonical band cell is an echo of a past diagonal.  The overlap ledger says
that row `s` has exactly `delta` echoes, while the canonical band has exactly
`delta` cells.  Hence the band values are not merely a subfamily: they are a
permutation of the complete echo population of row `s`.

The same forward-owner matching can then be solved exactly on every suffix
above the second special packet column.  Its only possible matching is the
successor matching `g |-> g+1`, yielding a literal south-west diagonal echo
staircase all the way to the final two-column packet.
-/

noncomputable def EventEDeepQuietBandValues
    (s delta c b0 : Nat) : List Nat :=
  (EventEDefectBandSlots s delta c b0).map (fun g => gameF s g)

private theorem r55_nodup_map_of_injective_on
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

private theorem r55_perm_of_nodup_subset_length_le
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

/-- Exact ledger saturation: the canonical band values are precisely all
past-diagonal echoes in the old event row. -/
theorem gameF_deep_quiet_band_values_perm_all_old_echoes
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    (EventEDeepQuietBandValues s delta c b0).Perm
      (PastDiagonalEchoValues s) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\ _ at hresData
  rcases hresData.1 with ⟨hdip0, hmargin, hdip1⟩
  have hecho := gameF_margin_eventE_overlap_echo_staircase
    hU hdip0 hmargin hdip1
  change StrictRowEchoCount s = delta /\ _ at hecho
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, hslotsLen, hslotsProps, _hweak⟩
  let bandValues := EventEDeepQuietBandValues s delta c b0
  have hbandNodup : bandValues.Nodup := by
    apply r55_nodup_map_of_injective_on
      (fun g => gameF s g) (EventEDefectBandSlots s delta c b0)
      hslotsNodup
    intro g hg k hk hEq
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsProps g hg).1)
      (Nat.le_of_lt (hslotsProps k hk).1) hEq
  have hbandSub : bandValues ⊆ PastDiagonalEchoValues s := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨g, hgBand, rfl⟩
    have hforward := gameF_deep_quiet_every_band_slot_has_forward_owner
      hU hres hcross hterm g hgBand
    rcases hforward with ⟨i, _hgi, his, howner⟩
    have hgs := (hslotsProps g hgBand).1
    have hpref : gameF s g ∈ StrictRowPrefixValues gameF s :=
      List.mem_map.mpr ⟨g, List.mem_range.mpr hgs, rfl⟩
    have hband := gameF_strict_prefix_value_band hpref
    have hpast : gameF s g ∈ PastLowerDiagonalValues s := by
      apply mem_pastLowerDiagonalValues_iff.mpr
      exact ⟨i, his, howner, hband.2⟩
    apply List.mem_filter.mpr
    refine ⟨hpref, ?_⟩
    simpa [PastDiagonalEchoValues] using hpast
  have hbandLen : bandValues.length = delta := by
    simpa [bandValues, EventEDeepQuietBandValues] using hslotsLen
  have hechoLen : (PastDiagonalEchoValues s).length = delta := by
    simpa [StrictRowEchoCount] using hecho.1
  apply r55_perm_of_nodup_subset_length_le hbandNodup hbandSub
  omega

/-- A suffix of canonical band slots has only one possible forward-owner
matching: every slot `g` is owned by the immediately following diagonal
row `g+1`. -/
theorem gameF_deep_quiet_band_suffix_is_successor_echo_staircase
    (hU : UnitDip gameRecurrenceModel) {s c b0 g : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hgBand : g ∈ EventEDefectBandSlots
      s (2 * s - gameF (s + 1) (s + 1)) c b0)
    (hsuffix : forall k, g < k -> k < s - 1 ->
      k ∈ EventEDefectBandSlots
        s (2 * s - gameF (s + 1) (s + 1)) c b0) :
    gameF (g + 1) (g + 1) = gameF s g := by
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  change g ∈ EventEDefectBandSlots s delta c b0 at hgBand
  change forall k, g < k -> k < s - 1 ->
    k ∈ EventEDefectBandSlots s delta c b0 at hsuffix
  have hforward : forall x,
      x ∈ EventEDefectBandSlots s delta c b0 ->
      exists i, x < i /\ i < s /\ gameF i i = gameF s x :=
    gameF_deep_quiet_every_band_slot_has_forward_owner
      hU hres hcross hterm
  let P : Nat -> Prop := fun n =>
    forall x, s - 1 - x = n ->
      x ∈ EventEDefectBandSlots s delta c b0 ->
      (forall k, x < k -> k < s - 1 ->
        k ∈ EventEDefectBandSlots s delta c b0) ->
      gameF (x + 1) (x + 1) = gameF s x
  have hP : forall n, P n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro x hmeasure hxBand hxSuffix
        rcases hforward x hxBand with ⟨i, hxi, his, howner⟩
        by_cases hiSucc : i = x + 1
        · simpa [hiSucc] using howner
        · have hgap : x + 1 < i := by omega
          let k := i - 1
          have hxk : x < k := by
            dsimp [k]
            omega
          have hks : k < s - 1 := by
            dsimp [k]
            omega
          have hkBand : k ∈ EventEDefectBandSlots s delta c b0 :=
            hxSuffix k hxk hks
          have hkSuffix : forall j, k < j -> j < s - 1 ->
              j ∈ EventEDefectBandSlots s delta c b0 := by
            intro j hkj hjs
            exact hxSuffix j (by omega) hjs
          have hkMeasure : s - 1 - k < n := by
            rw [← hmeasure]
            omega
          have hkEcho := ih (s - 1 - k) hkMeasure
            k rfl hkBand hkSuffix
          have hki : k + 1 = i := by
            dsimp [k]
            omega
          have hrowEq : gameF s x = gameF s k := by
            rw [← howner, ← hkEcho, hki]
          have hxEqK := gameRecurrenceModel.fixed_q_injective
            (q := s) (b₁ := x) (b₂ := k)
            (by omega) (by omega) hrowEq
          omega
  exact hP (s - 1 - g) g rfl hgBand hsuffix

/-- Complete south-west normal form of the deep-quiet atom.  One high
packet column is the last old-prefix column; above the other packet column,
every intervening band cell is exactly the echo of its successor diagonal.
The reversed packet order additionally carries the forced earlier `z` ride.
-/
theorem gameF_deep_quiet_complete_southwest_staircase_to_tail_packet
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let z := gameF (s + 1) (s + 1) - 1
    (c = s - 1 /\ gameF s (s - 1) = z + 1 /\
      (forall g, b0 < g -> g < s - 1 ->
        gameF (g + 1) (g + 1) = gameF s g)) \/
    (b0 = s - 1 /\ gameF s (s - 1) = z /\
      (exists a, c < a /\ a < s /\ gameF a c = z) /\
      (forall g, c < g -> g < s - 1 ->
        gameF (g + 1) (g + 1) = gameF s g)) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\ _ at hresData
  have hInv := hresData.2.1
  rcases hInv with
    ⟨_hdeltaPos, _hdeltaUpper, _hsum, _hz,
      ci, bi, _b1, _dc, _d0, _d1,
      hci, hbi, _hb1, _hciNe, _hbiNe,
      hSuccI, hBaseI, _hHost1,
      hciLower, hbiLower, _hb1Lower, _rest⟩
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨hc, hb0, _hcNe, hSucc, hBase,
      _hslotsNodup, _hslotsLen, _hslotsProps, _hweak⟩
  have hciEq : ci = c :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hci) (Nat.le_of_lt hc)
      (hSuccI.trans hSucc.symm)
  have hbiEq : bi = b0 :=
    gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hbi) (Nat.le_of_lt hb0)
      (hBaseI.trans hBase.symm)
  have hcLower : s - delta - 1 <= c := by omega
  have hb0Lower : s - delta - 2 <= b0 := by omega
  have hnormal := gameF_deep_quiet_last_column_or_extra_z_ride
    hU hres hcross hterm
  rcases hnormal with hSuccLast | hBaseLast
  · left
    rcases hSuccLast with ⟨hcLast, hlastValue⟩
    refine ⟨hcLast, hlastValue, ?_⟩
    intro g hb0g hgs
    have hgRange : g ∈ List.range' (s - delta - 2) (delta + 2) := by
      apply List.mem_range'_1.mpr
      constructor <;> omega
    have hgBand : g ∈ EventEDefectBandSlots s delta c b0 := by
      change g ∈
        ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
      have hgc : g ≠ c := by rw [hcLast]; omega
      have hgb : g ≠ b0 := by omega
      exact (List.mem_erase_of_ne hgb).mpr
        ((List.mem_erase_of_ne hgc).mpr hgRange)
    apply gameF_deep_quiet_band_suffix_is_successor_echo_staircase
      hU hres hcross hterm hgBand
    intro k hgk hks
    have hkRange : k ∈ List.range' (s - delta - 2) (delta + 2) := by
      apply List.mem_range'_1.mpr
      constructor <;> omega
    have hkc : k ≠ c := by rw [hcLast]; omega
    have hkb : k ≠ b0 := by omega
    change k ∈
      ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
    exact (List.mem_erase_of_ne hkb).mpr
      ((List.mem_erase_of_ne hkc).mpr hkRange)

  · right
    rcases hBaseLast with ⟨hbLast, hlastValue, hprior⟩
    refine ⟨hbLast, hlastValue, hprior, ?_⟩
    intro g hcg hgs
    have hgRange : g ∈ List.range' (s - delta - 2) (delta + 2) := by
      apply List.mem_range'_1.mpr
      constructor <;> omega
    have hgBand : g ∈ EventEDefectBandSlots s delta c b0 := by
      change g ∈
        ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
      have hgc : g ≠ c := by omega
      have hgb : g ≠ b0 := by rw [hbLast]; omega
      exact (List.mem_erase_of_ne hgb).mpr
        ((List.mem_erase_of_ne hgc).mpr hgRange)
    apply gameF_deep_quiet_band_suffix_is_successor_echo_staircase
      hU hres hcross hterm hgBand
    intro k hgk hks
    have hkRange : k ∈ List.range' (s - delta - 2) (delta + 2) := by
      apply List.mem_range'_1.mpr
      constructor <;> omega
    have hkc : k ≠ c := by omega
    have hkb : k ≠ b0 := by rw [hbLast]; omega
    change k ∈
      ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
    exact (List.mem_erase_of_ne hkb).mpr
      ((List.mem_erase_of_ne hkc).mpr hkRange)

/-- A south-west echo lying to the right of a high MEX packet cell must
return through a genuinely off-diagonal source in the packet column.  The
diagonal owner itself cannot be that source, by fixed-row injectivity. -/
theorem gameF_right_echo_below_high_cell_has_offdiagonal_column_return
    {s m g u p : Nat}
    (hms : m < s) (hmg : m < g) (hgs : g < s)
    (hout : gameF s m = u) (hhost : gameF s g = p)
    (howner : gameF (g + 1) (g + 1) = p)
    (hsu : s < u) (hpu : p < u) :
    exists a,
      m < a /\ a < s /\ a ≠ g + 1 /\ gameF a m = p := by
  have hpPos : 0 < p := by
    have hgt := gameRecurrenceModel.value_gt_index
      (q := s) (r := g) (Nat.le_of_lt hgs)
    change g < gameF s g at hgt
    rw [hhost] at hgt
    omega
  have hpB : B gameF s m p := by
    apply gameRecurrenceModel.mex_no_skip (Nat.le_of_lt hms)
    · change s < gameF s m
      rw [hout]
      exact hsu
    · exact hpPos
    · change p < gameF s m
      rw [hout]
      exact hpu
  have hpR : R gameF s m p := by
    rcases hpB with hpR | hpC
    · exact hpR
    · exfalso
      rcases hpC with ⟨b, hbm, hbval⟩
      have hbg := gameRecurrenceModel.fixed_q_injective
        (q := s) (b₁ := b) (b₂ := g)
        (by omega) (Nat.le_of_lt hgs)
        (hbval.trans hhost.symm)
      omega
  rcases hpR with ⟨a, has, hraw⟩
  have hma : m < a := by
    apply Nat.lt_of_not_ge
    intro ham
    have hdiagRaw : gameF a a = p := by
      simpa [Nat.min_eq_left ham] using hraw
    have hdiagEq : gameF a a = gameF (g + 1) (g + 1) :=
      hdiagRaw.trans howner.symm
    have haEq := diagonal_injective gameRecurrenceModel hdiagEq
    omega
  have hcolRaw : gameF a m = p := by
    simpa [Nat.min_eq_right (Nat.le_of_lt hma)] using hraw
  have haNeOwner : a ≠ g + 1 := by
    intro haEq
    subst a
    have hcols := gameRecurrenceModel.fixed_q_injective
      (q := g + 1) (b₁ := m) (b₂ := g + 1)
      (by omega) (Nat.le_refl _)
      (hcolRaw.trans howner.symm)
    omega
  exact ⟨a, hma, has, haNeOwner, hcolRaw⟩

/-- The complete owner-index form of the deep-quiet ledger saturation.
There are `delta` distinct forward owners in an interval of size
`delta+1`; hence the owner list is the whole interval with one uniquely
missing row. -/
def EventEDeepQuietNearPerfectOwnerMatching
    (s delta c b0 : Nat) : Prop :=
  let slots := EventEDefectBandSlots s delta c b0
  let ownerRows := List.range' (s - delta - 1) (delta + 1)
  exists owner : Nat -> Nat, exists hole : Nat,
    hole ∈ ownerRows /\
    (slots.map owner).Perm (ownerRows.erase hole) /\
    (forall g, g ∈ slots ->
      g < owner g /\ owner g < s /\
        gameF (owner g) (owner g) = gameF s g) /\
    (forall i, i ∈ ownerRows -> i ∉ slots.map owner -> i = hole)

theorem gameF_deep_quiet_near_perfect_forward_owner_matching
    (hU : UnitDip gameRecurrenceModel) {s c b0 : Nat}
    (hres : NonmaxMarginEventECrossEdgeResidual s)
    (hcross : EventECrossEdgeSurvivorCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0)
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s (2 * s - gameF (s + 1) (s + 1))
        (gameF (s + 1) (s + 1) - 1) c b0) :
    let delta := 2 * s - gameF (s + 1) (s + 1)
    EventEDeepQuietNearPerfectOwnerMatching s delta c b0 := by
  classical
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  let slots := EventEDefectBandSlots s delta c b0
  let ownerRows := List.range' (s - delta - 1) (delta + 1)
  change NonmaxMarginEventECrossEdgeResidual s at hres
  change EventECrossEdgeSurvivorCertificate s delta z c b0 at hcross
  change EventENonDipDeepQuietTerminalCertificate
    s delta z c b0 at hterm
  have hresData := hres
  change MarginEventECounterexample s /\
      EventEDefectPacketInvariant s d delta z /\ _ at hresData
  have hdeltaUpper : delta + 4 <= s := hresData.2.1.2.1
  have hbase := hcross.1.1.1
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, _hSucc, _hBase,
      hslotsNodup, hslotsLen, _hslotsProps, _hweak⟩
  have hforward : forall g, g ∈ slots ->
      exists i, g < i /\ i < s /\ gameF i i = gameF s g := by
    intro g hg
    exact gameF_deep_quiet_every_band_slot_has_forward_owner
      hU hres hcross hterm g hg
  let owner : Nat -> Nat := fun g =>
    if hg : g ∈ slots then Classical.choose (hforward g hg) else 0
  have howner : forall g, g ∈ slots ->
      g < owner g /\ owner g < s /\
        gameF (owner g) (owner g) = gameF s g := by
    intro g hg
    dsimp [owner]
    rw [dif_pos hg]
    exact Classical.choose_spec (hforward g hg)
  have hownerInj : forall g, g ∈ slots -> forall k, k ∈ slots ->
      owner g = owner k -> g = k := by
    intro g hg k hk hEq
    have hgVal := (howner g hg).2.2
    have hkVal := (howner k hk).2.2
    have hrowEq : gameF s g = gameF s k := by
      rw [← hgVal, ← hkVal, hEq]
    have hgS : g < s :=
      Nat.lt_trans (howner g hg).1 (howner g hg).2.1
    have hkS : k < s :=
      Nat.lt_trans (howner k hk).1 (howner k hk).2.1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hgS) (Nat.le_of_lt hkS) hrowEq
  have hownersNodup : (slots.map owner).Nodup :=
    r55_nodup_map_of_injective_on owner slots
      hslotsNodup hownerInj
  have hownerRowsNodup : ownerRows.Nodup := by
    dsimp [ownerRows]
    exact List.nodup_range' 1
  have hownersSub : slots.map owner ⊆ ownerRows := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨g, hg, rfl⟩
    have hgRaw : g ∈
        List.range' (s - delta - 2) (delta + 2) := by
      change g ∈
        ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
        at hg
      exact List.mem_of_mem_erase (List.mem_of_mem_erase hg)
    rcases List.mem_range'_1.mp hgRaw with ⟨hgLower, hgUpper⟩
    rcases howner g hg with ⟨hgOwner, hownerS, _hvalue⟩
    apply List.mem_range'_1.mpr
    constructor <;> omega
  have hownersLen : (slots.map owner).length = delta := by
    rw [List.length_map]
    simpa [slots] using hslotsLen
  have hownerRowsLen : ownerRows.length = delta + 1 := by
    simp [ownerRows]
  have hmissing : exists hole, hole ∈ ownerRows /\
      hole ∉ slots.map owner := by
    apply Classical.byContradiction
    intro hnone
    have hownerRowsSub : ownerRows ⊆ slots.map owner := by
      intro i hi
      apply Classical.byContradiction
      intro himiss
      exact hnone ⟨i, hi, himiss⟩
    have hlen := nodup_subset_length_le hownerRowsNodup hownerRowsSub
    rw [hownerRowsLen, hownersLen] at hlen
    omega
  rcases hmissing with ⟨hole, hhUniverse, hhMissing⟩
  have hownersEraseSub : slots.map owner ⊆ ownerRows.erase hole := by
    intro i hi
    have hiUniverse := hownersSub hi
    have hiNe : i ≠ hole := by
      intro hEq
      subst i
      exact hhMissing hi
    exact (List.mem_erase_of_ne hiNe).mpr hiUniverse
  have heraseLen : (ownerRows.erase hole).length = delta := by
    have hlen := List.length_erase_of_mem hhUniverse
    omega
  have hperm : (slots.map owner).Perm (ownerRows.erase hole) :=
    r55_perm_of_nodup_subset_length_le
      hownersNodup hownersEraseSub (by omega)
  have hunique : forall i, i ∈ ownerRows ->
      i ∉ slots.map owner -> i = hole := by
    intro i hiUniverse hiMissing
    apply Classical.byContradiction
    intro hiNe
    have hiErase : i ∈ ownerRows.erase hole :=
      (List.mem_erase_of_ne hiNe).mpr hiUniverse
    exact hiMissing (hperm.mem_iff.mpr hiErase)
  change EventEDeepQuietNearPerfectOwnerMatching s delta c b0
  dsimp [EventEDeepQuietNearPerfectOwnerMatching]
  exact ⟨owner, hole, hhUniverse, hperm, howner, hunique⟩

#print axioms gameF_deep_quiet_band_values_perm_all_old_echoes
#print axioms gameF_deep_quiet_band_suffix_is_successor_echo_staircase
#print axioms gameF_deep_quiet_complete_southwest_staircase_to_tail_packet
#print axioms gameF_right_echo_below_high_cell_has_offdiagonal_column_return
#print axioms gameF_deep_quiet_near_perfect_forward_owner_matching

end ChompLean
