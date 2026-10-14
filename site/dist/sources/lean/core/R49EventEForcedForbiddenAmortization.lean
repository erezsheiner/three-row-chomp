import R48EventEAmortizedMissingBand
import R48AdjacentDipAmortizedBackfillPacking

set_option autoImplicit false

namespace ChompLean

/-!
Publication scope: The game-specific margin Event E and RM2 specializations below retain their
explicit UnitDip, numerical-margin, dip and residual/certificate hypotheses.
Generic source, packing and overlap lemmas retain only the assumptions
displayed in their own signatures.

R49: charge the forced high missing value in addition to the event-E defect
band.

At the first dip of event E, `z+1=d(s+1)` occurs in the old strict prefix but
cannot occur in the new strict prefix, because it is the new diagonal value.
Adding this forced forbidden value to the genuinely missing band values
improves R48 from

`2*|M|+3 <= s`

to

`2*|M|+5 <= s`.
-/

def EventEForcedForbiddenAmortizedCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventEMissingBandAmortizedCertificate s delta z c b0 ∧
  2 * (EventEMissingBandSlots s delta c b0).length + 5 ≤ s

private theorem r49_nodup_map_of_injective_on
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) (xs : List α)
    (hxs : xs.Nodup)
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.map_cons]
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

/-- Strong event-E missing-band certificate.  The extra two units come from
the forced forbidden value `z+1`. -/
theorem gameF_margin_eventE_forced_forbidden_amortized_bound
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    ∃ c b0,
      EventEForcedForbiddenAmortizedCertificate s delta z c b0 := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  have hbase := gameF_margin_eventE_missing_band_amortized_bound
    hU hdip hmargin hnextDip
  change ∃ c b0,
    EventEMissingBandAmortizedCertificate s delta z c b0 at hbase
  rcases hbase with ⟨c, b0, hcert⟩
  rcases hcert with
    ⟨hc, hb0, hcNe, hSucc, hBase,
      hslotsNodup, hslotsLen, hslotsProps, hweakBound⟩
  let missing := EventEMissingBandSlots s delta c b0
  let lowForbidden := missing.map (fun g => gameF s g)
  let forbidden := (z + 1) :: lowForbidden

  have hmissingNodup : missing.Nodup := by
    dsimp [missing, EventEMissingBandSlots]
    exact List.filter_sublist.nodup hslotsNodup
  have hlowNodup : lowForbidden.Nodup := by
    apply r49_nodup_map_of_injective_on
      (fun g => gameF s g) missing hmissingNodup
    intro g hg k hk heq
    have hgSlots := (List.mem_filter.mp hg).1
    have hkSlots := (List.mem_filter.mp hk).1
    exact gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt (hslotsProps g hgSlots).1)
      (Nat.le_of_lt (hslotsProps k hkSlots).1) heq
  have hhighNotLow : z + 1 ∉ lowForbidden := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨g, hg, hEq⟩
    have hgSlots := (List.mem_filter.mp hg).1
    have htransition := (hslotsProps g hgSlots).2.2.2
    have hLower : gameF s g < z := by
      simpa [EventELowerTransition] using htransition.2.1
    omega
  have hforbiddenNodup : forbidden.Nodup := by
    dsimp [forbidden]
    exact List.nodup_cons.mpr ⟨hhighNotLow, hlowNodup⟩

  have hforbiddenSub : forbidden ⊆ StrictRowPrefixValues gameF s := by
    intro v hv
    rcases List.mem_cons.mp hv with hvHigh | hvLow
    · subst v
      apply mem_strictRowPrefixValues_iff_C.mpr
      exact ⟨c, hc, hSucc⟩
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hgSlots := (List.mem_filter.mp hg).1
      apply mem_strictRowPrefixValues_iff_C.mpr
      exact ⟨g, (hslotsProps g hgSlots).1, rfl⟩

  have hdiagPos : 0 < d := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 1)
    change s + 1 < d at hgt
    omega
  have hzDiag : z + 1 = d := by
    dsimp [z]
    omega
  have hhighMissing : z + 1 ∉ StrictRowPrefixValues gameF (s + 1) := by
    intro hmem
    rcases mem_strictRowPrefixValues_iff_C.mp hmem with ⟨b, hb, hEq⟩
    have hrowEq : gameF (s + 1) b = gameF (s + 1) (s + 1) := by
      rw [hEq, hzDiag]
    have hcols := gameRecurrenceModel.fixed_q_injective
      (Nat.le_of_lt hb) (Nat.le_refl _) hrowEq
    omega
  have hforbiddenMissing : ∀ v, v ∈ forbidden →
      v ∉ StrictRowPrefixValues gameF (s + 1) := by
    intro v hv
    rcases List.mem_cons.mp hv with hvHigh | hvLow
    · subst v
      exact hhighMissing
    · rcases List.mem_map.mp hvLow with ⟨g, hg, rfl⟩
      have hfilter := (List.mem_filter.mp hg).2
      simpa [missing, EventEMissingBandSlots] using hfilter

  have hbound := game_adjacent_dip_forbidden_amortized_bound
    hdip hforbiddenNodup hforbiddenSub hforbiddenMissing
  have hstrong : 2 * missing.length + 5 ≤ s := by
    dsimp [forbidden, lowForbidden] at hbound
    simp only [List.length_map] at hbound
    omega
  refine ⟨c, b0, ?_⟩
  exact ⟨⟨hc, hb0, hcNe, hSucc, hBase,
    hslotsNodup, hslotsLen, hslotsProps, hweakBound⟩, hstrong⟩

/-- Improved large-defect dichotomy: if `s<2*delta+5`, at least one
canonical lower-band value is rehosted in the new strict prefix. -/
theorem gameF_margin_eventE_forced_high_large_defect_rehost
    (hU : UnitDip gameRecurrenceModel) {s : Nat}
    (hdip : gameF (s + 1) (s + 1) < gameF s s)
    (hmargin : s = 0 ∨
      ∃ j, s = j + 1 ∧
        RMax gameRecurrenceModel j < gameF (s + 1) (s + 1) - 1)
    (hnextDip :
      gameF (s + 2) (s + 2) < gameF (s + 1) (s + 1)) :
    let d := gameF (s + 1) (s + 1)
    let delta := 2 * s - d
    let z := d - 1
    s < 2 * delta + 5 →
      ∃ c b0 g,
        gameF s c = z + 1 ∧ gameF s b0 = z ∧
        g ∈ EventEDefectBandSlots s delta c b0 ∧
        g < s ∧ g ≠ c ∧ g ≠ b0 ∧
        gameF s g < z ∧
        C gameF (s + 1) (s + 1) (gameF s g) := by
  dsimp only
  let d := gameF (s + 1) (s + 1)
  let delta := 2 * s - d
  let z := d - 1
  intro hlarge
  have hcert := gameF_margin_eventE_forced_forbidden_amortized_bound
    hU hdip hmargin hnextDip
  change ∃ c b0,
    EventEForcedForbiddenAmortizedCertificate s delta z c b0 at hcert
  rcases hcert with ⟨c, b0, hbase, hstrong⟩
  rcases hbase with
    ⟨_hc, _hb0, _hcNe, hSucc, hBase,
      hslotsNodup, hslotsLen, hslotsProps, _hweak⟩
  let slots := EventEDefectBandSlots s delta c b0
  let missing := EventEMissingBandSlots s delta c b0
  have hpresent : ∃ g, g ∈ slots ∧
      gameF s g ∈ StrictRowPrefixValues gameF (s + 1) := by
    apply Classical.byContradiction
    intro hnone
    have hallAbsent : ∀ g, g ∈ slots →
        gameF s g ∉ StrictRowPrefixValues gameF (s + 1) := by
      intro g hg hmem
      apply hnone
      exact ⟨g, hg, hmem⟩
    have hslotsSub : slots ⊆ missing := by
      intro g hg
      change g ∈ slots.filter (fun x =>
        !(decide (gameF s x ∈ StrictRowPrefixValues gameF (s + 1))))
      apply List.mem_filter.mpr
      refine ⟨hg, ?_⟩
      simpa using hallAbsent g hg
    have hlen := nodup_subset_length_le hslotsNodup hslotsSub
    change slots.length ≤ missing.length at hlen
    change slots.length = delta at hslotsLen
    change 2 * missing.length + 5 ≤ s at hstrong
    omega
  rcases hpresent with ⟨g, hgSlots, hgNew⟩
  have hgData := hslotsProps g hgSlots
  have hLower : gameF s g < z := by
    have htransition := hgData.2.2.2
    simpa [EventELowerTransition] using htransition.2.1
  have hgC : C gameF (s + 1) (s + 1) (gameF s g) :=
    mem_strictRowPrefixValues_iff_C.mp hgNew
  exact ⟨c, b0, g, hSucc, hBase, hgSlots,
    hgData.1, hgData.2.1, hgData.2.2.1, hLower, hgC⟩

#print axioms gameF_margin_eventE_forced_forbidden_amortized_bound
#print axioms gameF_margin_eventE_forced_high_large_defect_rehost

end ChompLean
