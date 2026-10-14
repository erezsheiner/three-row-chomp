import R54NonmaxEventEQuietStrictOwnerReduction

set_option autoImplicit false

namespace ChompLean

/-!
R54: exact scheduler reduction for the deep no-third-dip terminal.

The full Brouwer recurrence does give more than the owner/count interface.
If a positive value `p` is absent from the strict prefix of row `q`, then
at every column `r<q` at least one of the following explanations is
available:

* an older-row source already blocks `p`;
* the constant branch carries a value below `q`; or
* the MEX branch is diverted by a strictly smaller source hole.

This is the precise first-eligible obstruction.  Applied to a deep-quiet
three-ride value, it shows that every column below its past-diagonal owner
must be covered by one of those three mechanisms.  What the present
recurrence library does *not* prove is that such a complete cover is
impossible.  The final theorems isolate that missing statement exactly,
including the case in which the triple packet is already empty.
-/

/-- Three exhaustive (not asserted mutually exclusive) reasons why a value
absent from the new strict prefix is not selected at a particular column. -/
def MissingPrefixSchedulerDisposition (q p r : Nat) : Prop :=
  R gameF q r p \/
  (gameF (q - 1) r < q /\
    gameF q r = gameF (q - 1) r) \/
  (IsMex (B gameF q r) (gameF q r) /\
    gameF q r < p)

/-- Exact-recurrence scheduler cover.  This uses the complete Brouwer
recurrence for `gameF`, rather than only `RecurrenceModel.mex_no_skip`.
At a column where `p` has no historical `R` blocker, failure to emit `p`
is therefore either a low constant carry or a genuinely smaller MEX
diversion. -/
theorem gameF_missing_prefix_exact_scheduler_cover
    {q p : Nat}
    (hpPos : 0 < p)
    (hpMissing : p ∉ StrictRowPrefixValues gameF q) :
    forall r, r < q -> MissingPrefixSchedulerDisposition q p r := by
  intro r hrq
  let hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  by_cases hR : R gameF q r p
  · exact Or.inl hR
  · right
    by_cases hfirst : r < q /\ gameF (q - 1) r < q
    · left
      exact ⟨hfirst.2, hrec.1 hfirst.1 hfirst.2⟩
    · right
      have hmex : IsMex (B gameF q r) (gameF q r) :=
        hrec.2 (Nat.le_of_lt hrq) hfirst
      have hpNotC : Not (C gameF q r p) := by
        intro hC
        apply hpMissing
        apply mem_strictRowPrefixValues_iff_C.mpr
        rcases hC with ⟨b, hbr, hvalue⟩
        exact ⟨b, by omega, hvalue⟩
      have hpNotB : Not (B gameF q r p) := by
        intro hB
        rcases hB with hBR | hBC
        · exact hR hBR
        · exact hpNotC hBC
      have houtNe : gameF q r ≠ p := by
        intro hout
        apply hpMissing
        apply mem_strictRowPrefixValues_iff_C.mpr
        exact ⟨r, hrq, hout⟩
      have houtLt : gameF q r < p := by
        apply Nat.lt_of_not_ge
        intro hpLe
        have hpLt : p < gameF q r := Nat.lt_of_le_of_ne hpLe (Ne.symm houtNe)
        exact hpNotB (hmex.2.2 p hpPos hpLt)
      exact ⟨hmex, houtLt⟩

/-- In a deep terminal all the apparently additional numerical clauses are
forced by the strict certificate plus emptiness of the four-prefix packet.
Thus `strict certificate + Q4=[]` is the irreducible logical core. -/
theorem eventE_deep_quiet_terminal_iff_strict_empty_four
    {s delta z c b0 : Nat} :
    EventENonDipDeepQuietTerminalCertificate s delta z c b0 <->
      EventENonDipStrictSharedOwnerCertificate s delta z c b0 /\
      EventEFourPrefixBandSlots s delta c b0 = [] := by
  constructor
  · intro hterm
    exact ⟨hterm.1, hterm.2.1⟩
  · rintro ⟨hcert, hfour⟩
    have hpartition := hcert.1.1.2.1
    have hfourLen :
        (EventEFourPrefixBandSlots s delta c b0).length = 0 := by
      rw [hfour]
      simp
    have htripleMissing :
        (EventETriplePrefixBandSlots s delta c b0).length =
          (EventEThirdMissingBandSlots s delta c b0).length := by
      omega
    have hdeep := hcert.2.2.2
    rw [hfour] at hdeep
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hdeep
    exact ⟨hcert, hfour, htripleMissing, by omega, hdeep⟩

/-- Full chronological normal form of every triple value in the deep
terminal.  Its three known hosts lie strictly to the left of its distinct
past-diagonal owner.  On the fourth row, every column below that owner is
covered by the exact scheduler disjunction above. -/
theorem eventE_deep_quiet_three_ride_exact_scheduler_cover
    {s delta z c b0 g : Nat}
    (hterm : EventENonDipDeepQuietTerminalCertificate
      s delta z c b0)
    (hg : g ∈ EventETriplePrefixBandSlots s delta c b0) :
    exists i b1 b2,
      i < s /\ g < i /\ b1 < i /\ b2 < i /\
      g ≠ b1 /\ g ≠ b2 /\ b1 ≠ b2 /\
      gameF i i = gameF s g /\
      gameF (s + 1) b1 = gameF s g /\
      gameF (s + 2) b2 = gameF s g /\
      s + 2 < gameF s g /\ gameF s g < z /\
      gameF s g ∉ StrictRowPrefixValues gameF (s + 3) /\
      forall r, r < i ->
        MissingPrefixSchedulerDisposition (s + 3) (gameF s g) r := by
  have hpoint :=
    eventE_deep_quiet_every_triple_is_high_past_owner_loss hterm g hg
  rcases hpoint with
    ⟨_hgMissing, i, b2, hi, hb2, howner, hhost2, hhigh, hbelow⟩

  have hgSurv : g ∈ EventESurvivingBandSlots s delta c b0 :=
    (List.mem_filter.mp hg).1
  have hgSlots : g ∈ EventEDefectBandSlots s delta c b0 :=
    (List.mem_filter.mp hgSurv).1
  have hgRange :
      g ∈ List.range' (s - delta - 2) (delta + 2) := by
    change g ∈
      ((List.range' (s - delta - 2) (delta + 2)).erase c).erase b0
      at hgSlots
    exact List.mem_of_mem_erase (List.mem_of_mem_erase hgSlots)
  have hgBound : g < s := by
    have hrange := List.mem_range'_1.mp hgRange
    have hdeep := hterm.2.2.2.2
    omega

  have hrow1 :
      gameF s g ∈ StrictRowPrefixValues gameF (s + 1) := by
    have hfilter := (List.mem_filter.mp hgSurv).2
    simpa [EventESurvivingBandSlots] using hfilter
  rcases mem_strictRowPrefixValues_iff_C.mp hrow1 with
    ⟨b1, hb1, hhost1⟩

  have hgLeOwner : g <= i := by
    apply Nat.le_of_not_gt
    intro hig
    exact gameRecurrenceModel.diagonal_general_no_attack
      hig (Nat.le_of_lt hgBound) howner
  have hgNeOwner : g ≠ i := by
    intro hEq
    subst g
    exact
      (encoding_diagonal_value_not_reemitted_in_owner_column
        game_encodes hi) howner.symm
  have hgOwner : g < i := Nat.lt_of_le_of_ne hgLeOwner hgNeOwner

  have hb1LeOwner : b1 <= i := by
    apply Nat.le_of_not_gt
    intro hib1
    exact gameRecurrenceModel.diagonal_general_no_attack
      hib1 (Nat.le_of_lt hb1) (howner.trans hhost1.symm)
  have hb1NeOwner : b1 ≠ i := by
    intro hEq
    subst b1
    exact
      (encoding_diagonal_value_not_reemitted_in_owner_column
        game_encodes (by omega : i < s + 1))
        (howner.trans hhost1.symm).symm
  have hb1Owner : b1 < i := Nat.lt_of_le_of_ne hb1LeOwner hb1NeOwner

  have hb2LeOwner : b2 <= i := by
    apply Nat.le_of_not_gt
    intro hib2
    exact gameRecurrenceModel.diagonal_general_no_attack
      hib2 (Nat.le_of_lt hb2) (howner.trans hhost2.symm)
  have hb2NeOwner : b2 ≠ i := by
    intro hEq
    subst b2
    exact
      (encoding_diagonal_value_not_reemitted_in_owner_column
        game_encodes (by omega : i < s + 2))
        (howner.trans hhost2.symm).symm
  have hb2Owner : b2 < i := Nat.lt_of_le_of_ne hb2LeOwner hb2NeOwner

  have hgb1 : g ≠ b1 := by
    intro hEq
    subst b1
    exact encoding_same_lower_no_repeat game_encodes
      (s := g) (t₁ := s) (t₂ := s + 1) (p := gameF s g)
      hgBound (by omega) (by omega) rfl hhost1
  have hgb2 : g ≠ b2 := by
    intro hEq
    subst b2
    exact encoding_same_lower_no_repeat game_encodes
      (s := g) (t₁ := s) (t₂ := s + 2) (p := gameF s g)
      hgBound (by omega) hhigh rfl hhost2
  have hb1b2 : b1 ≠ b2 := by
    intro hEq
    subst b2
    exact encoding_same_lower_no_repeat game_encodes
      (s := b1) (t₁ := s + 1) (t₂ := s + 2) (p := gameF s g)
      hb1 (by omega) hhigh hhost1 hhost2

  have hpMissing : gameF s g ∉
      StrictRowPrefixValues gameF (s + 3) := by
    intro hpRow
    have hgFour : g ∈ EventEFourPrefixBandSlots s delta c b0 := by
      apply List.mem_filter.mpr
      refine ⟨hg, ?_⟩
      simpa [EventEFourPrefixBandSlots] using hpRow
    rw [hterm.2.1] at hgFour
    simp at hgFour
  have hsched := gameF_missing_prefix_exact_scheduler_cover
    (p := gameF s g) (q := s + 3) (by omega) hpMissing
  exact ⟨i, b1, b2, hi, hgOwner, hb1Owner, hb2Owner,
    hgb1, hgb2, hb1b2, howner, hhost1, hhost2,
    hhigh, hbelow, hpMissing,
    fun r hri => hsched r (by omega)⟩

/-- The genuinely missing scheduler law.  It deliberately quantifies over
the whole strict certificate, so it also handles the case in which the
triple packet was already emptied on one of the first two edges. -/
def EventENonDipDeepQuietEscape : Prop :=
  forall s delta z c b0,
    EventENonDipStrictSharedOwnerCertificate s delta z c b0 ->
    exists g, g ∈ EventEFourPrefixBandSlots s delta c b0

/-- Exact reformulation: the escape law is equivalent to excluding every
deep-quiet terminal. The scheduler cover above is a necessary consequence
for each present triple-packet value, not an equivalent exclusion principle.
A proof of the escape law must also handle an already empty triple packet. -/
theorem eventE_nonDip_deep_quiet_escape_iff_no_terminal :
    EventENonDipDeepQuietEscape <->
      forall s delta z c b0,
        Not (EventENonDipDeepQuietTerminalCertificate
          s delta z c b0) := by
  constructor
  · intro hescape s delta z c b0 hterm
    rcases hescape s delta z c b0 hterm.1 with ⟨g, hg⟩
    rw [hterm.2.1] at hg
    simp at hg
  · intro hno s delta z c b0 hcert
    by_cases hfour : EventEFourPrefixBandSlots s delta c b0 = []
    · exact False.elim
        (hno s delta z c b0
          ((eventE_deep_quiet_terminal_iff_strict_empty_four).2
            ⟨hcert, hfour⟩))
    · exact List.exists_mem_of_ne_nil _ hfour

#print axioms gameF_missing_prefix_exact_scheduler_cover
#print axioms eventE_deep_quiet_terminal_iff_strict_empty_four
#print axioms eventE_deep_quiet_three_ride_exact_scheduler_cover
#print axioms eventE_nonDip_deep_quiet_escape_iff_no_terminal

end ChompLean
