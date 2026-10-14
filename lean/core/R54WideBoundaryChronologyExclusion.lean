import R54EventEThirdDipBoundarySaturation

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
R54: the exact chronology left by the wide third-dip boundary atom.

The boundary source at `(s,g)` has no spare slot.  Exact MEX at the two
subsequent prehosts therefore gives sharp lower bounds on their columns.
There are only two possibilities:

* the value follows the exact south-west staircase
  `(s,g),(s+1,g-1),(s+2,g-2)`, and all three source lists are permutations
  of the same full positive interval; or
* one of the later hosts jumps to the right of `g`, with at least two (or
  three) spare source slots.

This is a genuine reduction of the chronology debt.  It does not assert
that either alternative is impossible.
-/

/-- A high cell of the actual encoding is the exact positive MEX of its
literal Brouwer source. -/
theorem gameF_high_cell_exact_mex
    {q b p : Nat} (hbq : b <= q) (hqp : q < p)
    (hhost : gameF q b = p) :
    IsMex (B gameF q b) p := by
  refine ⟨by omega, ?_, ?_⟩
  · have habs := encoded_ge_not_blocked game_encodes hbq (by
      change q <= gameF q b
      rw [hhost]
      omega)
    simpa [hhost] using habs
  · intro k hkpos hkp
    exact gameRecurrenceModel.mex_no_skip hbq (by
      change q < gameF q b
      simpa [hhost] using hqp) hkpos (by
        change k < gameF q b
        simpa [hhost] using hkp)

/-- The zero-slack south-west outcome.  Besides the three host positions,
this records the exact MEX statements and the three equal full source
permutations. -/
def WideBoundarySouthwestExactChain
    (s p g b1 b2 : Nat) : Prop :=
  3 <= g /\
  b1 + 1 = g /\ b2 + 2 = g /\
  gameF s g = p /\
  gameF (s + 1) b1 = p /\
  gameF (s + 2) b2 = p /\
  IsMex (B gameF s g) p /\
  IsMex (B gameF (s + 1) b1) p /\
  IsMex (B gameF (s + 2) b2) p /\
  (List.range' 1 (p - 1)).Perm (BValueList gameF s g) /\
  (List.range' 1 (p - 1)).Perm
    (BValueList gameF (s + 1) b1) /\
  (List.range' 1 (p - 1)).Perm
    (BValueList gameF (s + 2) b2)

/-- A later prehost escapes to the right of the exact boundary.  The
displayed inequalities quantify the resulting source-capacity slack. -/
def WideBoundaryRightEscape
    (s p g b1 b2 : Nat) : Prop :=
  (g + 1 <= b1 /\ p - 1 + 2 <= (s + 1) + b1) \/
  (g + 1 <= b2 /\ p - 1 + 3 <= (s + 2) + b2)

/-- Full recurrence/source normal form extracted from the boundary atom. -/
def EventEThirdDipWideBoundaryChronologyCertificate
    (s delta z c b0 : Nat) : Prop :=
  EventEThirdDipBoundarySaturationCertificate s delta z c b0 /\
  exists g b1 b2,
    g = s - delta - 3 /\
    3 <= g /\
    g - 1 <= b1 /\ g - 2 <= b2 /\
    g ≠ b1 /\ b1 ≠ b2 /\ g ≠ b2 /\
    gameF s g = z - 1 /\
    gameF (s + 1) b1 = z - 1 /\
    gameF (s + 2) b2 = z - 1 /\
    IsMex (B gameF s g) (z - 1) /\
    IsMex (B gameF (s + 1) b1) (z - 1) /\
    IsMex (B gameF (s + 2) b2) (z - 1) /\
    (WideBoundarySouthwestExactChain s (z - 1) g b1 b2 \/
      WideBoundaryRightEscape s (z - 1) g b1 b2)

/-- Every wide exact boundary atom is either the exact south-west source
chain or has a quantitatively nontrivial right escape. -/
theorem eventE_third_dip_boundary_chronology_normal_form
    {s delta z c b0 : Nat}
    (hcert : EventEThirdDipBoundarySaturationCertificate
      s delta z c b0) :
    EventEThirdDipWideBoundaryChronologyCertificate
      s delta z c b0 := by
  have hcertFull := hcert
  rcases hcert with
    ⟨_hextra, hstair, _hlast, _hweighted, _hfour,
      g, b1, b2, hgEq, hg, hb1, hb2,
      hhost0, hhost1, hhost2, hgb1, hb1b2, hgb2,
      hcapacity, hsat0⟩
  rcases hstair with
    ⟨hdeltaSix, _hdiag0, _hdiag1, _hdiag2, hdiag3, _hstairHosts⟩
  have hgThree : 3 <= g := by omega
  have hpHigh3 : s + 3 < z - 1 := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    rw [hdiag3] at hgt
    exact hgt
  have hmex0 : IsMex (B gameF s g) (z - 1) :=
    gameF_high_cell_exact_mex (Nat.le_of_lt hg) (by omega) hhost0
  have hmex1 : IsMex (B gameF (s + 1) b1) (z - 1) :=
    gameF_high_cell_exact_mex (Nat.le_of_lt hb1) (by omega) hhost1
  have hmex2 : IsMex (B gameF (s + 2) b2) (z - 1) :=
    gameF_high_cell_exact_mex (Nat.le_of_lt hb2) (by omega) hhost2
  have hcap1 := high_cell_output_source_capacity
    gameRecurrenceModel (q := s + 1) (r := b1) (m := z - 1)
      (Nat.le_of_lt hb1) (by omega) hhost1
  have hcap2 := high_cell_output_source_capacity
    gameRecurrenceModel (q := s + 2) (r := b2) (m := z - 1)
      (Nat.le_of_lt hb2) (by omega) hhost2
  have hb1Lower : g - 1 <= b1 := by omega
  have hb2Lower : g - 2 <= b2 := by omega
  refine ⟨hcertFull, g, b1, b2, hgEq, hgThree,
    hb1Lower, hb2Lower, hgb1, hb1b2, hgb2,
    hhost0, hhost1, hhost2, hmex0, hmex1, hmex2, ?_⟩
  by_cases hb1Exact : b1 + 1 = g
  · by_cases hb2Exact : b2 + 2 = g
    · left
      have hperm0 := lowerSaturated_exact_source_perm hsat0 hcapacity
      have hsat1 : LowerSaturated gameF (s + 1) b1 (z - 1) :=
        hmex1.2.2
      have hsat2 : LowerSaturated gameF (s + 2) b2 (z - 1) :=
        hmex2.2.2
      have hcapExact1 : (z - 1) - 1 = (s + 1) + b1 := by omega
      have hcapExact2 : (z - 1) - 1 = (s + 2) + b2 := by omega
      have hperm1 := lowerSaturated_exact_source_perm hsat1 hcapExact1
      have hperm2 := lowerSaturated_exact_source_perm hsat2 hcapExact2
      exact ⟨hgThree, hb1Exact, hb2Exact,
        hhost0, hhost1, hhost2, hmex0, hmex1, hmex2,
        hperm0, hperm1, hperm2⟩
    · right
      right
      have hb2Right : g + 1 <= b2 := by omega
      exact ⟨hb2Right, by omega⟩
  · right
    left
    have hb1Right : g + 1 <= b1 := by omega
    exact ⟨hb1Right, by omega⟩

/-- A clean conditional elimination theorem.  It isolates exactly the two
chronology statements that would close this atom: no exact south-west chain,
and no unresolved right escape. -/
theorem no_eventE_third_dip_boundary_of_chronology_resolution
    {s delta z c b0 : Nat}
    (hNoChain : forall g b1 b2,
      WideBoundarySouthwestExactChain s (z - 1) g b1 b2 -> False)
    (hNoEscape : forall g b1 b2,
      WideBoundaryRightEscape s (z - 1) g b1 b2 -> False) :
    Not (EventEThirdDipBoundarySaturationCertificate s delta z c b0) := by
  intro hcert
  have hnormal := eventE_third_dip_boundary_chronology_normal_form hcert
  rcases hnormal.2 with
    ⟨g, b1, b2, _hgEq, _hgThree, _hb1Lower, _hb2Lower,
      _hgb1, _hb1b2, _hgb2, _hhost0, _hhost1, _hhost2,
      _hmex0, _hmex1, _hmex2, hsplit⟩
  rcases hsplit with hchain | hescape
  · exact hNoChain g b1 b2 hchain
  · exact hNoEscape g b1 b2 hescape

/-! ## Exact south-west source counterframe

The next finite frame is not claimed to be a global Chomp encoding.  It is
stronger than the earlier one-source audit: all three cells of the exact
south-west chain have their literal full MEX source, the three local copy
guards are false, the four diagonal values make the required unit staircase,
and the relevant rows are injective.  Thus a pure extension of R44 based
only on those three source permutations cannot eliminate the chain.
-/

def r54SouthwestExactSourceFrame (q r : Nat) : Nat :=
  if q <= 5 then
    if r = q then q + 1 else 200 + 20 * q + r
  else if q = 6 then
    if r = 5 then 8 else if r = 6 then 7 else 320 + r
  else if q = 7 then
    if r = 5 then 10 else if r = 6 then 9
    else if r = 7 then 8 else 340 + r
  else if q = 8 then
    if r = 5 then 11 else if r = 6 then 10
    else if r = 7 then 9 else if r = 8 then 30 else 360 + r
  else if q = 9 then
    if r = 5 then 12 else if r = 6 then 11
    else if r = 7 then 10 else if r = 9 then 31 else 380 + r
  else if q = 10 then
    if r = 5 then 13 else if r = 6 then 12
    else if r = 7 then 11 else if r = 10 then 32 else 400 + r
  else if q = 11 then
    if r = 0 then 12 else if r = 1 then 13 else if r = 2 then 14
    else if r = 3 then 15 else if r = 4 then 17 else if r = 5 then 16
    else if r = 6 then 18 else if r = 7 then 19
    else if r = 11 then 22 else 420 + r
  else if q = 12 then
    if r = 0 then 8 else if r = 1 then 13 else if r = 2 then 14
    else if r = 3 then 15 else if r = 4 then 16 else if r = 5 then 17
    else if r = 6 then 19 else if r = 12 then 21 else 440 + r
  else if q = 13 then
    if r = 0 then 7 else if r = 1 then 9 else if r = 2 then 14
    else if r = 3 then 15 else if r = 4 then 18 else if r = 5 then 19
    else if r = 13 then 20 else 460 + r
  else if q = 14 then
    if r = 14 then 19 else 480 + r
  else 500 + 20 * q + r

theorem r54_southwest_source0_exact :
    BValueList r54SouthwestExactSourceFrame 11 7 =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
       12, 13, 14, 15, 17, 16, 18] := by
  decide

theorem r54_southwest_source1_exact :
    BValueList r54SouthwestExactSourceFrame 12 6 =
      [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 18,
       8, 13, 14, 15, 16, 17] := by
  decide

theorem r54_southwest_source2_exact :
    BValueList r54SouthwestExactSourceFrame 13 5 =
      [1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 16, 17,
       7, 9, 14, 15, 18] := by
  decide

private theorem r54_isMex_nineteen_of_source_membership
    {f : Nat -> Nat -> Nat} {q r : Nat}
    (hsource : forall k, k ∈ BValueList f q r <-> 1 <= k /\ k <= 18) :
    IsMex (B f q r) 19 := by
  refine ⟨by omega, ?_, ?_⟩
  · intro hB
    have hmem := mem_BValueList_iff.mpr hB
    have := (hsource 19).mp hmem
    omega
  · intro k hkpos hklt
    apply mem_BValueList_iff.mp
    exact (hsource k).mpr ⟨by omega, by omega⟩

theorem r54_southwest_source0_isMex :
    IsMex (B r54SouthwestExactSourceFrame 11 7) 19 := by
  apply r54_isMex_nineteen_of_source_membership
  intro k
  rw [r54_southwest_source0_exact]
  simp
  omega

theorem r54_southwest_source1_isMex :
    IsMex (B r54SouthwestExactSourceFrame 12 6) 19 := by
  apply r54_isMex_nineteen_of_source_membership
  intro k
  rw [r54_southwest_source1_exact]
  simp
  omega

theorem r54_southwest_source2_isMex :
    IsMex (B r54SouthwestExactSourceFrame 13 5) 19 := by
  apply r54_isMex_nineteen_of_source_membership
  intro k
  rw [r54_southwest_source2_exact]
  simp
  omega

/-- The three-source interface left by the exact south-west alternative. -/
def WideBoundarySouthwestThreeSourceInterface
    (f : Nat -> Nat -> Nat) : Prop :=
  f 11 7 = 19 /\ f 12 6 = 19 /\ f 13 5 = 19 /\
  f 11 11 = 22 /\ f 12 12 = 21 /\
  f 13 13 = 20 /\ f 14 14 = 19 /\
  IsMex (B f 11 7) 19 /\
  IsMex (B f 12 6) 19 /\
  IsMex (B f 13 5) 19 /\
  (List.range' 1 18).Perm (BValueList f 11 7) /\
  (List.range' 1 18).Perm (BValueList f 12 6) /\
  (List.range' 1 18).Perm (BValueList f 13 5) /\
  Not (f 10 7 < 11) /\ Not (f 11 6 < 12) /\ Not (f 12 5 < 13) /\
  ((List.range 12).map (fun r => f 11 r)).Nodup /\
  ((List.range 13).map (fun r => f 12 r)).Nodup /\
  ((List.range 14).map (fun r => f 13 r)).Nodup

/-- All three exact MEX sources, the local recurrence guards, the unit
diagonal staircase, and the relevant row-injectivity checks are jointly
consistent. -/
theorem r54_southwest_three_source_interface_is_consistent :
    WideBoundarySouthwestThreeSourceInterface
      r54SouthwestExactSourceFrame := by
  dsimp [WideBoundarySouthwestThreeSourceInterface]
  refine ⟨by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    r54_southwest_source0_isMex,
    r54_southwest_source1_isMex,
    r54_southwest_source2_isMex, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide, by decide⟩
  · rw [r54_southwest_source0_exact]
    decide
  · rw [r54_southwest_source1_exact]
    decide
  · rw [r54_southwest_source2_exact]
    decide

#print axioms gameF_high_cell_exact_mex
#print axioms eventE_third_dip_boundary_chronology_normal_form
#print axioms no_eventE_third_dip_boundary_of_chronology_resolution
#print axioms r54_southwest_three_source_interface_is_consistent

end ChompLean
