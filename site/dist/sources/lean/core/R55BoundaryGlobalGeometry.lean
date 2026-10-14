import R54WideBoundaryChronologyExclusion

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
R55: global game geometry behind the wide third-dip boundary.

This file goes beyond a comparison of finite source permutations.  Its
basic observation is a vertical scheduler law for the actual encoding.
Suppose a high cell `(q,r)` emits `p`, while the next diagonal is at most
`p+1`.  The old value `p` itself enters the next source through its `R`
part.  The next cell cannot emit `p`, and it cannot emit `p+1` either:
that would collide with the next diagonal.  Exact MEX therefore forces the
next cell to emit a smaller value.  Since all old `R` sources survive the
vertical step, that smaller value has to come from the old *row prefix*.

Applied to the last two prehosts of the boundary atom, this produces two
strict high prefix echoes.  In the zero-slack south-west chain the echoes
are distinct.  Thus the terminal is not merely three compatible source
permutations: it necessarily creates a new, lower-valued echo cascade in
the genuine Chomp scheduler.
-/

/-- A high cell followed by a diagonal no larger than its successor forces
the next cell in the same column to echo a strict-prefix value from the old
row.

This is an actual-game statement: the proof uses encoding/completeness,
diagonal maximality and the literal Brouwer source.  No `UnitDip`, RM2, or
counting hypothesis is used. -/
theorem gameF_slow_next_diagonal_forces_prefix_echo
    {q r p : Nat}
    (hrq : r < q)
    (hhost : gameF q r = p)
    (hhigh : q < p)
    (hnextDiag : gameF (q + 1) (q + 1) <= p + 1) :
    exists b,
      b < r /\
      gameF (q + 1) r = gameF q b /\
      q < gameF (q + 1) r /\
      gameF (q + 1) r < p /\
      Not (B gameF (q + 1) r (gameF (q + 1) r)) := by
  let m := gameF (q + 1) r
  have hrNext : r <= q + 1 := by omega
  have hnotFirst :
      Not (r < q + 1 /\ gameF ((q + 1) - 1) r < q + 1) := by
    intro hfirst
    have hprev : gameF q r < q + 1 := by
      simpa only [Nat.add_sub_cancel] using hfirst.2
    rw [hhost] at hprev
    omega
  have hmGe : q + 1 <= m := by
    dsimp [m]
    exact not_first_implies_ge_of_encoding
      game_encodes game_complete hrNext hnotFirst
  have hmDiag : m <= gameF (q + 1) (q + 1) := by
    dsimp [m]
    exact game_diagonal_maximal hrNext
  have hpR : R gameF (q + 1) r p := by
    refine ⟨q, by omega, ?_⟩
    rw [Nat.min_eq_right (Nat.le_of_lt hrq)]
    exact hhost
  have hpB : B gameF (q + 1) r p := Or.inl hpR
  have hmNotB : Not (B gameF (q + 1) r m) := by
    dsimp [m]
    exact encoded_ge_not_blocked game_encodes hrNext hmGe
  have hmNeP : m ≠ p := by
    intro hm
    apply hmNotB
    simpa only [hm] using hpB
  have hmNeSucc : m ≠ p + 1 := by
    intro hm
    have hdiagEq : gameF (q + 1) (q + 1) = p + 1 := by
      omega
    have hcols := gameRecurrenceModel.fixed_q_injective
      (q := q + 1) (b₁ := r) (b₂ := q + 1)
      hrNext (Nat.le_refl (q + 1)) (by
        dsimp [m] at hm
        exact hm.trans hdiagEq.symm)
    omega
  have hmLt : m < p := by omega
  have hmPos : 0 < m := by omega
  have hmOldB : B gameF q r m := by
    apply gameRecurrenceModel.mex_no_skip (Nat.le_of_lt hrq)
    · change q < gameF q r
      rw [hhost]
      exact hhigh
    · exact hmPos
    · change m < gameF q r
      rw [hhost]
      exact hmLt
  rcases hmOldB with hmOldR | hmOldC
  · rcases hmOldR with ⟨a, haq, haValue⟩
    have hmNewR : R gameF (q + 1) r m :=
      ⟨a, by omega, haValue⟩
    exact False.elim (hmNotB (Or.inl hmNewR))
  · rcases hmOldC with ⟨b, hbr, hbValue⟩
    exact ⟨b, hbr, by
      change gameF (q + 1) r = gameF q b
      exact hbValue.symm,
      by simpa [m] using hmGe,
      hmLt, hmNotB⟩

/-- Exact-source overlap exclusion.  If `B(t,r)` has no duplicate values,
a past diagonal echo in row `t` cannot have both its diagonal owner and its
row host strictly to the left of `r`: the diagonal occurrence lies in the
`R` half of the source and the row occurrence lies in its `C` half.

This is the pointwise geometric form of the overlap-ledger constraint at an
exact boundary source. -/
theorem exact_source_forbids_low_owner_low_host
    {t r p i b v : Nat}
    (hperm : (List.range' 1 (p - 1)).Perm (BValueList gameF t r))
    (hit : i < t) (hir : i < r) (hbr : b < r)
    (howner : gameF i i = v) (hhost : gameF t b = v) : False := by
  have hnodup : (BValueList gameF t r).Nodup :=
    hperm.nodup (List.nodup_range' 1)
  have hparts := List.nodup_append.mp hnodup
  have hvR : v ∈ RValueList gameF t r := by
    apply mem_RValueList_iff.mpr
    refine ⟨i, hit, ?_⟩
    rw [Nat.min_eq_left (Nat.le_of_lt hir)]
    exact howner
  have hvC : v ∈ CValueList gameF t r := by
    exact mem_CValueList_iff.mpr ⟨b, hbr, hhost⟩
  exact (hparts.2.2 v hvR v hvC) rfl

/-- Usable disjunctive form: every diagonal echo seen by an exact source
has either a high owner or a high row host. -/
theorem exact_source_echo_owner_or_host_reaches_cut
    {t r p i b v : Nat}
    (hperm : (List.range' 1 (p - 1)).Perm (BValueList gameF t r))
    (hit : i < t)
    (howner : gameF i i = v) (hhost : gameF t b = v) :
    r <= i \/ r <= b := by
  by_cases hir : r <= i
  · exact Or.inl hir
  · right
    apply Nat.le_of_not_gt
    intro hbr
    exact exact_source_forbids_low_owner_low_host hperm hit
      (Nat.lt_of_not_ge hir) hbr howner hhost

/-- The two strict prefix echoes forced by the last two vertical steps of a
wide boundary atom.  If their values coincide, row injectivity pins the
second echo's old host to the first prehost column, and hence forces the
prehost columns to point strictly to the right. -/
def WideBoundaryDoublePrefixEcho
    (s p b1 b2 : Nat) : Prop :=
  exists a1 a2,
    a1 < b1 /\ a2 < b2 /\
    gameF (s + 2) b1 = gameF (s + 1) a1 /\
    gameF (s + 3) b2 = gameF (s + 2) a2 /\
    s + 1 < gameF (s + 2) b1 /\
    gameF (s + 2) b1 < p /\
    s + 2 < gameF (s + 3) b2 /\
    gameF (s + 3) b2 < p /\
    Not (B gameF (s + 2) b1 (gameF (s + 2) b1)) /\
    Not (B gameF (s + 3) b2 (gameF (s + 3) b2)) /\
    (gameF (s + 2) b1 ≠ gameF (s + 3) b2 \/
      (a2 = b1 /\ b1 < b2))

/-- Every wide third-dip boundary atom in the actual game creates a double
strict-prefix echo below its boundary value.  This conclusion is independent
of whether the prehost chronology is south-west exact or escapes right. -/
theorem eventE_third_dip_boundary_forces_double_prefix_echo
    {s delta z c b0 : Nat}
    (hcert : EventEThirdDipBoundarySaturationCertificate
      s delta z c b0) :
    exists g b1 b2,
      g = s - delta - 3 /\
      g < s /\ b1 < s + 1 /\ b2 < s + 2 /\
      gameF s g = z - 1 /\
      gameF (s + 1) b1 = z - 1 /\
      gameF (s + 2) b2 = z - 1 /\
      WideBoundaryDoublePrefixEcho s (z - 1) b1 b2 := by
  rcases hcert with
    ⟨_hextra, hstair, _hlast, _hweighted, _hfour,
      g, b1, b2, hgEq, hg, hb1, hb2,
      hhost0, hhost1, hhost2, _hgb1, hb1b2, _hgb2,
      _hcapacity, _hsat⟩
  rcases hstair with
    ⟨_hdeltaSix, _hdiag0, _hdiag1, hdiag2, hdiag3, _hhosts⟩
  have hpHigh3 : s + 3 < z - 1 := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    rw [hdiag3] at hgt
    exact hgt
  have hpHigh1 : s + 1 < z - 1 := by omega
  have hpHigh2 : s + 2 < z - 1 := by omega
  have hnext1 : gameF (s + 2) (s + 2) <= (z - 1) + 1 := by
    rw [hdiag2]
    omega
  have hnext2 : gameF (s + 3) (s + 3) <= (z - 1) + 1 := by
    rw [hdiag3]
    omega
  rcases gameF_slow_next_diagonal_forces_prefix_echo
      hb1 hhost1 hpHigh1 hnext1 with
    ⟨a1, ha1, heq1, hlo1, hhi1, habs1⟩
  rcases gameF_slow_next_diagonal_forces_prefix_echo
      hb2 hhost2 hpHigh2 hnext2 with
    ⟨a2, ha2, heq2, hlo2, hhi2, habs2⟩
  have hcollision :
      gameF (s + 2) b1 ≠ gameF (s + 3) b2 \/
        (a2 = b1 /\ b1 < b2) := by
    by_cases hne : gameF (s + 2) b1 ≠ gameF (s + 3) b2
    · exact Or.inl hne
    · right
      have heq : gameF (s + 2) b1 = gameF (s + 3) b2 :=
        Classical.not_not.mp hne
      have ha2Eq : gameF (s + 2) a2 = gameF (s + 2) b1 := by
        exact heq2.symm.trans heq.symm
      have hidx : a2 = b1 :=
        gameRecurrenceModel.fixed_q_injective
          (by omega) (by omega) ha2Eq
      exact ⟨hidx, by omega⟩
  refine ⟨g, b1, b2, hgEq, hg, hb1, hb2,
    hhost0, hhost1, hhost2, ?_⟩
  exact ⟨a1, a2, ha1, ha2, heq1, heq2,
    hlo1, hhi1, hlo2, hhi2, habs1, habs2, hcollision⟩

/-- In the zero-slack south-west chronology, the two forced echoes are
necessarily distinct.  Thus the exact chain spawns two new high values,
not a single value counted twice. -/
def WideBoundarySouthwestDistinctEchoCascade
    (s p b1 b2 : Nat) : Prop :=
  exists a1 a2,
    a1 < b1 /\ a2 < b2 /\
    gameF (s + 2) b1 = gameF (s + 1) a1 /\
    gameF (s + 3) b2 = gameF (s + 2) a2 /\
    s + 1 < gameF (s + 2) b1 /\
    gameF (s + 2) b1 < p /\
    s + 2 < gameF (s + 3) b2 /\
    gameF (s + 3) b2 < p /\
    gameF (s + 2) b1 ≠ gameF (s + 3) b2

theorem wideBoundary_southwest_chain_forces_distinct_echo_cascade
    {s z g b1 b2 : Nat}
    (hchain : WideBoundarySouthwestExactChain
      s (z - 1) g b1 b2)
    (_hg : g < s) (hb1 : b1 < s + 1) (hb2 : b2 < s + 2)
    (hdiag2 : gameF (s + 2) (s + 2) = z)
    (hdiag3 : gameF (s + 3) (s + 3) = z - 1) :
    WideBoundarySouthwestDistinctEchoCascade
      s (z - 1) b1 b2 := by
  rcases hchain with
    ⟨hgThree, hb1Eq, hb2Eq,
      _hhost0, hhost1, hhost2, _hmex0, _hmex1, _hmex2,
      _hperm0, _hperm1, _hperm2⟩
  have hpHigh3 : s + 3 < z - 1 := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    rw [hdiag3] at hgt
    exact hgt
  have hpHigh1 : s + 1 < z - 1 := by omega
  have hpHigh2 : s + 2 < z - 1 := by omega
  have hnext1 : gameF (s + 2) (s + 2) <= (z - 1) + 1 := by
    rw [hdiag2]
    omega
  have hnext2 : gameF (s + 3) (s + 3) <= (z - 1) + 1 := by
    rw [hdiag3]
    omega
  rcases gameF_slow_next_diagonal_forces_prefix_echo
      hb1 hhost1 hpHigh1 hnext1 with
    ⟨a1, ha1, heq1, hlo1, hhi1, _habs1⟩
  rcases gameF_slow_next_diagonal_forces_prefix_echo
      hb2 hhost2 hpHigh2 hnext2 with
    ⟨a2, ha2, heq2, hlo2, hhi2, _habs2⟩
  have hb2b1 : b2 < b1 := by omega
  have ha2b1 : a2 < b1 := Nat.lt_trans ha2 hb2b1
  have hne : gameF (s + 2) b1 ≠ gameF (s + 3) b2 := by
    intro heq
    have hsame : gameF (s + 2) b1 = gameF (s + 2) a2 :=
      heq.trans heq2
    have hidx := gameRecurrenceModel.fixed_q_injective
      (by omega) (by omega) hsame
    omega
  exact ⟨a1, a2, ha1, ha2, heq1, heq2,
    hlo1, hhi1, hlo2, hhi2, hne⟩

/-- The first forced echo in the south-west chain is not just a repeated
row value.  It is the value lost on the literal horizontal source edge
`b2 -> b2+1=b1` in row `s+2`.  Consequently it has a strict parked host
in column `b2`, and every diagonal/row-start opening of that value lies
strictly to the right of `b2`.

This is the precise bridge from the exact-source terminal to an
`OverlapLedger`-style echo charge: the new echo comes with a named source
edge and a named interior host, rather than only contributing one to a
cardinality. -/
def WideBoundarySouthwestFirstEchoLoss
    (s p b1 b2 : Nat) : Prop :=
  let e := gameF (s + 2) b1
  b2 + 1 = b1 /\
  s + 1 < e /\ e < p /\
  B gameF (s + 2) b2 e /\
  Not (B gameF (s + 2) (b2 + 1) e) /\
  (exists a, StrictParkedHost gameRecurrenceModel (s + 2) b2 e a) /\
  ((exists i, b2 < i /\ i < e /\ gameF i i = e) \/
    (exists r, b2 < r /\ r < e /\ gameF e r = e))

theorem wideBoundary_southwest_chain_first_echo_is_strict_source_loss
    {s z g b1 b2 : Nat}
    (hchain : WideBoundarySouthwestExactChain
      s (z - 1) g b1 b2)
    (_hg : g < s) (hb1 : b1 < s + 1)
    (hdiag2 : gameF (s + 2) (s + 2) = z)
    (hdiag3 : gameF (s + 3) (s + 3) = z - 1) :
    WideBoundarySouthwestFirstEchoLoss s (z - 1) b1 b2 := by
  rcases hchain with
    ⟨_hgThree, hb1Eq, hb2Eq,
      _hhost0, hhost1, _hhost2, _hmex0, _hmex1, hmex2,
      _hperm0, _hperm1, _hperm2⟩
  have hbStep : b2 + 1 = b1 := by omega
  have hpHigh3 : s + 3 < z - 1 := by
    have hgt := gameRecurrenceModel.diagonal_gt (s + 3)
    change s + 3 < gameF (s + 3) (s + 3) at hgt
    rw [hdiag3] at hgt
    exact hgt
  have hpHigh1 : s + 1 < z - 1 := by omega
  have hnext1 : gameF (s + 2) (s + 2) <= (z - 1) + 1 := by
    rw [hdiag2]
    omega
  rcases gameF_slow_next_diagonal_forces_prefix_echo
      hb1 hhost1 hpHigh1 hnext1 with
    ⟨a1, ha1, heq1, hlo1, hhi1, habs1⟩
  let e := gameF (s + 2) b1
  have hePos : 0 < e := by
    change 0 < gameF (s + 2) b1
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlo1
  have heLt : e < z - 1 := by simpa [e] using hhi1
  have heHere : B gameF (s + 2) b2 e := by
    exact hmex2.2.2 e hePos heLt
  have heLost : Not (B gameF (s + 2) (b2 + 1) e) := by
    simpa [e, hbStep] using habs1
  have hstrict := source_loss_has_strict_parked_host
    gameRecurrenceModel heHere heLost
  have hopen := source_loss_future_opening_normal_form
    gameRecurrenceModel heHere heLost
  change WideBoundarySouthwestFirstEchoLoss s (z - 1) b1 b2
  dsimp only [WideBoundarySouthwestFirstEchoLoss]
  refine ⟨hbStep, by simpa [e] using hlo1, heLt,
    heHere, heLost, hstrict.2, ?_⟩
  rcases hopen with hopenD | hopenS
  · rcases hopenD with ⟨i, hbi, hie, hiOwner⟩
    exact Or.inl ⟨i, hbi, hie, hiOwner⟩
  · rcases hopenS with ⟨r, hbr, hre, hrStart⟩
    exact Or.inr ⟨r, hbr, hre, hrStart⟩

#print axioms gameF_slow_next_diagonal_forces_prefix_echo
#print axioms exact_source_forbids_low_owner_low_host
#print axioms exact_source_echo_owner_or_host_reaches_cut
#print axioms eventE_third_dip_boundary_forces_double_prefix_echo
#print axioms wideBoundary_southwest_chain_forces_distinct_echo_cascade
#print axioms wideBoundary_southwest_chain_first_echo_is_strict_source_loss

end ChompLean
