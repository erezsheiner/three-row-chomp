import R43FutureDiagonalSourceCapacityCollapse
import R40FutureDiagonalPrehostCharge
import EventEPacketSourceCapacity
import R56NeverVanish
import R69Arc24Correction
import DipZRehostRM2IndependentAudit
import R41DelayedPredecessorStructure
import R183Lag8DynamicHighLateOwner

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ChompLean

/-!
# R184: the future-diagonal pin — unconditional geometry, four named atoms,
and the conditional deep-cell theorem

Target (A2 / `FutureDiagonalPin`): an off-diagonal cell can equal a
present-or-future diagonal value only as the penultimate one-row preplay
`t = q+1`, `c = q-1`.

This file proves unconditionally:

* `futureDiagonal_not_same_row` — the `t = q` slice;
* `futureDiagonal_owner_window` — **owner-delay ≤ host-column**:
  `t+1 ≤ F(q,c) ≤ q+c+1`, hence `t ≤ q+c`.  New sharp band: for a deep
  host the owner cannot be far, and column `0` never previews any
  present-or-future diagonal;
* `dip_twin_preview` — **twin preview at a dip**: when `D(u+1) < D(u)`,
  both the incoming diagonal value `D(u+1)` and the incoming first hole
  `V1(u+1)` were already hosted in the strict prefix of row `u`, as
  values `≥ u+1`, at two distinct columns (receipts: 53/53 dips in
  `F4000`, zero violations).

The deep theorem itself is assembled from four *named, receipt-clean,
mutually non-circular atoms* by strong induction on the owner delay
(`noDeepFutureDiagonal_of_atoms`).  Conditional corollaries:
`NoInteriorEaten` (from atom A alone), the location pin `t=q+1 ∧ c=q-1`,
`NoDelayedDiagonalPredecessor`, and the collapse of the future-diagonal
arm of the R183 chronology (`..._dichotomy_of_atoms`).

None of RM2 / UnitDip / NIE / FC is assumed anywhere; atom A is exactly
the spatial NIE, atoms B and D are strictly weaker localized fragments of
RM2, and atom C is the delayed penultimate echo (the R72 HOLD arm).
-/

/-! ## 1. The same-row slice -/

/-- An off-diagonal cell never equals its own row's diagonal. -/
theorem futureDiagonal_not_same_row
    (M : RecurrenceModel) {q c : Nat} (hcq : c < q)
    (heq : M.f q c = M.f q q) : False := by
  have h := M.fixed_q_injective (Nat.le_of_lt hcq) (Nat.le_refl q) heq
  omega

/-! ## 2. Owner-delay is at most the host column -/

/-- **Owner window.**  A strictly-future diagonal previewed at `(q,c)`
pins three inequalities: `t+1 ≤ F(q,c)`, `F(q,c) ≤ q+c+1`, and hence the
owner-distance bound `t ≤ q+c`.  Sharper than the R43 band `t+1 ≤ 2q`
whenever the host is deep. -/
theorem futureDiagonal_owner_window
    (M : RecurrenceModel) {q c t : Nat}
    (hcq : c < q) (hqt : q < t)
    (heq : M.f q c = M.f t t) :
    t + 1 <= M.f q c /\ M.f q c <= q + c + 1 /\ t <= q + c := by
  have hdt : t < M.f t t := M.diagonal_gt t
  have h1 : t + 1 <= M.f q c := by rw [heq]; omega
  have hqm : q < M.f q c := by omega
  have hcap := high_cell_output_source_capacity M
      (r := c) (q := q) (m := M.f q c) (Nat.le_of_lt hcq) hqm rfl
  exact ⟨h1, by omega, by omega⟩

/-- Delay is at most the host column (weak form covering `t = q`). -/
theorem futureDiagonal_owner_row_le_row_add_column
    (M : RecurrenceModel) {q c t : Nat}
    (hcq : c < q) (hqt : q <= t)
    (heq : M.f q c = M.f t t) :
    t <= q + c := by
  by_cases hqt' : t = q
  · omega
  · have hband := futureDiagonal_owner_window M hcq (by omega) heq
    omega

/-- Column `0` never hosts a present-or-future diagonal value. -/
theorem no_futureDiagonal_in_column_zero
    (M : RecurrenceModel) {q t : Nat}
    (h0q : 0 < q) (hqt : q <= t)
    (heq : M.f q 0 = M.f t t) : False := by
  have hb := futureDiagonal_owner_row_le_row_add_column M h0q hqt heq
  have ht : t = q := by omega
  subst ht
  exact futureDiagonal_not_same_row M h0q heq

/-! ## 3. Twin preview at a diagonal dip -/

/-- **Twin preview.**  At every diagonal dip `D(u+1) < D(u)`, BOTH the
incoming diagonal value `v = D(u+1)` and the incoming first hole
`y = V1(u+1)` were already hosted in the strict prefix of row `u`, at
two distinct columns; moreover `u+1 ≤ y < v`.

The `v` half is the classical preview; the `y` half is new: `y` cannot
be an old diagonal (`diagonal_general_no_attack` at `(u+1, u)`), cannot
be `D(u)` (it is below the dip), and cannot be small (a small value
would carry into row `u+1` and re-enter the source of `(u+1,u)`). -/
theorem dip_twin_preview
    (M : RecurrenceModel) {u : Nat}
    (hdip : M.f (u + 1) (u + 1) < M.f u u) :
    M.f (u + 1) u < M.f (u + 1) (u + 1) /\
    u + 1 <= M.f (u + 1) u /\
    (exists cv, cv < u /\ M.f u cv = M.f (u + 1) (u + 1)) /\
    (exists b, b < u /\ M.f u b = M.f (u + 1) u /\
      M.f u b ≠ M.f (u + 1) (u + 1)) := by
  have hvgt : u + 1 < M.f (u + 1) (u + 1) := M.diagonal_gt (u + 1)
  have hugt : u < M.f u u := M.diagonal_gt u
  have hyle : M.f (u + 1) u <= M.f (u + 1) (u + 1) :=
    diagonalMaximal M (by omega)
  have hylt : M.f (u + 1) u < M.f (u + 1) (u + 1) := by
    rcases Nat.lt_or_ge (M.f (u + 1) u) (M.f (u + 1) (u + 1)) with h | h
    · exact h
    · exfalso
      have heq : M.f (u + 1) u = M.f (u + 1) (u + 1) := by omega
      have := M.fixed_q_injective (q := u + 1)
        (by omega) (Nat.le_refl (u + 1)) heq
      omega
  -- the incoming first hole is absent from its own source set
  have hyNotB : Not (B M.f (u + 1) u (M.f (u + 1) u)) := by
    intro hB
    rcases hB with hR | hC
    · rcases hR with ⟨a, ha, hval⟩
      have hau : a <= u := by omega
      rw [Nat.min_eq_left hau] at hval
      by_cases hau' : a = u
      · subst hau'
        omega
      · exact M.diagonal_general_no_attack
          (i := a) (s := u) (q := u + 1) (by omega) (by omega) hval
    · rcases hC with ⟨b, hb, hval⟩
      have := M.fixed_q_injective (q := u + 1) (by omega) (by omega) hval
      omega
  -- it is nevertheless blocked at the old diagonal, via the row prefix
  have hyPos : 0 < M.f (u + 1) u := by
    have h := M.value_gt_index (q := u + 1) (r := u) (by omega)
    omega
  have hyB : B M.f u u (M.f (u + 1) u) :=
    M.mex_no_skip (Nat.le_refl u) hugt hyPos (by omega)
  have hyC : C M.f u u (M.f (u + 1) u) := by
    rcases hyB with hR | hC
    · exfalso
      apply hyNotB
      rcases hR with ⟨a, ha, hval⟩
      exact Or.inl ⟨a, by omega, hval⟩
    · exact hC
  rcases hyC with ⟨b, hbu, hbval⟩
  -- and it is large: a small value would carry into row u+1
  have hyBig : u + 1 <= M.f (u + 1) u := by
    rcases Nat.lt_or_ge (M.f (u + 1) u) (u + 1) with hsmall | hbig
    · exfalso
      apply hyNotB
      have hcarry : M.f (u + 1) b = M.f u b :=
        M.constant_step (by omega) (by rw [hbval]; omega)
      exact Or.inr ⟨b, by omega, by rw [hcarry, hbval]⟩
    · exact hbig
  -- the incoming diagonal value was previewed in the old row prefix
  have hvB : B M.f u u (M.f (u + 1) (u + 1)) :=
    M.mex_no_skip (Nat.le_refl u) hugt (by omega) hdip
  have hvC : C M.f u u (M.f (u + 1) (u + 1)) := by
    rcases hvB with hR | hC
    · exfalso
      rcases hR with ⟨a, ha, hval⟩
      have hau : a <= u := by omega
      rw [Nat.min_eq_left hau] at hval
      have := diagonal_injective M hval
      omega
    · exact hC
  rcases hvC with ⟨cv, hcvu, hcvval⟩
  exact ⟨hylt, hyBig, ⟨cv, hcvu, hcvval⟩,
    ⟨b, hbu, hbval, by rw [hbval]; omega⟩⟩

/-- Twin preview for the actual game. -/
theorem gameF_dip_twin_preview {u : Nat}
    (hdip : gameF (u + 1) (u + 1) < gameF u u) :
    gameF (u + 1) u < gameF (u + 1) (u + 1) /\
    u + 1 <= gameF (u + 1) u /\
    (exists cv, cv < u /\ gameF u cv = gameF (u + 1) (u + 1)) /\
    (exists b, b < u /\ gameF u b = gameF (u + 1) u /\
      gameF u b ≠ gameF (u + 1) (u + 1)) :=
  dip_twin_preview gameRecurrenceModel hdip

/-! ## 4. The four residual atoms

All four are receipt-clean on `F4000` with the owner horizon closed by
the long diagonal cache (rows to 136,558): atom A has 0 violations on
4,736,042 active cells (the census hits are all `c = q-1`), atoms B and
D are localized fragments strictly weaker than RM2, atom C is the
delayed penultimate echo (all 53 observed penultimate previews have
delay exactly one).  None is assumed anywhere in Parts 1-3. -/

/-- Atom A — the delay-one deep kill.  This is exactly the spatial form
of `NoInteriorEaten`. -/
def DeepDelayOnePin : Prop :=
  forall q c : Nat, c + 1 < q -> gameF q c ≠ gameF (q + 1) (q + 1)

/-- Atom B — no future diagonal is sandwiched strictly between `D(q+1)`
and `D(q)` with owner delay at least two.  (RM2 would make this vacuous;
it is strictly weaker than RM2.) -/
def NoFutureSandwich : Prop :=
  forall q t : Nat, q + 2 <= t ->
    gameF (q + 1) (q + 1) < gameF t t -> gameF t t < gameF q q -> False

/-- Atom C — a penultimate (first-hole) preview has owner delay exactly
one: `V1(r+1) = F(r+1, r)` never equals a diagonal two or more rows
ahead.  (The R72 HOLD arm.) -/
def NoDelayedPenultimateEcho : Prop :=
  forall r t : Nat, r + 3 <= t -> gameF (r + 1) r ≠ gameF t t

/-- Atom D — at a dip the incoming diagonal value has no host two rows
back: if `D(u+2) < D(u+1)` then row `u` does not host `D(u+2)` strictly
left of its diagonal.  (A dip-localized fragment of RM2.) -/
def NoTwoBackPreview : Prop :=
  forall u b : Nat, gameF (u + 2) (u + 2) < gameF (u + 1) (u + 1) ->
    b < u -> gameF u b ≠ gameF (u + 2) (u + 2)

/-! ## 5. The deep theorem from the atoms -/

/-- **Deep-cell future-diagonal exclusion, modulo the four atoms.**
Strong induction on the owner delay `t - q`.  At delay `≥ 2` the row
`q+1` trichotomy either sandwiches the owner (atom B), collides with it
(diagonal injectivity), or re-hosts the value in row `q+1` — deeply
(induction), or at the penultimate seat, which atom C kills at delay
`≥ 3` and atom D kills at delay `2`. -/
theorem noDeepFutureDiagonal_of_atoms
    (hA : DeepDelayOnePin) (hB : NoFutureSandwich)
    (hC : NoDelayedPenultimateEcho) (hD : NoTwoBackPreview) :
    forall {q c t : Nat}, c + 1 < q -> q <= t ->
      gameF q c = gameF t t -> False := by
  have hP : forall d : Nat, forall q c t : Nat,
      c + 1 < q -> q <= t -> t - q = d ->
      gameF q c = gameF t t -> False := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro q c t hdeep hqt hdelay heq
      by_cases hqt0 : t = q
      · subst hqt0
        exact futureDiagonal_not_same_row gameRecurrenceModel
          (by omega) heq
      by_cases hqt1 : t = q + 1
      · subst hqt1
        exact hA q c hdeep heq
      have hqt2 : q + 2 <= t := by omega
      -- strict row maximality: the previewed value sits below D(q)
      have hvle : gameF q c <= gameF q q :=
        game_diagonal_maximal (by omega)
      have hvlt : gameF q c < gameF q q := by
        rcases Nat.lt_or_ge (gameF q c) (gameF q q) with h | h
        · exact h
        · exfalso
          have heqq : gameF q c = gameF q q := by omega
          exact futureDiagonal_not_same_row gameRecurrenceModel
            (by omega) heqq
      rcases Nat.lt_trichotomy (gameF (q + 1) (q + 1)) (gameF q c) with
        hlt | heq1 | hgt
      · -- the owner is sandwiched: atom B
        apply hB q t hqt2
        · rw [← heq]; exact hlt
        · rw [← heq]; exact hvlt
      · -- owner collision at q+1
        have hcol : q + 1 = t :=
          diagonal_injective gameRecurrenceModel (heq1.trans heq)
        omega
      · -- the value is re-hosted in row q+1
        rcases game_future_diagonal_below_row_has_interior_host
            (r := q + 1) (a := t) (by omega) heq.symm hgt with
          ⟨b, hb, hhost⟩
        by_cases hbdeep : b + 1 < q + 1
        · exact ih (t - (q + 1)) (by omega) (q + 1) b t hbdeep
            (by omega) rfl (hhost.trans heq)
        · have hbq : b = q := by omega
          rw [hbq] at hhost
          by_cases ht3 : q + 3 <= t
          · exact hC q t ht3 (hhost.trans heq)
          · have ht2 : t = q + 2 := by omega
            subst ht2
            exact hD q c (by rw [← heq]; exact hgt) (by omega) heq
  intro q c t hdeep hqt heq
  exact hP (t - q) q c t hdeep hqt rfl heq

/-! ## 6. Conditional corollaries -/

/-- Atom A alone already yields `NoInteriorEaten`: at a dip the incoming
diagonal value is non-past, hence previewed in the old row prefix (R56),
and the deep seats are forbidden, pinning the preview to `V1(q)`. -/
theorem noInteriorEaten_of_deepDelayOnePin
    (hA : DeepDelayOnePin) : NoInteriorEaten := by
  intro q hdip
  have hvPos : 0 < gameF (q + 1) (q + 1) := by
    have h := gameRecurrenceModel.diagonal_gt (q + 1)
    change q + 1 < gameF (q + 1) (q + 1) at h
    omega
  have hNonpast :
      Not (PastDiagonalValueBefore gameRecurrenceModel q
        (gameF (q + 1) (q + 1))) := by
    intro hpast
    rcases hpast with ⟨a, haq, hval⟩
    have hae : a = q + 1 := diagonal_injective gameRecurrenceModel hval
    omega
  have hCq := recurrence_nonpast_below_diagonal_strict_prefix
      gameRecurrenceModel hvPos hdip hNonpast
  rcases hCq with ⟨b, hbq, hval⟩
  by_cases hdeep : b + 1 < q
  · exact absurd hval (hA q b hdeep)
  · have hb : b = q - 1 := by omega
    subst hb
    show gameF (q + 1) (q + 1) = gameF q (q - 1)
    exact hval.symm

/-- The location half of the full pin, modulo the atoms: every
present-or-future diagonal preview sits at `(q, q-1)` with owner
`t = q+1`. -/
theorem gameF_futureDiagonal_location_of_atoms
    (hA : DeepDelayOnePin) (hB : NoFutureSandwich)
    (hC : NoDelayedPenultimateEcho) (hD : NoTwoBackPreview)
    {q c t : Nat} (hcq : c < q) (hqt : q <= t)
    (heq : gameF q c = gameF t t) :
    t = q + 1 /\ c = q - 1 := by
  have hcpin : c = q - 1 := by
    by_cases hdeep : c + 1 < q
    · exact absurd heq
        (fun h => noDeepFutureDiagonal_of_atoms hA hB hC hD hdeep hqt h)
    · omega
  refine ⟨?_, hcpin⟩
  by_cases hqt0 : t = q
  · exfalso
    subst hqt0
    exact futureDiagonal_not_same_row gameRecurrenceModel hcq heq
  by_cases ht1 : t = q + 1
  · exact ht1
  · exfalso
    have ht3 : (q - 1) + 3 <= t := by omega
    have hkey : gameF ((q - 1) + 1) (q - 1) = gameF t t := by
      have hidx : (q - 1) + 1 = q := by omega
      rw [hidx, ← hcpin]
      exact heq
    exact hC (q - 1) t ht3 hkey

/-- The delayed reverse-adjacent diagonal law, modulo the atoms: no
diagonal is one above a diagonal two or more rows ahead.  (R38's clean
chronology premise, obtained here without RM2.) -/
theorem noDelayedDiagonalPredecessor_of_atoms
    (hA : DeepDelayOnePin) (hB : NoFutureSandwich)
    (hC : NoDelayedPenultimateEcho) (hD : NoTwoBackPreview) :
    NoDelayedDiagonalPredecessor gameRecurrenceModel := by
  intro a t hat hEq
  have hloss := delayedDiagonalPredecessor_is_futurePrehostLoss
      gameRecurrenceModel hat hEq
  rcases hloss.2.2.1 with ⟨b, hba, hhost⟩
  have hpin := gameF_futureDiagonal_location_of_atoms hA hB hC hD
      hba (by omega) hhost
  omega

/-- Collapse of the R183 late-opening chronology to a dichotomy: modulo
the atoms, the future-diagonal arm is empty.  (In that arm the host cell
`(t, g-1)` is deep — `g < t` — and the owner `d` is strictly later, so
the deep theorem applies verbatim.) -/
theorem gameF_strictLateOpening_highHost_chronology_dichotomy_of_atoms
    (hA : DeepDelayOnePin) (hB : NoFutureSandwich)
    (hC : NoDelayedPenultimateEcho) (hD : NoTwoBackPreview)
    {t g Y : Nat}
    (hgpos : 0 < g) (hgt : g < t)
    (hhost : gameF t (g - 1) = Y)
    (hLate : Lag8StrictLateOpening g Y) :
    (exists d,
      g < d /\ d < t /\ gameF d d = Y /\
      gameF t (g - 1) = Y /\ Y <= d + d + 1) \/
    (exists s host,
      g < s /\ s < Y /\ gameF Y s = Y /\
      gameF t (g - 1) = Y /\ Y <= s + s + 1 /\
      TerminalRelayHallCertificate Y s host) := by
  rcases gameF_strictLateOpening_highHost_chronology
      hgpos hgt hhost hLate with h1 | h2 | h3
  · exact Or.inl h1
  · exfalso
    rcases h2 with ⟨d, htd, _hdY, hdd, _hloss, _hcap⟩
    exact noDeepFutureDiagonal_of_atoms hA hB hC hD
      (q := t) (c := g - 1) (t := d)
      (by omega) (by omega) (hhost.trans hdd.symm)
  · exact Or.inr h3

#print axioms futureDiagonal_not_same_row
#print axioms futureDiagonal_owner_window
#print axioms futureDiagonal_owner_row_le_row_add_column
#print axioms no_futureDiagonal_in_column_zero
#print axioms dip_twin_preview
#print axioms gameF_dip_twin_preview
#print axioms noDeepFutureDiagonal_of_atoms
#print axioms noInteriorEaten_of_deepDelayOnePin
#print axioms gameF_futureDiagonal_location_of_atoms
#print axioms noDelayedDiagonalPredecessor_of_atoms
#print axioms gameF_strictLateOpening_highHost_chronology_dichotomy_of_atoms

end ChompLean
