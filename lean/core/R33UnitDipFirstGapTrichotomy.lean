import DipZRehostRM2Reduction
import PrefreezeHostDiagonalCriterion
import R32TerminalSubUBackfillReduction

set_option autoImplicit false

namespace ChompLean

/-!
R33: the exact first-gap anatomy of a non-unit diagonal dip.

Put `z = d(s+1)+1`.  If `z<d(s)`, opening completeness gives either a
diagonal owner or a row-start owner for `z`.  Diagonal injectivity splits
the former into a genuinely past owner (`a<s`) or a genuinely future owner
(`s+1<a`).  In the future-owner case, `z` is present in the old diagonal
source and absent from the new one.

In the row-start case, `rowstart_hosted_iff_below_diagonal` gives the same
exact old-source/new-source loss.  Moreover row-start propagation forces the
freeze column to satisfy `s+1 <= r`: an earlier freeze would already rehost
`z` on row `s+1`.  Thus this branch is precisely a one-row pre-freeze late
blocker/service failure, in the same vocabulary as the R24--R32 residuals.

Everything through the main trichotomy and the exact `UnitDip` equivalence
uses only `RecurrenceModel`; it does not assume RM2.  A final, separately
named specialization shows what RM2 would eliminate.  That specialization
is logically downstream of RM2 and must not be used in the
`UnitDip + ZRehost -> RM2` proof.
-/

/-- The least integer strictly above the lower diagonal at a proposed dip. -/
def DipFirstGap (M : RecurrenceModel) (s : Nat) : Nat :=
  M.f (s + 1) (s + 1) + 1

/-- A non-unit dip whose first gap is an earlier diagonal value. -/
def DipFirstGapPastDiagonal (M : RecurrenceModel) (s : Nat) : Prop :=
  DipFirstGap M s < M.f s s /\
    exists a, a < s /\ M.f a a = DipFirstGap M s

/-- A non-unit dip whose first gap has a future diagonal owner and undergoes
an exact loss between the two consecutive diagonal sources. -/
def DipFirstGapFutureDiagonalLoss
    (M : RecurrenceModel) (s : Nat) : Prop :=
  DipFirstGap M s < M.f s s /\
    exists a,
      s + 1 < a /\
      M.f a a = DipFirstGap M s /\
      C M.f s s (DipFirstGap M s) /\
      Not (B M.f (s + 1) (s + 1) (DipFirstGap M s))

/-- A non-unit dip whose first gap is a not-yet-active row-start value.  It
was hosted on row `s`, is absent from the whole next diagonal source, and
its freeze column is at or to the right of row `s+1`. -/
def DipFirstGapLateBlockerLoss
    (M : RecurrenceModel) (s : Nat) : Prop :=
  DipFirstGap M s < M.f s s /\
    exists r,
      s + 1 <= r /\
      r < DipFirstGap M s /\
      M.f (DipFirstGap M s) r = DipFirstGap M s /\
      C M.f s s (DipFirstGap M s) /\
      Not (B M.f (s + 1) (s + 1) (DipFirstGap M s))

/-- A future diagonal value strictly between two consecutive diagonals is
an exact old-to-new diagonal-source loss.  This is game-native and does not
use RM2. -/
theorem future_diagonal_between_consecutive_diagonals_is_exact_loss
    (M : RecurrenceModel) {s z a : Nat}
    (hzPos : 0 < z)
    (hzOld : z < M.f s s)
    (hzNew : M.f (s + 1) (s + 1) < z)
    (haFuture : s + 1 < a)
    (haOwner : M.f a a = z) :
    C M.f s s z /\ Not (B M.f (s + 1) (s + 1) z) := by
  have hOldB : B M.f s s z :=
    M.mex_no_skip (Nat.le_refl s) (M.diagonal_gt s) hzPos hzOld
  have hOldC : C M.f s s z := by
    rcases hOldB with hR | hC
    · rcases hR with ⟨i, his, hvalue⟩
      have hisLe : i <= s := Nat.le_of_lt his
      have hiOwner : M.f i i = z := by
        simpa [Nat.min_eq_left hisLe] using hvalue
      have hia : i = a :=
        diagonal_injective M (hiOwner.trans haOwner.symm)
      omega
    · exact hC
  refine ⟨hOldC, ?_⟩
  intro hNewB
  rcases hNewB with hR | hC
  · rcases hR with ⟨i, hi, hvalue⟩
    have hiLe : i <= s + 1 := Nat.le_of_lt hi
    have hiOwner : M.f i i = z := by
      simpa [Nat.min_eq_left hiLe] using hvalue
    have hia : i = a :=
      diagonal_injective M (hiOwner.trans haOwner.symm)
    omega
  · rcases hC with ⟨b, hb, hhost⟩
    have hmax : M.f (s + 1) b <= M.f (s + 1) (s + 1) :=
      diagonalMaximal M (Nat.le_of_lt hb)
    rw [hhost] at hmax
    omega

/-- A blocker strictly between two consecutive diagonals is an exact
pre-freeze late-blocker loss.  The hosting/missing assertions are the exact
two directions of `rowstart_hosted_iff_below_diagonal`; the late-freeze
bound follows from `rowStartPropagation`. -/
theorem blocker_between_consecutive_diagonals_is_exact_late_loss
    (M : RecurrenceModel) {s z r : Nat}
    (hzOld : z < M.f s s)
    (hzNew : M.f (s + 1) (s + 1) < z)
    (hrz : r < z) (hstart : M.f z r = z) :
    s + 1 <= r /\
      C M.f s s z /\
      Not (B M.f (s + 1) (s + 1) z) := by
  have hOldC : C M.f s s z :=
    (rowstart_hosted_iff_below_diagonal M hrz hstart).2
      (Nat.le_of_lt hzOld)
  have hNewC : Not (C M.f (s + 1) (s + 1) z) :=
    (rowstart_missing_iff_above_diagonal M hrz hstart).2 hzNew
  have hNewB : Not (B M.f (s + 1) (s + 1) z) := by
    intro hB
    rcases hB with hR | hC
    · rcases hR with ⟨a, ha, hvalue⟩
      have haLe : a <= s + 1 := Nat.le_of_lt ha
      have haOwner : M.f a a = z := by
        simpa [Nat.min_eq_left haLe] using hvalue
      exact disjoint_D_S M ⟨a, haOwner⟩ ⟨r, hrz, hstart⟩
    · exact hNewC hC
  have htz : s + 1 < z := by
    have hdiag := M.diagonal_gt (s + 1)
    omega
  have hrLate : s + 1 <= r := by
    apply Nat.le_of_not_gt
    intro hrEarly
    rcases rowStartPropagation M hstart hrz hrEarly htz with
      ⟨b, hbr, hhost⟩
    exact hNewC ⟨b, by omega, hhost⟩
  exact ⟨hrLate, hOldC, hNewB⟩

/-- Main game-native trichotomy.  Every non-unit dip is witnessed at its
first gap by exactly one of the three proof-relevant species: a past
diagonal, a future-diagonal source loss, or a late-blocker source loss. -/
theorem nonunit_dip_first_gap_trichotomy
    (M : RecurrenceModel) {s : Nat}
    (hgap : DipFirstGap M s < M.f s s) :
    DipFirstGapPastDiagonal M s \/
      DipFirstGapFutureDiagonalLoss M s \/
      DipFirstGapLateBlockerLoss M s := by
  let z := DipFirstGap M s
  have hzPos : 0 < z := by
    dsimp [z, DipFirstGap]
    omega
  rcases M.opening_cover hzPos with hDiagonal | hRowStart
  · rcases hDiagonal with ⟨a, _haz, haOwner⟩
    by_cases haPast : a < s
    · left
      change z < M.f s s /\ exists i, i < s /\ M.f i i = z
      exact ⟨hgap, a, haPast, haOwner⟩
    · have hzNew : M.f (s + 1) (s + 1) < z := by
        dsimp [z, DipFirstGap]
        omega
      have haNeS : a ≠ s := by
        intro ha
        subst a
        rw [haOwner] at hgap
        omega
      have haNeNext : a ≠ s + 1 := by
        intro ha
        subst a
        rw [haOwner] at hzNew
        omega
      have haFuture : s + 1 < a := by omega
      have hloss :=
        future_diagonal_between_consecutive_diagonals_is_exact_loss
          M hzPos hgap hzNew haFuture haOwner
      right
      left
      change z < M.f s s /\
        exists i, s + 1 < i /\ M.f i i = z /\
          C M.f s s z /\ Not (B M.f (s + 1) (s + 1) z)
      exact ⟨hgap, a, haFuture, haOwner, hloss.1, hloss.2⟩
  · rcases hRowStart with ⟨r, hrz, hstart⟩
    have hzNew : M.f (s + 1) (s + 1) < z := by
      dsimp [z, DipFirstGap]
      omega
    have hloss :=
      blocker_between_consecutive_diagonals_is_exact_late_loss
        M hgap hzNew hrz hstart
    right
    right
    change z < M.f s s /\
      exists r', s + 1 <= r' /\ r' < z /\ M.f z r' = z /\
        C M.f s s z /\ Not (B M.f (s + 1) (s + 1) z)
    exact ⟨hgap, r, hloss.1, hrz, hstart, hloss.2.1, hloss.2.2⟩

/-- The three certificates are pairwise disjoint: past and future diagonal
owners conflict with diagonal injectivity, while either diagonal species
conflicts with a row-start species by `D`/`S` disjointness. -/
theorem dip_first_gap_obstructions_pairwise_disjoint
    (M : RecurrenceModel) (s : Nat) :
    Not (DipFirstGapPastDiagonal M s /\
      DipFirstGapFutureDiagonalLoss M s) /\
    Not (DipFirstGapPastDiagonal M s /\
      DipFirstGapLateBlockerLoss M s) /\
    Not (DipFirstGapFutureDiagonalLoss M s /\
      DipFirstGapLateBlockerLoss M s) := by
  constructor
  · rintro ⟨hPast, hFuture⟩
    rcases hPast.2 with ⟨a, haPast, haOwner⟩
    rcases hFuture.2 with ⟨a', haFuture, haOwner', _⟩
    have haa' : a = a' :=
      diagonal_injective M (haOwner.trans haOwner'.symm)
    omega
  · constructor
    · rintro ⟨hPast, hBlocker⟩
      rcases hPast.2 with ⟨a, _haPast, haOwner⟩
      rcases hBlocker.2 with
        ⟨r, _hrLate, hrz, hstart, _hOld, _hNew⟩
      exact disjoint_D_S M ⟨a, haOwner⟩ ⟨r, hrz, hstart⟩
    · rintro ⟨hFuture, hBlocker⟩
      rcases hFuture.2 with
        ⟨a, _haFuture, haOwner, _hOldD, _hNewD⟩
      rcases hBlocker.2 with
        ⟨r, _hrLate, hrz, hstart, _hOldS, _hNewS⟩
      exact disjoint_D_S M ⟨a, haOwner⟩ ⟨r, hrz, hstart⟩

/-- Every dip is either unit depth or has one of the three first-gap
certificates. -/
theorem dip_is_unit_or_first_gap_trichotomy
    (M : RecurrenceModel) {s : Nat}
    (hdip : M.f (s + 1) (s + 1) < M.f s s) :
    M.f (s + 1) (s + 1) + 1 = M.f s s \/
      DipFirstGapPastDiagonal M s \/
      DipFirstGapFutureDiagonalLoss M s \/
      DipFirstGapLateBlockerLoss M s := by
  by_cases hunit : M.f (s + 1) (s + 1) + 1 = M.f s s
  · exact Or.inl hunit
  · right
    have hgap : DipFirstGap M s < M.f s s := by
      dsimp [DipFirstGap]
      omega
    exact nonunit_dip_first_gap_trichotomy M hgap

/-- Exact reduction of the open `UnitDip` law to exclusion of the three
first-gap obstructions.  No RM2 assumption occurs here. -/
theorem unitDip_iff_no_first_gap_obstructions (M : RecurrenceModel) :
    UnitDip M <->
      forall s,
        Not (DipFirstGapPastDiagonal M s) /\
        Not (DipFirstGapFutureDiagonalLoss M s) /\
        Not (DipFirstGapLateBlockerLoss M s) := by
  constructor
  · intro hUnit s
    have hnoGap (hgap : DipFirstGap M s < M.f s s) : False := by
      have hdip : M.f (s + 1) (s + 1) < M.f s s := by
        dsimp [DipFirstGap] at hgap
        omega
      have heq := hUnit s hdip
      dsimp [DipFirstGap] at hgap
      omega
    constructor
    · intro h
      exact hnoGap h.1
    · constructor
      · intro h
        exact hnoGap h.1
      · intro h
        exact hnoGap h.1
  · intro hNo s hdip
    by_cases hunit : M.f (s + 1) (s + 1) + 1 = M.f s s
    · exact hunit
    · have hgap : DipFirstGap M s < M.f s s := by
        dsimp [DipFirstGap]
        omega
      rcases nonunit_dip_first_gap_trichotomy M hgap with
        hPast | hFuture | hBlocker
      · exact False.elim ((hNo s).1 hPast)
      · exact False.elim ((hNo s).2.1 hFuture)
      · exact False.elim ((hNo s).2.2 hBlocker)

/-- If the first gap has no diagonal owner, the unconditional trichotomy
collapses all the way to the local late-blocker/service-loss atom. -/
theorem nonunit_dip_without_diagonal_first_gap_is_late_blocker_loss
    (M : RecurrenceModel) {s : Nat}
    (hgap : DipFirstGap M s < M.f s s)
    (hNoDiagonal : forall a, M.f a a ≠ DipFirstGap M s) :
    DipFirstGapLateBlockerLoss M s := by
  rcases nonunit_dip_first_gap_trichotomy M hgap with
    hPast | hFuture | hBlocker
  · rcases hPast.2 with ⟨a, _ha, haOwner⟩
    exact False.elim (hNoDiagonal a haOwner)
  · rcases hFuture.2 with ⟨a, _ha, haOwner, _⟩
    exact False.elim (hNoDiagonal a haOwner)
  · exact hBlocker

/-- RM2-only specialization: RM2 rules out the future-diagonal branch, so
a non-unit dip leaves a past diagonal first gap or the local late-blocker
loss.  This theorem records the dependency explicitly; using it to prove
`UnitDip` on the route `UnitDip + ZRehost -> RM2` would be circular. -/
theorem nonunit_dip_first_gap_of_rm2_is_past_or_late_blocker
    (M : RecurrenceModel) {s : Nat}
    (hRM2 : TwoStepDiagonalRecordLaw M)
    (hgap : DipFirstGap M s < M.f s s) :
    DipFirstGapPastDiagonal M s \/
      DipFirstGapLateBlockerLoss M s := by
  rcases nonunit_dip_first_gap_trichotomy M hgap with
    hPast | hFuture | hBlocker
  · exact Or.inl hPast
  · rcases hFuture.2 with
      ⟨a, haFuture, haOwner, _hOld, _hNew⟩
    have hrecord : M.f s s < M.f a a := hRM2 (by omega)
    rw [haOwner] at hrecord
    omega
  · exact Or.inr hBlocker

end ChompLean
