import ChompLean.Proof

set_option autoImplicit false

namespace ChompLean

/-!
R141: a direct audit of the BottomBarrier crossing port.

The first part proves the game-native form of CROSSING-SOURCE-EQUIVALENCE.
It also proves that, on the hypothetical range branch `d(t)=v`, neither a
same-row host nor a later frontier MEX host above the owner cutoff can equal
`v`.  Thus those host statements cannot be intermediate consequences of the
range branch: they are exactly what has to refute it.

The second part is a recurrence-interface counterframe.  It realizes both
predecessor-owner geometries with an arbitrary previous first hole `x`,
including both DROP (`x=q`) and PERSIST (`x!=q`).  In the owner-`t-2` branch
it also realizes the exact record/unit-dip/plus-one rebound.  This is not a
second Chomp table; it checks that the local source equations and the
critical arithmetic ledger still admit the bad crossing.
-/

/-- At a diagonal crossing, a not-yet-diagonal value is skipped exactly
when it has a strict current-row host.  This is the `RecurrenceModel` form of
R139's abstract source equivalence. -/
theorem crossing_skip_iff_strict_row_host
    (M : RecurrenceModel) {t v : Nat}
    (hv : 0 < v)
    (hCross : v <= M.f t t)
    (hNotPast : forall a, a < t -> M.f a a ≠ v) :
    v < M.f t t <-> exists e, e < t /\ M.f t e = v := by
  constructor
  · intro hvd
    have hB : B M.f t t v :=
      M.mex_no_skip (Nat.le_refl t) (M.diagonal_gt t) hv hvd
    cases hB with
    | inl hR =>
        rcases hR with ⟨a, hat, ha⟩
        have hmin : min a t = a := Nat.min_eq_left (Nat.le_of_lt hat)
        exact False.elim (hNotPast a hat (by simpa [hmin] using ha))
    | inr hC =>
        rcases hC with ⟨e, het, he⟩
        exact ⟨e, het, he⟩
  · rintro ⟨e, het, he⟩
    have hne : M.f t t ≠ v := by
      intro hdiag
      have hidx : e = t :=
        M.fixed_q_injective (Nat.le_of_lt het) (Nat.le_refl t)
          (he.trans hdiag.symm)
      omega
    omega

/-- If the crossing value is the diagonal itself, fixed-row injectivity
forbids any strict same-row copy. -/
theorem bad_diagonal_forbids_same_row_host
    (M : RecurrenceModel) {t e v : Nat}
    (het : e < t) (hdiag : M.f t t = v) :
    M.f t e ≠ v := by
  intro he
  have hidx : e = t :=
    M.fixed_q_injective (Nat.le_of_lt het) (Nat.le_refl t)
      (he.trans hdiag.symm)
  omega

/-- A diagonal owner at or to the left of a later source cutoff places its
value in that later source. -/
theorem diagonal_owner_le_cutoff_is_in_source
    (M : RecurrenceModel) {t h r v : Nat}
    (htr : t < r) (hth : t <= h) (hdiag : M.f t t = v) :
    B M.f r h v := by
  left
  refine ⟨t, htr, ?_⟩
  have hmin : min t h = t := Nat.min_eq_left hth
  simpa [hmin] using hdiag

/-- Hence a later live/MEX cell above that cutoff cannot re-emit the
diagonal value.  This is the exact obstruction to the proposed lag-three
frontier host on the hypothetical range branch. -/
theorem bad_diagonal_forbids_later_frontier_host
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f)
    {t h r v : Nat}
    (hth : t <= h) (hhr : h < r) (hrv : r < v)
    (hdiag : M.f t t = v) :
    M.f r h ≠ v := by
  intro hhost
  have hB : B M.f r h v :=
    diagonal_owner_le_cutoff_is_in_source M (by omega) hth hdiag
  have habs : Not (B M.f r h (M.f r h)) :=
    recurrence_mex_absent hrec (Nat.le_of_lt hhr) (by rw [hhost]; exact hrv)
  apply habs
  simpa [hhost] using hB

/-- Candidate-frontier specialization.  A RangeInD-style owner bound
`t <= a0-1`, combined with `a0-1 <= h`, makes every later frontier host
impossible on the bad diagonal branch. -/
theorem bad_diagonal_forbids_candidate_frontier_host
    (M : RecurrenceModel) (hrec : BrouwerRecurrence M.f)
    {t a0 h r v : Nat}
    (htFrontier : t <= a0 - 1)
    (hFrontier : a0 - 1 <= h)
    (hhr : h < r) (hrv : r < v)
    (hdiag : M.f t t = v) :
    M.f r h ≠ v := by
  exact bad_diagonal_forbids_later_frontier_host M hrec
    (Nat.le_trans htFrontier hFrontier) hhr hrv hdiag

/-- A future blocker which is missing from a current source must freeze
strictly to the right of that source cutoff.  This is the exact freeze
localization of the final blocker hole on a bad crossing. -/
theorem missing_future_rowstart_forces_freeze_right
    (M : RecurrenceModel) {t c q r : Nat}
    (hct : c < t) (htq : t < q)
    (hrq : r < q) (hstart : M.f q r = q)
    (hmissing : Not (B M.f t c q)) :
    c < r := by
  by_cases hcr : c < r
  · exact hcr
  · have hrc : r <= c := Nat.le_of_not_gt hcr
    have hrt : r < t := Nat.lt_of_le_of_lt hrc hct
    rcases rowStartPropagation M hstart hrq hrt htq with ⟨b, hbr, hb⟩
    apply False.elim (hmissing (Or.inr ?_))
    exact ⟨b, Nat.lt_of_lt_of_le hbr hrc, hb⟩

/-- In particular, a future blocker emitted as the current V1/final hole
cannot have an earlier or equal freeze column. -/
theorem future_v1_hole_forces_late_freeze
    (M : RecurrenceModel) {t q r : Nat}
    (ht : 0 < t) (htq : t < q)
    (hrq : r < q) (hstart : M.f q r = q)
    (hV1Mex : IsMex (B M.f t (t - 1)) q) :
    t - 1 < r := by
  apply missing_future_rowstart_forces_freeze_right M (by omega) htq hrq hstart
  exact hV1Mex.2.1

/-! ## Parametric top-two source counterframes -/

/-- Previous `V1` source: every positive value below `l` except `x`. -/
def PrevSource (x l z : Nat) : Prop :=
  0 < z /\ z < l /\ z ≠ x

/-- The common current-row core, with precisely the three named holes. -/
def CrossingCore (bound y q l z : Nat) : Prop :=
  0 < z /\ z < bound /\ z ≠ y /\ z ≠ q /\ z ≠ l

theorem prevSource_mex
    {x l : Nat} (hx : 0 < x) (hxl : x < l) :
    IsMex (PrevSource x l) x := by
  refine ⟨hx, ?_, ?_⟩
  · intro h
    exact h.2.2 rfl
  · intro z hz hzx
    exact ⟨hz, Nat.lt_trans hzx hxl, by omega⟩

theorem prevSource_insert_mex
    {x l : Nat} (hx : 0 < x) (hxl : x < l) :
    IsMex (fun z => PrevSource x l z \/ z = x) l := by
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    rcases h with h | h
    · exact (Nat.lt_irrefl l h.2.1).elim
    · omega
  · intro z hz hzl
    by_cases hzx : z = x
    · exact Or.inr hzx
    · exact Or.inl ⟨hz, hzl, hzx⟩

/-- The V2 source has least hole `y`, whether the previous V1 `x` is the
later hole `q` (DROP) or is already in the common core (PERSIST). -/
theorem crossingCore_v2_mex
    {bound x y q l : Nat}
    (hy : 0 < y) (hyq : y < q) (hql : q < l)
    (hlb : l < bound) (hxne : x ≠ y) :
    IsMex (fun z => CrossingCore bound y q l z \/ z = x) y := by
  refine ⟨hy, ?_, ?_⟩
  · intro h
    rcases h with h | h
    · exact h.2.2.1 rfl
    · exact hxne h.symm
  · intro z hz hzy
    left
    refine ⟨hz, Nat.lt_trans hzy (Nat.lt_trans hyq (Nat.lt_trans hql hlb)), ?_⟩
    exact ⟨by omega, by omega, by omega⟩

/-- After adjoining the newest diagonal `l` and V2 value `y`, the unique
least hole is `q`. -/
theorem crossingCore_v1_mex
    {bound y q l : Nat}
    (hy : 0 < y) (hyq : y < q) (hql : q < l) (hlb : l < bound) :
    IsMex (fun z => CrossingCore bound y q l z \/ z = l \/ z = y) q := by
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    rcases h with h | h
    · exact h.2.2.2.1 rfl
    · rcases h with h | h <;> omega
  · intro z hz hzq
    by_cases hzy : z = y
    · exact Or.inr (Or.inr hzy)
    · left
      refine ⟨hz, Nat.lt_trans hzq (Nat.lt_trans hql hlb), hzy, ?_⟩
      exact ⟨by omega, by omega⟩

/-- Once the V1 hole `q` is adjoined, the diagonal sees the entire positive
initial segment below `bound`. -/
theorem crossingCore_diagonal_mex
    {bound y q l : Nat}
    (hy : 0 < y) (hyq : y < q) (hql : q < l) (hlb : l < bound) :
    IsMex
      (fun z => CrossingCore bound y q l z \/ z = l \/ z = y \/ z = q)
      bound := by
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    rcases h with h | h
    · exact (Nat.lt_irrefl bound h.2.1).elim
    · rcases h with h | h
      · omega
      · rcases h with h | h <;> omega
  · intro z hz hzb
    by_cases hzl : z = l
    · exact Or.inr (Or.inl hzl)
    by_cases hzy : z = y
    · exact Or.inr (Or.inr (Or.inl hzy))
    by_cases hzq : z = q
    · exact Or.inr (Or.inr (Or.inr hzq))
    · exact Or.inl ⟨hz, hzb, hzy, hzq, hzl⟩

/-- DROP and PERSIST are both admitted by the same parametric source frame:
`x=q` makes the previous V1 the final missing core value; `x!=q` (with the
displayed order) puts it in the core already. -/
theorem crossingCore_drop_or_persist
    {bound x y q l : Nat}
    (hx : 0 < x) (hxl : x < l) (hxne : x ≠ y)
    (hlb : l < bound) :
    (x = q -> Not (CrossingCore bound y q l x)) /\
    (x ≠ q -> CrossingCore bound y q l x) := by
  constructor
  · intro hxq hcore
    exact hcore.2.2.2.1 hxq
  · intro hxq
    exact ⟨hx, Nat.lt_trans hxl hlb, hxne, hxq, by omega⟩

/-- Owner `t-1` bad-crossing source frame: previous diagonal `l=v-1`,
then the bad diagonal `v=l+1`. -/
theorem owner_one_bad_crossing_frame
    {x y q l : Nat}
    (hx : 0 < x) (hxl : x < l) (hxne : x ≠ y)
    (hy : 0 < y) (hyq : y < q) (hql : q < l) :
    IsMex (PrevSource x l) x /\
    IsMex (fun z => PrevSource x l z \/ z = x) l /\
    IsMex (fun z => CrossingCore (l + 1) y q l z \/ z = x) y /\
    IsMex (fun z => CrossingCore (l + 1) y q l z \/ z = l \/ z = y) q /\
    IsMex
      (fun z => CrossingCore (l + 1) y q l z \/ z = l \/ z = y \/ z = q)
      (l + 1) := by
  exact ⟨prevSource_mex hx hxl, prevSource_insert_mex hx hxl,
    crossingCore_v2_mex hy hyq hql (by omega) hxne,
    crossingCore_v1_mex hy hyq hql (by omega),
    crossingCore_diagonal_mex hy hyq hql (by omega)⟩

/-- Owner `t-2` bad-crossing source frame: record `l+1`, unit dip to the
previous diagonal `l`, and bad plus-one rebound to `l+2`.  The old record is
already in the common core. -/
theorem owner_two_bad_crossing_frame
    {x y q l : Nat}
    (hx : 0 < x) (hxl : x < l) (hxne : x ≠ y)
    (hy : 0 < y) (hyq : y < q) (hql : q < l) :
    IsMex (PrevSource x l) x /\
    IsMex (fun z => PrevSource x l z \/ z = x) l /\
    CrossingCore (l + 2) y q l (l + 1) /\
    IsMex (fun z => CrossingCore (l + 2) y q l z \/ z = x) y /\
    IsMex (fun z => CrossingCore (l + 2) y q l z \/ z = l \/ z = y) q /\
    IsMex
      (fun z => CrossingCore (l + 2) y q l z \/ z = l \/ z = y \/ z = q)
      (l + 2) := by
  refine ⟨prevSource_mex hx hxl, prevSource_insert_mex hx hxl, ?_,
    crossingCore_v2_mex hy hyq hql (by omega) hxne,
    crossingCore_v1_mex hy hyq hql (by omega),
    crossingCore_diagonal_mex hy hyq hql (by omega)⟩
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## A critical arithmetic family for the interface frame -/

def FrameA (k : Nat) : Nat := 4 * k
def FrameAA (k : Nat) : Nat := 2 * k
def FrameT (k : Nat) : Nat := 6 * k + 3
def FrameV (k : Nat) : Nat := 10 * k + 4
def FrameY (k : Nat) : Nat := 10 * k - 2
def FrameQ (k : Nat) : Nat := 10 * k + 1
def FrameL (k : Nat) : Nat := 10 * k + 2

/-- An all-index counting-function interface family.  Up to `4k` it marks
the even values; afterwards it marks `4k+3j+1` for `1 <= j <= 2k`, and then
stops.  Thus it has no run of three marked values. -/
def FrameCount (k n : Nat) : Nat :=
  if n <= 4 * k then n / 2
  else 2 * k + min ((n - 4 * k - 1) / 3) (2 * k)

def FrameE (k n : Nat) : Int :=
  (FrameCount k (FrameCount k n) : Int) +
    2 * (FrameCount k n : Int) - (n : Int)

def FrameBlocker (k n : Nat) : Prop :=
  FrameCount k n = FrameCount k (n - 1) + 1

theorem frame_critical_identity (k : Nat) :
    FrameV k = 2 * FrameA k + FrameAA k + 4 := by
  simp [FrameV, FrameA, FrameAA]
  omega

theorem frame_crossing_row (k : Nat) :
    FrameT k = FrameV k - FrameA k - 1 := by
  simp [FrameT, FrameV, FrameA]
  omega

theorem frame_bad_overlap_ledger (k : Nat) :
    2 * FrameT k + 1 - FrameV k = FrameAA k + 3 := by
  simp [FrameT, FrameV, FrameAA]
  omega

theorem frame_E_minus_three (k : Nat) :
    (FrameAA k : Int) + 2 * (FrameA k : Int) - ((FrameV k - 1 : Nat) : Int)
      = -3 := by
  simp [FrameAA, FrameA, FrameV]
  omega

theorem frameCount_at_a (k : Nat) :
    FrameCount k (4 * k) = 2 * k := by
  simp only [FrameCount, if_pos (Nat.le_refl _)]
  rw [show 4 * k = (2 * k) * 2 by omega]
  exact Nat.mul_div_left (2 * k) (by decide)

theorem frameCount_at_final_prefix (k : Nat) (hk : 1 <= k) :
    FrameCount k (10 * k + 3) = 4 * k := by
  have hnot : Not (10 * k + 3 <= 4 * k) := by omega
  simp only [FrameCount, if_neg hnot]
  rw [show 10 * k + 3 - 4 * k - 1 = 6 * k + 2 by omega]
  rw [show (6 * k + 2) / 3 = 2 * k by omega]
  simp
  omega

theorem frame_v_is_range (k : Nat) (hk : 1 <= k) :
    FrameCount k (10 * k + 4) = FrameCount k (10 * k + 3) := by
  have hnot1 : Not (10 * k + 4 <= 4 * k) := by omega
  have hnot2 : Not (10 * k + 3 <= 4 * k) := by omega
  simp only [FrameCount, if_neg hnot1, if_neg hnot2]
  rw [show 10 * k + 4 - 4 * k - 1 = 6 * k + 3 by omega]
  rw [show (6 * k + 3) / 3 = 2 * k + 1 by omega]
  rw [show 10 * k + 3 - 4 * k - 1 = 6 * k + 2 by omega]
  rw [show (6 * k + 2) / 3 = 2 * k by omega]
  simp

theorem frameCount_at_previous_critical (k : Nat) (hk : 1 <= k) :
    FrameCount k (10 * k) = 4 * k - 1 := by
  have hnot : Not (10 * k <= 4 * k) := by omega
  simp only [FrameCount, if_neg hnot]
  rw [show 10 * k - 4 * k - 1 = 6 * k - 1 by omega]
  rw [show (6 * k - 1) / 3 = 2 * k - 1 by omega]
  simp
  omega

theorem frame_q_is_blocker (k : Nat) (hk : 1 <= k) :
    FrameBlocker k (10 * k + 1) := by
  unfold FrameBlocker
  have hpred : 10 * k + 1 - 1 = 10 * k := by omega
  rw [hpred]
  have hnot1 : Not (10 * k + 1 <= 4 * k) := by omega
  have hnot2 : Not (10 * k <= 4 * k) := by omega
  simp only [FrameCount, if_neg hnot1, if_neg hnot2]
  rw [show 10 * k + 1 - 4 * k - 1 = 6 * k by omega]
  rw [show (6 * k) / 3 = 2 * k by omega]
  rw [show 10 * k - 4 * k - 1 = 6 * k - 1 by omega]
  rw [show (6 * k - 1) / 3 = 2 * k - 1 by omega]
  simp
  omega

theorem frame_y_is_blocker (k : Nat) (hk : 2 <= k) :
    FrameBlocker k (10 * k - 2) := by
  unfold FrameBlocker
  have hnot1 : Not (10 * k - 2 <= 4 * k) := by omega
  have hnot2 : Not (10 * k - 3 <= 4 * k) := by omega
  have hpred : 10 * k - 2 - 1 = 10 * k - 3 := by omega
  rw [hpred]
  simp only [FrameCount, if_neg hnot1, if_neg hnot2]
  rw [show 10 * k - 2 - 4 * k - 1 = 6 * k - 3 by omega]
  rw [show (6 * k - 3) / 3 = 2 * k - 1 by omega]
  rw [show 10 * k - 3 - 4 * k - 1 = 6 * k - 4 by omega]
  rw [show (6 * k - 4) / 3 = 2 * k - 2 by omega]
  simp
  omega

theorem frame_E_previous_critical (k : Nat) (hk : 1 <= k) :
    FrameE k (10 * k) = -3 := by
  simp only [FrameE]
  rw [frameCount_at_previous_critical k hk]
  rw [show FrameCount k (4 * k - 1) = 2 * k - 1 by
    have hle : 4 * k - 1 <= 4 * k := by omega
    simp only [FrameCount, if_pos hle]
    rw [show 4 * k - 1 = 2 * (2 * k - 1) + 1 by omega]
    omega]
  simp
  omega

theorem frame_E_final_critical (k : Nat) (hk : 1 <= k) :
    FrameE k (10 * k + 3) = -3 := by
  simp only [FrameE]
  rw [frameCount_at_final_prefix k hk]
  rw [frameCount_at_a]
  simp
  omega

/-- The owner-`t-2` DROP frame can be instantiated at arbitrarily large
critical coordinates while all named top values remain live and ordered. -/
theorem parametric_owner_two_drop_frame (k : Nat) (hk : 2 <= k) :
    FrameT k < FrameY k /\
    FrameY k < FrameQ k /\
    FrameQ k < FrameL k /\
    IsMex (PrevSource (FrameQ k) (FrameL k)) (FrameQ k) /\
    IsMex
      (fun z => PrevSource (FrameQ k) (FrameL k) z \/ z = FrameQ k)
      (FrameL k) /\
    CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k) (FrameL k)
      (FrameL k + 1) /\
    IsMex
      (fun z => CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k)
        (FrameL k) z \/ z = FrameQ k)
      (FrameY k) /\
    IsMex
      (fun z => CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k)
        (FrameL k) z \/ z = FrameL k \/ z = FrameY k)
      (FrameQ k) /\
    IsMex
      (fun z => CrossingCore (FrameL k + 2) (FrameY k) (FrameQ k)
        (FrameL k) z \/ z = FrameL k \/ z = FrameY k \/ z = FrameQ k)
      (FrameL k + 2) := by
  have hty : FrameT k < FrameY k := by
    simp [FrameT, FrameY]
    omega
  have hy : 0 < FrameY k := by
    simp [FrameY]
    omega
  have hyq : FrameY k < FrameQ k := by
    simp [FrameY, FrameQ]
    omega
  have hql : FrameQ k < FrameL k := by
    simp [FrameQ, FrameL]
  have hx : 0 < FrameQ k := by omega
  have hframe := owner_two_bad_crossing_frame
    (x := FrameQ k) (y := FrameY k) (q := FrameQ k) (l := FrameL k)
    hx hql (by omega) hy hyq hql
  exact ⟨hty, hyq, hql, hframe.1, hframe.2.1, hframe.2.2.1,
    hframe.2.2.2.1, hframe.2.2.2.2.1, hframe.2.2.2.2.2⟩

#print axioms crossing_skip_iff_strict_row_host
#print axioms bad_diagonal_forbids_later_frontier_host
#print axioms owner_one_bad_crossing_frame
#print axioms owner_two_bad_crossing_frame
#print axioms parametric_owner_two_drop_frame

end ChompLean
