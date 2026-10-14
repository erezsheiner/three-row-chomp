import R146FinalHoleTripleTailUnification
import R147BackwardHistoryGraftObstruction

set_option autoImplicit false

namespace ChompLean

/-!
R148c: the freeze-cross incidence inequality.

If the freeze column of an earlier blocker `bh` carries a later blocker `bi`,
the occurrence is strictly before row `bh`.  CellCeiling therefore gives the
sharp reach condition `bi <= bh + ch`.  BIJ/PiZero count how many such
earlier-frozen loads are required.  Under FreezeOrder the reachable ranks are
a suffix, and the cardinal inequality becomes a one-point recurrence.

The last section checks both sides of the audit on the R141/R146 `A_k` word:
the repaired low endpoint `c_q=t` violates the recurrence for all `k>=10`,
whereas a high-freeze tail `c_i=2i-2` has one predecessor load at every late
rank and survives the incidence interface.
-/

/-! ## Pointwise reach and the exact capacity inequality -/

/-- Sharp CellCeiling consequence for a load occurring before the earlier
column freezes.  In the game application `row<bh` follows from persistence of
the freeze value in column `ch` from row `bh` onward. -/
theorem earlierFreezeLoad_reach
    {bi bh ch row : Nat}
    (hrow : row < bh)
    (hCellCeiling : bi <= row + ch + 1) :
    bi <= bh + ch := by
  omega

/-- PiZero/BIJ ledger in subtraction-free form.  In the application

`loaded = kappa_i` and
`c_i + L_i + kappa_i = 2*i-1`.

The separately proved pointwise reach lemma injects those `loaded` columns
into the `reachable` earlier columns, giving `loaded<=reachable`.  The
theorem below is the subtraction-free cardinal conclusion. -/
theorem pizero_loaded_capacity
    {i ci Li loaded reachable : Nat}
    (hPiZero : ci + Li + loaded = 2 * i - 1)
    (hInjection : loaded <= reachable) :
    ci + Li + reachable >= 2 * i - 1 := by
  omega

/-! ## FreezeOrder: suffix capacity becomes a scalar recurrence -/

/-- Arithmetic heart of the ordered recurrence.  If reachable prior ranks
form the suffix `[tau,i)`, its capacity is `i-tau`.  PiZero says the required
load is `kappa=2i-1-c`.  Hence the suffix must start no later than
`p=c-i+1`. -/
theorem orderedReach_threshold_le_p
    {i ci kappa tau : Nat}
    (hi : 1 <= i)
    (hpDefined : i <= ci)
    (hTau : tau <= i)
    (hPiZero : ci + kappa = 2 * i - 1)
    (hCapacity : kappa <= i - tau) :
    tau <= ci - i + 1 := by
  omega

/-- One-point form of the incidence recurrence.  Under FreezeOrder,
`s_h=b_h+c_h` is strictly increasing.  If `tau` is the first reachable rank,
then PiZero capacity forces

`b_i <= b_(c_i-i+1) + c_(c_i-i+1)`.

The hypotheses expose the exact logical load: `hPiZero` has `L_i=0`, hence
this theorem is conditional on FreezeOrder (or an independently supplied
zero-inversion statement). -/
theorem orderedFreezeCross_recurrence
    (s : Nat -> Nat) {bi i ci kappa tau : Nat}
    (hi : 1 <= i)
    (hpDefined : i <= ci)
    (hTau : tau <= i)
    (hPiZero : ci + kappa = 2 * i - 1)
    (hCapacity : kappa <= i - tau)
    (hsMono : forall {a b}, a <= b -> s a <= s b)
    (hFirstReach : bi <= s tau) :
    bi <= s (ci - i + 1) := by
  have htp := orderedReach_threshold_le_p hi hpDefined hTau hPiZero hCapacity
  exact Nat.le_trans hFirstReach (hsMono htp)

/-! ## The repaired R146 low endpoint is impossible -/

/-- At the repaired endpoint `c_q=t=6k+3`, the recurrence probes rank
`p=c_q-4k+1=2k+4`, i.e. the fourth late blocker. -/
theorem r146_repaired_endpoint_probe_rank (k : Nat) :
    r146FinalFreeze k - 4 * k + 1 = 2 * k + 4 := by
  simp [r146FinalFreeze, FrameT]
  omega

/-- Even allowing the probed earlier freeze column its full PiZero ceiling
`c_p<=2p-1`, its reach is below `q=10k+1` for `k>=10`.  Consequently the
ordered scalar recurrence contradicts the repaired endpoint `c_q=t` on an
unbounded tail. -/
theorem r146_repaired_endpoint_breaks_freezeCross
    (k cp : Nat) (hk : 10 <= k)
    (hPiZeroCap : cp <= 2 * (2 * k + 4) - 1)
    (hRecurrence : FrameQ k <= r146LateBlocker k 4 + cp) :
    False := by
  simp [FrameQ, r146LateBlocker] at hRecurrence
  omega

/-- For the literal prior schedule printed in R146, the failure begins even
earlier, at `k=6`.  The preceding theorem is stronger logically because it
permits an arbitrary prior column up to the universal PiZero cap. -/
theorem r146_displayed_schedule_breaks_freezeCross
    (k : Nat) (hk : 6 <= k) :
    Not (FrameQ k <=
      r146LateBlocker k 4 + r146LateFreeze k 4) := by
  simp [FrameQ, r146LateBlocker, r146LateFreeze]
  omega

/-! ## A high-freeze tail survives -/

/-- A PiZero-compatible high schedule with exactly one earlier-frozen load
per blocker rank. -/
def R148HighFreeze (i : Nat) : Nat := 2 * i - 2

theorem highFreeze_pizero_one_load
    {i : Nat} (hi : 1 <= i) :
    R148HighFreeze i + 1 = 2 * i - 1 := by
  simp [R148HighFreeze]
  omega

theorem highFreeze_strict
    {i j : Nat} (hi : 1 <= i) (hij : i < j) :
    R148HighFreeze i < R148HighFreeze j := by
  simp only [R148HighFreeze]
  omega

/-- The transition from the last early blocker to the first late blocker can
use the predecessor freeze column. -/
theorem highFreeze_firstLate_predecessor_reaches
    (k : Nat) (hk : 2 <= k) :
    r146LateBlocker k 1 <=
      r146EarlyBlocker (2 * k) + R148HighFreeze (2 * k) := by
  simp [r146LateBlocker, r146EarlyBlocker, R148HighFreeze]
  omega

/-- Every subsequent late blocker can likewise use its immediate predecessor
column.  Thus the complete late tail, not only the critical endpoint, meets
the new incidence requirement with `kappa=1`. -/
theorem highFreeze_late_predecessor_reaches
    (k j : Nat) (hk : 2 <= k) (hj : 2 <= j) :
    r146LateBlocker k j <=
      r146LateBlocker k (j - 1) +
        R148HighFreeze (r146LateRank k (j - 1)) := by
  simp [r146LateBlocker, r146LateRank, R148HighFreeze]
  omega

/-- At the critical final blocker, the high schedule satisfies PiZero with
one prior-freeze load, the banked `5c>=3b-1` floor, the future-hole deadline,
and the predecessor reach inequality. -/
theorem highFreeze_critical_frame_survives
    (k : Nat) (hk : 4 <= k) :
    let i := 4 * k
    let cq := R148HighFreeze i
    cq + 1 = 2 * i - 1 /\
    FrameT k <= cq /\
    3 * FrameQ k - 1 <= 5 * cq /\
    FrameQ k <=
      r146LateBlocker k (2 * k - 1) +
        R148HighFreeze (i - 1) := by
  dsimp [R148HighFreeze]
  simp [FrameT, FrameQ, r146LateBlocker]
  omega

/-- BIJ count at the high critical schedule: `i-1` live-left columns plus
the single predecessor frozen load give exactly `i` loaded columns. -/
theorem highFreeze_critical_bij_count
    (k : Nat) (hk : 1 <= k) :
    let i := 4 * k
    let cq := R148HighFreeze i
    cq - (i - 1) = i - 1 /\
    (cq - (i - 1)) + 1 = i := by
  dsimp [R148HighFreeze]
  omega

/-! ## Coupling the high endpoint to the R147 target histories -/

def R148TargetCol (k j : Nat) : Nat := r147C0 k + j
def R148QHostRow (k j : Nat) : Nat := R148TargetCol k j + 1

/-- Three explicit pre-freeze hosts for the final blocker.  They lie in
different rows and columns, are correctly oriented column-history witnesses,
satisfy CellCeiling with room to spare, and all lie before the final freeze
row. -/
theorem highFreeze_target_q_host_geometry
    (k j : Nat) (hk : 5 <= k) (hj : j <= 2) :
    R148TargetCol k j < R148QHostRow k j /\
    R148QHostRow k j < FrameQ k /\
    FrameQ k <= R148QHostRow k j + R148TargetCol k j + 1 /\
    R148TargetCol k j < R148HighFreeze (4 * k) := by
  simp [R148TargetCol, R148QHostRow, r147C0, FrameQ,
    R148HighFreeze]
  omega

theorem highFreeze_target_q_hosts_distinct
    (k i j : Nat) (hij : i < j) :
    R148TargetCol k i < R148TargetCol k j /\
    R148QHostRow k i < R148QHostRow k j := by
  simp [R148TargetCol, R148QHostRow, r147C0]
  omega

/-- The additive packet already covers `q` in its low base interval.  Adding
the three genuine q-column histories therefore changes no MEX equation: they
duplicate an existing source label. -/
theorem r147_additive_source_already_covers_final_blocker
    (k n j : Nat) :
    R147AddSource (r147SeedM k) n j (FrameQ k) := by
  left
  simp [r147SeedM, FrameQ]
  omega

/-! A frozen target column cannot itself realize a later additive MEX cell.
It remains on the carry branch and keeps its own freeze value.  Thus source
membership of `q` is insufficient: all three R147 target columns must be
nonfreezing if all three displayed additive outputs are to exist. -/

theorem frozenTarget_cannot_emit_later_additive
    (M : RecurrenceModel) {freezeValue col targetRow additive : Nat}
    (hcol : col < freezeValue)
    (hfreeze : M.f freezeValue col = freezeValue)
    (hafter : freezeValue <= targetRow)
    (hne : additive ≠ freezeValue) :
    M.f targetRow col ≠ additive := by
  intro hout
  have hconst := constant_from M hcol (by rw [hfreeze]; omega)
      (targetRow - freezeValue)
  have hidx : freezeValue + (targetRow - freezeValue) = targetRow := by
    omega
  rw [hidx] at hconst
  exact hne (hout.symm.trans (hconst.trans hfreeze))

/-! The actual repair removes every target from the earlier freeze set.  It
creates a run of three nonfreezing columns, so it is valid only against the
current bank: NO-THREE-LIVE is a finite receipt/open law, not a theorem. -/

theorem evenTarget_allLive_surgery
    (m : Nat) (hm : 2 <= m) :
    let h := 7 * m + 1
    let leftCol := 14 * m - 1
    let rightCol := 14 * m + 3
    (2 * (h - 1) - 2 < leftCol) /\
    (leftCol < 14 * m) /\
    (14 * m + 2 < rightCol) /\
    (rightCol < 2 * (h + 2) - 2) /\
    (leftCol + 2 = 2 * h - 1) /\
    (rightCol = 2 * (h + 1) - 1) /\
    r146LateBlocker (2 * m) (3 * m + 1) <=
      r146LateBlocker (2 * m) (3 * m) + (14 * m - 2) /\
    r146LateBlocker (2 * m) (3 * m + 1) <=
      r146LateBlocker (2 * m) (3 * m - 1) + (14 * m - 4) := by
  dsimp
  simp [r146LateBlocker]
  omega

theorem oddTarget_allLive_surgery
    (m : Nat) (hm : 2 <= m) :
    let h := 7 * m + 5
    let leftCol := 14 * m + 5
    let rightCol := 14 * m + 6
    (2 * (h - 2) - 2 < leftCol) /\
    (leftCol < rightCol) /\
    (rightCol < 14 * m + 7) /\
    (14 * m + 9 < 2 * (h + 1) - 2) /\
    (leftCol + 2 = 2 * (h - 1) - 1) /\
    (rightCol + 3 = 2 * h - 1) /\
    r146LateBlocker (2 * m + 1) (3 * m + 2) <=
      r146LateBlocker (2 * m + 1) (3 * m + 1) + (14 * m + 4) /\
    r146LateBlocker (2 * m + 1) (3 * m + 2) <=
      r146LateBlocker (2 * m + 1) (3 * m) + (14 * m + 2) /\
    r146LateBlocker (2 * m + 1) (3 * m + 3) <=
      r146LateBlocker (2 * m + 1) (3 * m + 2) + leftCol /\
    r146LateBlocker (2 * m + 1) (3 * m + 3) <=
      r146LateBlocker (2 * m + 1) (3 * m + 1) + (14 * m + 4) /\
    r146LateBlocker (2 * m + 1) (3 * m + 3) <=
      r146LateBlocker (2 * m + 1) (3 * m) + (14 * m + 2) := by
  dsimp
  simp [r146LateBlocker]
  omega

#print axioms earlierFreezeLoad_reach
#print axioms pizero_loaded_capacity
#print axioms orderedFreezeCross_recurrence
#print axioms r146_repaired_endpoint_breaks_freezeCross
#print axioms highFreeze_critical_frame_survives
#print axioms highFreeze_target_q_host_geometry
#print axioms r147_additive_source_already_covers_final_blocker
#print axioms frozenTarget_cannot_emit_later_additive
#print axioms evenTarget_allLive_surgery
#print axioms oddTarget_allLive_surgery

end ChompLean
